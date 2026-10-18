/*
 * uka_regexp.cpp - a small backtracking regular expression engine for wchar_t strings.
 *
 * Overview
 *   pattern --(Compiler: parser)--> syntax tree --(Compiler: code generator)--> int code
 *   subject --(Matcher: backtracking VM with an explicit stack)--> captures
 *
 * Everything the matcher changes (captures, loop counters, ...) lives in one int array and every
 * change is recorded on the backtrack stack, so failing simply pops the stack and restores state.
 * No recursion is used while matching, so long subjects cannot overflow the C stack.
 *
 * Kept deliberately plain (C++98, no STL, simple templates) so that old compilers can build it.
 * Loop variables are declared outside of for() because VC6 leaks their scope.
 */
#include "uka_regexp.h"

#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------------------------ */
/* CRegexpException / CRegexpString                                                            */
/* ------------------------------------------------------------------------------------------ */

CRegexpException::CRegexpException(int code, int position, const char* message)
    : m_code(code), m_pos(position)
{
    int i = 0;
    while (message[i] != 0 && i < (int)sizeof(m_msg) - 1) {
        m_msg[i] = message[i];
        ++i;
    }
    m_msg[i] = 0;
}

static const wchar_t g_emptyWide[1] = { 0 };

CRegexpString::CRegexpString() : m_buf(0), m_len(0), m_cap(0) {}

CRegexpString::~CRegexpString() { free(m_buf); }

const wchar_t* CRegexpString::c_str() const { return m_buf ? m_buf : g_emptyWide; }

void CRegexpString::clear()
{
    m_len = 0;
    if (m_buf) m_buf[0] = 0;
}

void CRegexpString::Reserve(int n)   /* room for n characters plus the terminator */
{
    if (n + 1 <= m_cap) return;
    int cap = m_cap ? m_cap : 32;
    while (cap < n + 1) cap *= 2;
    wchar_t* p = (wchar_t*)realloc(m_buf, sizeof(wchar_t) * cap);
    if (!p) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
    m_buf = p;
    m_cap = cap;
}

void CRegexpString::append(const wchar_t* s, int n)
{
    if (n <= 0) return;
    Reserve(m_len + n);
    memcpy(m_buf + m_len, s, sizeof(wchar_t) * n);
    m_len += n;
    m_buf[m_len] = 0;
}

void CRegexpString::push_back(wchar_t c)
{
    Reserve(m_len + 1);
    m_buf[m_len++] = c;
    m_buf[m_len] = 0;
}

namespace UkaRegexpImpl {

typedef unsigned int Cp;   /* a code point */

static int WLen(const wchar_t* s)
{
    int n = 0;
    while (s[n]) ++n;
    return n;
}

/* A growable array of plain-old-data elements. */
template <class T>
class Vec {
public:
    Vec() : m_p(0), m_n(0), m_cap(0) {}
    ~Vec() { free(m_p); }
    int Size() const { return m_n; }
    bool Empty() const { return m_n == 0; }
    T& operator[](int i) { return m_p[i]; }
    const T& operator[](int i) const { return m_p[i]; }
    T& Back() { return m_p[m_n - 1]; }
    T* Data() { return m_p; }
    const T* Data() const { return m_p; }
    void Clear() { m_n = 0; }
    void Pop() { --m_n; }
    void Resize(int n)   /* new elements are uninitialised */
    {
        if (n > m_cap) Reserve(n);
        m_n = n;
    }
    void Push(const T& v)
    {
        T tmp = v;   /* v may live inside this array */
        if (m_n == m_cap) Reserve(m_n + 1);
        m_p[m_n++] = tmp;
    }
    void Reserve(int n)
    {
        if (n <= m_cap) return;
        int cap = m_cap ? m_cap * 2 : 16;
        while (cap < n) cap *= 2;
        T* p = (T*)realloc(m_p, sizeof(T) * cap);
        if (!p) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
        m_p = p;
        m_cap = cap;
    }
private:
    Vec(const Vec&);
    Vec& operator=(const Vec&);
    T* m_p;
    int m_n;
    int m_cap;
};

/* ------------------------------------------------------------------------------------------ */
/* Unicode data (the tables are generated; the functions are at the end of this file)          */
/* ------------------------------------------------------------------------------------------ */

enum {   /* general categories; the order must match tools/gen_unicode_tables.py */
    CAT_Cn, CAT_Cc, CAT_Cf, CAT_Co, CAT_Cs, CAT_Ll, CAT_Lm, CAT_Lo, CAT_Lt, CAT_Lu,
    CAT_Mc, CAT_Me, CAT_Mn, CAT_Nd, CAT_Nl, CAT_No, CAT_Pc, CAT_Pd, CAT_Pe, CAT_Pf,
    CAT_Pi, CAT_Po, CAT_Ps, CAT_Sc, CAT_Sk, CAT_Sm, CAT_So, CAT_Zl, CAT_Zp, CAT_Zs,
    CAT_COUNT
};

struct CaseRange { unsigned int lo; unsigned int hi; int step; int delta; };

extern const unsigned int g_catRuns[];
extern const int g_catRunsCount;
extern const CaseRange g_foldTable[];
extern const int g_foldTableCount;
extern const CaseRange g_upperTable[];
extern const int g_upperTableCount;
extern const CaseRange g_lowerTable[];
extern const int g_lowerTableCount;

int UcCategory(Cp c);      /* 0..CAT_COUNT-1 */
Cp UcFold(Cp c);           /* simple case folding: equal folds mean equal ignoring case */
Cp UcUpper(Cp c);
Cp UcLower(Cp c);
bool UcHasCaseVariants(Cp c);

/* ------------------------------------------------------------------------------------------ */
/* Compiled program                                                                            */
/* ------------------------------------------------------------------------------------------ */

enum {
    OP_MATCH = 1,
    OP_CHAR,          /* c */
    OP_CHARI,         /* folded c */
    OP_ANY,           /* any character but \n */
    OP_ANYNL,         /* any character */
    OP_CLASS,         /* class index */
    OP_BOL, OP_MBOL, OP_EOL, OP_MEOL, OP_BOS, OP_EOS, OP_EOSNL,
    OP_WORDB, OP_NWORDB, OP_GPOS,
    OP_KEEP,          /* \K */
    OP_JMP,           /* target */
    OP_SPLIT,         /* first, second: try first, remember second */
    OP_OPEN,          /* group */
    OP_CLOSE,         /* group */
    OP_CLOSEBAL,      /* group (0: none), popped group: .NET balancing group */
    OP_BACKREF,       /* group */
    OP_BACKREFI,      /* group */
    OP_ATOMIC_BEGIN,
    OP_ATOMIC_END,
    OP_LOOK_BEGIN,    /* pc to continue at when the assertion body fails (-1: keep failing) */
    OP_LB_BEGIN,      /* fail pc, min length, max length (-1: unbounded) */
    OP_LB_CHECK,      /* lookbehind body must end where the lookbehind started */
    OP_LOOK_OK_CUT,   /* assertion body matched: keep captures, drop alternatives, restore position */
    OP_LOOK_OK_FAIL,  /* negative assertion body matched: undo everything and fail */
    OP_LOOK_OK_JUMP,  /* negative condition body matched: undo everything and jump */
    OP_REP,           /* mode, min, max, atom op, atom arg: repeat of a single character matcher */
    OP_LOOP_INIT,     /* loop id */
    OP_LOOP_TEST,     /* id, min, max, lazy, exit pc */
    OP_LOOP_BODY,     /* id */
    OP_LOOP_END,      /* id, min, max, test pc */
    OP_COND_GROUP,    /* group, else pc */
    OP_CALL           /* group, target pc: subroutine call / recursion */
};

enum { REP_GREEDY = 0, REP_LAZY = 1, REP_POSSESSIVE = 2 };

struct Range { int lo; int hi; };

struct ClassProp {       /* a \p{..} item inside a character class */
    unsigned int mask;   /* bit per general category */
    unsigned int extra;  /* EX_* flags */
    int neg;
};

struct CharClass {
    unsigned int bitmap[8];   /* membership of code points below 256 (before negation) */
    int rbeg, rcnt;           /* sorted ranges of code points >= 256 in Program::ranges */
    int pbeg, pcnt;           /* property items in Program::props */
    int negate;
};

struct NameEnt { int off; int group; };

struct Program {
    Vec<int> code;
    Vec<CharClass> classes;
    Vec<Range> ranges;
    Vec<ClassProp> props;
    Vec<wchar_t> namePool;    /* NUL terminated names */
    Vec<NameEnt> names;
    Vec<char> balTarget;      /* per group: keep a capture history for .NET balancing groups */
    int ngroups;
    int nloops;
    int global;
    int anchored;             /* a match can only start at the search start */
    int firstChar;            /* a match must start with this character, or -1 */

    Program() : ngroups(0), nloops(0), global(0), anchored(0), firstChar(-1) {}
private:
    Program(const Program&);
    Program& operator=(const Program&);
};

/* ------------------------------------------------------------------------------------------ */
/* Character sets                                                                              */
/* ------------------------------------------------------------------------------------------ */

#define ARRAY_COUNT(a) ((int)(sizeof(a) / sizeof((a)[0])))
#define MAX_CP 0x10FFFF

static const Range kDigit[]  = { {'0', '9'} };
static const Range kWord[]   = { {'0', '9'}, {'A', 'Z'}, {'_', '_'}, {'a', 'z'} };
static const Range kSpace[]  = { {9, 13}, {32, 32} };
static const Range kHSpace[] = { {9, 9}, {32, 32}, {0xA0, 0xA0}, {0x1680, 0x1680}, {0x2000, 0x200A},
                                 {0x202F, 0x202F}, {0x205F, 0x205F}, {0x3000, 0x3000} };

static const Range kAlpha[]  = { {'A', 'Z'}, {'a', 'z'} };
static const Range kAlnum[]  = { {'0', '9'}, {'A', 'Z'}, {'a', 'z'} };
static const Range kAscii[]  = { {0, 127} };
static const Range kBlank[]  = { {9, 9}, {32, 32} };
static const Range kCntrl[]  = { {0, 31}, {127, 127} };
static const Range kGraph[]  = { {33, 126} };
static const Range kLower[]  = { {'a', 'z'} };
static const Range kPrint[]  = { {32, 126} };
static const Range kPunct[]  = { {33, 47}, {58, 64}, {91, 96}, {123, 126} };
static const Range kUpper[]  = { {'A', 'Z'} };
static const Range kXdigit[] = { {'0', '9'}, {'A', 'F'}, {'a', 'f'} };

struct PosixDef {
    const char* name;
    const Range* r;
    int n;
    int caseSensitive;   /* [:upper:] and [:lower:] follow the ignore-case flag like literals do */
};

static const PosixDef kPosix[] = {
    { "alnum",  kAlnum,  ARRAY_COUNT(kAlnum),  0 },
    { "alpha",  kAlpha,  ARRAY_COUNT(kAlpha),  0 },
    { "ascii",  kAscii,  ARRAY_COUNT(kAscii),  0 },
    { "blank",  kBlank,  ARRAY_COUNT(kBlank),  0 },
    { "cntrl",  kCntrl,  ARRAY_COUNT(kCntrl),  0 },
    { "digit",  kDigit,  ARRAY_COUNT(kDigit),  0 },
    { "graph",  kGraph,  ARRAY_COUNT(kGraph),  0 },
    { "lower",  kLower,  ARRAY_COUNT(kLower),  1 },
    { "print",  kPrint,  ARRAY_COUNT(kPrint),  0 },
    { "punct",  kPunct,  ARRAY_COUNT(kPunct),  0 },
    { "space",  kSpace,  ARRAY_COUNT(kSpace),  0 },
    { "upper",  kUpper,  ARRAY_COUNT(kUpper),  1 },
    { "word",   kWord,   ARRAY_COUNT(kWord),   0 },
    { "xdigit", kXdigit, ARRAY_COUNT(kXdigit), 0 }
};

/* \p{..} */
enum {
    EX_ASCII = 1,        /* U+0000..U+007F */
    EX_WHITE = 2,        /* Unicode White_Space */
    EX_JOIN = 4,         /* U+200C, U+200D */
    EX_UNDERSCORE = 8,
    EX_PSP = 16          /* TAB, LF, VT, FF, CR */
};

#define CATBIT(c) (1u << (c))
#define MASK_ALL      ((1u << CAT_COUNT) - 1u)
#define MASK_LC       (CATBIT(CAT_Ll) | CATBIT(CAT_Lt) | CATBIT(CAT_Lu))
#define MASK_L        (MASK_LC | CATBIT(CAT_Lm) | CATBIT(CAT_Lo))
#define MASK_M        (CATBIT(CAT_Mc) | CATBIT(CAT_Me) | CATBIT(CAT_Mn))
#define MASK_N        (CATBIT(CAT_Nd) | CATBIT(CAT_Nl) | CATBIT(CAT_No))
#define MASK_P        (CATBIT(CAT_Pc) | CATBIT(CAT_Pd) | CATBIT(CAT_Pe) | CATBIT(CAT_Pf) | \
                       CATBIT(CAT_Pi) | CATBIT(CAT_Po) | CATBIT(CAT_Ps))
#define MASK_S        (CATBIT(CAT_Sc) | CATBIT(CAT_Sk) | CATBIT(CAT_Sm) | CATBIT(CAT_So))
#define MASK_Z        (CATBIT(CAT_Zl) | CATBIT(CAT_Zp) | CATBIT(CAT_Zs))
#define MASK_C        (CATBIT(CAT_Cc) | CATBIT(CAT_Cf) | CATBIT(CAT_Cn) | CATBIT(CAT_Co) | CATBIT(CAT_Cs))

struct PropName { const char* name; unsigned int mask; unsigned int extra; };

static const PropName kPropNames[] = {
    { "L", MASK_L, 0 }, { "L&", MASK_LC, 0 }, { "LC", MASK_LC, 0 },
    { "M", MASK_M, 0 }, { "N", MASK_N, 0 }, { "P", MASK_P, 0 },
    { "S", MASK_S, 0 }, { "Z", MASK_Z, 0 }, { "C", MASK_C, 0 },
    { "Cn", CATBIT(CAT_Cn), 0 }, { "Cc", CATBIT(CAT_Cc), 0 }, { "Cf", CATBIT(CAT_Cf), 0 },
    { "Co", CATBIT(CAT_Co), 0 }, { "Cs", CATBIT(CAT_Cs), 0 },
    { "Ll", CATBIT(CAT_Ll), 0 }, { "Lm", CATBIT(CAT_Lm), 0 }, { "Lo", CATBIT(CAT_Lo), 0 },
    { "Lt", CATBIT(CAT_Lt), 0 }, { "Lu", CATBIT(CAT_Lu), 0 },
    { "Mc", CATBIT(CAT_Mc), 0 }, { "Me", CATBIT(CAT_Me), 0 }, { "Mn", CATBIT(CAT_Mn), 0 },
    { "Nd", CATBIT(CAT_Nd), 0 }, { "Nl", CATBIT(CAT_Nl), 0 }, { "No", CATBIT(CAT_No), 0 },
    { "Pc", CATBIT(CAT_Pc), 0 }, { "Pd", CATBIT(CAT_Pd), 0 }, { "Pe", CATBIT(CAT_Pe), 0 },
    { "Pf", CATBIT(CAT_Pf), 0 }, { "Pi", CATBIT(CAT_Pi), 0 }, { "Po", CATBIT(CAT_Po), 0 },
    { "Ps", CATBIT(CAT_Ps), 0 },
    { "Sc", CATBIT(CAT_Sc), 0 }, { "Sk", CATBIT(CAT_Sk), 0 }, { "Sm", CATBIT(CAT_Sm), 0 },
    { "So", CATBIT(CAT_So), 0 },
    { "Zl", CATBIT(CAT_Zl), 0 }, { "Zp", CATBIT(CAT_Zp), 0 }, { "Zs", CATBIT(CAT_Zs), 0 },
    { "Any", MASK_ALL, 0 },
    { "Assigned", MASK_ALL & ~CATBIT(CAT_Cn), 0 },
    { "ASCII", 0, EX_ASCII },
    { "White_Space", 0, EX_WHITE }, { "Space", 0, EX_WHITE },
    { "Word", MASK_L | MASK_M | CATBIT(CAT_Nd) | CATBIT(CAT_Nl) | CATBIT(CAT_Pc), EX_JOIN },
    { "Xan", MASK_L | MASK_N, 0 },
    { "Xwd", MASK_L | MASK_N, EX_UNDERSCORE },
    { "Xsp", MASK_Z, EX_PSP }, { "Xps", MASK_Z, EX_PSP }
};

static bool IsUniWhite(Cp c)
{
    return (c >= 9 && c <= 13) || c == 32 || c == 0x85 || c == 0xA0 || c == 0x1680 ||
           (c >= 0x2000 && c <= 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F ||
           c == 0x205F || c == 0x3000;
}

static bool PropMatch(const ClassProp& p, Cp c)
{
    bool r = false;
    if ((p.mask >> UcCategory(c)) & 1u) {
        r = true;
    } else if (p.extra) {
        if ((p.extra & EX_ASCII) && c < 128) r = true;
        else if ((p.extra & EX_WHITE) && IsUniWhite(c)) r = true;
        else if ((p.extra & EX_JOIN) && (c == 0x200C || c == 0x200D)) r = true;
        else if ((p.extra & EX_UNDERSCORE) && c == '_') r = true;
        else if ((p.extra & EX_PSP) && c >= 9 && c <= 13) r = true;
    }
    return r != (p.neg != 0);
}

static int CmpRange(const void* a, const void* b)
{
    const Range* x = (const Range*)a;
    const Range* y = (const Range*)b;
    if (x->lo != y->lo) return x->lo < y->lo ? -1 : 1;
    if (x->hi != y->hi) return x->hi < y->hi ? -1 : 1;
    return 0;
}

/* sort and merge overlapping or adjacent ranges */
static void NormalizeRanges(Vec<Range>& v)
{
    int n = v.Size();
    int i, w;
    if (n < 2) return;
    qsort(v.Data(), n, sizeof(Range), CmpRange);
    w = 0;
    for (i = 1; i < n; ++i) {
        if (v[i].lo <= v[w].hi + 1) {
            if (v[i].hi > v[w].hi) v[w].hi = v[i].hi;
        } else {
            ++w;
            v[w] = v[i];
        }
    }
    v.Resize(w + 1);
}

static bool InRanges(const Range* r, int n, Cp c)
{
    int lo = 0, hi = n - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (c < (Cp)r[mid].lo) hi = mid - 1;
        else if (c > (Cp)r[mid].hi) lo = mid + 1;
        else return true;
    }
    return false;
}

static void AddRange(Vec<Range>& v, int lo, int hi)
{
    Range r;
    r.lo = lo;
    r.hi = hi;
    v.Push(r);
}

/* add the complement of the sorted, non-overlapping ranges src */
static void AddComplement(Vec<Range>& dst, const Range* src, int n)
{
    int cur = 0, i;
    for (i = 0; i < n; ++i) {
        if (src[i].lo > cur) AddRange(dst, cur, src[i].lo - 1);
        cur = src[i].hi + 1;
    }
    if (cur <= MAX_CP) AddRange(dst, cur, MAX_CP);
}

static void AddSet(Vec<Range>& dst, const Range* src, int n, bool negated)
{
    int i;
    if (negated) {
        AddComplement(dst, src, n);
    } else {
        for (i = 0; i < n; ++i) dst.Push(src[i]);
    }
}

/* Make the (normalised) ranges also contain the other case variants of every member. */
static void ExpandCase(Vec<Range>& r)
{
    Vec<Range> add;
    int i;
    Cp c;
    for (i = 0; i < g_foldTableCount; ++i) {   /* members -> their folded form */
        const CaseRange& e = g_foldTable[i];
        for (c = e.lo; c <= e.hi; c += (Cp)e.step) {
            if (InRanges(r.Data(), r.Size(), c)) {
                Cp f = (Cp)((int)c + e.delta);
                AddRange(add, (int)f, (int)f);
            }
        }
    }
    for (i = 0; i < add.Size(); ++i) r.Push(add[i]);
    NormalizeRanges(r);
    add.Clear();
    for (i = 0; i < g_foldTableCount; ++i) {   /* folded form -> every character folding to it */
        const CaseRange& e = g_foldTable[i];
        for (c = e.lo; c <= e.hi; c += (Cp)e.step) {
            Cp f = (Cp)((int)c + e.delta);
            if (InRanges(r.Data(), r.Size(), f)) AddRange(add, (int)c, (int)c);
        }
    }
    for (i = 0; i < add.Size(); ++i) r.Push(add[i]);
    NormalizeRanges(r);
}

/* a character class under construction */
struct ClassBuilder {
    Vec<Range> lit;        /* literal characters and ranges (follow the ignore-case flag) */
    Vec<Range> esc;        /* \d \w [:alpha:] ... (never case-expanded) */
    Vec<ClassProp> props;
    int negate;
    int icase;
    ClassBuilder() : negate(0), icase(0) {}
};

/* Turn the builder into a CharClass of the program; returns its index. */
static int FinishClass(Program& prog, ClassBuilder& cb)
{
    Vec<Range> all;
    CharClass cc;
    int i, c;

    NormalizeRanges(cb.lit);
    if (cb.icase) {
        ExpandCase(cb.lit);
        for (i = 0; i < cb.props.Size(); ++i) {   /* \p{Lu} etc. match every cased letter when ignoring case */
            ClassProp& p = cb.props[i];
            if ((p.mask & MASK_LC) != 0 && (p.mask & ~MASK_LC) == 0 && p.extra == 0) p.mask = MASK_LC;
        }
    }
    for (i = 0; i < cb.lit.Size(); ++i) all.Push(cb.lit[i]);
    for (i = 0; i < cb.esc.Size(); ++i) all.Push(cb.esc[i]);
    NormalizeRanges(all);

    memset(&cc, 0, sizeof(cc));
    for (i = 0; i < all.Size(); ++i) {
        for (c = all[i].lo; c <= all[i].hi && c < 256; ++c) cc.bitmap[c >> 5] |= 1u << (c & 31);
    }
    for (c = 0; c < 256; ++c) {
        for (i = 0; i < cb.props.Size(); ++i) {
            if (PropMatch(cb.props[i], (Cp)c)) cc.bitmap[c >> 5] |= 1u << (c & 31);
        }
    }
    cc.rbeg = prog.ranges.Size();
    for (i = 0; i < all.Size(); ++i) {
        if (all[i].hi >= 256) AddRange(prog.ranges, all[i].lo < 256 ? 256 : all[i].lo, all[i].hi);
    }
    cc.rcnt = prog.ranges.Size() - cc.rbeg;
    cc.pbeg = prog.props.Size();
    for (i = 0; i < cb.props.Size(); ++i) prog.props.Push(cb.props[i]);
    cc.pcnt = cb.props.Size();
    cc.negate = cb.negate;
    prog.classes.Push(cc);
    return prog.classes.Size() - 1;
}

static bool ClassMatch(const Program& prog, int idx, Cp c)
{
    const CharClass& cc = prog.classes[idx];
    bool r;
    if (c < 256) {
        r = ((cc.bitmap[c >> 5] >> (c & 31)) & 1u) != 0;
    } else {
        r = InRanges(prog.ranges.Data() + cc.rbeg, cc.rcnt, c);
        if (!r) {
            int i;
            for (i = 0; i < cc.pcnt; ++i) {
                if (PropMatch(prog.props[cc.pbeg + i], c)) { r = true; break; }
            }
        }
    }
    return r != (cc.negate != 0);
}

/* ------------------------------------------------------------------------------------------ */
/* Compiler: parser                                                                            */
/* ------------------------------------------------------------------------------------------ */

enum { F_I = 1, F_M = 2, F_S = 4, F_X = 8, F_G = 16 };

enum {
    N_EMPTY, N_CHAR, N_ANY, N_CLASS, N_ASSERT, N_KEEP, N_CAT, N_ALT, N_GROUP, N_REPEAT,
    N_ATOMIC, N_LOOK, N_BACKREF, N_CALL, N_COND
};

/*
 * Syntax tree node.  Meaning of the fields per type:
 *   N_CHAR    a = code point, b = ignore case
 *   N_ANY     a = also matches \n
 *   N_CLASS   a = class index
 *   N_ASSERT  a = opcode (OP_BOL ...)
 *   N_CAT/N_ALT  child = list of children (linked by next)
 *   N_GROUP   a = group number (0: none), child = body;
 *             d = balancing group: b = popped group number or c = name reference (name offset + 1)
 *   N_REPEAT  a = min, b = max (-1: unbounded), c = REP_*, child
 *   N_ATOMIC  child
 *   N_LOOK    a = lookbehind, b = negative, child
 *   N_BACKREF a = group number or 0 / b = name reference, c = ignore case
 *   N_CALL    a = group number or 0 / b = name reference ("a == 0 && b == 0" calls the whole pattern)
 *   N_COND    a = 0 group test (b/c = group or name reference), 1 assertion (e = N_LOOK node),
 *             2 DEFINE;  child = yes branch, d = no branch or -1
 */
struct Node {
    int type;
    int a, b, c, d, e;
    int child;
    int next;
    int pos;   /* pattern offset, for error messages */
};

#define MAX_NEST 200
#define MAX_STACKED 32
#define MAX_COUNT 65535

static bool IsDigitCp(Cp c) { return c >= '0' && c <= '9'; }

static int HexValue(Cp c)
{
    if (c >= '0' && c <= '9') return (int)(c - '0');
    if (c >= 'a' && c <= 'f') return (int)(c - 'a') + 10;
    if (c >= 'A' && c <= 'F') return (int)(c - 'A') + 10;
    return -1;
}

static bool IsNameChar(Cp c)
{
    return (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_' || c >= 0x80;
}

static bool EqAscii(const wchar_t* w, int n, const char* a)
{
    int i;
    for (i = 0; i < n; ++i) {
        if (a[i] == 0 || (Cp)w[i] != (Cp)(unsigned char)a[i]) return false;
    }
    return a[n] == 0;
}

class Compiler {
public:
    Compiler(Program& prog, const wchar_t* pat, int len, unsigned int flags)
        : m_prog(prog), m_p(pat), m_len(len), m_pos(0), m_flags(flags & 31u),
          m_counter(0), m_maxGroup(0), m_quote(0), m_depth(0)
    {
        if (flags & 16u) prog.global = 1;
    }
    void Run();

private:
    Compiler(const Compiler&);
    Compiler& operator=(const Compiler&);

    /* --- helpers --- */
    void Error(const char* msg, int pos = -2) const
    {
        throw CRegexpException(CRegexpException::ERR_SYNTAX, pos == -2 ? m_pos : pos, msg);
    }
    bool More() const { return m_pos < m_len; }
    Cp At(int i) const { return (Cp)m_p[i]; }
    bool AtCh(int i, char ch) const { return i >= 0 && i < m_len && m_p[i] == (wchar_t)ch; }

    int NewNode(int type, int a = 0, int b = 0, int c = 0)
    {
        Node n;
        n.type = type; n.a = a; n.b = b; n.c = c; n.d = 0; n.e = 0;
        n.child = -1; n.next = -1; n.pos = m_pos;
        m_nodes.Push(n);
        return m_nodes.Size() - 1;
    }
    void Append(int& first, int& tail, int& count, int node)
    {
        if (first < 0) first = node; else m_nodes[tail].next = node;
        tail = node;
        ++count;
    }
    int BuildList(int type, int first, int count)
    {
        int n;
        if (count == 0) return NewNode(N_EMPTY);
        if (count == 1) return first;
        n = NewNode(type);
        m_nodes[n].child = first;
        return n;
    }

    /* --- parser --- */
    void SkipExtended();
    int ParseAlt(bool branchReset);
    int ParseSeq();
    int ParseAtom();
    int ParseQuantifiers(int atom);
    bool ReadQuantifier(int& mn, int& mx);
    int ParseGroup();
    int GroupBody(int open, bool branchReset);
    int ParseNamedGroup(int open, Cp term);
    int ParseOptions(int open);
    int ParseConditional(int open);
    int ParseCallGroup(int open);
    int FinishCall(int open, int num, int nameRef);
    int ParseEscape();
    int ParseNumericEscape(Cp first);
    int ParseKRef();
    int ParseGRef();
    int ParseClass();
    int ReadClassItem(ClassBuilder& cb, Cp& ch);
    bool ReadCharEscape(Cp c, Cp& out);
    bool ReadBracedHex(Cp& out);
    void ReadProperty(bool negated, ClassProp& p);
    void AddClassChars(ClassBuilder& cb, Cp lo, Cp hi);
    int MakeLiteral(Cp c);
    int CharNode(Cp c) { return NewNode(N_CHAR, (int)c, (m_flags & F_I) ? 1 : 0); }
    int SetNode(const Range* r, int n, bool negated);
    int AddName(int start, int len);
    bool NameEq(int a, int b) const;
    int FindNamedGroup(int off) const;
    bool ParseRefToken(int start, int len, int& num, int& nameRef);
    int ReadNameUntil(Cp term);

    /* --- code generator --- */
    void Gen(int n);
    void GenRepeat(int n);
    void GenLoop(int child, int mn, int mx, bool lazy);
    void GenLook(int look, int& failSlot);
    int ResolveRef(int num, int nameRef, int pos, bool allowZero);
    void MarkBalanceTargets();
    void LenOf(int n, int& mn, int& mx) const;
    bool HasGroup(int n) const;
    int FirstLiteral(int n) const;
    bool IsAnchored(int n) const;

    int Emit(int v) { m_prog.code.Push(v); return m_prog.code.Size() - 1; }
    int Emit2(int a, int b) { int p = Emit(a); Emit(b); return p; }
    int Emit3(int a, int b, int c) { int p = Emit(a); Emit(b); Emit(c); return p; }
    int PC() const { return m_prog.code.Size(); }

    Program& m_prog;
    const wchar_t* m_p;
    int m_len;
    int m_pos;
    unsigned int m_flags;
    int m_counter;      /* highest group number handed out so far */
    int m_maxGroup;
    int m_quote;        /* inside \Q..\E ('Q'), \U..\E ('U') or \L..\E ('L') */
    int m_depth;
    Vec<Node> m_nodes;
    Vec<int> m_callPatch;
    Vec<int> m_groupPc;
};

void Compiler::SkipExtended()
{
    if (!(m_flags & F_X)) return;
    while (m_pos < m_len) {
        Cp c = At(m_pos);
        if (c == ' ' || (c >= 9 && c <= 13)) {
            ++m_pos;
        } else if (c == '#') {
            while (m_pos < m_len && At(m_pos) != '\n') ++m_pos;
        } else {
            break;
        }
    }
}

/* alternatives, up to the closing parenthesis or the end of the pattern */
int Compiler::ParseAlt(bool branchReset)
{
    int first = -1, tail = -1, count = 0;
    int base = m_counter, maxc = m_counter;
    for (;;) {
        int seq;
        if (branchReset) m_counter = base;
        seq = ParseSeq();
        if (m_counter > maxc) maxc = m_counter;
        Append(first, tail, count, seq);
        if (m_quote == 0 && More() && At(m_pos) == '|') {
            ++m_pos;
            continue;
        }
        break;
    }
    if (branchReset) m_counter = maxc;
    return BuildList(N_ALT, first, count);
}

/* a sequence of quantified atoms, up to '|' or ')' */
int Compiler::ParseSeq()
{
    int first = -1, tail = -1, count = 0;
    for (;;) {
        int atom;
        if (m_quote == 0) SkipExtended();
        if (!More()) break;
        if (m_quote != 0) {
            Cp c = At(m_pos);
            if (c == '\\' && AtCh(m_pos + 1, 'E')) {
                m_pos += 2;
                m_quote = 0;
                continue;
            }
            ++m_pos;
            if (m_quote == 'U') c = UcUpper(c);
            else if (m_quote == 'L') c = UcLower(c);
            atom = MakeLiteral(c);
            if (AtCh(m_pos, '\\') && AtCh(m_pos + 1, 'E')) {   /* \Qab\E* : the quantifier belongs to b */
                m_pos += 2;
                m_quote = 0;
            }
            if (m_quote != 0) {
                Append(first, tail, count, atom);
                continue;
            }
        } else {
            Cp c = At(m_pos);
            if (c == '|' || c == ')') break;
            atom = ParseAtom();
            if (atom < 0) continue;
        }
        atom = ParseQuantifiers(atom);
        Append(first, tail, count, atom);
    }
    return BuildList(N_CAT, first, count);
}

int Compiler::MakeLiteral(Cp c)
{
    if (c > 0xFFFF && sizeof(wchar_t) == 2) {   /* UTF-16: a literal code point beyond the BMP becomes a surrogate pair */
        Cp v = c - 0x10000;
        int a = NewNode(N_CHAR, (int)(0xD800 + (v >> 10)), 0);
        int b = NewNode(N_CHAR, (int)(0xDC00 + (v & 0x3FF)), 0);
        int cat = NewNode(N_CAT);
        m_nodes[a].next = b;
        m_nodes[cat].child = a;
        return cat;
    }
    return CharNode(c);
}

int Compiler::ParseAtom()
{
    Cp c = At(m_pos);
    switch (c) {
    case '(':
        return ParseGroup();
    case '[':
        return ParseClass();
    case '.':
        ++m_pos;
        return NewNode(N_ANY, (m_flags & F_S) ? 1 : 0);
    case '^':
        ++m_pos;
        return NewNode(N_ASSERT, (m_flags & F_M) ? OP_MBOL : OP_BOL);
    case '$':
        ++m_pos;
        return NewNode(N_ASSERT, (m_flags & F_M) ? OP_MEOL : OP_EOL);
    case '\\':
        return ParseEscape();
    default:   /* includes a quantifier character with nothing to repeat, and '{' : taken literally */
        ++m_pos;
        return MakeLiteral(c);
    }
}

/* '*', '+', '?' or a valid {n}, {n,}, {n,m} at the current position */
bool Compiler::ReadQuantifier(int& mn, int& mx)
{
    Cp c = At(m_pos);
    if (c == '*') { mn = 0; mx = -1; ++m_pos; return true; }
    if (c == '+') { mn = 1; mx = -1; ++m_pos; return true; }
    if (c == '?') { mn = 0; mx = 1; ++m_pos; return true; }
    if (c == '{') {
        int p = m_pos + 1;
        long n = 0, m = -1;
        int digits = 0;
        while (p < m_len && IsDigitCp(At(p))) {
            n = n * 10 + (long)(At(p) - '0');
            if (n > 1000000L) n = 1000000L;
            ++p;
            ++digits;
        }
        if (digits == 0) return false;
        if (p < m_len && At(p) == '}') {
            m = n;
        } else if (p < m_len && At(p) == ',') {
            ++p;
            if (p < m_len && At(p) == '}') {
                m = -1;
            } else {
                int d2 = 0;
                m = 0;
                while (p < m_len && IsDigitCp(At(p))) {
                    m = m * 10 + (long)(At(p) - '0');
                    if (m > 1000000L) m = 1000000L;
                    ++p;
                    ++d2;
                }
                if (d2 == 0 || p >= m_len || At(p) != '}') return false;
            }
        } else {
            return false;
        }
        if (n > MAX_COUNT || m > MAX_COUNT) Error("number too big in {} quantifier");
        if (m >= 0 && n > m) Error("numbers out of order in {} quantifier");
        mn = (int)n;
        mx = (int)m;
        m_pos = p + 1;
        return true;
    }
    return false;
}

int Compiler::ParseQuantifiers(int atom)
{
    int stacked = 0;
    for (;;) {
        int mn, mx, mode = REP_GREEDY, r;
        SkipExtended();
        if (!More() || !ReadQuantifier(mn, mx)) break;
        if (More() && At(m_pos) == '?') { mode = REP_LAZY; ++m_pos; }
        else if (More() && At(m_pos) == '+') { mode = REP_POSSESSIVE; ++m_pos; }
        if (++stacked > MAX_STACKED) Error("too many quantifiers in a row");
        r = NewNode(N_REPEAT, mn, mx, mode);
        m_nodes[r].child = atom;
        atom = r;
    }
    return atom;
}

/* ---- groups ---- */

int Compiler::GroupBody(int open, bool branchReset)
{
    unsigned int saved = m_flags;
    int body;
    if (++m_depth > MAX_NEST) Error("pattern is nested too deeply", open);
    body = ParseAlt(branchReset);
    if (!More() || At(m_pos) != ')') Error("missing )", open);
    ++m_pos;
    --m_depth;
    m_flags = saved;
    return body;
}

int Compiler::AddName(int start, int len)
{
    int off = m_prog.namePool.Size(), i;
    for (i = 0; i < len; ++i) m_prog.namePool.Push(m_p[start + i]);
    m_prog.namePool.Push(0);
    return off;
}

bool Compiler::NameEq(int a, int b) const
{
    const wchar_t* pool = m_prog.namePool.Data();
    while (pool[a] == pool[b]) {
        if (pool[a] == 0) return true;
        ++a;
        ++b;
    }
    return false;
}

int Compiler::FindNamedGroup(int off) const   /* 0 when unknown */
{
    int i;
    for (i = 0; i < m_prog.names.Size(); ++i) {
        if (NameEq(m_prog.names[i].off, off)) return m_prog.names[i].group;
    }
    return 0;
}

/* (?<name>..) (?<2>..) (?<name-other>..) (?<-other>..) and the same with quotes; m_pos is after the opening '<' */
int Compiler::ParseNamedGroup(int open, Cp term)
{
    int s1 = m_pos, l1, s2 = 0, l2 = 0, num = 0, g, body;
    bool balancing = false;
    int otherNum = 0, otherName = 0, i;
    while (m_pos < m_len && IsNameChar(At(m_pos))) ++m_pos;
    l1 = m_pos - s1;
    if (m_pos < m_len && At(m_pos) == '-') {
        balancing = true;
        ++m_pos;
        s2 = m_pos;
        while (m_pos < m_len && IsNameChar(At(m_pos))) ++m_pos;
        l2 = m_pos - s2;
        if (l2 == 0) Error("group name expected after '-'");
    }
    if (!More() || At(m_pos) != term) Error("invalid group name");
    if (l1 == 0 && !balancing) Error("group name expected");
    ++m_pos;

    if (l1 > 0) {
        bool numeric = true;
        for (i = 0; i < l1; ++i) if (!IsDigitCp(At(s1 + i))) numeric = false;
        if (numeric) {
            long v = 0;
            for (i = 0; i < l1; ++i) { v = v * 10 + (long)(At(s1 + i) - '0'); if (v > 100000L) Error("group number too big", open); }
            if (v < 1) Error("group number must be positive", open);
            num = (int)v;
            if (num > m_counter) m_counter = num;
        } else {
            int off = AddName(s1, l1);
            num = FindNamedGroup(off);
            if (num == 0) {
                NameEnt ne;
                num = ++m_counter;
                ne.off = off;
                ne.group = num;
                m_prog.names.Push(ne);
            }
        }
        if (num > m_maxGroup) m_maxGroup = num;
    }
    if (balancing) {
        bool numeric = true;
        for (i = 0; i < l2; ++i) if (!IsDigitCp(At(s2 + i))) numeric = false;
        if (numeric) {
            long v = 0;
            for (i = 0; i < l2; ++i) { v = v * 10 + (long)(At(s2 + i) - '0'); if (v > 100000L) Error("group number too big", open); }
            otherNum = (int)v;
        } else {
            otherName = AddName(s2, l2) + 1;
        }
    }
    body = GroupBody(open, false);
    g = NewNode(N_GROUP, num, otherNum, otherName);
    m_nodes[g].d = balancing ? 1 : 0;
    m_nodes[g].child = body;
    m_nodes[g].pos = open;
    return g;
}

/* reads a group name up to term and returns its offset in the name pool */
int Compiler::ReadNameUntil(Cp term)
{
    int s = m_pos;
    while (m_pos < m_len && IsNameChar(At(m_pos))) ++m_pos;
    if (m_pos == s) Error("group name expected");
    if (!More() || At(m_pos) != term) Error("invalid group name");
    {
        int off = AddName(s, m_pos - s);
        ++m_pos;
        return off;
    }
}

/* number (optionally signed, relative to the groups opened so far) or name */
bool Compiler::ParseRefToken(int start, int len, int& num, int& nameRef)
{
    int i = 0, sign = 0;
    bool numeric;
    num = 0;
    nameRef = 0;
    if (len <= 0) return false;
    if (At(start) == '-') { sign = -1; i = 1; }
    else if (At(start) == '+') { sign = 1; i = 1; }
    numeric = (i < len);
    {
        int j;
        for (j = i; j < len; ++j) if (!IsDigitCp(At(start + j))) numeric = false;
    }
    if (numeric) {
        long v = 0;
        int j;
        for (j = i; j < len; ++j) { v = v * 10 + (long)(At(start + j) - '0'); if (v > 100000L) return false; }
        if (sign < 0) v = (long)m_counter - v + 1;
        else if (sign > 0) v = (long)m_counter + v;
        if (v < 0) return false;
        num = (int)v;
        return true;
    }
    {
        int j;
        for (j = 0; j < len; ++j) if (!IsNameChar(At(start + j))) return false;
    }
    nameRef = AddName(start, len) + 1;
    return true;
}

int Compiler::FinishCall(int open, int num, int nameRef)
{
    int n;
    if (!More() || At(m_pos) != ')') Error("missing ) after recursion/call", open);
    ++m_pos;
    n = NewNode(N_CALL, num, nameRef);
    m_nodes[n].pos = open;
    return n;
}

/* (?R) (?R1) (?R<name>) (?R'name') ; (?1) (?-1) (?+1) (?0).  m_pos is at the 'R', the sign or the first digit. */
int Compiler::ParseCallGroup(int open)
{
    int s, num, nameRef;
    if (At(m_pos) == 'R') {
        ++m_pos;
        if (More() && (At(m_pos) == '<' || At(m_pos) == '\'')) {
            Cp term = (At(m_pos) == '<') ? (Cp)'>' : (Cp)'\'';
            ++m_pos;
            return FinishCall(open, 0, ReadNameUntil(term) + 1);
        }
        if (More() && At(m_pos) == ')') return FinishCall(open, 0, 0);
    }
    s = m_pos;
    if (More() && (At(m_pos) == '-' || At(m_pos) == '+')) ++m_pos;
    while (More() && IsDigitCp(At(m_pos))) ++m_pos;
    if (!ParseRefToken(s, m_pos - s, num, nameRef) || nameRef != 0) Error("invalid group reference", open);
    return FinishCall(open, num, 0);
}

int Compiler::ParseOptions(int open)
{
    unsigned int setBits = 0, clrBits = 0;
    bool neg = false;
    for (;;) {
        unsigned int bit = 0;
        Cp c;
        if (!More()) Error("missing )", open);
        c = At(m_pos);
        if (c == '-') { neg = true; ++m_pos; continue; }
        switch (c) {
        case 'i': bit = F_I; break;
        case 'm': bit = F_M; break;
        case 's': bit = F_S; break;
        case 'x': bit = F_X; break;
        case 'g': bit = F_G; break;
        default: break;
        }
        if (!bit) break;
        if (neg) clrBits |= bit; else setBits |= bit;
        if (bit == F_G && !neg) m_prog.global = 1;
        ++m_pos;
    }
    if (More() && At(m_pos) == ')') {
        ++m_pos;
        m_flags = (m_flags | setBits) & ~clrBits;
        return -1;
    }
    if (More() && At(m_pos) == ':') {
        unsigned int saved = m_flags;
        int body;
        ++m_pos;
        m_flags = (m_flags | setBits) & ~clrBits;
        if (++m_depth > MAX_NEST) Error("pattern is nested too deeply", open);
        body = ParseAlt(false);
        if (!More() || At(m_pos) != ')') Error("missing )", open);
        ++m_pos;
        --m_depth;
        m_flags = saved;
        return body;
    }
    Error("unrecognized character after (?");
    return -1;
}

/* (?(cond)yes|no) ; m_pos is at the '(' that starts the condition */
int Compiler::ParseConditional(int open)
{
    int kind, num = 0, nameRef = 0, look = 0, yes, no = -1, n;
    unsigned int saved = m_flags;
    if (AtCh(m_pos + 1, '?')) {
        look = ParseGroup();
        if (look < 0 || m_nodes[look].type != N_LOOK) Error("assertion expected after (?(", open);
        kind = 1;
    } else {
        int s, term = ')';
        ++m_pos;
        if (More() && (At(m_pos) == '<' || At(m_pos) == '\'')) {
            term = (At(m_pos) == '<') ? '>' : '\'';
            ++m_pos;
        }
        s = m_pos;
        while (m_pos < m_len && At(m_pos) != (Cp)term) ++m_pos;
        if (!More()) Error("missing ) in condition", open);
        if (EqAscii(m_p + s, m_pos - s, "DEFINE") && term == ')') {
            kind = 2;
        } else {
            kind = 0;
            if (!ParseRefToken(s, m_pos - s, num, nameRef)) Error("invalid group reference in condition", s);
        }
        ++m_pos;
        if (term != ')') {
            if (!More() || At(m_pos) != ')') Error("missing ) after condition", open);
            ++m_pos;
        }
    }
    if (++m_depth > MAX_NEST) Error("pattern is nested too deeply", open);
    yes = ParseSeq();
    if (More() && At(m_pos) == '|' && m_quote == 0) {
        ++m_pos;
        no = ParseSeq();
        if (More() && At(m_pos) == '|' && m_quote == 0) Error("conditional group contains more than two branches", open);
    }
    if (!More() || At(m_pos) != ')') Error("missing )", open);
    ++m_pos;
    --m_depth;
    m_flags = saved;
    n = NewNode(N_COND, kind, num, nameRef);
    m_nodes[n].child = yes;
    m_nodes[n].d = no;
    m_nodes[n].e = look;
    m_nodes[n].pos = open;
    return n;
}

int Compiler::ParseGroup()
{
    int open = m_pos;
    Cp c;
    ++m_pos;
    if (!(More() && At(m_pos) == '?')) {   /* plain capturing group */
        int num = ++m_counter, body, g;
        if (num > m_maxGroup) m_maxGroup = num;
        body = GroupBody(open, false);
        g = NewNode(N_GROUP, num);
        m_nodes[g].child = body;
        m_nodes[g].pos = open;
        return g;
    }
    ++m_pos;   /* '?' */
    if (!More()) Error("unterminated group", open);
    c = At(m_pos);
    switch (c) {
    case '#':
        while (More() && At(m_pos) != ')') ++m_pos;
        if (!More()) Error("missing ) after comment", open);
        ++m_pos;
        return -1;
    case ':':
        ++m_pos;
        return GroupBody(open, false);
    case '|':
        ++m_pos;
        return GroupBody(open, true);
    case '>': {
        int body, n;
        ++m_pos;
        body = GroupBody(open, false);
        n = NewNode(N_ATOMIC);
        m_nodes[n].child = body;
        return n;
    }
    case '=':
    case '!': {
        int body, n;
        ++m_pos;
        body = GroupBody(open, false);
        n = NewNode(N_LOOK, 0, c == '!' ? 1 : 0);
        m_nodes[n].child = body;
        m_nodes[n].pos = open;
        return n;
    }
    case '<':
        if (AtCh(m_pos + 1, '=') || AtCh(m_pos + 1, '!')) {
            int neg = (At(m_pos + 1) == '!') ? 1 : 0, body, n;
            m_pos += 2;
            body = GroupBody(open, false);
            n = NewNode(N_LOOK, 1, neg);
            m_nodes[n].child = body;
            m_nodes[n].pos = open;
            return n;
        }
        ++m_pos;
        return ParseNamedGroup(open, '>');
    case '\'':
        ++m_pos;
        return ParseNamedGroup(open, '\'');
    case 'P':
        if (AtCh(m_pos + 1, '<')) {
            m_pos += 2;
            return ParseNamedGroup(open, '>');
        }
        if (AtCh(m_pos + 1, '=')) {   /* (?P=name) back reference */
            int off, n;
            m_pos += 2;
            off = ReadNameUntil(')');
            n = NewNode(N_BACKREF, 0, off + 1, (m_flags & F_I) ? 1 : 0);
            m_nodes[n].pos = open;
            return n;
        }
        if (AtCh(m_pos + 1, '>')) {   /* (?P>name) call */
            int off;
            m_pos += 2;
            off = ReadNameUntil(')');
            {
                int n = NewNode(N_CALL, 0, off + 1);
                m_nodes[n].pos = open;
                return n;
            }
        }
        Error("unrecognized character after (?P");
        return -1;
    case '&': {
        int off, n;
        ++m_pos;
        off = ReadNameUntil(')');
        n = NewNode(N_CALL, 0, off + 1);
        m_nodes[n].pos = open;
        return n;
    }
    case 'R':
        return ParseCallGroup(open);
    case '(':
        return ParseConditional(open);
    case '+':
    case '-':
        if (AtCh(m_pos + 1, '0') || (m_pos + 1 < m_len && IsDigitCp(At(m_pos + 1)))) return ParseCallGroup(open);
        return ParseOptions(open);
    default:
        if (IsDigitCp(c)) return ParseCallGroup(open);
        return ParseOptions(open);
    }
}

/* ---- escapes ---- */

bool Compiler::ReadBracedHex(Cp& out)   /* m_pos is at '{' */
{
    unsigned long v = 0;
    int digits = 0;
    ++m_pos;
    while (m_pos < m_len && HexValue(At(m_pos)) >= 0) {
        v = v * 16 + (unsigned long)HexValue(At(m_pos));
        if (v > 0x10FFFFUL) Error("code point value too large");
        ++m_pos;
        ++digits;
    }
    if (digits == 0 || !More() || At(m_pos) != '}') Error("malformed \\x{...} or \\u{...} escape");
    ++m_pos;
    out = (Cp)v;
    return true;
}

/* single character escapes; c is the character after the backslash and has been consumed */
bool Compiler::ReadCharEscape(Cp c, Cp& out)
{
    switch (c) {
    case 't': out = 9; return true;
    case 'n': out = 10; return true;
    case 'r': out = 13; return true;
    case 'f': out = 12; return true;
    case 'v': out = 11; return true;
    case 'a': out = 7; return true;
    case 'e': out = 27; return true;
    case 'x':
        if (AtCh(m_pos, '{')) return ReadBracedHex(out);
        {
            Cp v = 0;
            int n = 0;
            while (n < 2 && m_pos < m_len && HexValue(At(m_pos)) >= 0) {
                v = v * 16 + (Cp)HexValue(At(m_pos));
                ++m_pos;
                ++n;
            }
            out = v;
            return true;
        }
    case 'u':
        if (AtCh(m_pos, '{')) return ReadBracedHex(out);
        {
            Cp v = 0;
            int n;
            for (n = 0; n < 4; ++n) {
                if (m_pos + n >= m_len || HexValue(At(m_pos + n)) < 0) return false;   /* not \uHHHH: a plain 'u' */
                v = v * 16 + (Cp)HexValue(At(m_pos + n));
            }
            m_pos += 4;
            out = v;
            return true;
        }
    case 'c': {
        Cp x;
        if (!More()) Error("\\c at end of pattern");
        x = At(m_pos++);
        if (x >= 'a' && x <= 'z') x -= 32;
        out = x ^ 64;
        return true;
    }
    case '0': {
        Cp v = 0;
        int n = 0;
        while (n < 2 && m_pos < m_len && At(m_pos) >= '0' && At(m_pos) <= '7') {
            v = v * 8 + (At(m_pos) - '0');
            ++m_pos;
            ++n;
        }
        out = v;
        return true;
    }
    default:
        return false;
    }
}

int Compiler::SetNode(const Range* r, int n, bool negated)
{
    ClassBuilder cb;
    int node;
    AddSet(cb.esc, r, n, negated);
    node = NewNode(N_CLASS, FinishClass(m_prog, cb));
    return node;
}

void Compiler::ReadProperty(bool negated, ClassProp& p)   /* after \p or \P */
{
    int start, len, i;
    if (!More()) Error("malformed \\p or \\P sequence");
    if (At(m_pos) == '{') {
        ++m_pos;
        start = m_pos;
        while (More() && At(m_pos) != '}') ++m_pos;
        if (!More()) Error("missing } after \\p{");
        len = m_pos - start;
        ++m_pos;
    } else {
        start = m_pos;
        len = 1;
        ++m_pos;
    }
    if (len > 0 && At(start) == '^') {
        negated = !negated;
        ++start;
        --len;
    }
    p.mask = 0;
    p.extra = 0;
    p.neg = negated ? 1 : 0;
    for (i = 0; i < ARRAY_COUNT(kPropNames); ++i) {   /* unknown names match nothing */
        if (EqAscii(m_p + start, len, kPropNames[i].name)) {
            p.mask = kPropNames[i].mask;
            p.extra = kPropNames[i].extra;
            break;
        }
    }
}

/* \1 .. \9 (and longer numbers): back reference, or an octal escape for long numbers without that many groups */
int Compiler::ParseNumericEscape(Cp first)   /* the first digit has been consumed */
{
    int p = m_pos - 1, q = p, n;
    long num = 0;
    while (q < m_len && IsDigitCp(At(q))) {
        num = num * 10 + (long)(At(q) - '0');
        if (num > 100000L) num = 100000L;
        ++q;
    }
    if (first >= '8' || num < 10 || num <= (long)m_counter) {
        n = NewNode(N_BACKREF, (int)num, 0, (m_flags & F_I) ? 1 : 0);
        m_pos = q;
        return n;
    }
    {
        Cp v = 0;
        int digits = 0;
        q = p;
        while (digits < 3 && q < m_len && At(q) >= '0' && At(q) <= '7') {
            v = v * 8 + (At(q) - '0');
            ++q;
            ++digits;
        }
        m_pos = q;
        return MakeLiteral(v);
    }
}

/* \k<name> \k'name' \k{name} */
int Compiler::ParseKRef()
{
    int s, num, nameRef, n;
    Cp close;
    if (!More() || !(At(m_pos) == '<' || At(m_pos) == '\'' || At(m_pos) == '{')) Error("\\k must be followed by <name>, 'name' or {name}");
    close = (At(m_pos) == '<') ? (Cp)'>' : (At(m_pos) == '{') ? (Cp)'}' : (Cp)'\'';
    ++m_pos;
    s = m_pos;
    while (More() && At(m_pos) != close) ++m_pos;
    if (!More()) Error("missing terminator in \\k reference");
    if (!ParseRefToken(s, m_pos - s, num, nameRef)) Error("invalid group reference", s);
    ++m_pos;
    n = NewNode(N_BACKREF, num, nameRef, (m_flags & F_I) ? 1 : 0);
    return n;
}

/* \g1 \g-1 \g{1} \g{-1} \g{name} \g<name> \g'1' : back references */
int Compiler::ParseGRef()
{
    int s, num, nameRef;
    if (More() && (At(m_pos) == '{' || At(m_pos) == '<' || At(m_pos) == '\'')) {
        Cp close = (At(m_pos) == '{') ? (Cp)'}' : (At(m_pos) == '<') ? (Cp)'>' : (Cp)'\'';
        ++m_pos;
        s = m_pos;
        while (More() && At(m_pos) != close) ++m_pos;
        if (!More()) Error("missing terminator in \\g reference");
        if (!ParseRefToken(s, m_pos - s, num, nameRef)) Error("invalid group reference", s);
        ++m_pos;
    } else {
        s = m_pos;
        if (More() && (At(m_pos) == '-' || At(m_pos) == '+')) ++m_pos;
        while (More() && IsDigitCp(At(m_pos))) ++m_pos;
        if (!ParseRefToken(s, m_pos - s, num, nameRef) || nameRef != 0) Error("invalid group reference after \\g", s);
    }
    return NewNode(N_BACKREF, num, nameRef, (m_flags & F_I) ? 1 : 0);
}

int Compiler::ParseEscape()
{
    Cp c, ch;
    if (m_pos + 1 >= m_len) Error("\\ at end of pattern");
    c = At(m_pos + 1);
    m_pos += 2;
    switch (c) {
    case 'd': return SetNode(kDigit, ARRAY_COUNT(kDigit), false);
    case 'D': return SetNode(kDigit, ARRAY_COUNT(kDigit), true);
    case 'w': return SetNode(kWord, ARRAY_COUNT(kWord), false);
    case 'W': return SetNode(kWord, ARRAY_COUNT(kWord), true);
    case 's': return SetNode(kSpace, ARRAY_COUNT(kSpace), false);
    case 'S': return SetNode(kSpace, ARRAY_COUNT(kSpace), true);
    case 'h': return SetNode(kHSpace, ARRAY_COUNT(kHSpace), false);
    case 'H': return SetNode(kHSpace, ARRAY_COUNT(kHSpace), true);
    case 'b': return NewNode(N_ASSERT, OP_WORDB);
    case 'B': return NewNode(N_ASSERT, OP_NWORDB);
    case 'A': return NewNode(N_ASSERT, OP_BOS);
    case 'Z': return NewNode(N_ASSERT, OP_EOSNL);
    case 'z': return NewNode(N_ASSERT, OP_EOS);
    case 'G': return NewNode(N_ASSERT, OP_GPOS);
    case 'K': return NewNode(N_KEEP);
    case 'p':
    case 'P': {
        ClassBuilder cb;
        ClassProp p;
        cb.icase = (m_flags & F_I) ? 1 : 0;
        ReadProperty(c == 'P', p);
        cb.props.Push(p);
        return NewNode(N_CLASS, FinishClass(m_prog, cb));
    }
    case 'k': return ParseKRef();
    case 'g': return ParseGRef();
    case 'Q': m_quote = 'Q'; return -1;
    case 'U': m_quote = 'U'; return -1;
    case 'L': m_quote = 'L'; return -1;
    case 'E': return -1;
    default:
        break;
    }
    if (c >= '1' && c <= '9') return ParseNumericEscape(c);
    if (ReadCharEscape(c, ch)) return MakeLiteral(ch);
    return MakeLiteral(c);   /* \. \* \\ ... and unknown escapes stand for the character itself */
}

/* ---- character classes ---- */

void Compiler::AddClassChars(ClassBuilder& cb, Cp lo, Cp hi)
{
    if (sizeof(wchar_t) == 2 && hi > 0xFFFF) {   /* UTF-16: beyond the BMP only the surrogate halves can be listed */
        if (lo > 0xFFFF) {
            Cp v = lo - 0x10000;
            AddRange(cb.lit, (int)(0xD800 + (v >> 10)), (int)(0xD800 + (v >> 10)));
            AddRange(cb.lit, (int)(0xDC00 + (v & 0x3FF)), (int)(0xDC00 + (v & 0x3FF)));
            return;
        }
        hi = 0xFFFF;
    }
    AddRange(cb.lit, (int)lo, (int)hi);
}

/*
 * Reads one item of a character class.
 * Returns 0: a single character (in ch), 1: a set was added to cb, 2: nothing (\Q, \E ...).
 */
int Compiler::ReadClassItem(ClassBuilder& cb, Cp& ch)
{
    Cp c = At(m_pos);
    if (m_quote != 0) {
        if (c == '\\' && AtCh(m_pos + 1, 'E')) {
            m_pos += 2;
            m_quote = 0;
            return 2;
        }
        ++m_pos;
        if (m_quote == 'U') c = UcUpper(c);
        else if (m_quote == 'L') c = UcLower(c);
        ch = c;
        return 0;
    }
    if (c == '[' && AtCh(m_pos + 1, ':')) {   /* [:alpha:] [:^alpha:] */
        int p = m_pos + 2, s;
        bool neg = false;
        if (AtCh(p, '^')) { neg = true; ++p; }
        s = p;
        while (p < m_len && ((At(p) >= 'a' && At(p) <= 'z') || (At(p) >= 'A' && At(p) <= 'Z'))) ++p;
        if (AtCh(p, ':') && AtCh(p + 1, ']')) {
            int i, found = -1;
            for (i = 0; i < ARRAY_COUNT(kPosix); ++i) {
                if (EqAscii(m_p + s, p - s, kPosix[i].name)) { found = i; break; }
            }
            if (found < 0) Error("unknown POSIX class name", s);
            AddSet(kPosix[found].caseSensitive ? cb.lit : cb.esc, kPosix[found].r, kPosix[found].n, neg);
            m_pos = p + 2;
            return 1;
        }
    }
    if (c != '\\') {
        ++m_pos;
        ch = c;
        return 0;
    }
    if (m_pos + 1 >= m_len) Error("\\ at end of pattern");
    c = At(m_pos + 1);
    m_pos += 2;
    switch (c) {
    case 'd': AddSet(cb.esc, kDigit, ARRAY_COUNT(kDigit), false); return 1;
    case 'D': AddSet(cb.esc, kDigit, ARRAY_COUNT(kDigit), true); return 1;
    case 'w': AddSet(cb.esc, kWord, ARRAY_COUNT(kWord), false); return 1;
    case 'W': AddSet(cb.esc, kWord, ARRAY_COUNT(kWord), true); return 1;
    case 's': AddSet(cb.esc, kSpace, ARRAY_COUNT(kSpace), false); return 1;
    case 'S': AddSet(cb.esc, kSpace, ARRAY_COUNT(kSpace), true); return 1;
    case 'h': AddSet(cb.esc, kHSpace, ARRAY_COUNT(kHSpace), false); return 1;
    case 'H': AddSet(cb.esc, kHSpace, ARRAY_COUNT(kHSpace), true); return 1;
    case 'p':
    case 'P': {
        ClassProp p;
        ReadProperty(c == 'P', p);
        cb.props.Push(p);
        return 1;
    }
    case 'b': ch = 8; return 0;
    case 'Q': m_quote = 'Q'; return 2;
    case 'U': m_quote = 'U'; return 2;
    case 'L': m_quote = 'L'; return 2;
    case 'E': return 2;
    default: break;
    }
    if (c >= '1' && c <= '7') {   /* octal */
        Cp v = c - '0';
        int n = 1;
        while (n < 3 && m_pos < m_len && At(m_pos) >= '0' && At(m_pos) <= '7') {
            v = v * 8 + (At(m_pos) - '0');
            ++m_pos;
            ++n;
        }
        ch = v;
        return 0;
    }
    if (ReadCharEscape(c, ch)) return 0;
    ch = c;
    return 0;
}

int Compiler::ParseClass()
{
    int start = m_pos, idx;
    bool first = true;
    ClassBuilder cb;
    ++m_pos;
    cb.icase = (m_flags & F_I) ? 1 : 0;
    if (More() && At(m_pos) == '^') {
        cb.negate = 1;
        ++m_pos;
    }
    for (;;) {
        Cp lo, hi;
        int r;
        if (!More()) Error("missing terminating ] for character class", start);
        if (At(m_pos) == ']' && !first && m_quote == 0) {
            ++m_pos;
            break;
        }
        first = false;
        r = ReadClassItem(cb, lo);
        if (r != 0) continue;
        if (m_quote == 0 && AtCh(m_pos, '-') && m_pos + 1 < m_len && At(m_pos + 1) != ']') {
            int save = m_pos;
            ++m_pos;
            r = ReadClassItem(cb, hi);
            if (r == 0) {
                if (hi < lo) Error("range out of order in character class", save);
                AddClassChars(cb, lo, hi);
            } else {   /* [a-\d]: the '-' is an ordinary character */
                AddClassChars(cb, lo, lo);
                AddClassChars(cb, '-', '-');
            }
        } else {
            AddClassChars(cb, lo, lo);
        }
    }
    idx = FinishClass(m_prog, cb);
    {
        int n = NewNode(N_CLASS, idx);
        m_nodes[n].pos = start;
        return n;
    }
}

void Compiler::Run()
{
    int root;
    root = ParseAlt(false);
    if (m_pos < m_len) Error("unmatched )");
    m_prog.ngroups = m_maxGroup;
    {
        int i;
        m_prog.balTarget.Resize(m_maxGroup + 1);
        m_groupPc.Resize(m_maxGroup + 1);
        for (i = 0; i <= m_maxGroup; ++i) {
            m_prog.balTarget[i] = 0;
            m_groupPc[i] = -1;
        }
    }
    MarkBalanceTargets();
    m_groupPc[0] = PC();
    Emit2(OP_OPEN, 0);
    Gen(root);
    Emit2(OP_CLOSE, 0);
    Emit(OP_MATCH);
    {
        int i;
        for (i = 0; i < m_callPatch.Size(); ++i) {
            int at = m_callPatch[i];
            int g = m_prog.code[at - 1];
            if (m_groupPc[g] < 0) Error("reference to a group that is never defined", -1);
            m_prog.code[at] = m_groupPc[g];
        }
    }
    m_prog.anchored = IsAnchored(root) ? 1 : 0;
    m_prog.firstChar = FirstLiteral(root);
}

/* ------------------------------------------------------------------------------------------ */
/* Compiler: code generator                                                                    */
/* ------------------------------------------------------------------------------------------ */

int Compiler::ResolveRef(int num, int nameRef, int pos, bool allowZero)
{
    if (nameRef) {
        int g = FindNamedGroup(nameRef - 1);
        if (g == 0) Error("reference to a non-existent named group", pos);
        return g;
    }
    if (num < 0 || num > m_maxGroup || (num == 0 && !allowZero)) Error("reference to a non-existent group", pos);
    return num;
}

void Compiler::MarkBalanceTargets()
{
    int i;
    for (i = 0; i < m_nodes.Size(); ++i) {
        if (m_nodes[i].type == N_GROUP && m_nodes[i].d) {
            int other = ResolveRef(m_nodes[i].b, m_nodes[i].c, m_nodes[i].pos, false);
            m_prog.balTarget[other] = 1;
        }
    }
}

bool Compiler::HasGroup(int n) const
{
    const Node& nd = m_nodes[n];
    int c;
    switch (nd.type) {
    case N_GROUP:
        if (nd.a > 0) return true;
        return HasGroup(nd.child);
    case N_CAT:
    case N_ALT:
        for (c = nd.child; c >= 0; c = m_nodes[c].next) if (HasGroup(c)) return true;
        return false;
    case N_REPEAT:
    case N_ATOMIC:
    case N_LOOK:
        return HasGroup(nd.child);
    case N_COND:
        return HasGroup(nd.child) || (nd.d >= 0 && HasGroup(nd.d)) || (nd.a == 1 && HasGroup(nd.e));
    default:
        return false;
    }
}

#define LEN_CAP 0x0FFFFFFF

/* shortest and longest (-1: unbounded) number of characters a node can match */
void Compiler::LenOf(int n, int& mn, int& mx) const
{
    const Node& nd = m_nodes[n];
    int c, cm, cx;
    long a, b;
    switch (nd.type) {
    case N_CHAR:
    case N_ANY:
    case N_CLASS:
        mn = mx = 1;
        return;
    case N_CAT:
        a = 0;
        b = 0;
        mx = 0;
        for (c = nd.child; c >= 0; c = m_nodes[c].next) {
            LenOf(c, cm, cx);
            a += cm;
            if (cx < 0) mx = -1; else b += cx;
            if (a > LEN_CAP) a = LEN_CAP;
            if (b > LEN_CAP) b = LEN_CAP;
        }
        mn = (int)a;
        if (mx == 0) mx = (b >= LEN_CAP) ? -1 : (int)b;
        return;
    case N_ALT:
        mn = LEN_CAP;
        mx = 0;
        for (c = nd.child; c >= 0; c = m_nodes[c].next) {
            LenOf(c, cm, cx);
            if (cm < mn) mn = cm;
            if (cx < 0) mx = -1; else if (mx >= 0 && cx > mx) mx = cx;
        }
        return;
    case N_GROUP:
    case N_ATOMIC:
        LenOf(nd.child, mn, mx);
        return;
    case N_REPEAT:
        LenOf(nd.child, cm, cx);
        a = (long)cm * (long)nd.a;
        mn = (a > LEN_CAP) ? LEN_CAP : (int)a;
        if (cx == 0 || nd.b == 0) {
            mx = 0;
        } else if (cx < 0 || nd.b < 0) {
            mx = -1;
        } else {
            b = (long)cx * (long)nd.b;
            mx = (b >= LEN_CAP) ? -1 : (int)b;
        }
        return;
    case N_BACKREF:
    case N_CALL:
        mn = 0;
        mx = -1;
        return;
    case N_COND:
        if (nd.a == 2) { mn = 0; mx = 0; return; }
        LenOf(nd.child, mn, mx);
        if (nd.d >= 0) {
            LenOf(nd.d, cm, cx);
        } else {
            cm = 0;
            cx = 0;
        }
        if (cm < mn) mn = cm;
        if (mx >= 0 && (cx < 0 || cx > mx)) mx = cx;
        return;
    default:   /* empty, assertions, \K, lookaround */
        mn = mx = 0;
        return;
    }
}

/* the literal character every match must start with, or -1 */
int Compiler::FirstLiteral(int n) const
{
    const Node& nd = m_nodes[n];
    int c;
    switch (nd.type) {
    case N_CHAR:
        if (nd.b && UcHasCaseVariants((Cp)nd.a)) return -1;
        return nd.a;
    case N_CAT:
        for (c = nd.child; c >= 0; c = m_nodes[c].next) {
            int t = m_nodes[c].type;
            if (t == N_ASSERT || t == N_KEEP || t == N_EMPTY || t == N_LOOK) continue;
            return FirstLiteral(c);
        }
        return -1;
    case N_GROUP:
    case N_ATOMIC:
        return FirstLiteral(nd.child);
    case N_REPEAT:
        return nd.a >= 1 ? FirstLiteral(nd.child) : -1;
    default:
        return -1;
    }
}

/* can a match only begin at the position where the search starts? */
bool Compiler::IsAnchored(int n) const
{
    const Node& nd = m_nodes[n];
    int c;
    switch (nd.type) {
    case N_ASSERT:
        return nd.a == OP_BOS || nd.a == OP_BOL || nd.a == OP_GPOS;
    case N_CAT:
        return nd.child >= 0 && IsAnchored(nd.child);
    case N_GROUP:
    case N_ATOMIC:
        return IsAnchored(nd.child);
    case N_ALT:
        for (c = nd.child; c >= 0; c = m_nodes[c].next) if (!IsAnchored(c)) return false;
        return true;
    default:
        return false;
    }
}

static void CharOp(const Node& cn, int& aop, int& arg)
{
    if (cn.b && UcHasCaseVariants((Cp)cn.a)) {
        aop = OP_CHARI;
        arg = (int)UcFold((Cp)cn.a);
    } else {
        aop = OP_CHAR;
        arg = cn.a;
    }
}

void Compiler::GenLoop(int child, int mn, int mx, bool lazy)
{
    int cmn, cmx;
    LenOf(child, cmn, cmx);
    if (mx < 0 && mn <= 1 && cmn > 0) {
        /* an iteration always consumes input, so no counter and no empty-iteration check are needed */
        int sp, end;
        if (mn == 0) {   /* L: SPLIT body, exit;  body;  JMP L */
            int body;
            sp = Emit3(OP_SPLIT, 0, 0);
            body = PC();
            Gen(child);
            Emit2(OP_JMP, sp);
            end = PC();
            m_prog.code[sp + 1] = lazy ? end : body;
            m_prog.code[sp + 2] = lazy ? body : end;
        } else {         /* L: body;  SPLIT L, exit */
            int top = PC();
            Gen(child);
            sp = Emit3(OP_SPLIT, 0, 0);
            end = PC();
            m_prog.code[sp + 1] = lazy ? end : top;
            m_prog.code[sp + 2] = lazy ? top : end;
        }
        return;
    }
    if (mn == 0 && mx == 1) {
        int sp = Emit3(OP_SPLIT, 0, 0);
        int body = PC(), end;
        Gen(child);
        end = PC();
        m_prog.code[sp + 1] = lazy ? end : body;
        m_prog.code[sp + 2] = lazy ? body : end;
        return;
    }
    {
        int id = m_prog.nloops++;
        int test, exitSlot;
        Emit2(OP_LOOP_INIT, id);
        test = PC();
        Emit(OP_LOOP_TEST);
        Emit(id);
        Emit(mn);
        Emit(mx);
        Emit(lazy ? 1 : 0);
        exitSlot = Emit(0);
        Emit2(OP_LOOP_BODY, id);
        Gen(child);
        Emit(OP_LOOP_END);
        Emit(id);
        Emit(mn);
        Emit(mx);
        Emit(test);
        m_prog.code[exitSlot] = PC();
    }
}

void Compiler::GenRepeat(int n)
{
    Node nd = m_nodes[n];
    Node cn = m_nodes[nd.child];
    int mn = nd.a, mx = nd.b, mode = nd.c;
    if (mx == 0) {   /* never executed, but groups inside stay callable as subroutines */
        if (HasGroup(nd.child)) {
            int j = Emit2(OP_JMP, 0);
            Gen(nd.child);
            m_prog.code[j + 1] = PC();
        }
        return;
    }
    if (mn == 1 && mx == 1) {
        Gen(nd.child);
        return;
    }
    if (cn.type == N_CHAR || cn.type == N_ANY || cn.type == N_CLASS) {
        int aop, arg;
        if (cn.type == N_CHAR) CharOp(cn, aop, arg);
        else if (cn.type == N_ANY) { aop = cn.a ? OP_ANYNL : OP_ANY; arg = 0; }
        else { aop = OP_CLASS; arg = cn.a; }
        Emit(OP_REP);
        Emit(mode);
        Emit(mn);
        Emit(mx);
        Emit(aop);
        Emit(arg);
        return;
    }
    if (mode == REP_POSSESSIVE) {
        Emit(OP_ATOMIC_BEGIN);
        GenLoop(nd.child, mn, mx, false);
        Emit(OP_ATOMIC_END);
        return;
    }
    GenLoop(nd.child, mn, mx, mode == REP_LAZY);
}

void Compiler::Gen(int n)
{
    Node nd = m_nodes[n];
    int c;
    switch (nd.type) {
    case N_EMPTY:
        break;
    case N_CHAR: {
        int aop, arg;
        CharOp(nd, aop, arg);
        Emit2(aop, arg);
        break;
    }
    case N_ANY:
        Emit(nd.a ? OP_ANYNL : OP_ANY);
        break;
    case N_CLASS:
        Emit2(OP_CLASS, nd.a);
        break;
    case N_ASSERT:
        Emit(nd.a);
        break;
    case N_KEEP:
        Emit(OP_KEEP);
        break;
    case N_CAT:
        for (c = nd.child; c >= 0; c = m_nodes[c].next) Gen(c);
        break;
    case N_ALT: {
        Vec<int> jumps;
        int i;
        for (c = nd.child; c >= 0; c = m_nodes[c].next) {
            if (m_nodes[c].next >= 0) {
                int sp = Emit3(OP_SPLIT, 0, 0);
                int j;
                m_prog.code[sp + 1] = PC();
                Gen(c);
                j = Emit2(OP_JMP, 0);
                jumps.Push(j + 1);
                m_prog.code[sp + 2] = PC();
            } else {
                Gen(c);
            }
        }
        for (i = 0; i < jumps.Size(); ++i) m_prog.code[jumps[i]] = PC();
        break;
    }
    case N_GROUP:
        if (nd.a > 0) {
            if (m_groupPc[nd.a] < 0) m_groupPc[nd.a] = PC();
            Emit2(OP_OPEN, nd.a);
        }
        Gen(nd.child);
        if (nd.d) Emit3(OP_CLOSEBAL, nd.a, ResolveRef(nd.b, nd.c, nd.pos, false));
        else Emit2(OP_CLOSE, nd.a);
        break;
    case N_REPEAT:
        GenRepeat(n);
        break;
    case N_ATOMIC:
        Emit(OP_ATOMIC_BEGIN);
        Gen(nd.child);
        Emit(OP_ATOMIC_END);
        break;
    case N_LOOK: {
        int slot;   /* where the "assertion body failed" pc is stored */
        if (!nd.a) {
            slot = Emit2(OP_LOOK_BEGIN, -1) + 1;
        } else {
            int mn, mx;
            LenOf(nd.child, mn, mx);
            slot = Emit(OP_LB_BEGIN) + 1;
            Emit(-1);
            Emit(mn);
            Emit(mx);
        }
        Gen(nd.child);
        if (nd.a) Emit(OP_LB_CHECK);
        if (nd.b) {
            Emit(OP_LOOK_OK_FAIL);
            m_prog.code[slot] = PC();
        } else {
            Emit(OP_LOOK_OK_CUT);
        }
        break;
    }
    case N_BACKREF:
        Emit2(nd.c ? OP_BACKREFI : OP_BACKREF, ResolveRef(nd.a, nd.b, nd.pos, false));
        break;
    case N_CALL: {
        int g = (nd.a == 0 && nd.b == 0) ? 0 : ResolveRef(nd.a, nd.b, nd.pos, true);
        int at = Emit3(OP_CALL, g, 0);
        m_callPatch.Push(at + 2);
        break;
    }
    case N_COND: {
        int endJump;
        if (nd.a == 0) {   /* (?(group)yes|no) */
            int g = ResolveRef(nd.b, nd.c, nd.pos, false);
            int cj = Emit3(OP_COND_GROUP, g, 0);
            Gen(nd.child);
            if (nd.d >= 0) {
                endJump = Emit2(OP_JMP, 0);
                m_prog.code[cj + 2] = PC();
                Gen(nd.d);
                m_prog.code[endJump + 1] = PC();
            } else {
                m_prog.code[cj + 2] = PC();
            }
        } else if (nd.a == 2) {   /* (?(DEFINE)...) : never executed, only callable */
            endJump = Emit2(OP_JMP, 0);
            Gen(nd.child);
            m_prog.code[endJump + 1] = PC();
        } else {   /* (?(?=...)yes|no) */
            Node lk = m_nodes[nd.e];
            int slot, oj = 0;
            if (!lk.a) {
                slot = Emit2(OP_LOOK_BEGIN, -1) + 1;
            } else {
                int mn, mx;
                LenOf(lk.child, mn, mx);
                slot = Emit(OP_LB_BEGIN) + 1;
                Emit(-1);
                Emit(mn);
                Emit(mx);
            }
            Gen(lk.child);
            if (lk.a) Emit(OP_LB_CHECK);
            if (lk.b) oj = Emit2(OP_LOOK_OK_JUMP, 0) + 1;
            else Emit(OP_LOOK_OK_CUT);
            if (lk.b) {   /* body failed: the condition holds (negative assertion) */
                m_prog.code[slot] = PC();
                Gen(nd.child);
                if (nd.d >= 0) {
                    endJump = Emit2(OP_JMP, 0);
                    m_prog.code[oj] = PC();
                    Gen(nd.d);
                    m_prog.code[endJump + 1] = PC();
                } else {
                    m_prog.code[oj] = PC();
                }
            } else {      /* body failed: take the no branch */
                Gen(nd.child);
                if (nd.d >= 0) {
                    endJump = Emit2(OP_JMP, 0);
                    m_prog.code[slot] = PC();
                    Gen(nd.d);
                    m_prog.code[endJump + 1] = PC();
                } else {
                    m_prog.code[slot] = PC();
                }
            }
        }
        break;
    }
    default:
        break;
    }
}

/* ------------------------------------------------------------------------------------------ */
/* Matcher: backtracking virtual machine                                                       */
/* ------------------------------------------------------------------------------------------ */

/*
 * The backtrack stack holds fixed-size entries:
 *   BT_CHOICE  a = pc, b = pos                 resume here when everything above has failed
 *   BT_GREEDY  a = pc, b = lowest pos, c = next pos to try      (OP_REP, one entry for the whole loop)
 *   BT_LAZY    a = pc of OP_REP, b = pos, c = repetitions so far
 *   BT_MARK    a = pc (-1: none), b = pos      start of an atomic group / assertion
 *   BT_LB      a = pc, b = next start, c = lowest start         candidate starts of a lookbehind
 *   BT_UNDO    a = index in st[], b = old value
 *   BT_POOL    a = frames size, b = snaps size                  undo of a subroutine call's bookkeeping
 */
enum { BT_CHOICE = 1, BT_GREEDY, BT_LAZY, BT_MARK, BT_LB, BT_UNDO, BT_POOL };

struct BtEntry { int type; int a; int b; int c; };

struct Frame {   /* an active subroutine call / recursion */
    int ret;     /* where to continue after the call */
    int parent;  /* calling frame or -1 */
    int target;  /* called group */
    int pos;     /* position at the time of the call (to detect endless left recursion) */
    int snapOff; /* saved state in Work::snaps, restored when the call returns */
};

struct Work {
    Vec<BtEntry> stack;
    Vec<int> st;        /* captures, balancing history, loop counters, \K position, current frame */
    Vec<Frame> frames;
    Vec<int> snaps;
    Vec<int> hnodes;    /* capture history for balancing groups: start, end, previous node */
};

static inline bool IsWordCp(Cp c)
{
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_';
}

static inline bool AtomMatch(const Program& prog, int aop, int arg, Cp c)
{
    switch (aop) {
    case OP_CHAR:  return c == (Cp)arg;
    case OP_CHARI: return UcFold(c) == (Cp)arg;
    case OP_ANY:   return c != '\n';
    case OP_ANYNL: return true;
    default:       return ClassMatch(prog, arg, c);
    }
}

class Matcher {
public:
    Matcher(const Program& prog, Work& w, const wchar_t* s, int n, int gpos, int notEmptyAt, unsigned long limit);
    bool Search(int from);
    const int* Result() const { return m_w.st.Data(); }

private:
    Matcher(const Matcher&);
    Matcher& operator=(const Matcher&);

    bool Run(int startPos);
    void SetSt(int idx, int v)
    {
        int* st = m_w.st.Data();
        if (st[idx] != v) {
            BtEntry e;
            e.type = BT_UNDO; e.a = idx; e.b = st[idx]; e.c = 0;
            m_w.stack.Push(e);
            st[idx] = v;
        }
    }
    void PushBt(int type, int a, int b, int c)
    {
        BtEntry e;
        e.type = type; e.a = a; e.b = b; e.c = c;
        if (m_w.stack.Size() >= m_stackLimit)
            throw CRegexpException(CRegexpException::ERR_STEP_LIMIT, -1, "backtrack stack limit exceeded");
        m_w.stack.Push(e);
    }
    int FindMark() const
    {
        int i = m_w.stack.Size() - 1;
        while (i >= 0 && m_w.stack[i].type != BT_MARK) --i;
        return i;
    }
    void CutTo(int mark);
    void UnwindTo(int mark);
    void PushHist(int g, int s, int e);

    const Program& m_prog;
    Work& m_w;
    const wchar_t* m_s;
    int m_n;
    int m_gpos;
    int m_notEmptyAt;
    unsigned long m_limit;
    unsigned long m_steps;
    int m_stackLimit;   /* maximum number of backtrack stack entries */
    const int* m_code;
    int m_capN;     /* number of groups including group 0 */
    int m_tmp;      /* st[] index of the temporary start of group g: m_tmp + g */
    int m_hist;     /* st[] index of the balancing history head of group g */
    int m_loop;     /* st[] index of the first loop counter: counter, iteration start per loop */
    int m_kpos;     /* st[] index of the \K position */
    int m_frame;    /* st[] index of the current frame */
    int m_stSize;
};

Matcher::Matcher(const Program& prog, Work& w, const wchar_t* s, int n, int gpos, int notEmptyAt, unsigned long limit)
    : m_prog(prog), m_w(w), m_s(s), m_n(n), m_gpos(gpos), m_notEmptyAt(notEmptyAt),
      m_limit(limit), m_steps(0), m_code(prog.code.Data())
{
    int i;
    m_stackLimit = (n > (0x3FFFFFFF - (1 << 22)) / 32) ? 0x3FFFFFFF : (1 << 22) + 32 * n;
    m_capN = prog.ngroups + 1;
    m_tmp = 2 * m_capN;
    m_hist = m_tmp + m_capN;
    m_loop = m_hist + m_capN;
    m_kpos = m_loop + 2 * prog.nloops;
    m_frame = m_kpos + 1;
    m_stSize = m_frame + 1;
    w.stack.Clear();
    w.frames.Clear();
    w.snaps.Clear();
    w.hnodes.Clear();
    w.st.Resize(m_stSize);
    for (i = 0; i < m_stSize; ++i) w.st[i] = -1;
}

/* drop the choice points above mark (and the mark itself) but keep what is needed to undo state changes */
void Matcher::CutTo(int mark)
{
    Vec<BtEntry>& stk = m_w.stack;
    int w = mark, i, sz = stk.Size();
    for (i = mark + 1; i < sz; ++i) {
        int t = stk[i].type;
        if (t == BT_UNDO || t == BT_POOL) stk[w++] = stk[i];
    }
    stk.Resize(w);
}

/* pop everything down to and including mark, undoing state changes */
void Matcher::UnwindTo(int mark)
{
    Vec<BtEntry>& stk = m_w.stack;
    int* st = m_w.st.Data();
    while (stk.Size() > mark) {
        const BtEntry& e = stk.Back();
        if (e.type == BT_UNDO) {
            st[e.a] = e.b;
        } else if (e.type == BT_POOL) {
            m_w.frames.Resize(e.a);
            m_w.snaps.Resize(e.b);
        }
        stk.Pop();
    }
}

void Matcher::PushHist(int g, int s, int e)
{
    int idx = m_w.hnodes.Size() / 3;
    m_w.hnodes.Push(s);
    m_w.hnodes.Push(e);
    m_w.hnodes.Push(m_w.st[m_hist + g]);
    SetSt(m_hist + g, idx);
}

bool Matcher::Run(int startPos)
{
    const int* code = m_code;
    Vec<BtEntry>& stk = m_w.stack;
    int* st = m_w.st.Data();
    const wchar_t* s = m_s;
    const int n = m_n;
    int pc = 0;
    int pos = startPos;

    m_w.hnodes.Clear();
    for (;;) {
        switch (code[pc]) {
        case OP_MATCH: {
            int ms = st[0];
            if (st[m_kpos] >= 0) ms = st[m_kpos];
            if (m_notEmptyAt >= 0 && ms == m_notEmptyAt && pos == m_notEmptyAt) goto fail;
            st[0] = ms;
            st[1] = pos;
            return true;
        }
        case OP_CHAR:
            if (pos < n && (Cp)s[pos] == (Cp)code[pc + 1]) { ++pos; pc += 2; continue; }
            goto fail;
        case OP_CHARI:
            if (pos < n && UcFold((Cp)s[pos]) == (Cp)code[pc + 1]) { ++pos; pc += 2; continue; }
            goto fail;
        case OP_ANY:
            if (pos < n && (Cp)s[pos] != '\n') { ++pos; ++pc; continue; }
            goto fail;
        case OP_ANYNL:
            if (pos < n) { ++pos; ++pc; continue; }
            goto fail;
        case OP_CLASS:
            if (pos < n && ClassMatch(m_prog, code[pc + 1], (Cp)s[pos])) { ++pos; pc += 2; continue; }
            goto fail;

        case OP_BOL:
        case OP_BOS:
            if (pos == 0) { ++pc; continue; }
            goto fail;
        case OP_MBOL:
            if (pos == 0 || (Cp)s[pos - 1] == '\n') { ++pc; continue; }
            goto fail;
        case OP_EOL:
        case OP_EOS:
            if (pos == n) { ++pc; continue; }
            goto fail;
        case OP_MEOL:
            if (pos == n || (Cp)s[pos] == '\n') { ++pc; continue; }
            goto fail;
        case OP_EOSNL:
            if (pos == n || (pos == n - 1 && (Cp)s[pos] == '\n')) { ++pc; continue; }
            goto fail;
        case OP_WORDB:
        case OP_NWORDB: {
            bool before = pos > 0 && IsWordCp((Cp)s[pos - 1]);
            bool after = pos < n && IsWordCp((Cp)s[pos]);
            if ((before != after) == (code[pc] == OP_WORDB)) { ++pc; continue; }
            goto fail;
        }
        case OP_GPOS:
            if (pos == m_gpos) { ++pc; continue; }
            goto fail;
        case OP_KEEP:
            SetSt(m_kpos, pos);
            ++pc;
            continue;

        case OP_JMP:
            pc = code[pc + 1];
            continue;
        case OP_SPLIT:
            PushBt(BT_CHOICE, code[pc + 2], pos, 0);
            pc = code[pc + 1];
            continue;

        case OP_OPEN:
            SetSt(m_tmp + code[pc + 1], pos);
            pc += 2;
            continue;
        case OP_CLOSE: {
            int g = code[pc + 1];
            int fr = st[m_frame];
            if (fr >= 0 && m_w.frames[fr].target == g) {   /* end of a subroutine call: restore and return */
                const Frame& f = m_w.frames[fr];
                const int* snap = m_w.snaps.Data() + f.snapOff;
                int i;
                pc = f.ret;
                for (i = 0; i < m_stSize; ++i) {
                    if (st[i] != snap[i]) SetSt(i, snap[i]);
                }
                continue;
            }
            SetSt(2 * g, st[m_tmp + g]);
            SetSt(2 * g + 1, pos);
            if (m_prog.balTarget[g]) PushHist(g, st[2 * g], st[2 * g + 1]);
            pc += 2;
            continue;
        }
        case OP_CLOSEBAL: {   /* (?<g-other>...) */
            int g = code[pc + 1];
            int other = code[pc + 2];
            int h = st[m_hist + other];
            int prev, os, oe;
            if (h < 0) goto fail;
            os = m_w.hnodes[3 * h];
            oe = m_w.hnodes[3 * h + 1];
            prev = m_w.hnodes[3 * h + 2];
            (void)os;
            SetSt(m_hist + other, prev);
            if (prev >= 0) {
                SetSt(2 * other, m_w.hnodes[3 * prev]);
                SetSt(2 * other + 1, m_w.hnodes[3 * prev + 1]);
            } else {
                SetSt(2 * other, -1);
                SetSt(2 * other + 1, -1);
            }
            if (g > 0) {   /* the text between the popped group and this group */
                int a = oe, b = st[m_tmp + g];
                if (a > b) { int t = a; a = b; b = t; }
                SetSt(2 * g, a);
                SetSt(2 * g + 1, b);
                if (m_prog.balTarget[g]) PushHist(g, a, b);
            }
            pc += 3;
            continue;
        }
        case OP_BACKREF:
        case OP_BACKREFI: {
            int g = code[pc + 1];
            int bs = st[2 * g], be = st[2 * g + 1];
            int len, i;
            if (bs < 0 || be < 0) goto fail;
            len = be - bs;
            if (n - pos < len) goto fail;
            if (code[pc] == OP_BACKREF) {
                for (i = 0; i < len; ++i) if (s[bs + i] != s[pos + i]) goto fail;
            } else {
                for (i = 0; i < len; ++i) if (UcFold((Cp)s[bs + i]) != UcFold((Cp)s[pos + i])) goto fail;
            }
            pos += len;
            pc += 2;
            continue;
        }

        case OP_ATOMIC_BEGIN:
            PushBt(BT_MARK, -1, pos, 0);
            ++pc;
            continue;
        case OP_ATOMIC_END: {
            int m = FindMark();
            if (m < 0) goto fail;
            CutTo(m);
            ++pc;
            continue;
        }
        case OP_LOOK_BEGIN:
            PushBt(BT_MARK, code[pc + 1], pos, 0);
            pc += 2;
            continue;
        case OP_LB_BEGIN: {
            int minL = code[pc + 2], maxL = code[pc + 3];
            int s0 = pos - minL, lo;
            PushBt(BT_MARK, code[pc + 1], pos, 0);
            if (s0 < 0) goto fail;
            lo = (maxL < 0 || pos - maxL < 0) ? 0 : pos - maxL;
            if (s0 > lo) PushBt(BT_LB, pc + 4, s0 - 1, lo);
            pos = s0;
            pc += 4;
            continue;
        }
        case OP_LB_CHECK: {
            int m = FindMark();
            if (m < 0 || pos != stk[m].b) goto fail;
            ++pc;
            continue;
        }
        case OP_LOOK_OK_CUT: {
            int m = FindMark();
            if (m < 0) goto fail;
            pos = stk[m].b;
            CutTo(m);
            ++pc;
            continue;
        }
        case OP_LOOK_OK_FAIL: {
            int m = FindMark();
            if (m < 0) goto fail;
            UnwindTo(m);
            goto fail;
        }
        case OP_LOOK_OK_JUMP: {
            int m = FindMark();
            if (m < 0) goto fail;
            pos = stk[m].b;
            UnwindTo(m);
            pc = code[pc + 1];
            continue;
        }

        case OP_REP: {
            int mode = code[pc + 1], mn = code[pc + 2], mx = code[pc + 3];
            int aop = code[pc + 4], arg = code[pc + 5];
            int cnt = 0, lim = n - pos;
            if (mode == REP_LAZY) {
                if (lim < mn) goto fail;
                while (cnt < mn && AtomMatch(m_prog, aop, arg, (Cp)s[pos + cnt])) ++cnt;
                if (cnt < mn) goto fail;
                pos += cnt;
                if (mx < 0 || mx > mn) PushBt(BT_LAZY, pc, pos, mn);
                pc += 6;
                continue;
            }
            if (mx >= 0 && mx < lim) lim = mx;
            while (cnt < lim && AtomMatch(m_prog, aop, arg, (Cp)s[pos + cnt])) ++cnt;
            if (cnt < mn) goto fail;
            if (mode == REP_GREEDY && cnt > mn) PushBt(BT_GREEDY, pc + 6, pos + mn, pos + cnt - 1);
            pos += cnt;
            pc += 6;
            continue;
        }

        case OP_LOOP_INIT: {
            int base = m_loop + 2 * code[pc + 1];
            SetSt(base, 0);
            SetSt(base + 1, -1);
            pc += 2;
            continue;
        }
        case OP_LOOP_TEST: {
            int cnt = st[m_loop + 2 * code[pc + 1]];
            int mn = code[pc + 2], mx = code[pc + 3];
            if (cnt < mn) { pc += 6; continue; }
            if (mx >= 0 && cnt >= mx) { pc = code[pc + 5]; continue; }
            if (code[pc + 4] == 0) {   /* greedy: another iteration first */
                PushBt(BT_CHOICE, code[pc + 5], pos, 0);
                pc += 6;
            } else {                   /* lazy: leave first */
                PushBt(BT_CHOICE, pc + 6, pos, 0);
                pc = code[pc + 5];
            }
            continue;
        }
        case OP_LOOP_BODY:
            SetSt(m_loop + 2 * code[pc + 1] + 1, pos);
            pc += 2;
            continue;
        case OP_LOOP_END: {
            int base = m_loop + 2 * code[pc + 1];
            int cnt = st[base] + 1;
            SetSt(base, cnt);
            if (pos == st[base + 1] && cnt >= code[pc + 2]) {   /* empty iteration: stop looping */
                pc += 5;
            } else {
                pc = code[pc + 4];
            }
            continue;
        }

        case OP_COND_GROUP: {
            int g = code[pc + 1];
            if (st[2 * g] >= 0 && st[2 * g + 1] >= 0) pc += 3;
            else pc = code[pc + 2];
            continue;
        }

        case OP_CALL: {
            int g = code[pc + 1];
            int f = st[m_frame];
            Frame nf;
            int i;
            while (f >= 0 && m_w.frames[f].pos == pos) {   /* the same call at the same place again: endless recursion */
                if (m_w.frames[f].target == g) goto fail;
                f = m_w.frames[f].parent;
            }
            PushBt(BT_POOL, m_w.frames.Size(), m_w.snaps.Size(), 0);
            nf.ret = pc + 3;
            nf.parent = st[m_frame];
            nf.target = g;
            nf.pos = pos;
            nf.snapOff = m_w.snaps.Size();
            for (i = 0; i < m_stSize; ++i) m_w.snaps.Push(st[i]);
            m_w.frames.Push(nf);
            SetSt(m_frame, m_w.frames.Size() - 1);
            pc = code[pc + 2];
            continue;
        }

        default:
            goto fail;   /* corrupt program */
        }

    fail:
        if (++m_steps > m_limit)
            throw CRegexpException(CRegexpException::ERR_STEP_LIMIT, -1, "backtrack limit exceeded");
        for (;;) {
            if (stk.Empty()) return false;
            BtEntry& e = stk.Back();
            switch (e.type) {
            case BT_UNDO:
                st[e.a] = e.b;
                stk.Pop();
                continue;
            case BT_POOL:
                m_w.frames.Resize(e.a);
                m_w.snaps.Resize(e.b);
                stk.Pop();
                continue;
            case BT_CHOICE:
                pc = e.a;
                pos = e.b;
                stk.Pop();
                goto resume;
            case BT_GREEDY:
                pc = e.a;
                pos = e.c;
                if (e.c > e.b) --e.c; else stk.Pop();
                goto resume;
            case BT_LAZY: {
                int rp = e.a;
                int mx = code[rp + 3];
                if ((mx >= 0 && e.c >= mx) || e.b >= n || !AtomMatch(m_prog, code[rp + 4], code[rp + 5], (Cp)s[e.b])) {
                    stk.Pop();
                    continue;
                }
                pos = e.b + 1;
                pc = rp + 6;
                ++e.c;
                if (mx >= 0 && e.c >= mx) stk.Pop(); else e.b = pos;
                goto resume;
            }
            case BT_MARK:
                if (e.a >= 0) {
                    pc = e.a;
                    pos = e.b;
                    stk.Pop();
                    goto resume;
                }
                stk.Pop();
                continue;
            case BT_LB:
                pc = e.a;
                pos = e.b;
                if (e.b > e.c) --e.b; else stk.Pop();
                goto resume;
            default:
                stk.Pop();
                continue;
            }
        }
    resume:
        ;
    }
}

bool Matcher::Search(int from)
{
    int p = from;
    for (;;) {
        if (m_prog.firstChar >= 0) {
            while (p < m_n && (Cp)m_s[p] != (Cp)m_prog.firstChar) ++p;
            if (p >= m_n) return false;
        }
        if (Run(p)) return true;
        if (m_prog.anchored) return false;
        if (++p > m_n) return false;
    }
}

/* ------------------------------------------------------------------------------------------ */
/* Unicode functions                                                                           */
/* ------------------------------------------------------------------------------------------ */

int UcCategory(Cp c)
{
    int lo = 0, hi = g_catRunsCount - 1;
    if (c > MAX_CP) return CAT_Cn;
    while (lo < hi) {   /* last run that starts at or before c */
        int mid = (lo + hi + 1) / 2;
        if ((g_catRuns[mid] >> 5) <= c) lo = mid; else hi = mid - 1;
    }
    return (int)(g_catRuns[lo] & 31u);
}

static Cp MapLookup(const CaseRange* t, int n, Cp c)
{
    int lo = 0, hi = n - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (c < t[mid].lo) {
            hi = mid - 1;
        } else if (c > t[mid].hi) {
            lo = mid + 1;
        } else {
            if (((c - t[mid].lo) % (Cp)t[mid].step) == 0) return (Cp)((int)c + t[mid].delta);
            return c;
        }
    }
    return c;
}

Cp UcFold(Cp c)
{
    if (c < 128) return (c >= 'A' && c <= 'Z') ? c + 32 : c;
    return MapLookup(g_foldTable, g_foldTableCount, c);
}

Cp UcUpper(Cp c)
{
    if (c < 128) return (c >= 'a' && c <= 'z') ? c - 32 : c;
    return MapLookup(g_upperTable, g_upperTableCount, c);
}

Cp UcLower(Cp c)
{
    if (c < 128) return (c >= 'A' && c <= 'Z') ? c + 32 : c;
    return MapLookup(g_lowerTable, g_lowerTableCount, c);
}

/* does another character exist that matches c when ignoring case? */
bool UcHasCaseVariants(Cp c)
{
    int i;
    if (UcFold(c) != c) return true;
    for (i = 0; i < g_foldTableCount; ++i) {   /* is c the folded form of something? */
        const CaseRange& e = g_foldTable[i];
        long lo = (long)e.lo + e.delta, hi = (long)e.hi + e.delta;
        if ((long)c >= lo && (long)c <= hi && (((long)c - lo) % e.step) == 0) return true;
    }
    return false;
}

// ==== BEGIN GENERATED TABLES (tools/gen_unicode_tables.py) ====
// Unicode 15.1.0. Do not edit by hand.
// General category runs: (first code point << 5) | category index (see CAT_* enum).
const unsigned int g_catRuns[] = {
    0x1,0x41D,0x435,0x497,0x4B5,0x516,0x532,0x555,
    0x579,0x595,0x5B1,0x5D5,0x60D,0x755,0x799,0x7F5,
    0x829,0xB76,0xB95,0xBB2,0xBD8,0xBF0,0xC18,0xC25,
    0xF76,0xF99,0xFB2,0xFD9,0xFE1,0x141D,0x1435,0x1457,
    0x14DA,0x14F5,0x1518,0x153A,0x1547,0x1574,0x1599,0x15A2,
    0x15DA,0x15F8,0x161A,0x1639,0x164F,0x1698,0x16A5,0x16D5,
    0x1718,0x172F,0x1747,0x1773,0x178F,0x17F5,0x1809,0x1AF9,
    0x1B09,0x1BE5,0x1EF9,0x1F05,0x2009,0x2025,0x2049,0x2065,
    0x2089,0x20A5,0x20C9,0x20E5,0x2109,0x2125,0x2149,0x2165,
    0x2189,0x21A5,0x21C9,0x21E5,0x2209,0x2225,0x2249,0x2265,
    0x2289,0x22A5,0x22C9,0x22E5,0x2309,0x2325,0x2349,0x2365,
    0x2389,0x23A5,0x23C9,0x23E5,0x2409,0x2425,0x2449,0x2465,
    0x2489,0x24A5,0x24C9,0x24E5,0x2509,0x2525,0x2549,0x2565,
    0x2589,0x25A5,0x25C9,0x25E5,0x2609,0x2625,0x2649,0x2665,
    0x2689,0x26A5,0x26C9,0x26E5,0x2729,0x2745,0x2769,0x2785,
    0x27A9,0x27C5,0x27E9,0x2805,0x2829,0x2845,0x2869,0x2885,
    0x28A9,0x28C5,0x28E9,0x2905,0x2949,0x2965,0x2989,0x29A5,
    0x29C9,0x29E5,0x2A09,0x2A25,0x2A49,0x2A65,0x2A89,0x2AA5,
    0x2AC9,0x2AE5,0x2B09,0x2B25,0x2B49,0x2B65,0x2B89,0x2BA5,
    0x2BC9,0x2BE5,0x2C09,0x2C25,0x2C49,0x2C65,0x2C89,0x2CA5,
    0x2CC9,0x2CE5,0x2D09,0x2D25,0x2D49,0x2D65,0x2D89,0x2DA5,
    0x2DC9,0x2DE5,0x2E09,0x2E25,0x2E49,0x2E65,0x2E89,0x2EA5,
    0x2EC9,0x2EE5,0x2F09,0x2F45,0x2F69,0x2F85,0x2FA9,0x2FC5,
    0x3029,0x3065,0x3089,0x30A5,0x30C9,0x3105,0x3129,0x3185,
    0x31C9,0x3245,0x3269,0x32A5,0x32C9,0x3325,0x3389,0x33C5,
    0x33E9,0x3425,0x3449,0x3465,0x3489,0x34A5,0x34C9,0x3505,
    0x3529,0x3545,0x3589,0x35A5,0x35C9,0x3605,0x3629,0x3685,
    0x36A9,0x36C5,0x36E9,0x3725,0x3767,0x3789,0x37A5,0x3807,
    0x3889,0x38A8,0x38C5,0x38E9,0x3908,0x3925,0x3949,0x3968,
    0x3985,0x39A9,0x39C5,0x39E9,0x3A05,0x3A29,0x3A45,0x3A69,
    0x3A85,0x3AA9,0x3AC5,0x3AE9,0x3B05,0x3B29,0x3B45,0x3B69,
    0x3B85,0x3BC9,0x3BE5,0x3C09,0x3C25,0x3C49,0x3C65,0x3C89,
    0x3CA5,0x3CC9,0x3CE5,0x3D09,0x3D25,0x3D49,0x3D65,0x3D89,
    0x3DA5,0x3DC9,0x3DE5,0x3E29,0x3E48,0x3E65,0x3E89,0x3EA5,
    0x3EC9,0x3F25,0x3F49,0x3F65,0x3F89,0x3FA5,0x3FC9,0x3FE5,
    0x4009,0x4025,0x4049,0x4065,0x4089,0x40A5,0x40C9,0x40E5,
    0x4109,0x4125,0x4149,0x4165,0x4189,0x41A5,0x41C9,0x41E5,
    0x4209,0x4225,0x4249,0x4265,0x4289,0x42A5,0x42C9,0x42E5,
    0x4309,0x4325,0x4349,0x4365,0x4389,0x43A5,0x43C9,0x43E5,
    0x4409,0x4425,0x4449,0x4465,0x4489,0x44A5,0x44C9,0x44E5,
    0x4509,0x4525,0x4549,0x4565,0x4589,0x45A5,0x45C9,0x45E5,
    0x4609,0x4625,0x4649,0x4665,0x4749,0x4785,0x47A9,0x47E5,
    0x4829,0x4845,0x4869,0x48E5,0x4909,0x4925,0x4949,0x4965,
    0x4989,0x49A5,0x49C9,0x49E5,0x5287,0x52A5,0x5606,0x5858,
    0x58C6,0x5A58,0x5C06,0x5CB8,0x5D86,0x5DB8,0x5DC6,0x5DF8,
    0x600C,0x6E09,0x6E25,0x6E49,0x6E65,0x6E86,0x6EB8,0x6EC9,
    0x6EE5,0x6F00,0x6F46,0x6F65,0x6FD5,0x6FE9,0x7000,0x7098,
    0x70C9,0x70F5,0x7109,0x7160,0x7189,0x71A0,0x71C9,0x7205,
    0x7229,0x7440,0x7469,0x7585,0x79E9,0x7A05,0x7A49,0x7AA5,
    0x7B09,0x7B25,0x7B49,0x7B65,0x7B89,0x7BA5,0x7BC9,0x7BE5,
    0x7C09,0x7C25,0x7C49,0x7C65,0x7C89,0x7CA5,0x7CC9,0x7CE5,
    0x7D09,0x7D25,0x7D49,0x7D65,0x7D89,0x7DA5,0x7DC9,0x7DE5,
    0x7E89,0x7EA5,0x7ED9,0x7EE9,0x7F05,0x7F29,0x7F65,0x7FA9,
    0x8605,0x8C09,0x8C25,0x8C49,0x8C65,0x8C89,0x8CA5,0x8CC9,
    0x8CE5,0x8D09,0x8D25,0x8D49,0x8D65,0x8D89,0x8DA5,0x8DC9,
    0x8DE5,0x8E09,0x8E25,0x8E49,0x8E65,0x8E89,0x8EA5,0x8EC9,
    0x8EE5,0x8F09,0x8F25,0x8F49,0x8F65,0x8F89,0x8FA5,0x8FC9,
    0x8FE5,0x9009,0x9025,0x905A,0x906C,0x910B,0x9149,0x9165,
    0x9189,0x91A5,0x91C9,0x91E5,0x9209,0x9225,0x9249,0x9265,
    0x9289,0x92A5,0x92C9,0x92E5,0x9309,0x9325,0x9349,0x9365,
    0x9389,0x93A5,0x93C9,0x93E5,0x9409,0x9425,0x9449,0x9465,
    0x9489,0x94A5,0x94C9,0x94E5,0x9509,0x9525,0x9549,0x9565,
    0x9589,0x95A5,0x95C9,0x95E5,0x9609,0x9625,0x9649,0x9665,
    0x9689,0x96A5,0x96C9,0x96E5,0x9709,0x9725,0x9749,0x9765,
    0x9789,0x97A5,0x97C9,0x97E5,0x9809,0x9845,0x9869,0x9885,
    0x98A9,0x98C5,0x98E9,0x9905,0x9929,0x9945,0x9969,0x9985,
    0x99A9,0x99C5,0x9A09,0x9A25,0x9A49,0x9A65,0x9A89,0x9AA5,
    0x9AC9,0x9AE5,0x9B09,0x9B25,0x9B49,0x9B65,0x9B89,0x9BA5,
    0x9BC9,0x9BE5,0x9C09,0x9C25,0x9C49,0x9C65,0x9C89,0x9CA5,
    0x9CC9,0x9CE5,0x9D09,0x9D25,0x9D49,0x9D65,0x9D89,0x9DA5,
    0x9DC9,0x9DE5,0x9E09,0x9E25,0x9E49,0x9E65,0x9E89,0x9EA5,
    0x9EC9,0x9EE5,0x9F09,0x9F25,0x9F49,0x9F65,0x9F89,0x9FA5,
    0x9FC9,0x9FE5,0xA009,0xA025,0xA049,0xA065,0xA089,0xA0A5,
    0xA0C9,0xA0E5,0xA109,0xA125,0xA149,0xA165,0xA189,0xA1A5,
    0xA1C9,0xA1E5,0xA209,0xA225,0xA249,0xA265,0xA289,0xA2A5,
    0xA2C9,0xA2E5,0xA309,0xA325,0xA349,0xA365,0xA389,0xA3A5,
    0xA3C9,0xA3E5,0xA409,0xA425,0xA449,0xA465,0xA489,0xA4A5,
    0xA4C9,0xA4E5,0xA509,0xA525,0xA549,0xA565,0xA589,0xA5A5,
    0xA5C9,0xA5E5,0xA600,0xA629,0xAAE0,0xAB26,0xAB55,0xAC05,
    0xB135,0xB151,0xB160,0xB1BA,0xB1F7,0xB200,0xB22C,0xB7D1,
    0xB7EC,0xB815,0xB82C,0xB875,0xB88C,0xB8D5,0xB8EC,0xB900,
    0xBA07,0xBD60,0xBDE7,0xBE75,0xBEA0,0xC002,0xC0D9,0xC135,
    0xC177,0xC195,0xC1DA,0xC20C,0xC375,0xC382,0xC3B5,0xC407,
    0xC806,0xC827,0xC96C,0xCC0D,0xCD55,0xCDC7,0xCE0C,0xCE27,
    0xDA95,0xDAA7,0xDACC,0xDBA2,0xDBDA,0xDBEC,0xDCA6,0xDCEC,
    0xDD3A,0xDD4C,0xDDC7,0xDE0D,0xDF47,0xDFBA,0xDFE7,0xE015,
    0xE1C0,0xE1E2,0xE207,0xE22C,0xE247,0xE60C,0xE960,0xE9A7,
    0xF4CC,0xF627,0xF640,0xF80D,0xF947,0xFD6C,0xFE86,0xFEDA,
    0xFEF5,0xFF46,0xFF60,0xFFAC,0xFFD7,0x10007,0x102CC,0x10346,
    0x1036C,0x10486,0x104AC,0x10506,0x1052C,0x105C0,0x10615,0x107E0,
    0x10807,0x10B2C,0x10B80,0x10BD5,0x10BE0,0x10C07,0x10D60,0x10E07,
    0x11118,0x11127,0x111E0,0x11202,0x11240,0x1130C,0x11407,0x11926,
    0x1194C,0x11C42,0x11C6C,0x1206A,0x12087,0x1274C,0x1276A,0x1278C,
    0x127A7,0x127CA,0x1282C,0x1292A,0x129AC,0x129CA,0x12A07,0x12A2C,
    0x12B07,0x12C4C,0x12C95,0x12CCD,0x12E15,0x12E26,0x12E47,0x1302C,
    0x1304A,0x13080,0x130A7,0x131A0,0x131E7,0x13220,0x13267,0x13520,
    0x13547,0x13620,0x13647,0x13660,0x136C7,0x13740,0x1378C,0x137A7,
    0x137CA,0x1382C,0x138A0,0x138EA,0x13920,0x1396A,0x139AC,0x139C7,
    0x139E0,0x13AEA,0x13B00,0x13B87,0x13BC0,0x13BE7,0x13C4C,0x13C80,
    0x13CCD,0x13E07,0x13E57,0x13E8F,0x13F5A,0x13F77,0x13F87,0x13FB5,
    0x13FCC,0x13FE0,0x1402C,0x1406A,0x14080,0x140A7,0x14160,0x141E7,
    0x14220,0x14267,0x14520,0x14547,0x14620,0x14647,0x14680,0x146A7,
    0x146E0,0x14707,0x14740,0x1478C,0x147A0,0x147CA,0x1482C,0x14860,
    0x148EC,0x14920,0x1496C,0x149C0,0x14A2C,0x14A40,0x14B27,0x14BA0,
    0x14BC7,0x14BE0,0x14CCD,0x14E0C,0x14E47,0x14EAC,0x14ED5,0x14EE0,
    0x1502C,0x1506A,0x15080,0x150A7,0x151C0,0x151E7,0x15240,0x15267,
    0x15520,0x15547,0x15620,0x15647,0x15680,0x156A7,0x15740,0x1578C,
    0x157A7,0x157CA,0x1582C,0x158C0,0x158EC,0x1592A,0x15940,0x1596A,
    0x159AC,0x159C0,0x15A07,0x15A20,0x15C07,0x15C4C,0x15C80,0x15CCD,
    0x15E15,0x15E37,0x15E40,0x15F27,0x15F4C,0x16000,0x1602C,0x1604A,
    0x16080,0x160A7,0x161A0,0x161E7,0x16220,0x16267,0x16520,0x16547,
    0x16620,0x16647,0x16680,0x166A7,0x16740,0x1678C,0x167A7,0x167CA,
    0x167EC,0x1680A,0x1682C,0x168A0,0x168EA,0x16920,0x1696A,0x169AC,
    0x169C0,0x16AAC,0x16AEA,0x16B00,0x16B87,0x16BC0,0x16BE7,0x16C4C,
    0x16C80,0x16CCD,0x16E1A,0x16E27,0x16E4F,0x16F00,0x1704C,0x17067,
    0x17080,0x170A7,0x17160,0x171C7,0x17220,0x17247,0x172C0,0x17327,
    0x17360,0x17387,0x173A0,0x173C7,0x17400,0x17467,0x174A0,0x17507,
    0x17560,0x175C7,0x17740,0x177CA,0x1780C,0x1782A,0x17860,0x178CA,
    0x17920,0x1794A,0x179AC,0x179C0,0x17A07,0x17A20,0x17AEA,0x17B00,
    0x17CCD,0x17E0F,0x17E7A,0x17F37,0x17F5A,0x17F60,0x1800C,0x1802A,
    0x1808C,0x180A7,0x181A0,0x181C7,0x18220,0x18247,0x18520,0x18547,
    0x18740,0x1878C,0x187A7,0x187CC,0x1882A,0x188A0,0x188CC,0x18920,
    0x1894C,0x189C0,0x18AAC,0x18AE0,0x18B07,0x18B60,0x18BA7,0x18BC0,
    0x18C07,0x18C4C,0x18C80,0x18CCD,0x18E00,0x18EF5,0x18F0F,0x18FFA,
    0x19007,0x1902C,0x1904A,0x19095,0x190A7,0x191A0,0x191C7,0x19220,
    0x19247,0x19520,0x19547,0x19680,0x196A7,0x19740,0x1978C,0x197A7,
    0x197CA,0x197EC,0x1980A,0x198A0,0x198CC,0x198EA,0x19920,0x1994A,
    0x1998C,0x199C0,0x19AAA,0x19AE0,0x19BA7,0x19BE0,0x19C07,0x19C4C,
    0x19C80,0x19CCD,0x19E00,0x19E27,0x19E6A,0x19E80,0x1A00C,0x1A04A,
    0x1A087,0x1A1A0,0x1A1C7,0x1A220,0x1A247,0x1A76C,0x1A7A7,0x1A7CA,
    0x1A82C,0x1A8A0,0x1A8CA,0x1A920,0x1A94A,0x1A9AC,0x1A9C7,0x1A9FA,
    0x1AA00,0x1AA87,0x1AAEA,0x1AB0F,0x1ABE7,0x1AC4C,0x1AC80,0x1ACCD,
    0x1AE0F,0x1AF3A,0x1AF47,0x1B000,0x1B02C,0x1B04A,0x1B080,0x1B0A7,
    0x1B2E0,0x1B347,0x1B640,0x1B667,0x1B780,0x1B7A7,0x1B7C0,0x1B807,
    0x1B8E0,0x1B94C,0x1B960,0x1B9EA,0x1BA4C,0x1BAA0,0x1BACC,0x1BAE0,
    0x1BB0A,0x1BC00,0x1BCCD,0x1BE00,0x1BE4A,0x1BE95,0x1BEA0,0x1C027,
    0x1C62C,0x1C647,0x1C68C,0x1C760,0x1C7F7,0x1C807,0x1C8C6,0x1C8EC,
    0x1C9F5,0x1CA0D,0x1CB55,0x1CB80,0x1D027,0x1D060,0x1D087,0x1D0A0,
    0x1D0C7,0x1D160,0x1D187,0x1D480,0x1D4A7,0x1D4C0,0x1D4E7,0x1D62C,
    0x1D647,0x1D68C,0x1D7A7,0x1D7C0,0x1D807,0x1D8A0,0x1D8C6,0x1D8E0,
    0x1D90C,0x1D9E0,0x1DA0D,0x1DB40,0x1DB87,0x1DC00,0x1E007,0x1E03A,
    0x1E095,0x1E27A,0x1E295,0x1E2BA,0x1E30C,0x1E35A,0x1E40D,0x1E54F,
    0x1E69A,0x1E6AC,0x1E6DA,0x1E6EC,0x1E71A,0x1E72C,0x1E756,0x1E772,
    0x1E796,0x1E7B2,0x1E7CA,0x1E807,0x1E900,0x1E927,0x1EDA0,0x1EE2C,
    0x1EFEA,0x1F00C,0x1F0B5,0x1F0CC,0x1F107,0x1F1AC,0x1F300,0x1F32C,
    0x1F7A0,0x1F7DA,0x1F8CC,0x1F8FA,0x1F9A0,0x1F9DA,0x1FA15,0x1FABA,
    0x1FB35,0x1FB60,0x20007,0x2056A,0x205AC,0x2062A,0x2064C,0x2070A,
    0x2072C,0x2076A,0x207AC,0x207E7,0x2080D,0x20955,0x20A07,0x20ACA,
    0x20B0C,0x20B47,0x20BCC,0x20C27,0x20C4A,0x20CA7,0x20CEA,0x20DC7,
    0x20E2C,0x20EA7,0x2104C,0x2106A,0x210AC,0x210EA,0x211AC,0x211C7,
    0x211EA,0x2120D,0x2134A,0x213AC,0x213DA,0x21409,0x218C0,0x218E9,
    0x21900,0x219A9,0x219C0,0x21A05,0x21F75,0x21F86,0x21FA5,0x22007,
    0x24920,0x24947,0x249C0,0x24A07,0x24AE0,0x24B07,0x24B20,0x24B47,
    0x24BC0,0x24C07,0x25120,0x25147,0x251C0,0x25207,0x25620,0x25647,
    0x256C0,0x25707,0x257E0,0x25807,0x25820,0x25847,0x258C0,0x25907,
    0x25AE0,0x25B07,0x26220,0x26247,0x262C0,0x26307,0x26B60,0x26BAC,
    0x26C15,0x26D2F,0x26FA0,0x27007,0x2721A,0x27340,0x27409,0x27EC0,
    0x27F05,0x27FC0,0x28011,0x28027,0x2CDBA,0x2CDD5,0x2CDE7,0x2D01D,
    0x2D027,0x2D376,0x2D392,0x2D3A0,0x2D407,0x2DD75,0x2DDCE,0x2DE27,
    0x2DF20,0x2E007,0x2E24C,0x2E2AA,0x2E2C0,0x2E3E7,0x2E64C,0x2E68A,
    0x2E6B5,0x2E6E0,0x2E807,0x2EA4C,0x2EA80,0x2EC07,0x2EDA0,0x2EDC7,
    0x2EE20,0x2EE4C,0x2EE80,0x2F007,0x2F68C,0x2F6CA,0x2F6EC,0x2F7CA,
    0x2F8CC,0x2F8EA,0x2F92C,0x2FA95,0x2FAE6,0x2FB15,0x2FB77,0x2FB87,
    0x2FBAC,0x2FBC0,0x2FC0D,0x2FD40,0x2FE0F,0x2FF40,0x30015,0x300D1,
    0x300F5,0x3016C,0x301C2,0x301EC,0x3020D,0x30340,0x30407,0x30866,
    0x30887,0x30F20,0x31007,0x310AC,0x310E7,0x3152C,0x31547,0x31560,
    0x31607,0x31EC0,0x32007,0x323E0,0x3240C,0x3246A,0x324EC,0x3252A,
    0x32580,0x3260A,0x3264C,0x3266A,0x3272C,0x32780,0x3281A,0x32820,
    0x32895,0x328CD,0x32A07,0x32DC0,0x32E07,0x32EA0,0x33007,0x33580,
    0x33607,0x33940,0x33A0D,0x33B4F,0x33B60,0x33BDA,0x34007,0x342EC,
    0x3432A,0x3436C,0x34380,0x343D5,0x34407,0x34AAA,0x34ACC,0x34AEA,
    0x34B0C,0x34BE0,0x34C0C,0x34C2A,0x34C4C,0x34C6A,0x34CAC,0x34DAA,
    0x34E6C,0x34FA0,0x34FEC,0x3500D,0x35140,0x3520D,0x35340,0x35415,
    0x354E6,0x35515,0x355C0,0x3560C,0x357CB,0x357EC,0x359E0,0x3600C,
    0x3608A,0x360A7,0x3668C,0x366AA,0x366CC,0x3676A,0x3678C,0x367AA,
    0x3684C,0x3686A,0x368A7,0x369A0,0x36A0D,0x36B55,0x36C3A,0x36D6C,
    0x36E9A,0x36FB5,0x36FE0,0x3700C,0x3704A,0x37067,0x3742A,0x3744C,
    0x374CA,0x3750C,0x3754A,0x3756C,0x375C7,0x3760D,0x37747,0x37CCC,
    0x37CEA,0x37D0C,0x37D4A,0x37DAC,0x37DCA,0x37DEC,0x37E4A,0x37E80,
    0x37F95,0x38007,0x3848A,0x3858C,0x3868A,0x386CC,0x38700,0x38775,
    0x3880D,0x38940,0x389A7,0x38A0D,0x38B47,0x38F06,0x38FD5,0x39005,
    0x39120,0x39209,0x39760,0x397A9,0x39815,0x39900,0x39A0C,0x39A75,
    0x39A8C,0x39C2A,0x39C4C,0x39D27,0x39DAC,0x39DC7,0x39E8C,0x39EA7,
    0x39EEA,0x39F0C,0x39F47,0x39F60,0x3A005,0x3A586,0x3AD65,0x3AF06,
    0x3AF25,0x3B366,0x3B80C,0x3C009,0x3C025,0x3C049,0x3C065,0x3C089,
    0x3C0A5,0x3C0C9,0x3C0E5,0x3C109,0x3C125,0x3C149,0x3C165,0x3C189,
    0x3C1A5,0x3C1C9,0x3C1E5,0x3C209,0x3C225,0x3C249,0x3C265,0x3C289,
    0x3C2A5,0x3C2C9,0x3C2E5,0x3C309,0x3C325,0x3C349,0x3C365,0x3C389,
    0x3C3A5,0x3C3C9,0x3C3E5,0x3C409,0x3C425,0x3C449,0x3C465,0x3C489,
    0x3C4A5,0x3C4C9,0x3C4E5,0x3C509,0x3C525,0x3C549,0x3C565,0x3C589,
    0x3C5A5,0x3C5C9,0x3C5E5,0x3C609,0x3C625,0x3C649,0x3C665,0x3C689,
    0x3C6A5,0x3C6C9,0x3C6E5,0x3C709,0x3C725,0x3C749,0x3C765,0x3C789,
    0x3C7A5,0x3C7C9,0x3C7E5,0x3C809,0x3C825,0x3C849,0x3C865,0x3C889,
    0x3C8A5,0x3C8C9,0x3C8E5,0x3C909,0x3C925,0x3C949,0x3C965,0x3C989,
    0x3C9A5,0x3C9C9,0x3C9E5,0x3CA09,0x3CA25,0x3CA49,0x3CA65,0x3CA89,
    0x3CAA5,0x3CAC9,0x3CAE5,0x3CB09,0x3CB25,0x3CB49,0x3CB65,0x3CB89,
    0x3CBA5,0x3CBC9,0x3CBE5,0x3CC09,0x3CC25,0x3CC49,0x3CC65,0x3CC89,
    0x3CCA5,0x3CCC9,0x3CCE5,0x3CD09,0x3CD25,0x3CD49,0x3CD65,0x3CD89,
    0x3CDA5,0x3CDC9,0x3CDE5,0x3CE09,0x3CE25,0x3CE49,0x3CE65,0x3CE89,
    0x3CEA5,0x3CEC9,0x3CEE5,0x3CF09,0x3CF25,0x3CF49,0x3CF65,0x3CF89,
    0x3CFA5,0x3CFC9,0x3CFE5,0x3D009,0x3D025,0x3D049,0x3D065,0x3D089,
    0x3D0A5,0x3D0C9,0x3D0E5,0x3D109,0x3D125,0x3D149,0x3D165,0x3D189,
    0x3D1A5,0x3D1C9,0x3D1E5,0x3D209,0x3D225,0x3D249,0x3D265,0x3D289,
    0x3D2A5,0x3D3C9,0x3D3E5,0x3D409,0x3D425,0x3D449,0x3D465,0x3D489,
    0x3D4A5,0x3D4C9,0x3D4E5,0x3D509,0x3D525,0x3D549,0x3D565,0x3D589,
    0x3D5A5,0x3D5C9,0x3D5E5,0x3D609,0x3D625,0x3D649,0x3D665,0x3D689,
    0x3D6A5,0x3D6C9,0x3D6E5,0x3D709,0x3D725,0x3D749,0x3D765,0x3D789,
    0x3D7A5,0x3D7C9,0x3D7E5,0x3D809,0x3D825,0x3D849,0x3D865,0x3D889,
    0x3D8A5,0x3D8C9,0x3D8E5,0x3D909,0x3D925,0x3D949,0x3D965,0x3D989,
    0x3D9A5,0x3D9C9,0x3D9E5,0x3DA09,0x3DA25,0x3DA49,0x3DA65,0x3DA89,
    0x3DAA5,0x3DAC9,0x3DAE5,0x3DB09,0x3DB25,0x3DB49,0x3DB65,0x3DB89,
    0x3DBA5,0x3DBC9,0x3DBE5,0x3DC09,0x3DC25,0x3DC49,0x3DC65,0x3DC89,
    0x3DCA5,0x3DCC9,0x3DCE5,0x3DD09,0x3DD25,0x3DD49,0x3DD65,0x3DD89,
    0x3DDA5,0x3DDC9,0x3DDE5,0x3DE09,0x3DE25,0x3DE49,0x3DE65,0x3DE89,
    0x3DEA5,0x3DEC9,0x3DEE5,0x3DF09,0x3DF25,0x3DF49,0x3DF65,0x3DF89,
    0x3DFA5,0x3DFC9,0x3DFE5,0x3E109,0x3E205,0x3E2C0,0x3E309,0x3E3C0,
    0x3E405,0x3E509,0x3E605,0x3E709,0x3E805,0x3E8C0,0x3E909,0x3E9C0,
    0x3EA05,0x3EB00,0x3EB29,0x3EB40,0x3EB69,0x3EB80,0x3EBA9,0x3EBC0,
    0x3EBE9,0x3EC05,0x3ED09,0x3EE05,0x3EFC0,0x3F005,0x3F108,0x3F205,
    0x3F308,0x3F405,0x3F508,0x3F605,0x3F6A0,0x3F6C5,0x3F709,0x3F788,
    0x3F7B8,0x3F7C5,0x3F7F8,0x3F845,0x3F8A0,0x3F8C5,0x3F909,0x3F988,
    0x3F9B8,0x3FA05,0x3FA80,0x3FAC5,0x3FB09,0x3FB80,0x3FBB8,0x3FC05,
    0x3FD09,0x3FDB8,0x3FE00,0x3FE45,0x3FEA0,0x3FEC5,0x3FF09,0x3FF88,
    0x3FFB8,0x3FFE0,0x4001D,0x40162,0x40211,0x402D5,0x40314,0x40333,
    0x40356,0x40374,0x403B3,0x403D6,0x403F4,0x40415,0x4051B,0x4053C,
    0x40542,0x405FD,0x40615,0x40734,0x40753,0x40775,0x407F0,0x40835,
    0x40899,0x408B6,0x408D2,0x408F5,0x40A59,0x40A75,0x40A90,0x40AB5,
    0x40BFD,0x40C02,0x40CA0,0x40CC2,0x40E0F,0x40E26,0x40E40,0x40E8F,
    0x40F59,0x40FB6,0x40FD2,0x40FE6,0x4100F,0x41159,0x411B6,0x411D2,
    0x411E0,0x41206,0x413A0,0x41417,0x41820,0x41A0C,0x41BAB,0x41C2C,
    0x41C4B,0x41CAC,0x41E20,0x4201A,0x42049,0x4207A,0x420E9,0x4211A,
    0x42145,0x42169,0x421C5,0x42209,0x42265,0x4229A,0x422A9,0x422DA,
    0x42319,0x42329,0x423DA,0x42489,0x424BA,0x424C9,0x424FA,0x42509,
    0x4253A,0x42549,0x425DA,0x425E5,0x42609,0x42685,0x426A7,0x42725,
    0x4275A,0x42785,0x427C9,0x42819,0x428A9,0x428C5,0x4295A,0x42979,
    0x4299A,0x429C5,0x429FA,0x42A0F,0x42C0E,0x43069,0x43085,0x430AE,
    0x4312F,0x4315A,0x43180,0x43219,0x432BA,0x43359,0x4339A,0x43419,
    0x4343A,0x43479,0x4349A,0x434D9,0x434FA,0x435D9,0x435FA,0x439D9,
    0x43A1A,0x43A59,0x43A7A,0x43A99,0x43ABA,0x43E99,0x4601A,0x46116,
    0x46132,0x46156,0x46172,0x4619A,0x46419,0x4645A,0x46536,0x46552,
    0x4657A,0x46F99,0x46FBA,0x47379,0x4769A,0x47B99,0x47C5A,0x484E0,
    0x4881A,0x48960,0x48C0F,0x4939A,0x49D4F,0x4A01A,0x4B6F9,0x4B71A,
    0x4B839,0x4B85A,0x4BF19,0x4C01A,0x4CDF9,0x4CE1A,0x4ED16,0x4ED32,
    0x4ED56,0x4ED72,0x4ED96,0x4EDB2,0x4EDD6,0x4EDF2,0x4EE16,0x4EE32,
    0x4EE56,0x4EE72,0x4EE96,0x4EEB2,0x4EECF,0x4F29A,0x4F819,0x4F8B6,
    0x4F8D2,0x4F8F9,0x4FCD6,0x4FCF2,0x4FD16,0x4FD32,0x4FD56,0x4FD72,
    0x4FD96,0x4FDB2,0x4FDD6,0x4FDF2,0x4FE19,0x5001A,0x52019,0x53076,
    0x53092,0x530B6,0x530D2,0x530F6,0x53112,0x53136,0x53152,0x53176,
    0x53192,0x531B6,0x531D2,0x531F6,0x53212,0x53236,0x53252,0x53276,
    0x53292,0x532B6,0x532D2,0x532F6,0x53312,0x53339,0x53B16,0x53B32,
    0x53B56,0x53B72,0x53B99,0x53F96,0x53FB2,0x53FD9,0x5601A,0x56619,
    0x568BA,0x568F9,0x569BA,0x56E80,0x56EDA,0x572C0,0x572FA,0x58009,
    0x58605,0x58C09,0x58C25,0x58C49,0x58CA5,0x58CE9,0x58D05,0x58D29,
    0x58D45,0x58D69,0x58D85,0x58DA9,0x58E25,0x58E49,0x58E65,0x58EA9,
    0x58EC5,0x58F86,0x58FC9,0x59025,0x59049,0x59065,0x59089,0x590A5,
    0x590C9,0x590E5,0x59109,0x59125,0x59149,0x59165,0x59189,0x591A5,
    0x591C9,0x591E5,0x59209,0x59225,0x59249,0x59265,0x59289,0x592A5,
    0x592C9,0x592E5,0x59309,0x59325,0x59349,0x59365,0x59389,0x593A5,
    0x593C9,0x593E5,0x59409,0x59425,0x59449,0x59465,0x59489,0x594A5,
    0x594C9,0x594E5,0x59509,0x59525,0x59549,0x59565,0x59589,0x595A5,
    0x595C9,0x595E5,0x59609,0x59625,0x59649,0x59665,0x59689,0x596A5,
    0x596C9,0x596E5,0x59709,0x59725,0x59749,0x59765,0x59789,0x597A5,
    0x597C9,0x597E5,0x59809,0x59825,0x59849,0x59865,0x59889,0x598A5,
    0x598C9,0x598E5,0x59909,0x59925,0x59949,0x59965,0x59989,0x599A5,
    0x599C9,0x599E5,0x59A09,0x59A25,0x59A49,0x59A65,0x59A89,0x59AA5,
    0x59AC9,0x59AE5,0x59B09,0x59B25,0x59B49,0x59B65,0x59B89,0x59BA5,
    0x59BC9,0x59BE5,0x59C09,0x59C25,0x59C49,0x59C65,0x59CBA,0x59D69,
    0x59D85,0x59DA9,0x59DC5,0x59DEC,0x59E49,0x59E65,0x59E80,0x59F35,
    0x59FAF,0x59FD5,0x5A005,0x5A4C0,0x5A4E5,0x5A500,0x5A5A5,0x5A5C0,
    0x5A607,0x5AD00,0x5ADE6,0x5AE15,0x5AE20,0x5AFEC,0x5B007,0x5B2E0,
    0x5B407,0x5B4E0,0x5B507,0x5B5E0,0x5B607,0x5B6E0,0x5B707,0x5B7E0,
    0x5B807,0x5B8E0,0x5B907,0x5B9E0,0x5BA07,0x5BAE0,0x5BB07,0x5BBE0,
    0x5BC0C,0x5C015,0x5C054,0x5C073,0x5C094,0x5C0B3,0x5C0D5,0x5C134,
    0x5C153,0x5C175,0x5C194,0x5C1B3,0x5C1D5,0x5C2F1,0x5C315,0x5C351,
    0x5C375,0x5C394,0x5C3B3,0x5C3D5,0x5C414,0x5C433,0x5C456,0x5C472,
    0x5C496,0x5C4B2,0x5C4D6,0x5C4F2,0x5C516,0x5C532,0x5C555,0x5C5E6,
    0x5C615,0x5C751,0x5C795,0x5C811,0x5C835,0x5C856,0x5C875,0x5CA1A,
    0x5CA55,0x5CAB6,0x5CAD2,0x5CAF6,0x5CB12,0x5CB36,0x5CB52,0x5CB76,
    0x5CB92,0x5CBB1,0x5CBC0,0x5D01A,0x5D340,0x5D37A,0x5DE80,0x5E01A,
    0x5FAC0,0x5FE1A,0x6001D,0x60035,0x6009A,0x600A6,0x600C7,0x600EE,
    0x60116,0x60132,0x60156,0x60172,0x60196,0x601B2,0x601D6,0x601F2,
    0x60216,0x60232,0x6025A,0x60296,0x602B2,0x602D6,0x602F2,0x60316,
    0x60332,0x60356,0x60372,0x60391,0x603B6,0x603D2,0x6041A,0x6042E,
    0x6054C,0x605CA,0x60611,0x60626,0x606DA,0x6070E,0x60766,0x60787,
    0x607B5,0x607DA,0x60800,0x60827,0x612E0,0x6132C,0x61378,0x613A6,
    0x613E7,0x61411,0x61427,0x61F75,0x61F86,0x61FE7,0x62000,0x620A7,
    0x62600,0x62627,0x631E0,0x6321A,0x6324F,0x632DA,0x63407,0x6381A,
    0x63C80,0x63DFA,0x63E07,0x6401A,0x643E0,0x6440F,0x6455A,0x6490F,
    0x64A1A,0x64A2F,0x64C1A,0x6500F,0x6515A,0x6562F,0x6581A,0x68007,
    0x9B81A,0x9C007,0x1402A6,0x1402C7,0x1491A0,0x14921A,0x1498E0,0x149A07,
    0x149F06,0x149FD5,0x14A007,0x14C186,0x14C1B5,0x14C207,0x14C40D,0x14C547,
    0x14C580,0x14C809,0x14C825,0x14C849,0x14C865,0x14C889,0x14C8A5,0x14C8C9,
    0x14C8E5,0x14C909,0x14C925,0x14C949,0x14C965,0x14C989,0x14C9A5,0x14C9C9,
    0x14C9E5,0x14CA09,0x14CA25,0x14CA49,0x14CA65,0x14CA89,0x14CAA5,0x14CAC9,
    0x14CAE5,0x14CB09,0x14CB25,0x14CB49,0x14CB65,0x14CB89,0x14CBA5,0x14CBC9,
    0x14CBE5,0x14CC09,0x14CC25,0x14CC49,0x14CC65,0x14CC89,0x14CCA5,0x14CCC9,
    0x14CCE5,0x14CD09,0x14CD25,0x14CD49,0x14CD65,0x14CD89,0x14CDA5,0x14CDC7,
    0x14CDEC,0x14CE0B,0x14CE75,0x14CE8C,0x14CFD5,0x14CFE6,0x14D009,0x14D025,
    0x14D049,0x14D065,0x14D089,0x14D0A5,0x14D0C9,0x14D0E5,0x14D109,0x14D125,
    0x14D149,0x14D165,0x14D189,0x14D1A5,0x14D1C9,0x14D1E5,0x14D209,0x14D225,
    0x14D249,0x14D265,0x14D289,0x14D2A5,0x14D2C9,0x14D2E5,0x14D309,0x14D325,
    0x14D349,0x14D365,0x14D386,0x14D3CC,0x14D407,0x14DCCE,0x14DE0C,0x14DE55,
    0x14DF00,0x14E018,0x14E2E6,0x14E418,0x14E449,0x14E465,0x14E489,0x14E4A5,
    0x14E4C9,0x14E4E5,0x14E509,0x14E525,0x14E549,0x14E565,0x14E589,0x14E5A5,
    0x14E5C9,0x14E5E5,0x14E649,0x14E665,0x14E689,0x14E6A5,0x14E6C9,0x14E6E5,
    0x14E709,0x14E725,0x14E749,0x14E765,0x14E789,0x14E7A5,0x14E7C9,0x14E7E5,
    0x14E809,0x14E825,0x14E849,0x14E865,0x14E889,0x14E8A5,0x14E8C9,0x14E8E5,
    0x14E909,0x14E925,0x14E949,0x14E965,0x14E989,0x14E9A5,0x14E9C9,0x14E9E5,
    0x14EA09,0x14EA25,0x14EA49,0x14EA65,0x14EA89,0x14EAA5,0x14EAC9,0x14EAE5,
    0x14EB09,0x14EB25,0x14EB49,0x14EB65,0x14EB89,0x14EBA5,0x14EBC9,0x14EBE5,
    0x14EC09,0x14EC25,0x14EC49,0x14EC65,0x14EC89,0x14ECA5,0x14ECC9,0x14ECE5,
    0x14ED09,0x14ED25,0x14ED49,0x14ED65,0x14ED89,0x14EDA5,0x14EDC9,0x14EDE5,
    0x14EE06,0x14EE25,0x14EF29,0x14EF45,0x14EF69,0x14EF85,0x14EFA9,0x14EFE5,
    0x14F009,0x14F025,0x14F049,0x14F065,0x14F089,0x14F0A5,0x14F0C9,0x14F0E5,
    0x14F106,0x14F138,0x14F169,0x14F185,0x14F1A9,0x14F1C5,0x14F1E7,0x14F209,
    0x14F225,0x14F249,0x14F265,0x14F2C9,0x14F2E5,0x14F309,0x14F325,0x14F349,
    0x14F365,0x14F389,0x14F3A5,0x14F3C9,0x14F3E5,0x14F409,0x14F425,0x14F449,
    0x14F465,0x14F489,0x14F4A5,0x14F4C9,0x14F4E5,0x14F509,0x14F525,0x14F549,
    0x14F5E5,0x14F609,0x14F6A5,0x14F6C9,0x14F6E5,0x14F709,0x14F725,0x14F749,
    0x14F765,0x14F789,0x14F7A5,0x14F7C9,0x14F7E5,0x14F809,0x14F825,0x14F849,
    0x14F865,0x14F889,0x14F905,0x14F929,0x14F945,0x14F960,0x14FA09,0x14FA25,
    0x14FA40,0x14FA65,0x14FA80,0x14FAA5,0x14FAC9,0x14FAE5,0x14FB09,0x14FB25,
    0x14FB40,0x14FE46,0x14FEA9,0x14FEC5,0x14FEE7,0x14FF06,0x14FF45,0x14FF67,
    0x15004C,0x150067,0x1500CC,0x1500E7,0x15016C,0x150187,0x15046A,0x1504AC,
    0x1504EA,0x15051A,0x15058C,0x1505A0,0x15060F,0x1506DA,0x150717,0x15073A,
    0x150740,0x150807,0x150E95,0x150F00,0x15100A,0x151047,0x15168A,0x15188C,
    0x1518C0,0x1519D5,0x151A0D,0x151B40,0x151C0C,0x151E47,0x151F15,0x151F67,
    0x151F95,0x151FA7,0x151FEC,0x15200D,0x152147,0x1524CC,0x1525D5,0x152607,
    0x1528EC,0x152A4A,0x152A80,0x152BF5,0x152C07,0x152FA0,0x15300C,0x15306A,
    0x153087,0x15366C,0x15368A,0x1536CC,0x15374A,0x15378C,0x1537CA,0x153835,
    0x1539C0,0x1539E6,0x153A0D,0x153B40,0x153BD5,0x153C07,0x153CAC,0x153CC6,
    0x153CE7,0x153E0D,0x153F47,0x153FE0,0x154007,0x15452C,0x1545EA,0x15462C,
    0x15466A,0x1546AC,0x1546E0,0x154807,0x15486C,0x154887,0x15498C,0x1549AA,
    0x1549C0,0x154A0D,0x154B40,0x154B95,0x154C07,0x154E06,0x154E27,0x154EFA,
    0x154F47,0x154F6A,0x154F8C,0x154FAA,0x154FC7,0x15560C,0x155627,0x15564C,
    0x1556A7,0x1556EC,0x155727,0x1557CC,0x155807,0x15582C,0x155847,0x155860,
    0x155B67,0x155BA6,0x155BD5,0x155C07,0x155D6A,0x155D8C,0x155DCA,0x155E15,
    0x155E47,0x155E66,0x155EAA,0x155ECC,0x155EE0,0x156027,0x1560E0,0x156127,
    0x1561E0,0x156227,0x1562E0,0x156407,0x1564E0,0x156507,0x1565E0,0x156605,
    0x156B78,0x156B86,0x156C05,0x156D26,0x156D58,0x156D80,0x156E05,0x157807,
    0x157C6A,0x157CAC,0x157CCA,0x157D0C,0x157D2A,0x157D75,0x157D8A,0x157DAC,
    0x157DC0,0x157E0D,0x157F40,0x158007,0x1AF480,0x1AF607,0x1AF8E0,0x1AF967,
    0x1AFF80,0x1B0004,0x1C0003,0x1F2007,0x1F4DC0,0x1F4E07,0x1F5B40,0x1F6005,
    0x1F60E0,0x1F6265,0x1F6300,0x1F63A7,0x1F63CC,0x1F63E7,0x1F6539,0x1F6547,
    0x1F66E0,0x1F6707,0x1F67A0,0x1F67C7,0x1F67E0,0x1F6807,0x1F6840,0x1F6867,
    0x1F68A0,0x1F68C7,0x1F7658,0x1F7860,0x1F7A67,0x1FA7D2,0x1FA7F6,0x1FA81A,
    0x1FAA07,0x1FB200,0x1FB247,0x1FB900,0x1FB9FA,0x1FBA00,0x1FBE07,0x1FBF97,
    0x1FBFBA,0x1FC00C,0x1FC215,0x1FC2F6,0x1FC312,0x1FC335,0x1FC340,0x1FC40C,
    0x1FC615,0x1FC631,0x1FC670,0x1FC6B6,0x1FC6D2,0x1FC6F6,0x1FC712,0x1FC736,
    0x1FC752,0x1FC776,0x1FC792,0x1FC7B6,0x1FC7D2,0x1FC7F6,0x1FC812,0x1FC836,
    0x1FC852,0x1FC876,0x1FC892,0x1FC8B5,0x1FC8F6,0x1FC912,0x1FC935,0x1FC9B0,
    0x1FCA15,0x1FCA60,0x1FCA95,0x1FCB11,0x1FCB36,0x1FCB52,0x1FCB76,0x1FCB92,
    0x1FCBB6,0x1FCBD2,0x1FCBF5,0x1FCC59,0x1FCC71,0x1FCC99,0x1FCCE0,0x1FCD15,
    0x1FCD37,0x1FCD55,0x1FCD80,0x1FCE07,0x1FCEA0,0x1FCEC7,0x1FDFA0,0x1FDFE2,
    0x1FE000,0x1FE035,0x1FE097,0x1FE0B5,0x1FE116,0x1FE132,0x1FE155,0x1FE179,
    0x1FE195,0x1FE1B1,0x1FE1D5,0x1FE20D,0x1FE355,0x1FE399,0x1FE3F5,0x1FE429,
    0x1FE776,0x1FE795,0x1FE7B2,0x1FE7D8,0x1FE7F0,0x1FE818,0x1FE825,0x1FEB76,
    0x1FEB99,0x1FEBB2,0x1FEBD9,0x1FEBF6,0x1FEC12,0x1FEC35,0x1FEC56,0x1FEC72,
    0x1FEC95,0x1FECC7,0x1FEE06,0x1FEE27,0x1FF3C6,0x1FF407,0x1FF7E0,0x1FF847,
    0x1FF900,0x1FF947,0x1FFA00,0x1FFA47,0x1FFB00,0x1FFB47,0x1FFBA0,0x1FFC17,
    0x1FFC59,0x1FFC78,0x1FFC9A,0x1FFCB7,0x1FFCE0,0x1FFD1A,0x1FFD39,0x1FFDBA,
    0x1FFDE0,0x1FFF22,0x1FFF9A,0x1FFFC0,0x200007,0x200180,0x2001A7,0x2004E0,
    0x200507,0x200760,0x200787,0x2007C0,0x2007E7,0x2009C0,0x200A07,0x200BC0,
    0x201007,0x201F60,0x202015,0x202060,0x2020EF,0x202680,0x2026FA,0x20280E,
    0x202EAF,0x202F3A,0x20314F,0x20319A,0x2031E0,0x20321A,0x2033A0,0x20341A,
    0x203420,0x203A1A,0x203FAC,0x203FC0,0x205007,0x2053A0,0x205407,0x205A20,
    0x205C0C,0x205C2F,0x205F80,0x206007,0x20640F,0x206480,0x2065A7,0x20682E,
    0x206847,0x20694E,0x206960,0x206A07,0x206ECC,0x206F60,0x207007,0x2073C0,
    0x2073F5,0x207407,0x207880,0x207907,0x207A15,0x207A2E,0x207AC0,0x208009,
    0x208505,0x208A07,0x2093C0,0x20940D,0x209540,0x209609,0x209A80,0x209B05,
    0x209F80,0x20A007,0x20A500,0x20A607,0x20AC80,0x20ADF5,0x20AE09,0x20AF60,
    0x20AF89,0x20B160,0x20B189,0x20B260,0x20B289,0x20B2C0,0x20B2E5,0x20B440,
    0x20B465,0x20B640,0x20B665,0x20B740,0x20B765,0x20B7A0,0x20C007,0x20E6E0,
    0x20E807,0x20EAC0,0x20EC07,0x20ED00,0x20F006,0x20F0C0,0x20F0E6,0x20F620,
    0x20F646,0x20F760,0x210007,0x2100C0,0x210107,0x210120,0x210147,0x2106C0,
    0x2106E7,0x210720,0x210787,0x2107A0,0x2107E7,0x210AC0,0x210AF5,0x210B0F,
    0x210C07,0x210EFA,0x210F2F,0x211007,0x2113E0,0x2114EF,0x211600,0x211C07,
    0x211E60,0x211E87,0x211EC0,0x211F6F,0x212007,0x2122CF,0x212380,0x2123F5,
    0x212407,0x212740,0x2127F5,0x212800,0x213007,0x213700,0x21378F,0x2137C7,
    0x21380F,0x213A00,0x213A4F,0x214007,0x21402C,0x214080,0x2140AC,0x2140E0,
    0x21418C,0x214207,0x214280,0x2142A7,0x214300,0x214327,0x2146C0,0x21470C,
    0x214760,0x2147EC,0x21480F,0x214920,0x214A15,0x214B20,0x214C07,0x214FAF,
    0x214FF5,0x215007,0x2153AF,0x215400,0x215807,0x21591A,0x215927,0x215CAC,
    0x215CE0,0x215D6F,0x215E15,0x215EE0,0x216007,0x2166C0,0x216735,0x216807,
    0x216AC0,0x216B0F,0x216C07,0x216E60,0x216F0F,0x217007,0x217240,0x217335,
    0x2173A0,0x21752F,0x217600,0x218007,0x218920,0x219009,0x219660,0x219805,
    0x219E60,0x219F4F,0x21A007,0x21A48C,0x21A500,0x21A60D,0x21A740,0x21CC0F,
    0x21CFE0,0x21D007,0x21D540,0x21D56C,0x21D5B1,0x21D5C0,0x21D607,0x21D640,
    0x21DFAC,0x21E007,0x21E3AF,0x21E4E7,0x21E500,0x21E607,0x21E8CC,0x21EA2F,
    0x21EAB5,0x21EB40,0x21EE07,0x21F04C,0x21F0D5,0x21F140,0x21F607,0x21F8AF,
    0x21F980,0x21FC07,0x21FEE0,0x22000A,0x22002C,0x22004A,0x220067,0x22070C,
    0x2208F5,0x2209C0,0x220A4F,0x220CCD,0x220E0C,0x220E27,0x220E6C,0x220EA7,
    0x220EC0,0x220FEC,0x22104A,0x221067,0x22160A,0x22166C,0x2216EA,0x22172C,
    0x221775,0x2217A2,0x2217D5,0x22184C,0x221860,0x2219A2,0x2219C0,0x221A07,
    0x221D20,0x221E0D,0x221F40,0x22200C,0x222067,0x2224EC,0x22258A,0x2225AC,
    0x2226A0,0x2226CD,0x222815,0x222887,0x2228AA,0x2228E7,0x222900,0x222A07,
    0x222E6C,0x222E95,0x222EC7,0x222EE0,0x22300C,0x22304A,0x223067,0x22366A,
    0x2236CC,0x2237EA,0x223827,0x2238B5,0x22392C,0x2239B5,0x2239CA,0x2239EC,
    0x223A0D,0x223B47,0x223B75,0x223B87,0x223BB5,0x223C00,0x223C2F,0x223EA0,
    0x224007,0x224240,0x224267,0x22458A,0x2245EC,0x22464A,0x22468C,0x2246AA,
    0x2246CC,0x224715,0x2247CC,0x2247E7,0x22482C,0x224840,0x225007,0x2250E0,
    0x225107,0x225120,0x225147,0x2251C0,0x2251E7,0x2253C0,0x2253E7,0x225535,
    0x225540,0x225607,0x225BEC,0x225C0A,0x225C6C,0x225D60,0x225E0D,0x225F40,
    0x22600C,0x22604A,0x226080,0x2260A7,0x2261A0,0x2261E7,0x226220,0x226267,
    0x226520,0x226547,0x226620,0x226647,0x226680,0x2266A7,0x226740,0x22676C,
    0x2267A7,0x2267CA,0x22680C,0x22682A,0x2268A0,0x2268EA,0x226920,0x22696A,
    0x2269C0,0x226A07,0x226A20,0x226AEA,0x226B00,0x226BA7,0x226C4A,0x226C80,
    0x226CCC,0x226DA0,0x226E0C,0x226EA0,0x228007,0x2286AA,0x22870C,0x22880A,
    0x22884C,0x2288AA,0x2288CC,0x2288E7,0x228975,0x228A0D,0x228B55,0x228B80,
    0x228BB5,0x228BCC,0x228BE7,0x228C40,0x229007,0x22960A,0x22966C,0x22972A,
    0x22974C,0x22976A,0x2297EC,0x22982A,0x22984C,0x229887,0x2298D5,0x2298E7,
    0x229900,0x229A0D,0x229B40,0x22B007,0x22B5EA,0x22B64C,0x22B6C0,0x22B70A,
    0x22B78C,0x22B7CA,0x22B7EC,0x22B835,0x22BB07,0x22BB8C,0x22BBC0,0x22C007,
    0x22C60A,0x22C66C,0x22C76A,0x22C7AC,0x22C7CA,0x22C7EC,0x22C835,0x22C887,
    0x22C8A0,0x22CA0D,0x22CB40,0x22CC15,0x22CDA0,0x22D007,0x22D56C,0x22D58A,
    0x22D5AC,0x22D5CA,0x22D60C,0x22D6CA,0x22D6EC,0x22D707,0x22D735,0x22D740,
    0x22D80D,0x22D940,0x22E007,0x22E360,0x22E3AC,0x22E40A,0x22E44C,0x22E4CA,
    0x22E4EC,0x22E580,0x22E60D,0x22E74F,0x22E795,0x22E7FA,0x22E807,0x22E8E0,
    0x230007,0x23058A,0x2305EC,0x23070A,0x23072C,0x230775,0x230780,0x231409,
    0x231805,0x231C0D,0x231D4F,0x231E60,0x231FE7,0x2320E0,0x232127,0x232140,
    0x232187,0x232280,0x2322A7,0x2322E0,0x232307,0x23260A,0x2326C0,0x2326EA,
    0x232720,0x23276C,0x2327AA,0x2327CC,0x2327E7,0x23280A,0x232827,0x23284A,
    0x23286C,0x232895,0x2328E0,0x232A0D,0x232B40,0x233407,0x233500,0x233547,
    0x233A2A,0x233A8C,0x233B00,0x233B4C,0x233B8A,0x233C0C,0x233C27,0x233C55,
    0x233C67,0x233C8A,0x233CA0,0x234007,0x23402C,0x234167,0x23466C,0x23472A,
    0x234747,0x23476C,0x2347F5,0x2348EC,0x234900,0x234A07,0x234A2C,0x234AEA,
    0x234B2C,0x234B87,0x23514C,0x2352EA,0x23530C,0x235355,0x2353A7,0x2353D5,
    0x235460,0x235607,0x235F20,0x236015,0x236140,0x238007,0x238120,0x238147,
    0x2385EA,0x23860C,0x2386E0,0x23870C,0x2387CA,0x2387EC,0x238807,0x238835,
    0x2388C0,0x238A0D,0x238B4F,0x238DA0,0x238E15,0x238E47,0x239200,0x23924C,
    0x239500,0x23952A,0x23954C,0x23962A,0x23964C,0x23968A,0x2396AC,0x2396E0,
    0x23A007,0x23A0E0,0x23A107,0x23A140,0x23A167,0x23A62C,0x23A6E0,0x23A74C,
    0x23A760,0x23A78C,0x23A7C0,0x23A7EC,0x23A8C7,0x23A8EC,0x23A900,0x23AA0D,
    0x23AB40,0x23AC07,0x23ACC0,0x23ACE7,0x23AD20,0x23AD47,0x23B14A,0x23B1E0,
    0x23B20C,0x23B240,0x23B26A,0x23B2AC,0x23B2CA,0x23B2EC,0x23B307,0x23B320,
    0x23B40D,0x23B540,0x23DC07,0x23DE6C,0x23DEAA,0x23DEF5,0x23DF20,0x23E00C,
    0x23E047,0x23E06A,0x23E087,0x23E220,0x23E247,0x23E68A,0x23E6CC,0x23E760,
    0x23E7CA,0x23E80C,0x23E82A,0x23E84C,0x23E875,0x23EA0D,0x23EB40,0x23F607,
    0x23F620,0x23F80F,0x23FABA,0x23FBB7,0x23FC3A,0x23FE40,0x23FFF5,0x240007,
    0x247340,0x24800E,0x248DE0,0x248E15,0x248EA0,0x249007,0x24A880,0x25F207,
    0x25FE35,0x25FE60,0x260007,0x268602,0x26880C,0x268827,0x2688EC,0x268AC0,
    0x288007,0x28C8E0,0x2D0007,0x2D4720,0x2D4807,0x2D4BE0,0x2D4C0D,0x2D4D40,
    0x2D4DD5,0x2D4E07,0x2D57E0,0x2D580D,0x2D5940,0x2D5A07,0x2D5DC0,0x2D5E0C,
    0x2D5EB5,0x2D5EC0,0x2D6007,0x2D660C,0x2D66F5,0x2D679A,0x2D6806,0x2D6895,
    0x2D68BA,0x2D68C0,0x2D6A0D,0x2D6B40,0x2D6B6F,0x2D6C40,0x2D6C67,0x2D6F00,
    0x2D6FA7,0x2D7200,0x2DC809,0x2DCC05,0x2DD00F,0x2DD2F5,0x2DD360,0x2DE007,
    0x2DE960,0x2DE9EC,0x2DEA07,0x2DEA2A,0x2DF100,0x2DF1EC,0x2DF266,0x2DF400,
    0x2DFC06,0x2DFC55,0x2DFC66,0x2DFC8C,0x2DFCA0,0x2DFE0A,0x2DFE40,0x2E0007,
    0x30FF00,0x310007,0x319AC0,0x31A007,0x31A120,0x35FE06,0x35FE80,0x35FEA6,
    0x35FF80,0x35FFA6,0x35FFE0,0x360007,0x362460,0x362647,0x362660,0x362A07,
    0x362A60,0x362AA7,0x362AC0,0x362C87,0x362D00,0x362E07,0x365F80,0x378007,
    0x378D60,0x378E07,0x378FA0,0x379007,0x379120,0x379207,0x379340,0x37939A,
    0x3793AC,0x3793F5,0x379402,0x379480,0x39E00C,0x39E5C0,0x39E60C,0x39E8E0,
    0x39EA1A,0x39F880,0x3A001A,0x3A1EC0,0x3A201A,0x3A24E0,0x3A253A,0x3A2CAA,
    0x3A2CEC,0x3A2D5A,0x3A2DAA,0x3A2E62,0x3A2F6C,0x3A307A,0x3A30AC,0x3A319A,
    0x3A354C,0x3A35DA,0x3A3D60,0x3A401A,0x3A484C,0x3A48BA,0x3A48C0,0x3A580F,
    0x3A5A80,0x3A5C0F,0x3A5E80,0x3A601A,0x3A6AE0,0x3A6C0F,0x3A6F20,0x3A8009,
    0x3A8345,0x3A8689,0x3A89C5,0x3A8AA0,0x3A8AC5,0x3A8D09,0x3A9045,0x3A9389,
    0x3A93A0,0x3A93C9,0x3A9400,0x3A9449,0x3A9460,0x3A94A9,0x3A94E0,0x3A9529,
    0x3A95A0,0x3A95C9,0x3A96C5,0x3A9740,0x3A9765,0x3A9780,0x3A97A5,0x3A9880,
    0x3A98A5,0x3A9A09,0x3A9D45,0x3AA089,0x3AA0C0,0x3AA0E9,0x3AA160,0x3AA1A9,
    0x3AA2A0,0x3AA2C9,0x3AA3A0,0x3AA3C5,0x3AA709,0x3AA740,0x3AA769,0x3AA7E0,
    0x3AA809,0x3AA8A0,0x3AA8C9,0x3AA8E0,0x3AA949,0x3AAA20,0x3AAA45,0x3AAD89,
    0x3AB0C5,0x3AB409,0x3AB745,0x3ABA89,0x3ABDC5,0x3AC109,0x3AC445,0x3AC789,
    0x3ACAC5,0x3ACE09,0x3AD145,0x3AD4C0,0x3AD509,0x3AD839,0x3AD845,0x3ADB79,
    0x3ADB85,0x3ADC49,0x3ADF79,0x3ADF85,0x3AE2B9,0x3AE2C5,0x3AE389,0x3AE6B9,
    0x3AE6C5,0x3AE9F9,0x3AEA05,0x3AEAC9,0x3AEDF9,0x3AEE05,0x3AF139,0x3AF145,
    0x3AF209,0x3AF539,0x3AF545,0x3AF879,0x3AF885,0x3AF949,0x3AF965,0x3AF980,
    0x3AF9CD,0x3B001A,0x3B400C,0x3B46FA,0x3B476C,0x3B4DBA,0x3B4EAC,0x3B4EDA,
    0x3B508C,0x3B50BA,0x3B50F5,0x3B5180,0x3B536C,0x3B5400,0x3B542C,0x3B5600,
    0x3BE005,0x3BE147,0x3BE165,0x3BE3E0,0x3BE4A5,0x3BE560,0x3C000C,0x3C00E0,
    0x3C010C,0x3C0320,0x3C036C,0x3C0440,0x3C046C,0x3C04A0,0x3C04CC,0x3C0560,
    0x3C0606,0x3C0DC0,0x3C11EC,0x3C1200,0x3C2007,0x3C25A0,0x3C260C,0x3C26E6,
    0x3C27C0,0x3C280D,0x3C2940,0x3C29C7,0x3C29FA,0x3C2A00,0x3C5207,0x3C55CC,
    0x3C55E0,0x3C5807,0x3C5D8C,0x3C5E0D,0x3C5F40,0x3C5FF7,0x3C6000,0x3C9A07,
    0x3C9D66,0x3C9D8C,0x3C9E0D,0x3C9F40,0x3CFC07,0x3CFCE0,0x3CFD07,0x3CFD80,
    0x3CFDA7,0x3CFDE0,0x3CFE07,0x3CFFE0,0x3D0007,0x3D18A0,0x3D18EF,0x3D1A0C,
    0x3D1AE0,0x3D2009,0x3D2445,0x3D288C,0x3D2966,0x3D2980,0x3D2A0D,0x3D2B40,
    0x3D2BD5,0x3D2C00,0x3D8E2F,0x3D959A,0x3D95AF,0x3D9617,0x3D962F,0x3D96A0,
    0x3DA02F,0x3DA5DA,0x3DA5EF,0x3DA7C0,0x3DC007,0x3DC080,0x3DC0A7,0x3DC400,
    0x3DC427,0x3DC460,0x3DC487,0x3DC4A0,0x3DC4E7,0x3DC500,0x3DC527,0x3DC660,
    0x3DC687,0x3DC700,0x3DC727,0x3DC740,0x3DC767,0x3DC780,0x3DC847,0x3DC860,
    0x3DC8E7,0x3DC900,0x3DC927,0x3DC940,0x3DC967,0x3DC980,0x3DC9A7,0x3DCA00,
    0x3DCA27,0x3DCA60,0x3DCA87,0x3DCAA0,0x3DCAE7,0x3DCB00,0x3DCB27,0x3DCB40,
    0x3DCB67,0x3DCB80,0x3DCBA7,0x3DCBC0,0x3DCBE7,0x3DCC00,0x3DCC27,0x3DCC60,
    0x3DCC87,0x3DCCA0,0x3DCCE7,0x3DCD60,0x3DCD87,0x3DCE60,0x3DCE87,0x3DCF00,
    0x3DCF27,0x3DCFA0,0x3DCFC7,0x3DCFE0,0x3DD007,0x3DD140,0x3DD167,0x3DD380,
    0x3DD427,0x3DD480,0x3DD4A7,0x3DD540,0x3DD567,0x3DD780,0x3DDE19,0x3DDE40,
    0x3E001A,0x3E0580,0x3E061A,0x3E1280,0x3E141A,0x3E15E0,0x3E163A,0x3E1800,
    0x3E183A,0x3E1A00,0x3E1A3A,0x3E1EC0,0x3E200F,0x3E21BA,0x3E35C0,0x3E3CDA,
    0x3E4060,0x3E421A,0x3E4780,0x3E481A,0x3E4920,0x3E4A1A,0x3E4A40,0x3E4C1A,
    0x3E4CC0,0x3E601A,0x3E7F78,0x3E801A,0x3EDB00,0x3EDB9A,0x3EDDA0,0x3EDE1A,
    0x3EDFA0,0x3EE01A,0x3EEEE0,0x3EEF7A,0x3EFB40,0x3EFC1A,0x3EFD80,0x3EFE1A,
    0x3EFE20,0x3F001A,0x3F0180,0x3F021A,0x3F0900,0x3F0A1A,0x3F0B40,0x3F0C1A,
    0x3F1100,0x3F121A,0x3F15C0,0x3F161A,0x3F1640,0x3F201A,0x3F4A80,0x3F4C1A,
    0x3F4DC0,0x3F4E1A,0x3F4FA0,0x3F501A,0x3F5120,0x3F521A,0x3F57C0,0x3F57FA,
    0x3F58C0,0x3F59DA,0x3F5B80,0x3F5C1A,0x3F5D20,0x3F5E1A,0x3F5F20,0x3F601A,
    0x3F7260,0x3F729A,0x3F7960,0x3F7E0D,0x3F7F40,0x400007,0x54DC00,0x54E007,
    0x56E740,0x56E807,0x5703C0,0x570407,0x59D440,0x59D607,0x5D7C20,0x5D7E07,
    0x5DCBC0,0x5F0007,0x5F43C0,0x600007,0x626960,0x626A07,0x647600,0x1C00022,
    0x1C00040,0x1C00402,0x1C01000,0x1C0200C,0x1C03E00,0x1E00003,0x1FFFFC0,0x2000003,
    0x21FFFC0,
};
const int g_catRunsCount = (int)(sizeof(g_catRuns) / sizeof(g_catRuns[0]));

// Simple case mappings: code points lo, lo+step, ... <= hi map to code point + delta.
const CaseRange g_foldTable[] = {
    {0x41,0x5A,1,32},
    {0xB5,0xB5,1,775},
    {0xC0,0xD6,1,32},
    {0xD8,0xDE,1,32},
    {0x100,0x12E,2,1},
    {0x132,0x136,2,1},
    {0x139,0x147,2,1},
    {0x14A,0x176,2,1},
    {0x178,0x178,1,-121},
    {0x179,0x17D,2,1},
    {0x17F,0x17F,1,-268},
    {0x181,0x181,1,210},
    {0x182,0x184,2,1},
    {0x186,0x186,1,206},
    {0x187,0x187,1,1},
    {0x189,0x18A,1,205},
    {0x18B,0x18B,1,1},
    {0x18E,0x18E,1,79},
    {0x18F,0x18F,1,202},
    {0x190,0x190,1,203},
    {0x191,0x191,1,1},
    {0x193,0x193,1,205},
    {0x194,0x194,1,207},
    {0x196,0x196,1,211},
    {0x197,0x197,1,209},
    {0x198,0x198,1,1},
    {0x19C,0x19C,1,211},
    {0x19D,0x19D,1,213},
    {0x19F,0x19F,1,214},
    {0x1A0,0x1A4,2,1},
    {0x1A6,0x1A6,1,218},
    {0x1A7,0x1A7,1,1},
    {0x1A9,0x1A9,1,218},
    {0x1AC,0x1AC,1,1},
    {0x1AE,0x1AE,1,218},
    {0x1AF,0x1AF,1,1},
    {0x1B1,0x1B2,1,217},
    {0x1B3,0x1B5,2,1},
    {0x1B7,0x1B7,1,219},
    {0x1B8,0x1B8,1,1},
    {0x1BC,0x1BC,1,1},
    {0x1C4,0x1C4,1,2},
    {0x1C5,0x1C5,1,1},
    {0x1C7,0x1C7,1,2},
    {0x1C8,0x1C8,1,1},
    {0x1CA,0x1CA,1,2},
    {0x1CB,0x1DB,2,1},
    {0x1DE,0x1EE,2,1},
    {0x1F1,0x1F1,1,2},
    {0x1F2,0x1F4,2,1},
    {0x1F6,0x1F6,1,-97},
    {0x1F7,0x1F7,1,-56},
    {0x1F8,0x21E,2,1},
    {0x220,0x220,1,-130},
    {0x222,0x232,2,1},
    {0x23A,0x23A,1,10795},
    {0x23B,0x23B,1,1},
    {0x23D,0x23D,1,-163},
    {0x23E,0x23E,1,10792},
    {0x241,0x241,1,1},
    {0x243,0x243,1,-195},
    {0x244,0x244,1,69},
    {0x245,0x245,1,71},
    {0x246,0x24E,2,1},
    {0x345,0x345,1,116},
    {0x370,0x372,2,1},
    {0x376,0x376,1,1},
    {0x37F,0x37F,1,116},
    {0x386,0x386,1,38},
    {0x388,0x38A,1,37},
    {0x38C,0x38C,1,64},
    {0x38E,0x38F,1,63},
    {0x391,0x3A1,1,32},
    {0x3A3,0x3AB,1,32},
    {0x3C2,0x3C2,1,1},
    {0x3CF,0x3CF,1,8},
    {0x3D0,0x3D0,1,-30},
    {0x3D1,0x3D1,1,-25},
    {0x3D5,0x3D5,1,-15},
    {0x3D6,0x3D6,1,-22},
    {0x3D8,0x3EE,2,1},
    {0x3F0,0x3F0,1,-54},
    {0x3F1,0x3F1,1,-48},
    {0x3F4,0x3F4,1,-60},
    {0x3F5,0x3F5,1,-64},
    {0x3F7,0x3F7,1,1},
    {0x3F9,0x3F9,1,-7},
    {0x3FA,0x3FA,1,1},
    {0x3FD,0x3FF,1,-130},
    {0x400,0x40F,1,80},
    {0x410,0x42F,1,32},
    {0x460,0x480,2,1},
    {0x48A,0x4BE,2,1},
    {0x4C0,0x4C0,1,15},
    {0x4C1,0x4CD,2,1},
    {0x4D0,0x52E,2,1},
    {0x531,0x556,1,48},
    {0x10A0,0x10C5,1,7264},
    {0x10C7,0x10C7,1,7264},
    {0x10CD,0x10CD,1,7264},
    {0x13F8,0x13FD,1,-8},
    {0x1C80,0x1C80,1,-6222},
    {0x1C81,0x1C81,1,-6221},
    {0x1C82,0x1C82,1,-6212},
    {0x1C83,0x1C84,1,-6210},
    {0x1C85,0x1C85,1,-6211},
    {0x1C86,0x1C86,1,-6204},
    {0x1C87,0x1C87,1,-6180},
    {0x1C88,0x1C88,1,35267},
    {0x1C90,0x1CBA,1,-3008},
    {0x1CBD,0x1CBF,1,-3008},
    {0x1E00,0x1E94,2,1},
    {0x1E9B,0x1E9B,1,-58},
    {0x1E9E,0x1E9E,1,-7615},
    {0x1EA0,0x1EFE,2,1},
    {0x1F08,0x1F0F,1,-8},
    {0x1F18,0x1F1D,1,-8},
    {0x1F28,0x1F2F,1,-8},
    {0x1F38,0x1F3F,1,-8},
    {0x1F48,0x1F4D,1,-8},
    {0x1F59,0x1F5F,2,-8},
    {0x1F68,0x1F6F,1,-8},
    {0x1F88,0x1F8F,1,-8},
    {0x1F98,0x1F9F,1,-8},
    {0x1FA8,0x1FAF,1,-8},
    {0x1FB8,0x1FB9,1,-8},
    {0x1FBA,0x1FBB,1,-74},
    {0x1FBC,0x1FBC,1,-9},
    {0x1FBE,0x1FBE,1,-7173},
    {0x1FC8,0x1FCB,1,-86},
    {0x1FCC,0x1FCC,1,-9},
    {0x1FD8,0x1FD9,1,-8},
    {0x1FDA,0x1FDB,1,-100},
    {0x1FE8,0x1FE9,1,-8},
    {0x1FEA,0x1FEB,1,-112},
    {0x1FEC,0x1FEC,1,-7},
    {0x1FF8,0x1FF9,1,-128},
    {0x1FFA,0x1FFB,1,-126},
    {0x1FFC,0x1FFC,1,-9},
    {0x2126,0x2126,1,-7517},
    {0x212A,0x212A,1,-8383},
    {0x212B,0x212B,1,-8262},
    {0x2132,0x2132,1,28},
    {0x2160,0x216F,1,16},
    {0x2183,0x2183,1,1},
    {0x24B6,0x24CF,1,26},
    {0x2C00,0x2C2F,1,48},
    {0x2C60,0x2C60,1,1},
    {0x2C62,0x2C62,1,-10743},
    {0x2C63,0x2C63,1,-3814},
    {0x2C64,0x2C64,1,-10727},
    {0x2C67,0x2C6B,2,1},
    {0x2C6D,0x2C6D,1,-10780},
    {0x2C6E,0x2C6E,1,-10749},
    {0x2C6F,0x2C6F,1,-10783},
    {0x2C70,0x2C70,1,-10782},
    {0x2C72,0x2C72,1,1},
    {0x2C75,0x2C75,1,1},
    {0x2C7E,0x2C7F,1,-10815},
    {0x2C80,0x2CE2,2,1},
    {0x2CEB,0x2CED,2,1},
    {0x2CF2,0x2CF2,1,1},
    {0xA640,0xA66C,2,1},
    {0xA680,0xA69A,2,1},
    {0xA722,0xA72E,2,1},
    {0xA732,0xA76E,2,1},
    {0xA779,0xA77B,2,1},
    {0xA77D,0xA77D,1,-35332},
    {0xA77E,0xA786,2,1},
    {0xA78B,0xA78B,1,1},
    {0xA78D,0xA78D,1,-42280},
    {0xA790,0xA792,2,1},
    {0xA796,0xA7A8,2,1},
    {0xA7AA,0xA7AA,1,-42308},
    {0xA7AB,0xA7AB,1,-42319},
    {0xA7AC,0xA7AC,1,-42315},
    {0xA7AD,0xA7AD,1,-42305},
    {0xA7AE,0xA7AE,1,-42308},
    {0xA7B0,0xA7B0,1,-42258},
    {0xA7B1,0xA7B1,1,-42282},
    {0xA7B2,0xA7B2,1,-42261},
    {0xA7B3,0xA7B3,1,928},
    {0xA7B4,0xA7C2,2,1},
    {0xA7C4,0xA7C4,1,-48},
    {0xA7C5,0xA7C5,1,-42307},
    {0xA7C6,0xA7C6,1,-35384},
    {0xA7C7,0xA7C9,2,1},
    {0xA7D0,0xA7D0,1,1},
    {0xA7D6,0xA7D8,2,1},
    {0xA7F5,0xA7F5,1,1},
    {0xAB70,0xABBF,1,-38864},
    {0xFF21,0xFF3A,1,32},
    {0x10400,0x10427,1,40},
    {0x104B0,0x104D3,1,40},
    {0x10570,0x1057A,1,39},
    {0x1057C,0x1058A,1,39},
    {0x1058C,0x10592,1,39},
    {0x10594,0x10595,1,39},
    {0x10C80,0x10CB2,1,64},
    {0x118A0,0x118BF,1,32},
    {0x16E40,0x16E5F,1,32},
    {0x1E900,0x1E921,1,34},
};
const int g_foldTableCount = (int)(sizeof(g_foldTable) / sizeof(g_foldTable[0]));
const CaseRange g_upperTable[] = {
    {0x61,0x7A,1,-32},
    {0xB5,0xB5,1,743},
    {0xE0,0xF6,1,-32},
    {0xF8,0xFE,1,-32},
    {0xFF,0xFF,1,121},
    {0x101,0x12F,2,-1},
    {0x131,0x131,1,-232},
    {0x133,0x137,2,-1},
    {0x13A,0x148,2,-1},
    {0x14B,0x177,2,-1},
    {0x17A,0x17E,2,-1},
    {0x17F,0x17F,1,-300},
    {0x180,0x180,1,195},
    {0x183,0x185,2,-1},
    {0x188,0x188,1,-1},
    {0x18C,0x18C,1,-1},
    {0x192,0x192,1,-1},
    {0x195,0x195,1,97},
    {0x199,0x199,1,-1},
    {0x19A,0x19A,1,163},
    {0x19E,0x19E,1,130},
    {0x1A1,0x1A5,2,-1},
    {0x1A8,0x1A8,1,-1},
    {0x1AD,0x1AD,1,-1},
    {0x1B0,0x1B0,1,-1},
    {0x1B4,0x1B6,2,-1},
    {0x1B9,0x1B9,1,-1},
    {0x1BD,0x1BD,1,-1},
    {0x1BF,0x1BF,1,56},
    {0x1C5,0x1C5,1,-1},
    {0x1C6,0x1C6,1,-2},
    {0x1C8,0x1C8,1,-1},
    {0x1C9,0x1C9,1,-2},
    {0x1CB,0x1CB,1,-1},
    {0x1CC,0x1CC,1,-2},
    {0x1CE,0x1DC,2,-1},
    {0x1DD,0x1DD,1,-79},
    {0x1DF,0x1EF,2,-1},
    {0x1F2,0x1F2,1,-1},
    {0x1F3,0x1F3,1,-2},
    {0x1F5,0x1F5,1,-1},
    {0x1F9,0x21F,2,-1},
    {0x223,0x233,2,-1},
    {0x23C,0x23C,1,-1},
    {0x23F,0x240,1,10815},
    {0x242,0x242,1,-1},
    {0x247,0x24F,2,-1},
    {0x250,0x250,1,10783},
    {0x251,0x251,1,10780},
    {0x252,0x252,1,10782},
    {0x253,0x253,1,-210},
    {0x254,0x254,1,-206},
    {0x256,0x257,1,-205},
    {0x259,0x259,1,-202},
    {0x25B,0x25B,1,-203},
    {0x25C,0x25C,1,42319},
    {0x260,0x260,1,-205},
    {0x261,0x261,1,42315},
    {0x263,0x263,1,-207},
    {0x265,0x265,1,42280},
    {0x266,0x266,1,42308},
    {0x268,0x268,1,-209},
    {0x269,0x269,1,-211},
    {0x26A,0x26A,1,42308},
    {0x26B,0x26B,1,10743},
    {0x26C,0x26C,1,42305},
    {0x26F,0x26F,1,-211},
    {0x271,0x271,1,10749},
    {0x272,0x272,1,-213},
    {0x275,0x275,1,-214},
    {0x27D,0x27D,1,10727},
    {0x280,0x280,1,-218},
    {0x282,0x282,1,42307},
    {0x283,0x283,1,-218},
    {0x287,0x287,1,42282},
    {0x288,0x288,1,-218},
    {0x289,0x289,1,-69},
    {0x28A,0x28B,1,-217},
    {0x28C,0x28C,1,-71},
    {0x292,0x292,1,-219},
    {0x29D,0x29D,1,42261},
    {0x29E,0x29E,1,42258},
    {0x345,0x345,1,84},
    {0x371,0x373,2,-1},
    {0x377,0x377,1,-1},
    {0x37B,0x37D,1,130},
    {0x3AC,0x3AC,1,-38},
    {0x3AD,0x3AF,1,-37},
    {0x3B1,0x3C1,1,-32},
    {0x3C2,0x3C2,1,-31},
    {0x3C3,0x3CB,1,-32},
    {0x3CC,0x3CC,1,-64},
    {0x3CD,0x3CE,1,-63},
    {0x3D0,0x3D0,1,-62},
    {0x3D1,0x3D1,1,-57},
    {0x3D5,0x3D5,1,-47},
    {0x3D6,0x3D6,1,-54},
    {0x3D7,0x3D7,1,-8},
    {0x3D9,0x3EF,2,-1},
    {0x3F0,0x3F0,1,-86},
    {0x3F1,0x3F1,1,-80},
    {0x3F2,0x3F2,1,7},
    {0x3F3,0x3F3,1,-116},
    {0x3F5,0x3F5,1,-96},
    {0x3F8,0x3F8,1,-1},
    {0x3FB,0x3FB,1,-1},
    {0x430,0x44F,1,-32},
    {0x450,0x45F,1,-80},
    {0x461,0x481,2,-1},
    {0x48B,0x4BF,2,-1},
    {0x4C2,0x4CE,2,-1},
    {0x4CF,0x4CF,1,-15},
    {0x4D1,0x52F,2,-1},
    {0x561,0x586,1,-48},
    {0x10D0,0x10FA,1,3008},
    {0x10FD,0x10FF,1,3008},
    {0x13F8,0x13FD,1,-8},
    {0x1C80,0x1C80,1,-6254},
    {0x1C81,0x1C81,1,-6253},
    {0x1C82,0x1C82,1,-6244},
    {0x1C83,0x1C84,1,-6242},
    {0x1C85,0x1C85,1,-6243},
    {0x1C86,0x1C86,1,-6236},
    {0x1C87,0x1C87,1,-6181},
    {0x1C88,0x1C88,1,35266},
    {0x1D79,0x1D79,1,35332},
    {0x1D7D,0x1D7D,1,3814},
    {0x1D8E,0x1D8E,1,35384},
    {0x1E01,0x1E95,2,-1},
    {0x1E9B,0x1E9B,1,-59},
    {0x1EA1,0x1EFF,2,-1},
    {0x1F00,0x1F07,1,8},
    {0x1F10,0x1F15,1,8},
    {0x1F20,0x1F27,1,8},
    {0x1F30,0x1F37,1,8},
    {0x1F40,0x1F45,1,8},
    {0x1F51,0x1F57,2,8},
    {0x1F60,0x1F67,1,8},
    {0x1F70,0x1F71,1,74},
    {0x1F72,0x1F75,1,86},
    {0x1F76,0x1F77,1,100},
    {0x1F78,0x1F79,1,128},
    {0x1F7A,0x1F7B,1,112},
    {0x1F7C,0x1F7D,1,126},
    {0x1FB0,0x1FB1,1,8},
    {0x1FBE,0x1FBE,1,-7205},
    {0x1FD0,0x1FD1,1,8},
    {0x1FE0,0x1FE1,1,8},
    {0x1FE5,0x1FE5,1,7},
    {0x214E,0x214E,1,-28},
    {0x2170,0x217F,1,-16},
    {0x2184,0x2184,1,-1},
    {0x24D0,0x24E9,1,-26},
    {0x2C30,0x2C5F,1,-48},
    {0x2C61,0x2C61,1,-1},
    {0x2C65,0x2C65,1,-10795},
    {0x2C66,0x2C66,1,-10792},
    {0x2C68,0x2C6C,2,-1},
    {0x2C73,0x2C73,1,-1},
    {0x2C76,0x2C76,1,-1},
    {0x2C81,0x2CE3,2,-1},
    {0x2CEC,0x2CEE,2,-1},
    {0x2CF3,0x2CF3,1,-1},
    {0x2D00,0x2D25,1,-7264},
    {0x2D27,0x2D27,1,-7264},
    {0x2D2D,0x2D2D,1,-7264},
    {0xA641,0xA66D,2,-1},
    {0xA681,0xA69B,2,-1},
    {0xA723,0xA72F,2,-1},
    {0xA733,0xA76F,2,-1},
    {0xA77A,0xA77C,2,-1},
    {0xA77F,0xA787,2,-1},
    {0xA78C,0xA78C,1,-1},
    {0xA791,0xA793,2,-1},
    {0xA794,0xA794,1,48},
    {0xA797,0xA7A9,2,-1},
    {0xA7B5,0xA7C3,2,-1},
    {0xA7C8,0xA7CA,2,-1},
    {0xA7D1,0xA7D1,1,-1},
    {0xA7D7,0xA7D9,2,-1},
    {0xA7F6,0xA7F6,1,-1},
    {0xAB53,0xAB53,1,-928},
    {0xAB70,0xABBF,1,-38864},
    {0xFF41,0xFF5A,1,-32},
    {0x10428,0x1044F,1,-40},
    {0x104D8,0x104FB,1,-40},
    {0x10597,0x105A1,1,-39},
    {0x105A3,0x105B1,1,-39},
    {0x105B3,0x105B9,1,-39},
    {0x105BB,0x105BC,1,-39},
    {0x10CC0,0x10CF2,1,-64},
    {0x118C0,0x118DF,1,-32},
    {0x16E60,0x16E7F,1,-32},
    {0x1E922,0x1E943,1,-34},
};
const int g_upperTableCount = (int)(sizeof(g_upperTable) / sizeof(g_upperTable[0]));
const CaseRange g_lowerTable[] = {
    {0x41,0x5A,1,32},
    {0xC0,0xD6,1,32},
    {0xD8,0xDE,1,32},
    {0x100,0x12E,2,1},
    {0x132,0x136,2,1},
    {0x139,0x147,2,1},
    {0x14A,0x176,2,1},
    {0x178,0x178,1,-121},
    {0x179,0x17D,2,1},
    {0x181,0x181,1,210},
    {0x182,0x184,2,1},
    {0x186,0x186,1,206},
    {0x187,0x187,1,1},
    {0x189,0x18A,1,205},
    {0x18B,0x18B,1,1},
    {0x18E,0x18E,1,79},
    {0x18F,0x18F,1,202},
    {0x190,0x190,1,203},
    {0x191,0x191,1,1},
    {0x193,0x193,1,205},
    {0x194,0x194,1,207},
    {0x196,0x196,1,211},
    {0x197,0x197,1,209},
    {0x198,0x198,1,1},
    {0x19C,0x19C,1,211},
    {0x19D,0x19D,1,213},
    {0x19F,0x19F,1,214},
    {0x1A0,0x1A4,2,1},
    {0x1A6,0x1A6,1,218},
    {0x1A7,0x1A7,1,1},
    {0x1A9,0x1A9,1,218},
    {0x1AC,0x1AC,1,1},
    {0x1AE,0x1AE,1,218},
    {0x1AF,0x1AF,1,1},
    {0x1B1,0x1B2,1,217},
    {0x1B3,0x1B5,2,1},
    {0x1B7,0x1B7,1,219},
    {0x1B8,0x1B8,1,1},
    {0x1BC,0x1BC,1,1},
    {0x1C4,0x1C4,1,2},
    {0x1C5,0x1C5,1,1},
    {0x1C7,0x1C7,1,2},
    {0x1C8,0x1C8,1,1},
    {0x1CA,0x1CA,1,2},
    {0x1CB,0x1DB,2,1},
    {0x1DE,0x1EE,2,1},
    {0x1F1,0x1F1,1,2},
    {0x1F2,0x1F4,2,1},
    {0x1F6,0x1F6,1,-97},
    {0x1F7,0x1F7,1,-56},
    {0x1F8,0x21E,2,1},
    {0x220,0x220,1,-130},
    {0x222,0x232,2,1},
    {0x23A,0x23A,1,10795},
    {0x23B,0x23B,1,1},
    {0x23D,0x23D,1,-163},
    {0x23E,0x23E,1,10792},
    {0x241,0x241,1,1},
    {0x243,0x243,1,-195},
    {0x244,0x244,1,69},
    {0x245,0x245,1,71},
    {0x246,0x24E,2,1},
    {0x370,0x372,2,1},
    {0x376,0x376,1,1},
    {0x37F,0x37F,1,116},
    {0x386,0x386,1,38},
    {0x388,0x38A,1,37},
    {0x38C,0x38C,1,64},
    {0x38E,0x38F,1,63},
    {0x391,0x3A1,1,32},
    {0x3A3,0x3AB,1,32},
    {0x3CF,0x3CF,1,8},
    {0x3D8,0x3EE,2,1},
    {0x3F4,0x3F4,1,-60},
    {0x3F7,0x3F7,1,1},
    {0x3F9,0x3F9,1,-7},
    {0x3FA,0x3FA,1,1},
    {0x3FD,0x3FF,1,-130},
    {0x400,0x40F,1,80},
    {0x410,0x42F,1,32},
    {0x460,0x480,2,1},
    {0x48A,0x4BE,2,1},
    {0x4C0,0x4C0,1,15},
    {0x4C1,0x4CD,2,1},
    {0x4D0,0x52E,2,1},
    {0x531,0x556,1,48},
    {0x10A0,0x10C5,1,7264},
    {0x10C7,0x10C7,1,7264},
    {0x10CD,0x10CD,1,7264},
    {0x13A0,0x13EF,1,38864},
    {0x13F0,0x13F5,1,8},
    {0x1C90,0x1CBA,1,-3008},
    {0x1CBD,0x1CBF,1,-3008},
    {0x1E00,0x1E94,2,1},
    {0x1E9E,0x1E9E,1,-7615},
    {0x1EA0,0x1EFE,2,1},
    {0x1F08,0x1F0F,1,-8},
    {0x1F18,0x1F1D,1,-8},
    {0x1F28,0x1F2F,1,-8},
    {0x1F38,0x1F3F,1,-8},
    {0x1F48,0x1F4D,1,-8},
    {0x1F59,0x1F5F,2,-8},
    {0x1F68,0x1F6F,1,-8},
    {0x1F88,0x1F8F,1,-8},
    {0x1F98,0x1F9F,1,-8},
    {0x1FA8,0x1FAF,1,-8},
    {0x1FB8,0x1FB9,1,-8},
    {0x1FBA,0x1FBB,1,-74},
    {0x1FBC,0x1FBC,1,-9},
    {0x1FC8,0x1FCB,1,-86},
    {0x1FCC,0x1FCC,1,-9},
    {0x1FD8,0x1FD9,1,-8},
    {0x1FDA,0x1FDB,1,-100},
    {0x1FE8,0x1FE9,1,-8},
    {0x1FEA,0x1FEB,1,-112},
    {0x1FEC,0x1FEC,1,-7},
    {0x1FF8,0x1FF9,1,-128},
    {0x1FFA,0x1FFB,1,-126},
    {0x1FFC,0x1FFC,1,-9},
    {0x2126,0x2126,1,-7517},
    {0x212A,0x212A,1,-8383},
    {0x212B,0x212B,1,-8262},
    {0x2132,0x2132,1,28},
    {0x2160,0x216F,1,16},
    {0x2183,0x2183,1,1},
    {0x24B6,0x24CF,1,26},
    {0x2C00,0x2C2F,1,48},
    {0x2C60,0x2C60,1,1},
    {0x2C62,0x2C62,1,-10743},
    {0x2C63,0x2C63,1,-3814},
    {0x2C64,0x2C64,1,-10727},
    {0x2C67,0x2C6B,2,1},
    {0x2C6D,0x2C6D,1,-10780},
    {0x2C6E,0x2C6E,1,-10749},
    {0x2C6F,0x2C6F,1,-10783},
    {0x2C70,0x2C70,1,-10782},
    {0x2C72,0x2C72,1,1},
    {0x2C75,0x2C75,1,1},
    {0x2C7E,0x2C7F,1,-10815},
    {0x2C80,0x2CE2,2,1},
    {0x2CEB,0x2CED,2,1},
    {0x2CF2,0x2CF2,1,1},
    {0xA640,0xA66C,2,1},
    {0xA680,0xA69A,2,1},
    {0xA722,0xA72E,2,1},
    {0xA732,0xA76E,2,1},
    {0xA779,0xA77B,2,1},
    {0xA77D,0xA77D,1,-35332},
    {0xA77E,0xA786,2,1},
    {0xA78B,0xA78B,1,1},
    {0xA78D,0xA78D,1,-42280},
    {0xA790,0xA792,2,1},
    {0xA796,0xA7A8,2,1},
    {0xA7AA,0xA7AA,1,-42308},
    {0xA7AB,0xA7AB,1,-42319},
    {0xA7AC,0xA7AC,1,-42315},
    {0xA7AD,0xA7AD,1,-42305},
    {0xA7AE,0xA7AE,1,-42308},
    {0xA7B0,0xA7B0,1,-42258},
    {0xA7B1,0xA7B1,1,-42282},
    {0xA7B2,0xA7B2,1,-42261},
    {0xA7B3,0xA7B3,1,928},
    {0xA7B4,0xA7C2,2,1},
    {0xA7C4,0xA7C4,1,-48},
    {0xA7C5,0xA7C5,1,-42307},
    {0xA7C6,0xA7C6,1,-35384},
    {0xA7C7,0xA7C9,2,1},
    {0xA7D0,0xA7D0,1,1},
    {0xA7D6,0xA7D8,2,1},
    {0xA7F5,0xA7F5,1,1},
    {0xFF21,0xFF3A,1,32},
    {0x10400,0x10427,1,40},
    {0x104B0,0x104D3,1,40},
    {0x10570,0x1057A,1,39},
    {0x1057C,0x1058A,1,39},
    {0x1058C,0x10592,1,39},
    {0x10594,0x10595,1,39},
    {0x10C80,0x10CB2,1,64},
    {0x118A0,0x118BF,1,32},
    {0x16E40,0x16E5F,1,32},
    {0x1E900,0x1E921,1,34},
};
const int g_lowerTableCount = (int)(sizeof(g_lowerTable) / sizeof(g_lowerTable[0]));
// ==== END GENERATED TABLES ====

}  // namespace UkaRegexpImpl

/* ------------------------------------------------------------------------------------------ */
/* CRegexpContext                                                                              */
/* ------------------------------------------------------------------------------------------ */

using namespace UkaRegexpImpl;

CRegexpContext::CRegexpContext()
    : m_caps(0), m_ngroups(-1), m_capsCap(0), m_next(0), m_lastEmpty(0), m_work(0)
{
}

CRegexpContext::~CRegexpContext()
{
    free(m_caps);
    delete m_work;
}

int CRegexpContext::GetGroupCount() const { return m_ngroups < 0 ? 0 : m_ngroups; }

bool CRegexpContext::IsMatched(int group) const { return GetStart(group) >= 0; }

int CRegexpContext::GetStart(int group) const
{
    if (m_ngroups < 0 || group < 0 || group > m_ngroups) return -1;
    return m_caps[2 * group + 1] < 0 ? -1 : m_caps[2 * group];
}

int CRegexpContext::GetEnd(int group) const
{
    if (m_ngroups < 0 || group < 0 || group > m_ngroups) return -1;
    return m_caps[2 * group] < 0 ? -1 : m_caps[2 * group + 1];
}

void CRegexpContext::Clear()
{
    m_ngroups = -1;
}

void CRegexpContext::Reset()
{
    Clear();
    m_next = 0;
    m_lastEmpty = 0;
}

void CRegexpContext::SetResult(int ngroups, const int* caps)
{
    int n = 2 * (ngroups + 1);
    if (n > m_capsCap) {
        int* p = (int*)realloc(m_caps, sizeof(int) * n);
        if (!p) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
        m_caps = p;
        m_capsCap = n;
    }
    memcpy(m_caps, caps, sizeof(int) * n);
    m_ngroups = ngroups;
}

/* ------------------------------------------------------------------------------------------ */
/* CRegexpW                                                                                    */
/* ------------------------------------------------------------------------------------------ */

CRegexpW::CRegexpW() : m_prog(0), m_stepBase(1000000UL), m_stepPer(256UL) {}

CRegexpW::CRegexpW(const wchar_t* pattern, unsigned int flags)
    : m_prog(0), m_stepBase(1000000UL), m_stepPer(256UL)
{
    Compile(pattern, flags);
}

CRegexpW::~CRegexpW() { delete m_prog; }

void CRegexpW::Compile(const wchar_t* pattern, unsigned int flags)
{
    Program* prog = new Program;
    if (!prog) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
    try {
        Compiler c(*prog, pattern, WLen(pattern), flags);
        c.Run();
    } catch (...) {
        delete prog;
        throw;
    }
    delete m_prog;
    m_prog = prog;
}

int CRegexpW::GetGroupCount() const { return m_prog ? m_prog->ngroups : 0; }

int CRegexpW::GetGroupNumber(const wchar_t* name) const
{
    int i;
    if (!m_prog) return -1;
    for (i = 0; i < m_prog->names.Size(); ++i) {
        const wchar_t* pool = m_prog->namePool.Data() + m_prog->names[i].off;
        int k = 0;
        while (pool[k] && pool[k] == name[k]) ++k;
        if (pool[k] == 0 && name[k] == 0) return m_prog->names[i].group;
    }
    return -1;
}

void CRegexpW::SetStepLimit(unsigned long base, unsigned long perChar)
{
    m_stepBase = base;
    m_stepPer = perChar;
}

bool CRegexpW::Match(const wchar_t* str, CRegexpContext& ctx) const
{
    return Match(str, -1, ctx, -1);
}

bool CRegexpW::Match(const wchar_t* str, int len, CRegexpContext& ctx, int start) const
{
    int from, notEmpty = -1;
    unsigned long limit;
    bool ok;

    if (!m_prog) throw CRegexpException(CRegexpException::ERR_NOT_COMPILED, -1, "pattern is not compiled");
    if (len < 0) len = WLen(str);
    ctx.Clear();
    if (start >= 0) {
        from = start;
    } else {
        from = 0;
        if (m_prog->global) {
            from = ctx.m_next;
            if (ctx.m_lastEmpty) notEmpty = from;
        }
    }
    ctx.m_next = 0;
    ctx.m_lastEmpty = 0;
    if (from > len) return false;

    if (len > (int)((0xFFFFFFFFUL - m_stepBase) / (m_stepPer ? m_stepPer : 1UL))) limit = 0xFFFFFFFFUL;
    else limit = m_stepBase + m_stepPer * (unsigned long)len;

    if (!ctx.m_work) {
        ctx.m_work = new Work;
        if (!ctx.m_work) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
    }
    {
        Matcher m(*m_prog, *ctx.m_work, str, len, from, notEmpty, limit);
        ok = m.Search(from);
        if (ok) {
            const int* st = m.Result();
            ctx.SetResult(m_prog->ngroups, st);
            ctx.m_next = st[1];
            ctx.m_lastEmpty = (st[0] == st[1]) ? 1 : 0;
        }
    }
    return ok;
}

/* append the expansion of the replacement template for the match held by ctx */
static void ExpandTemplate(CRegexpString& out, const wchar_t* repl, const wchar_t* str, int len,
                           const CRegexpContext& ctx, const CRegexpW& re)
{
    int ngroups = re.GetGroupCount();
    int i = 0;
    while (repl[i]) {
        Cp c = (Cp)repl[i];
        Cp d;
        if (c != '$') {
            out.push_back(repl[i++]);
            continue;
        }
        d = (Cp)repl[i + 1];   /* the terminator stops the scan, so this is safe */
        if (d == '$') {
            out.push_back(L'$');
            i += 2;
        } else if (d == '&') {
            out.append(str + ctx.GetStart(0), ctx.GetEnd(0) - ctx.GetStart(0));
            i += 2;
        } else if (d == '`') {
            out.append(str, ctx.GetStart(0));
            i += 2;
        } else if (d == '\'') {
            out.append(str + ctx.GetEnd(0), len - ctx.GetEnd(0));
            i += 2;
        } else if (d == '_') {
            out.append(str, len);
            i += 2;
        } else if (d == '+') {
            int g;
            for (g = ngroups; g >= 1; --g) {
                if (ctx.IsMatched(g)) {
                    out.append(str + ctx.GetStart(g), ctx.GetEnd(g) - ctx.GetStart(g));
                    break;
                }
            }
            i += 2;
        } else if (d == '{') {
            int j = i + 2, g = -1;
            while (repl[j] && repl[j] != L'}') ++j;
            if (repl[j] == L'}') {
                CRegexpString name;
                bool numeric = (j > i + 2);
                int k;
                name.append(repl + i + 2, j - (i + 2));
                for (k = i + 2; k < j; ++k) if (repl[k] < L'0' || repl[k] > L'9') numeric = false;
                if (numeric) {
                    long v = 0;
                    for (k = i + 2; k < j && v <= ngroups; ++k) v = v * 10 + (repl[k] - L'0');
                    g = (v <= ngroups) ? (int)v : -1;
                } else {
                    g = re.GetGroupNumber(name.c_str());
                }
            }
            if (g >= 0) {
                if (ctx.IsMatched(g)) out.append(str + ctx.GetStart(g), ctx.GetEnd(g) - ctx.GetStart(g));
                i = j + 1;
            } else {   /* not a group: keep the text as it is */
                out.push_back(L'$');
                ++i;
            }
        } else if (d >= '0' && d <= '9') {
            int j = i + 1, digits = 0;
            long v = 0;
            while (repl[j] >= L'0' && repl[j] <= L'9') { ++j; ++digits; }
            /* use as many digits as still name an existing group */
            while (digits > 0) {
                int k;
                v = 0;
                for (k = 0; k < digits; ++k) { v = v * 10 + (repl[i + 1 + k] - L'0'); if (v > 100000L) break; }
                if (v <= ngroups) break;
                --digits;
            }
            if (digits > 0) {
                if (ctx.IsMatched((int)v)) out.append(str + ctx.GetStart((int)v), ctx.GetEnd((int)v) - ctx.GetStart((int)v));
                i += 1 + digits;
            } else {
                out.push_back(L'$');
                ++i;
            }
        } else {
            out.push_back(L'$');
            ++i;
        }
    }
}

int CRegexpW::Replace(const wchar_t* str, const wchar_t* repl, CRegexpString& out) const
{
    return Replace(str, -1, repl, out);
}

int CRegexpW::Replace(const wchar_t* str, int len, const wchar_t* repl, CRegexpString& out) const
{
    CRegexpContext ctx;
    int last = 0, count = 0;
    if (!m_prog) throw CRegexpException(CRegexpException::ERR_NOT_COMPILED, -1, "pattern is not compiled");
    if (len < 0) len = WLen(str);
    out.clear();
    for (;;) {
        int ms, me;
        bool ok = m_prog->global ? Match(str, len, ctx, -1) : Match(str, len, ctx, 0);
        if (!ok) break;
        ms = ctx.GetStart(0);
        me = ctx.GetEnd(0);
        if (ms < last) ms = last;
        if (me < ms) me = ms;
        out.append(str + last, ms - last);
        ExpandTemplate(out, repl, str, len, ctx, *this);
        last = me;
        ++count;
        if (!m_prog->global) break;
    }
    out.append(str + last, len - last);
    return count;
}
