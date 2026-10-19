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

/*
 * Where wchar_t is 16 bit the subject is UTF-16: a high surrogate followed by a low surrogate is
 * one character.  A lone surrogate is a character of its own.  Offsets stay in wchar_t units, but a
 * match never starts or ends between the two halves of a pair.  Where wchar_t is 32 bit all of this
 * folds away at compile time.
 */

/* the code point at s[i] (i < n) and its length in wchar_t units */
static inline Cp DecodeAt(const wchar_t* s, int n, int i, int& len)
{
    Cp c = (Cp)s[i];
    len = 1;
    if (sizeof(wchar_t) == 2 && c >= 0xD800 && c < 0xDC00 && i + 1 < n) {
        Cp d = (Cp)s[i + 1];
        if (d >= 0xDC00 && d < 0xE000) {
            len = 2;
            return 0x10000 + ((c - 0xD800) << 10) + (d - 0xDC00);
        }
    }
    return c;
}

/* length of the character that ends at s[i] (i > 0) */
static inline int PrevLen(const wchar_t* s, int i)
{
    if (sizeof(wchar_t) == 2 && i >= 2 && (Cp)s[i - 1] >= 0xDC00 && (Cp)s[i - 1] < 0xE000 &&
        (Cp)s[i - 2] >= 0xD800 && (Cp)s[i - 2] < 0xDC00) return 2;
    return 1;
}

/* is i in the middle of a surrogate pair? */
static inline bool IsMidPair(const wchar_t* s, int n, int i)
{
    return sizeof(wchar_t) == 2 && i > 0 && i < n && (Cp)s[i] >= 0xDC00 && (Cp)s[i] < 0xE000 &&
           (Cp)s[i - 1] >= 0xD800 && (Cp)s[i - 1] < 0xDC00;
}

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

struct ScriptName { const char* name; int id; };
struct ScxRange { unsigned int lo; unsigned int hi; int off; };
struct StrPair { const char* a; const char* b; };

extern const unsigned int g_catRuns[];
extern const int g_catRunsCount;
extern const CaseRange g_foldTable[];
extern const int g_foldTableCount;
extern const CaseRange g_upperTable[];
extern const int g_upperTableCount;
extern const CaseRange g_lowerTable[];
extern const int g_lowerTableCount;

extern const unsigned int g_scriptRuns[];
extern const int g_scriptRunsCount;
extern const ScriptName g_scriptNames[];
extern const int g_scriptNamesCount;
extern const ScxRange g_scxRanges[];
extern const int g_scxRangesCount;
extern const unsigned char g_scxData[];
extern const unsigned int g_gcbRuns[];
extern const int g_gcbRunsCount;
extern const StrPair g_gcAliases[];
extern const int g_gcAliasesCount;

int UcCategory(Cp c);      /* 0..CAT_COUNT-1 */
int UcScript(Cp c);        /* script id */
bool UcScriptExt(Cp c, int id);   /* is the script among the Script_Extensions of c? */
int UcGcb(Cp c);           /* Grapheme_Cluster_Break value */
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
    OP_UWORDB, OP_UNWORDB,   /* \b \B with (*UCP) */
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
    OP_CALL,          /* group, target pc: subroutine call / recursion */
    OP_FAIL,
    OP_VERB,          /* VERB_COMMIT / VERB_PRUNE / VERB_SKIP */
    OP_BSR,           /* \R: 1 = only CR, LF, CRLF */
    OP_GRAPHEME,      /* \X */
    OP_COND_REC       /* group (-1: any), else pc: are we inside a recursion (into that group)? */
};

enum { REP_GREEDY = 0, REP_LAZY = 1, REP_POSSESSIVE = 2 };

struct Range { int lo; int hi; };

struct BinPropDef { const char* name; const char* alias; const Range* r; int n; };
extern const BinPropDef g_binProps[];
extern const int g_binPropsCount;
extern const Range g_incbConsonant[];
extern const int g_incbConsonantCount;
extern const Range g_incbLinker[];
extern const int g_incbLinkerCount;
extern const Range g_incbExtend[];
extern const int g_incbExtendCount;
extern const Range g_binExtendedPictographic[];
extern const int g_binExtendedPictographicCount;

struct ClassProp {       /* a \p{..} item inside a character class */
    unsigned int mask;   /* bit per general category */
    unsigned int extra;  /* EX_* flags */
    int neg;
    int script;          /* >= 0: script id (see g_scriptNames) */
    int scx;             /* use Script_Extensions instead of Script */
    int bin;             /* >= 0: index into g_binProps */
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
    int newline;              /* NL_* newline convention */
    int bsrAnyCrlf;           /* \R only matches CR, LF and CRLF */
    int notEmpty;             /* 1: never return an empty match; 2: not an empty match at the search start */
    int dollarEndOnly;        /* $ only matches at the very end (DOLLAR_ENDONLY) */
    int ucp;                  /* \d \w \s \b and POSIX classes use Unicode properties (UCP, (*UCP)) */
    unsigned long limitMatch; /* (*LIMIT_MATCH=n), 0: none */

    Program() : ngroups(0), nloops(0), global(0), anchored(0), firstChar(-1),
                newline(0), bsrAnyCrlf(0), notEmpty(0), dollarEndOnly(0), ucp(0), limitMatch(0) {}
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
static const Range kHSpace[] = { {9, 9}, {32, 32}, {0xA0, 0xA0}, {0x1680, 0x1680}, {0x180E, 0x180E},
                                 {0x2000, 0x200A}, {0x202F, 0x202F}, {0x205F, 0x205F}, {0x3000, 0x3000} };
static const Range kVSpace[] = { {10, 13}, {0x85, 0x85}, {0x2028, 0x2029} };   /* \v: LF VT FF CR NEL LS PS */

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
    EX_PSP = 16,         /* TAB, LF, VT, FF, CR */
    EX_GRAPH = 32,       /* [:graph:] with (*UCP) */
    EX_PRINT = 64,       /* [:print:] with (*UCP) */
    EX_PUNCT = 128       /* [:punct:] with (*UCP) */
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

static bool InRanges(const Range* r, int n, Cp c);

static bool IsUniWhite(Cp c)
{
    return (c >= 9 && c <= 13) || c == 32 || c == 0x85 || c == 0xA0 || c == 0x1680 ||
           (c >= 0x2000 && c <= 0x200A) || c == 0x2028 || c == 0x2029 || c == 0x202F ||
           c == 0x205F || c == 0x3000;
}

/* [:graph:] with (*UCP): L M N P S and Cf, except three characters that PCRE2 leaves out */
static bool IsUcpGraph(Cp c)
{
    if (c == 0x061C || c == 0x180E || (c >= 0x2066 && c <= 0x2069)) return false;
    return (((MASK_L | MASK_M | MASK_N | MASK_P | MASK_S | CATBIT(CAT_Cf)) >> UcCategory(c)) & 1u) != 0;
}

static bool PropMatch(const ClassProp& p, Cp c)
{
    bool r = false;
    if (p.script >= 0) {
        r = p.scx ? UcScriptExt(c, p.script) : (UcScript(c) == p.script);
    } else if (p.bin >= 0) {
        r = InRanges(g_binProps[p.bin].r, g_binProps[p.bin].n, c);
    } else if ((p.mask >> UcCategory(c)) & 1u) {
        r = true;
    } else if (p.extra) {
        if ((p.extra & EX_ASCII) && c < 128) r = true;
        else if ((p.extra & EX_WHITE) && IsUniWhite(c)) r = true;
        else if ((p.extra & EX_JOIN) && (c == 0x200C || c == 0x200D)) r = true;
        else if ((p.extra & EX_UNDERSCORE) && c == '_') r = true;
        else if ((p.extra & EX_PSP) && c >= 9 && c <= 13) r = true;
        else if ((p.extra & EX_GRAPH) && IsUcpGraph(c)) r = true;
        else if ((p.extra & EX_PRINT) && (IsUcpGraph(c) || UcCategory(c) == CAT_Zs)) r = true;
        else if ((p.extra & EX_PUNCT) && (((MASK_P >> UcCategory(c)) & 1u) || (c < 256 && ((MASK_S >> UcCategory(c)) & 1u)))) r = true;
    }
    return r != (p.neg != 0);
}

static ClassProp MakeProp(unsigned int mask, unsigned int extra, bool neg)
{
    ClassProp p;
    p.mask = mask;
    p.extra = extra;
    p.neg = neg ? 1 : 0;
    p.script = -1;
    p.scx = 0;
    p.bin = -1;
    return p;
}

/* \d \D \w \W \s \S with (*UCP): c is the letter after the backslash */
static bool UcpShorthand(Cp c, ClassProp& p)
{
    switch (c) {
    case 'd': p = MakeProp(CATBIT(CAT_Nd), 0, false); return true;
    case 'D': p = MakeProp(CATBIT(CAT_Nd), 0, true); return true;
    case 'w': p = MakeProp(MASK_L | MASK_N, EX_UNDERSCORE, false); return true;
    case 'W': p = MakeProp(MASK_L | MASK_N, EX_UNDERSCORE, true); return true;
    case 's': p = MakeProp(MASK_Z, EX_PSP, false); return true;
    case 'S': p = MakeProp(MASK_Z, EX_PSP, true); return true;
    default: return false;
    }
}

static bool EqAscii(const wchar_t* w, int n, const char* a);

struct UcpPosixDef { const char* name; unsigned int mask; unsigned int extra; };

/* POSIX class names with (*UCP); false for the ones that stay ASCII (ascii, xdigit) or become \h (blank) */
static bool UcpPosix(const wchar_t* w, int n, bool neg, ClassProp& p)
{
    static const UcpPosixDef kUcpPosix[] = {
        { "alnum", MASK_L | MASK_N, 0 }, { "alpha", MASK_L, 0 }, { "cntrl", CATBIT(CAT_Cc), 0 },
        { "digit", CATBIT(CAT_Nd), 0 }, { "lower", CATBIT(CAT_Ll), 0 }, { "upper", CATBIT(CAT_Lu), 0 },
        { "space", MASK_Z, EX_PSP }, { "word", MASK_L | MASK_N, EX_UNDERSCORE },
        { "graph", 0, EX_GRAPH }, { "print", 0, EX_PRINT }, { "punct", 0, EX_PUNCT }
    };
    int i;
    for (i = 0; i < ARRAY_COUNT(kUcpPosix); ++i) {
        if (EqAscii(w, n, kUcpPosix[i].name)) {
            p = MakeProp(kUcpPosix[i].mask, kUcpPosix[i].extra, neg);
            return true;
        }
    }
    return false;
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
            if (p.script < 0 && p.bin < 0 && (p.mask & MASK_LC) != 0 && (p.mask & ~MASK_LC) == 0 && p.extra == 0) p.mask = MASK_LC;
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

enum { F_I = 1, F_M = 2, F_S = 4, F_X = 8, F_G = 16,   /* same values as the public flags */
       F_XX = 0x100, F_N = 0x200, F_U = 0x400 };        /* (?xx) (?n) (?U): pattern-only options */

enum { NL_LF = 0, NL_CR, NL_CRLF, NL_ANYCRLF, NL_ANY };   /* newline conventions */
enum { VERB_COMMIT = 1, VERB_PRUNE, VERB_SKIP };

enum {
    N_EMPTY, N_CHAR, N_ANY, N_CLASS, N_ASSERT, N_KEEP, N_CAT, N_ALT, N_GROUP, N_REPEAT,
    N_ATOMIC, N_LOOK, N_BACKREF, N_CALL, N_COND, N_BSR, N_GRAPHEME, N_VERB
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
 *             2 DEFINE, 3 recursion test (b = group or -1 for any, c = name reference);
 *             child = yes branch, d = no branch or -1
 *   N_BSR     \R
 *   N_GRAPHEME \X
 *   N_VERB    a = 0 (*FAIL), VERB_COMMIT, VERB_PRUNE or VERB_SKIP
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
    Compiler(Program& prog, const wchar_t* pat, int len, unsigned int flags,
             CRegexpResolveProc resolver, void* resolverUser)
        : m_prog(prog), m_p(pat), m_len(len), m_pos(0), m_flags(flags & 31u),
          m_counter(0), m_maxGroup(0), m_quote(0), m_depth(0), m_look(0),
          m_initFlags(flags & 31u), m_resolver(resolver), m_resolverUser(resolverUser)
    {
        if (flags & 16u) prog.global = 1;
        prog.newline = (int)((flags >> 5) & 7u);
        if (prog.newline > NL_ANY) prog.newline = NL_LF;
        prog.bsrAnyCrlf = (flags & 256u) ? 1 : 0;
        prog.dollarEndOnly = (flags & 512u) ? 1 : 0;
        prog.ucp = (flags & 1024u) ? 1 : 0;
    }
    void Run();

private:
    void ResolveExternal();
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
    int ParseVerb(int open);
    void ParseStartVerbs();
    bool ReadUPlus(Cp& out);
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
    Cp TakeCp();
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
    int m_look;         /* nesting depth of assertions */
    unsigned int m_initFlags;
    CRegexpResolveProc m_resolver;
    void* m_resolverUser;
    Vec<int> m_external;   /* group nodes made from the patterns the resolver returned */
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
            c = TakeCp();
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
    return CharNode(c);
}

/* the character at m_pos (a surrogate pair is one character), consumed */
Cp Compiler::TakeCp()
{
    int len;
    Cp c = DecodeAt(m_p, m_len, m_pos, len);
    m_pos += len;
    return c;
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
        /* like PCRE: also before a newline that ends the subject, unless DOLLAR_ENDONLY */
        return NewNode(N_ASSERT, (m_flags & F_M) ? OP_MEOL : (m_prog.dollarEndOnly ? OP_EOL : OP_EOSNL));
    case '\\':
        return ParseEscape();
    default:   /* includes a quantifier character with nothing to repeat, and '{' : taken literally */
        return MakeLiteral(TakeCp());
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
        if (digits == 0 && !(p < m_len && At(p) == ',')) return false;
        if (digits == 0) {   /* {,m} is {0,m}, as in PCRE2 10.43 */
            if (!(p + 1 < m_len && IsDigitCp(At(p + 1)))) return false;
        }
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
        if ((m_flags & F_U) && mode != REP_POSSESSIVE) mode = (mode == REP_LAZY) ? REP_GREEDY : REP_LAZY;
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
    unsigned int setBits = 0, clrBits = 0, caretMask = 0;
    bool neg = false;
    if (More() && At(m_pos) == '^') {   /* (?^...): start again from the defaults */
        caretMask = F_I | F_M | F_S | F_X | F_XX | F_N;
        ++m_pos;
    }
    for (;;) {
        unsigned int bit = 0;
        Cp c;
        if (!More()) Error("missing )", open);
        c = At(m_pos);
        if (c == '-' && caretMask == 0) { neg = true; ++m_pos; continue; }
        switch (c) {
        case 'i': bit = F_I; break;
        case 'm': bit = F_M; break;
        case 's': bit = F_S; break;
        case 'x':
            bit = F_X;
            if (AtCh(m_pos + 1, 'x')) { bit = F_X | F_XX; ++m_pos; }
            break;
        case 'g': bit = F_G; break;
        case 'n': bit = F_N; break;
        case 'U': bit = F_U; break;
        default: break;
        }
        if (!bit) break;
        if (neg) clrBits |= (bit & F_X) ? (unsigned int)(F_X | F_XX) : bit; else setBits |= bit;
        if (bit == F_G && !neg) m_prog.global = 1;
        ++m_pos;
    }
    if (More() && At(m_pos) == ')') {
        ++m_pos;
        m_flags = ((m_flags & ~caretMask) | setBits) & ~clrBits;
        return -1;
    }
    if (More() && At(m_pos) == ':') {
        unsigned int saved = m_flags;
        int body;
        ++m_pos;
        m_flags = ((m_flags & ~caretMask) | setBits) & ~clrBits;
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
        } else if (term == ')' && At(s) == 'R' && (m_pos - s == 1 || IsDigitCp(At(s + 1)) || At(s + 1) == '&')) {
            kind = 3;   /* (?(R)..) (?(R1)..) (?(R&name)..) */
            if (m_pos - s == 1) {
                num = -1;
            } else if (At(s + 1) == '&') {
                if (m_pos - s == 2) Error("group name expected after (?(R&", s);
                nameRef = AddName(s + 2, m_pos - s - 2) + 1;
            } else {
                int j;
                for (j = s + 1; j < m_pos; ++j) {
                    if (!IsDigitCp(At(j))) Error("invalid recursion condition", s);
                    num = num * 10 + (int)(At(j) - '0');
                    if (num > 100000) Error("group number too big", s);
                }
            }
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
    if (AtCh(m_pos + 1, '*')) return ParseVerb(open);
    ++m_pos;
    if (!(More() && At(m_pos) == '?')) {
        int num, body, g;
        if (m_flags & F_N) return GroupBody(open, false);   /* (?n): plain parentheses do not capture */
        num = ++m_counter;
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
        ++m_look;
        body = GroupBody(open, false);
        --m_look;
        n = NewNode(N_LOOK, 0, c == '!' ? 1 : 0);
        m_nodes[n].child = body;
        m_nodes[n].pos = open;
        return n;
    }
    case '<':
        if (AtCh(m_pos + 1, '=') || AtCh(m_pos + 1, '!')) {
            int neg = (At(m_pos + 1) == '!') ? 1 : 0, body, n;
            m_pos += 2;
            ++m_look;
            body = GroupBody(open, false);
            --m_look;
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

/* \N{U+hhhh} after the \N: returns false (nothing consumed) when the text does not follow */
bool Compiler::ReadUPlus(Cp& out)
{
    unsigned long v = 0;
    int digits = 0;
    if (!(AtCh(m_pos, '{') && AtCh(m_pos + 1, 'U') && AtCh(m_pos + 2, '+'))) return false;
    m_pos += 3;
    while (m_pos < m_len && HexValue(At(m_pos)) >= 0) {
        v = v * 16 + (unsigned long)HexValue(At(m_pos));
        if (v > 0x10FFFFUL) Error("code point value too large");
        ++m_pos;
        ++digits;
    }
    if (digits == 0 || !More() || At(m_pos) != '}') Error("malformed \\N{U+hhhh} escape");
    ++m_pos;
    out = (Cp)v;
    return true;
}

static bool IsVerbChar(Cp c)
{
    return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_';
}

/* (*VERB) (*VERB:arg) (*pla:...) ; m_pos is at the '(' */
int Compiler::ParseVerb(int open)
{
    int ns, nl, as = 0, al = 0, n;
    bool colon = false;
    m_pos += 2;
    ns = m_pos;
    while (More() && IsVerbChar(At(m_pos))) ++m_pos;
    nl = m_pos - ns;
    if (More() && At(m_pos) == ':') {
        colon = true;
        ++m_pos;
        if (nl > 0) {   /* assertions written with names: (*pla:...) */
            struct AssertName { const char* name; int look; int behind; int neg; };
            static const AssertName kAssert[] = {
                { "pla", 1, 0, 0 }, { "positive_lookahead", 1, 0, 0 },
                { "nla", 1, 0, 1 }, { "negative_lookahead", 1, 0, 1 },
                { "plb", 1, 1, 0 }, { "positive_lookbehind", 1, 1, 0 },
                { "nlb", 1, 1, 1 }, { "negative_lookbehind", 1, 1, 1 },
                { "atomic", 0, 0, 0 }
            };
            int i;
            for (i = 0; i < ARRAY_COUNT(kAssert); ++i) {
                if (EqAscii(m_p + ns, nl, kAssert[i].name)) {
                    int body;
                    if (kAssert[i].look) ++m_look;
                    body = GroupBody(open, false);
                    if (kAssert[i].look) --m_look;
                    n = NewNode(kAssert[i].look ? N_LOOK : N_ATOMIC, kAssert[i].behind, kAssert[i].neg);
                    m_nodes[n].child = body;
                    m_nodes[n].pos = open;
                    return n;
                }
            }
        }
        as = m_pos;
        while (More() && At(m_pos) != ')') ++m_pos;
        al = m_pos - as;
    }
    if (!More() || At(m_pos) != ')') Error("malformed (*VERB)", open);
    ++m_pos;
    (void)al;
    if (nl == 0 && colon) return -1;                                 /* (*:NAME) mark: nothing to do */
    if (EqAscii(m_p + ns, nl, "MARK") && colon) return -1;
    if (EqAscii(m_p + ns, nl, "FAIL") || EqAscii(m_p + ns, nl, "F")) {
        n = NewNode(N_VERB, 0);
        m_nodes[n].pos = open;
        return n;
    }
    if (EqAscii(m_p + ns, nl, "COMMIT") || EqAscii(m_p + ns, nl, "PRUNE") || EqAscii(m_p + ns, nl, "SKIP")) {
        int kind = EqAscii(m_p + ns, nl, "COMMIT") ? VERB_COMMIT : EqAscii(m_p + ns, nl, "PRUNE") ? VERB_PRUNE : VERB_SKIP;
        if (kind == VERB_SKIP && colon) Error("(*SKIP:NAME) is not supported", open);
        if (m_look > 0) Error("backtracking control verbs are not supported inside assertions", open);
        n = NewNode(N_VERB, kind);
        m_nodes[n].pos = open;
        return n;
    }
    if (EqAscii(m_p + ns, nl, "THEN") || EqAscii(m_p + ns, nl, "ACCEPT")) Error("(*THEN) and (*ACCEPT) are not supported", open);
    Error("unknown or misplaced (*VERB)", open);
    return -1;
}

/* leading option verbs such as (*CRLF) (*UTF8) (*LIMIT_MATCH=1000) */
void Compiler::ParseStartVerbs()
{
    for (;;) {
        int p = m_pos + 2, ns, nl;
        long val = -1;
        if (!(AtCh(m_pos, '(') && AtCh(m_pos + 1, '*'))) return;
        ns = p;
        while (p < m_len && (IsVerbChar(At(p)))) ++p;
        nl = p - ns;
        if (AtCh(p, '=')) {
            ++p;
            val = 0;
            if (!(p < m_len && IsDigitCp(At(p)))) Error("number expected after =");
            while (p < m_len && IsDigitCp(At(p))) {
                val = val * 10 + (long)(At(p) - '0');
                if (val > 2000000000L) val = 2000000000L;
                ++p;
            }
        }
        if (!AtCh(p, ')')) return;
        if (EqAscii(m_p + ns, nl, "UTF") || EqAscii(m_p + ns, nl, "UTF8") || EqAscii(m_p + ns, nl, "UTF16") ||
            EqAscii(m_p + ns, nl, "UTF32") || EqAscii(m_p + ns, nl, "NO_START_OPT") ||
            EqAscii(m_p + ns, nl, "NO_AUTO_POSSESS") || EqAscii(m_p + ns, nl, "NO_DOTSTAR_ANCHOR") ||
            EqAscii(m_p + ns, nl, "NO_JIT") || EqAscii(m_p + ns, nl, "LIMIT_DEPTH") ||
            EqAscii(m_p + ns, nl, "LIMIT_HEAP") || EqAscii(m_p + ns, nl, "LIMIT_RECURSION")) {
            /* nothing to do: wchar_t is always Unicode, and these only tune PCRE's optimiser and limits */
        } else if (EqAscii(m_p + ns, nl, "UCP")) {
            m_prog.ucp = 1;
        } else if (EqAscii(m_p + ns, nl, "NUL")) {
            Error("(*NUL) is not supported");
        } else if (EqAscii(m_p + ns, nl, "LF")) { m_prog.newline = NL_LF;
        } else if (EqAscii(m_p + ns, nl, "CR")) { m_prog.newline = NL_CR;
        } else if (EqAscii(m_p + ns, nl, "CRLF")) { m_prog.newline = NL_CRLF;
        } else if (EqAscii(m_p + ns, nl, "ANYCRLF")) { m_prog.newline = NL_ANYCRLF;
        } else if (EqAscii(m_p + ns, nl, "ANY")) { m_prog.newline = NL_ANY;
        } else if (EqAscii(m_p + ns, nl, "BSR_ANYCRLF")) { m_prog.bsrAnyCrlf = 1;
        } else if (EqAscii(m_p + ns, nl, "BSR_UNICODE")) { m_prog.bsrAnyCrlf = 0;
        } else if (EqAscii(m_p + ns, nl, "NOTEMPTY")) { m_prog.notEmpty = 1;
        } else if (EqAscii(m_p + ns, nl, "NOTEMPTY_ATSTART")) { m_prog.notEmpty = 2;
        } else if (EqAscii(m_p + ns, nl, "LIMIT_MATCH") && val >= 0) { m_prog.limitMatch = (unsigned long)val;
        } else {
            return;   /* a verb that belongs to the pattern body */
        }
        m_pos = p + 1;
    }
}

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
            if (v >= 0xD800 && v < 0xDC00 && AtCh(m_pos, '\\') && AtCh(m_pos + 1, 'u')) {   /* U+1F600 etc. : a surrogate pair is one character */
                Cp lo = 0;
                for (n = 0; n < 4; ++n) {
                    if (m_pos + 2 + n >= m_len || HexValue(At(m_pos + 2 + n)) < 0) break;
                    lo = lo * 16 + (Cp)HexValue(At(m_pos + 2 + n));
                }
                if (n == 4 && lo >= 0xDC00 && lo < 0xE000) {
                    m_pos += 6;
                    v = 0x10000 + ((v - 0xD800) << 10) + (lo - 0xDC00);
                }
            }
            out = v;
            return true;
        }
    case 'o': {
        unsigned long v = 0;
        int digits = 0;
        if (!AtCh(m_pos, '{')) return false;   /* a plain 'o' */
        ++m_pos;
        while (m_pos < m_len && At(m_pos) >= '0' && At(m_pos) <= '7') {
            v = v * 8 + (unsigned long)(At(m_pos) - '0');
            if (v > 0x10FFFFUL) Error("code point value too large");
            ++m_pos;
            ++digits;
        }
        if (digits == 0 || !More() || At(m_pos) != '}') Error("malformed \\o{...} escape");
        ++m_pos;
        out = (Cp)v;
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

/* names are compared loosely like PCRE2 does: case, spaces, '_' and '-' do not matter */
static bool LooseEq(const wchar_t* w, int n, const char* a)
{
    int i = 0, j = 0;
    for (;;) {
        Cp x, y;
        while (i < n && (w[i] == ' ' || w[i] == '_' || w[i] == '-')) ++i;
        while (a[j] == ' ' || a[j] == '_' || a[j] == '-') ++j;
        if (i >= n || a[j] == 0) return i >= n && a[j] == 0;
        x = (Cp)w[i];
        y = (Cp)(unsigned char)a[j];
        if (x >= 'A' && x <= 'Z') x += 32;
        if (y >= 'A' && y <= 'Z') y += 32;
        if (x != y) return false;
        ++i;
        ++j;
    }
}

static bool FindCategoryProp(const wchar_t* w, int n, unsigned int& mask, unsigned int& extra)
{
    int i, k;
    for (i = 0; i < ARRAY_COUNT(kPropNames); ++i) {
        if (LooseEq(w, n, kPropNames[i].name)) {
            mask = kPropNames[i].mask;
            extra = kPropNames[i].extra;
            return true;
        }
    }
    for (i = 0; i < g_gcAliasesCount; ++i) {   /* Uppercase_Letter, Letter, ... */
        if (!LooseEq(w, n, g_gcAliases[i].a)) continue;
        for (k = 0; k < ARRAY_COUNT(kPropNames); ++k) {
            if (strcmp(kPropNames[k].name, g_gcAliases[i].b) == 0) {
                mask = kPropNames[k].mask;
                extra = kPropNames[k].extra;
                return true;
            }
        }
    }
    return false;
}

void Compiler::ReadProperty(bool negated, ClassProp& p)   /* after \p or \P */
{
    int start, len, i, colon = -1, mode = 0;   /* mode: 0 any name, 1 category, 2 Script, 3 Script_Extensions */
    const wchar_t* nm;
    int nl;
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
    p.script = -1;
    p.scx = 0;
    p.bin = -1;   /* unknown names match nothing */
    nm = m_p + start;
    nl = len;
    for (i = 0; i < len; ++i) {
        if (m_p[start + i] == ':' || m_p[start + i] == '=') { colon = i; break; }
    }
    if (colon >= 0) {   /* sc:Hira  Script=Hiragana  scx:Hira  gc=Lu */
        if (LooseEq(nm, colon, "sc") || LooseEq(nm, colon, "script")) mode = 2;
        else if (LooseEq(nm, colon, "scx") || LooseEq(nm, colon, "scriptextensions")) mode = 3;
        else if (LooseEq(nm, colon, "gc") || LooseEq(nm, colon, "generalcategory") || LooseEq(nm, colon, "category")) mode = 1;
        else return;
        nm += colon + 1;
        nl = len - colon - 1;
    }
    if ((mode == 0 || mode == 1) && FindCategoryProp(nm, nl, p.mask, p.extra)) return;
    if (mode == 0) {
        for (i = 0; i < g_binPropsCount; ++i) {
            if (LooseEq(nm, nl, g_binProps[i].name) || (g_binProps[i].alias[0] && LooseEq(nm, nl, g_binProps[i].alias))) {
                p.bin = i;
                return;
            }
        }
    }
    if (mode == 0 || mode == 2 || mode == 3) {
        for (i = 0; i < g_scriptNamesCount; ++i) {
            if (LooseEq(nm, nl, g_scriptNames[i].name)) {
                p.script = g_scriptNames[i].id;
                p.scx = (mode == 2) ? 0 : 1;   /* \p{Hiragana} uses Script_Extensions, as PCRE2 and Perl do */
                return;
            }
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

/*
 * \g1 \g-1 \g{1} \g{-1} \g{name}: back references;
 * \g<name> \g<1> \g<-1> \g'name' : subroutine calls, as in PCRE2 (resolved by the callback if undefined)
 */
int Compiler::ParseGRef()
{
    int s, num, nameRef;
    bool call = false;
    if (More() && (At(m_pos) == '{' || At(m_pos) == '<' || At(m_pos) == '\'')) {
        Cp close = (At(m_pos) == '{') ? (Cp)'}' : (At(m_pos) == '<') ? (Cp)'>' : (Cp)'\'';
        call = (close != '}');
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
    if (call) {
        int n = NewNode(N_CALL, num, nameRef);
        m_nodes[n].pos = s;
        return n;
    }
    return NewNode(N_BACKREF, num, nameRef, (m_flags & F_I) ? 1 : 0);
}

int Compiler::ParseEscape()
{
    Cp c, ch;
    if (m_pos + 1 >= m_len) Error("\\ at end of pattern");
    c = At(m_pos + 1);
    m_pos += 2;
    if (m_prog.ucp) {
        ClassProp up;
        if (UcpShorthand(c, up)) {
            ClassBuilder cb;
            cb.props.Push(up);
            return NewNode(N_CLASS, FinishClass(m_prog, cb));
        }
    }
    switch (c) {
    case 'd': return SetNode(kDigit, ARRAY_COUNT(kDigit), false);
    case 'D': return SetNode(kDigit, ARRAY_COUNT(kDigit), true);
    case 'w': return SetNode(kWord, ARRAY_COUNT(kWord), false);
    case 'W': return SetNode(kWord, ARRAY_COUNT(kWord), true);
    case 's': return SetNode(kSpace, ARRAY_COUNT(kSpace), false);
    case 'S': return SetNode(kSpace, ARRAY_COUNT(kSpace), true);
    case 'h': return SetNode(kHSpace, ARRAY_COUNT(kHSpace), false);
    case 'H': return SetNode(kHSpace, ARRAY_COUNT(kHSpace), true);
    case 'b': return NewNode(N_ASSERT, m_prog.ucp ? OP_UWORDB : OP_WORDB);
    case 'B': return NewNode(N_ASSERT, m_prog.ucp ? OP_UNWORDB : OP_NWORDB);
    case 'A': return NewNode(N_ASSERT, OP_BOS);
    case 'Z': return NewNode(N_ASSERT, OP_EOSNL);
    case 'z': return NewNode(N_ASSERT, OP_EOS);
    case 'G': return NewNode(N_ASSERT, OP_GPOS);
    case 'K':
        if (m_look > 0) Error("\\K is not supported inside assertions", m_pos - 2);   /* as PCRE2 10.38+ */
        return NewNode(N_KEEP);
    case 'R': return NewNode(N_BSR);
    case 'X': return NewNode(N_GRAPHEME);
    case 'C':
        Error("\\C is not supported", m_pos - 2);
        return -1;
    case 'v': return SetNode(kVSpace, ARRAY_COUNT(kVSpace), false);
    case 'V': return SetNode(kVSpace, ARRAY_COUNT(kVSpace), true);
    case 'N': {
        Cp v;
        if (ReadUPlus(v)) return MakeLiteral(v);
        return NewNode(N_ANY, 0);   /* \N: any character but a newline, even with (?s) */
    }
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
    --m_pos;   /* an unknown escape stands for the character itself (a surrogate pair is one character) */
    return MakeLiteral(TakeCp());   /* \. \* \\ ... and unknown escapes stand for the character itself */
}

/* ---- character classes ---- */

void Compiler::AddClassChars(ClassBuilder& cb, Cp lo, Cp hi)
{
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
        c = TakeCp();
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
            if (m_prog.ucp) {
                ClassProp up;
                if (UcpPosix(m_p + s, p - s, neg, up)) {
                    cb.props.Push(up);
                    m_pos = p + 2;
                    return 1;
                }
                if (EqAscii(m_p + s, p - s, "blank")) {
                    AddSet(cb.esc, kHSpace, ARRAY_COUNT(kHSpace), neg);
                    m_pos = p + 2;
                    return 1;
                }
            }
            AddSet(kPosix[found].caseSensitive ? cb.lit : cb.esc, kPosix[found].r, kPosix[found].n, neg);
            m_pos = p + 2;
            return 1;
        }
    }
    if (c != '\\') {
        ch = TakeCp();
        return 0;
    }
    if (m_pos + 1 >= m_len) Error("\\ at end of pattern");
    c = At(m_pos + 1);
    m_pos += 2;
    if (m_prog.ucp) {
        ClassProp up;
        if (UcpShorthand(c, up)) {
            cb.props.Push(up);
            return 1;
        }
    }
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
    case 'v': AddSet(cb.esc, kVSpace, ARRAY_COUNT(kVSpace), false); return 1;
    case 'V': AddSet(cb.esc, kVSpace, ARRAY_COUNT(kVSpace), true); return 1;
    case 'C':
        Error("\\C is not supported", m_pos - 2);
        return 2;
    case 'R':
    case 'X':
    case 'B':
        Error("escape sequence is invalid in a character class", m_pos - 2);
        return 2;
    case 'N':
        if (ReadUPlus(ch)) return 0;
        Error("\\N is not allowed in a character class", m_pos - 2);
        return 2;
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
    --m_pos;   /* an unknown escape stands for the character itself */
    ch = TakeCp();
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
        if ((m_flags & F_XX) && m_quote == 0 && (At(m_pos) == ' ' || At(m_pos) == '\t')) {   /* (?xx) */
            ++m_pos;
            continue;
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

/* "<prefix>'<name>'<suffix>" into a message buffer of 96 bytes (non-ASCII characters of the name become '?') */
static void SubroutineMessage(char* msg, const char* prefix, const wchar_t* name, const char* suffix)
{
    int k = 0, j = 0;
    while (prefix[k] && k < 40) { msg[k] = prefix[k]; ++k; }
    msg[k++] = '\'';
    while (name[j] && j < 20 && k < 70) { msg[k++] = ((Cp)name[j] < 128) ? (char)name[j] : '?'; ++j; }
    msg[k++] = '\'';
    for (j = 0; suffix[j] && k < 95; ++j) msg[k++] = suffix[j];
    msg[k] = 0;
}

/* Subroutine calls to names that the pattern does not define are resolved through the callback. */
void Compiler::ResolveExternal()
{
    int guard = 0;
    if (!m_resolver) return;   /* the calls stay unresolved and are reported by ResolveRef() */
    for (;;) {
        int i, found = -1, nameOff, num, g, body, savedLen, savedPos;
        CRegexpString text;   /* the pattern the resolver returns (owned here until it is parsed) */
        const wchar_t* savedP;
        unsigned int savedFlags;
        NameEnt ne;
        for (i = 0; i < m_nodes.Size(); ++i) {
            if (m_nodes[i].type == N_CALL && m_nodes[i].b != 0 && FindNamedGroup(m_nodes[i].b - 1) == 0) {
                found = i;
                break;
            }
        }
        if (found < 0) return;
        if (++guard > 256) Error("too many subroutines from the resolver", -1);
        nameOff = m_nodes[found].b - 1;
        if (!m_resolver(m_prog.namePool.Data() + nameOff, text, m_resolverUser)) {
            char msg[96];
            SubroutineMessage(msg, "undefined subroutine ", m_prog.namePool.Data() + nameOff, "");
            Error(msg, m_nodes[found].pos);
        }

        num = ++m_maxGroup;   /* the subroutine becomes a named group after all other groups */
        m_counter = m_maxGroup;
        ne.off = nameOff;
        ne.group = num;
        m_prog.names.Push(ne);

        savedP = m_p; savedLen = m_len; savedPos = m_pos; savedFlags = m_flags;
        m_p = text.c_str();
        m_len = text.size();
        m_pos = 0;
        m_flags = m_initFlags;
        m_quote = 0;
        m_depth = 0;
        m_look = 0;
        try {
            body = ParseAlt(false);
            if (m_pos < m_len) Error("unmatched )");
        } catch (CRegexpException& e) {
            char msg[96], tail[64];
            int j;
            tail[0] = ':'; tail[1] = ' ';
            for (j = 0; e.what()[j] && j < 60; ++j) tail[2 + j] = e.what()[j];
            tail[2 + j] = 0;
            SubroutineMessage(msg, "in subroutine ", m_prog.namePool.Data() + nameOff, tail);
            throw CRegexpException(CRegexpException::ERR_SYNTAX, -1, msg);
        }
        m_p = savedP; m_len = savedLen; m_pos = savedPos; m_flags = savedFlags;
        g = NewNode(N_GROUP, num);
        m_nodes[g].child = body;
        m_nodes[g].pos = m_nodes[found].pos;
        m_external.Push(g);
    }
}

void Compiler::Run()
{
    int root;
    ParseStartVerbs();
    root = ParseAlt(false);
    if (m_pos < m_len) Error("unmatched )");
    ResolveExternal();
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
        for (i = 0; i < m_external.Size(); ++i) Gen(m_external[i]);   /* after MATCH: reachable by calls only */
    }
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
    if (sizeof(wchar_t) == 2 && m_prog.firstChar > 0xFFFF)   /* the search compares wchar_t units: use the high surrogate */
        m_prog.firstChar = (int)(0xD800 + ((Cp)(m_prog.firstChar - 0x10000) >> 10));
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
    case N_BSR:
        mn = 1;
        mx = 2;
        return;
    case N_GRAPHEME:
        mn = 1;
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

/* the longest length in wchar_t units of text of mx characters (a character is two units where wchar_t is UTF-16) */
static int MaxUnits(int mx)
{
    if (mx < 0 || sizeof(wchar_t) != 2) return mx;
    return mx > LEN_CAP / 2 ? -1 : mx * 2;
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
            /* like PCRE, a leading (*COMMIT) does not anchor: the search skips ahead to the first literal */
            if (t == N_ASSERT || t == N_KEEP || t == N_EMPTY || t == N_LOOK || t == N_VERB) continue;
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
            mx = MaxUnits(mx);
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
    case N_BSR:
        Emit2(OP_BSR, m_prog.bsrAnyCrlf);
        break;
    case N_GRAPHEME:
        Emit(OP_GRAPHEME);
        break;
    case N_VERB:
        if (nd.a == 0) Emit(OP_FAIL);
        else Emit2(OP_VERB, nd.a);
        break;
    case N_COND: {
        int endJump;
        if (nd.a == 0 || nd.a == 3) {   /* (?(group)yes|no)  (?(R)yes|no) */
            int g, cj;
            if (nd.a == 0) g = ResolveRef(nd.b, nd.c, nd.pos, false);
            else if (nd.c) g = ResolveRef(0, nd.c, nd.pos, false);
            else if (nd.b > 0) g = ResolveRef(nd.b, 0, nd.pos, false);
            else g = -1;
            cj = Emit3(nd.a == 0 ? OP_COND_GROUP : OP_COND_REC, g, 0);
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
                mx = MaxUnits(mx);
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
 *   BT_VERB    a = VERB_*, b = pos                              (*COMMIT) (*PRUNE) (*SKIP): backtracking onto it ends the attempt
 */
enum { BT_CHOICE = 1, BT_GREEDY, BT_LAZY, BT_MARK, BT_LB, BT_UNDO, BT_POOL, BT_VERB };

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

static inline bool IsUcpWordCp(Cp c)
{
    return c == '_' || (((MASK_L | MASK_N) >> UcCategory(c)) & 1u) != 0;
}

static inline bool IsAnyNewline(Cp c)
{
    return c == 10 || c == 11 || c == 12 || c == 13 || c == 0x85 || c == 0x2028 || c == 0x2029;
}

/* length of the newline sequence that starts at s[i] (i < n) for the newline convention mode, 0 if none */
static inline int NlAt(int mode, const wchar_t* s, int i, int n)
{
    Cp c = (Cp)s[i];
    switch (mode) {
    case NL_LF:
        return c == '\n' ? 1 : 0;
    case NL_CR:
        return c == '\r' ? 1 : 0;
    case NL_CRLF:
        return (c == '\r' && i + 1 < n && s[i + 1] == '\n') ? 2 : 0;
    case NL_ANYCRLF:
        if (c == '\r') return (i + 1 < n && s[i + 1] == '\n') ? 2 : 1;
        return c == '\n' ? 1 : 0;
    default:
        if (c == '\r') return (i + 1 < n && s[i + 1] == '\n') ? 2 : 1;
        return IsAnyNewline(c) ? 1 : 0;
    }
}

/* does a newline sequence end exactly at position i (0 < i <= n)? */
static inline bool NlBefore(int mode, const wchar_t* s, int i, int n)
{
    Cp c = (Cp)s[i - 1];
    switch (mode) {
    case NL_LF:
        return c == '\n';
    case NL_CR:
        return c == '\r';
    case NL_CRLF:
        return c == '\n' && i >= 2 && s[i - 2] == '\r';
    case NL_ANYCRLF:
        if (c == '\r') return !(i < n && s[i] == '\n');
        return c == '\n';
    default:
        if (c == '\r') return !(i < n && s[i] == '\n');
        return IsAnyNewline(c);
    }
}

/* does the single character matcher (aop, arg) match the character at s[i] (i < n)?  Returns its length in wchar_t units, 0 if not */
static inline int AtomLen(const Program& prog, int aop, int arg, const wchar_t* s, int i, int n)
{
    int len;
    Cp c = DecodeAt(s, n, i, len);
    switch (aop) {
    case OP_CHAR:  return c == (Cp)arg ? len : 0;
    case OP_CHARI: return UcFold(c) == (Cp)arg ? len : 0;
    case OP_ANY:   return NlAt(prog.newline, s, i, n) == 0 ? len : 0;
    case OP_ANYNL: return len;
    default:       return ClassMatch(prog, arg, c) ? len : 0;
    }
}

/*
 * Walk over up to limit (-1: any number of) characters that the single character matcher (aop, arg)
 * accepts, starting at q.  Returns the position after them and adds their number to *count.
 * The same as calling AtomLen() in a loop, but with the choice of the matcher made once.
 */
#define SCAN_ATOMS(TEST) \
    while (q < n && (limit < 0 || cnt < limit)) { \
        Cp c = (Cp)s[q]; \
        int len = 1; \
        if (sizeof(wchar_t) == 2 && c >= 0xD800 && c < 0xDC00) c = DecodeAt(s, n, q, len); \
        if (!(TEST)) break; \
        q += len; \
        ++cnt; \
    }

static int ScanAtoms(const Program& prog, int aop, int arg, const wchar_t* s, int q, int n, int limit, int* count)
{
    int cnt = 0;
    switch (aop) {
    case OP_CHAR:  SCAN_ATOMS(c == (Cp)arg) break;
    case OP_CHARI: SCAN_ATOMS(UcFold(c) == (Cp)arg) break;
    case OP_ANY:   SCAN_ATOMS(NlAt(prog.newline, s, q, n) == 0) break;
    case OP_ANYNL: SCAN_ATOMS(true) break;
    default:       SCAN_ATOMS(ClassMatch(prog, arg, c)) break;
    }
    *count += cnt;
    return q;
}
#undef SCAN_ATOMS

enum { GCB_OTHER, GCB_CR, GCB_LF, GCB_CONTROL, GCB_EXTEND, GCB_ZWJ, GCB_RI, GCB_PREPEND, GCB_SPACING,
       GCB_L, GCB_V, GCB_T, GCB_LV, GCB_LVT };

static bool IsExtPict(Cp c)
{
    return InRanges(g_binExtendedPictographic, g_binExtendedPictographicCount, c);
}

static int UcIncb(Cp c)   /* Indic_Conjunct_Break: 1 Consonant, 2 Linker, 3 Extend, 0 none */
{
    if (InRanges(g_incbConsonant, g_incbConsonantCount, c)) return 1;
    if (InRanges(g_incbLinker, g_incbLinkerCount, c)) return 2;
    if (InRanges(g_incbExtend, g_incbExtendCount, c)) return 3;
    return 0;
}

/* length of the extended grapheme cluster (Unicode UAX #29) that starts at s[pos] (pos < n) */
static int GraphemeLen(const wchar_t* s, int n, int pos)
{
    int len1, i;
    Cp c = DecodeAt(s, n, pos, len1);
    int prev = UcGcb(c);
    int epState = IsExtPict(c) ? 1 : 0;    /* ExtPict Extend* (1), then ZWJ (2) */
    int riCount = (prev == GCB_RI) ? 1 : 0;
    int incbState = (UcIncb(c) == 1) ? 1 : 0;   /* Consonant [Extend Linker]* (1), with a Linker (2) */
    i = pos + len1;
    while (i < n) {
        int len2;
        Cp c2 = DecodeAt(s, n, i, len2);
        int g2 = UcGcb(c2);
        int ic = UcIncb(c2);
        bool brk;
        if (prev == GCB_CR && g2 == GCB_LF) brk = false;                                           /* GB3 */
        else if (prev == GCB_CONTROL || prev == GCB_CR || prev == GCB_LF) brk = true;              /* GB4 */
        else if (g2 == GCB_CONTROL || g2 == GCB_CR || g2 == GCB_LF) brk = true;                    /* GB5 */
        else if (prev == GCB_L && (g2 == GCB_L || g2 == GCB_V || g2 == GCB_LV || g2 == GCB_LVT)) brk = false;   /* GB6 */
        else if ((prev == GCB_LV || prev == GCB_V) && (g2 == GCB_V || g2 == GCB_T)) brk = false;   /* GB7 */
        else if ((prev == GCB_LVT || prev == GCB_T) && g2 == GCB_T) brk = false;                   /* GB8 */
        else if (g2 == GCB_EXTEND || g2 == GCB_ZWJ) brk = false;                                   /* GB9 */
        else if (g2 == GCB_SPACING) brk = false;                                                   /* GB9a */
        else if (prev == GCB_PREPEND) brk = false;                                                 /* GB9b */
        else if (incbState == 2 && ic == 1) brk = false;                                           /* GB9c */
        else if (epState == 2 && IsExtPict(c2)) brk = false;                                       /* GB11 */
        else if (prev == GCB_RI && g2 == GCB_RI && (riCount & 1)) brk = false;                     /* GB12, GB13 */
        else brk = true;                                                                           /* GB999 */
        if (brk) break;
        if (IsExtPict(c2)) epState = 1;
        else if (g2 == GCB_EXTEND && epState == 1) epState = 1;
        else if (g2 == GCB_ZWJ && epState == 1) epState = 2;
        else epState = 0;
        riCount = (g2 == GCB_RI) ? riCount + 1 : 0;
        if (ic == 1) incbState = 1;
        else if (ic == 2) incbState = (incbState >= 1) ? 2 : 0;
        else if (ic == 3) { /* Extend: keeps the state */ }
        else incbState = 0;
        prev = g2;
        i += len2;
    }
    return i - pos;
}

class Matcher {
public:
    Matcher(const Program& prog, Work& w, const wchar_t* s, int n, int gpos, int notEmptyAt, unsigned long limit);
    bool Search(int from);
    void SetExact() { m_exact = true; }   /* a match must end at the end of the subject */
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
    bool m_exact;
    unsigned long m_limit;
    unsigned long m_steps;
    int m_stackLimit;   /* maximum number of backtrack stack entries */
    int m_verb;         /* VERB_* that ended the last Run(), or 0 */
    int m_verbPos;
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
    : m_prog(prog), m_w(w), m_s(s), m_n(n), m_gpos(gpos), m_notEmptyAt(notEmptyAt), m_exact(false),
      m_limit(limit), m_steps(0), m_verb(0), m_verbPos(0), m_code(prog.code.Data())
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
        if (t == BT_UNDO || t == BT_POOL || t == BT_VERB) stk[w++] = stk[i];
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

    const int nl = m_prog.newline;

    m_verb = 0;
    m_w.hnodes.Clear();
    for (;;) {
        switch (code[pc]) {
        case OP_MATCH: {
            int ms = st[0];
            if (st[m_kpos] >= 0) ms = st[m_kpos];
            if (ms > pos) ms = pos;   /* a \K reached through a subroutine call from an assertion */
            if (ms < startPos) ms = startPos;
            if (m_notEmptyAt >= 0 && ms == m_notEmptyAt && pos == m_notEmptyAt) goto fail;
            if (m_prog.notEmpty == 1 && ms == pos) goto fail;
            if (m_exact && pos != n) goto fail;
            st[0] = ms;
            st[1] = pos;
            return true;
        }
        case OP_CHAR:
        case OP_CHARI:
        case OP_CLASS: {
            int len;
            if (pos >= n) goto fail;
            len = AtomLen(m_prog, code[pc], code[pc + 1], s, pos, n);
            if (len == 0) goto fail;
            pos += len;
            pc += 2;
            continue;
        }
        case OP_ANY:
        case OP_ANYNL: {
            int len;
            if (pos >= n) goto fail;
            len = AtomLen(m_prog, code[pc], 0, s, pos, n);
            if (len == 0) goto fail;
            pos += len;
            ++pc;
            continue;
        }

        case OP_BOL:
        case OP_BOS:
            if (pos == 0) { ++pc; continue; }
            goto fail;
        case OP_MBOL:   /* like PCRE: not after a newline that ends the subject */
            if (pos == 0 || (pos < n && NlBefore(nl, s, pos, n))) { ++pc; continue; }
            goto fail;
        case OP_EOL:
        case OP_EOS:
            if (pos == n) { ++pc; continue; }
            goto fail;
        case OP_MEOL:
            if (pos == n || NlAt(nl, s, pos, n) > 0) { ++pc; continue; }
            goto fail;
        case OP_EOSNL:
            if (pos == n || (NlAt(nl, s, pos, n) > 0 && pos + NlAt(nl, s, pos, n) == n)) { ++pc; continue; }
            goto fail;
        case OP_WORDB:
        case OP_NWORDB: {
            bool before = pos > 0 && IsWordCp((Cp)s[pos - 1]);
            bool after = pos < n && IsWordCp((Cp)s[pos]);
            if ((before != after) == (code[pc] == OP_WORDB)) { ++pc; continue; }
            goto fail;
        }
        case OP_UWORDB:
        case OP_UNWORDB: {
            int len;
            bool before = pos > 0 && IsUcpWordCp(DecodeAt(s, n, pos - PrevLen(s, pos), len));
            bool after = pos < n && IsUcpWordCp(DecodeAt(s, n, pos, len));
            if ((before != after) == (code[pc] == OP_UWORDB)) { ++pc; continue; }
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
                for (i = 0; i < len; ) {   /* character by character: a surrogate pair is folded as one character */
                    int l1, l2;
                    Cp c1 = DecodeAt(s, n, bs + i, l1);
                    Cp c2 = DecodeAt(s, n, pos + i, l2);
                    if (l1 != l2 || UcFold(c1) != UcFold(c2)) goto fail;
                    i += l1;
                }
                if (i != len) goto fail;
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
            if (IsMidPair(s, n, s0)) goto fail;   /* the body cannot start inside a surrogate pair */
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
            int cnt = 0, q = ScanAtoms(m_prog, aop, arg, s, pos, n, mn, &cnt);   /* cnt characters from pos to q */
            if (cnt < mn) goto fail;
            if (mode == REP_LAZY) {
                pos = q;
                if (mx < 0 || mx > mn) PushBt(BT_LAZY, pc, pos, mn);
                pc += 6;
                continue;
            }
            {
                int minEnd = q;   /* where the mandatory part ends: greedy gives back down to here */
                q = ScanAtoms(m_prog, aop, arg, s, q, n, mx < 0 ? -1 : mx - mn, &cnt);
                if (mode == REP_GREEDY && q > minEnd) PushBt(BT_GREEDY, pc + 6, minEnd, q - PrevLen(s, q));
            }
            pos = q;
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

        case OP_COND_REC: {
            int g = code[pc + 1];
            int fr = st[m_frame];
            if (fr >= 0 && (g < 0 || m_w.frames[fr].target == g)) pc += 3;
            else pc = code[pc + 2];
            continue;
        }
        case OP_FAIL:
            goto fail;
        case OP_VERB:
            PushBt(BT_VERB, code[pc + 1], pos, 0);
            pc += 2;
            continue;
        case OP_BSR: {   /* \R: atomic, CRLF is never split */
            Cp c;
            if (pos >= n) goto fail;
            c = (Cp)s[pos];
            if (c == '\r') pos += (pos + 1 < n && s[pos + 1] == '\n') ? 2 : 1;
            else if (c == '\n' || (!code[pc + 1] && (c == 11 || c == 12 || c == 0x85 || c == 0x2028 || c == 0x2029))) ++pos;
            else goto fail;
            pc += 2;
            continue;
        }
        case OP_GRAPHEME:
            if (pos >= n) goto fail;
            pos += GraphemeLen(s, n, pos);
            ++pc;
            continue;

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
            case BT_GREEDY:   /* give back one character at a time */
                pc = e.a;
                pos = e.c;
                if (e.c > e.b) e.c -= PrevLen(s, e.c); else stk.Pop();
                goto resume;
            case BT_LAZY: {
                int rp = e.a;
                int mx = code[rp + 3];
                int len = 0;
                if ((mx >= 0 && e.c >= mx) || e.b >= n || (len = AtomLen(m_prog, code[rp + 4], code[rp + 5], s, e.b, n)) == 0) {
                    stk.Pop();
                    continue;
                }
                pos = e.b + len;
                pc = rp + 6;
                ++e.c;
                if (mx >= 0 && e.c >= mx) stk.Pop(); else e.b = pos;
                goto resume;
            }
            case BT_VERB:
                m_verb = e.a;
                m_verbPos = e.b;
                UnwindTo(0);
                return false;
            case BT_MARK:
                if (e.a >= 0) {
                    pc = e.a;
                    pos = e.b;
                    stk.Pop();
                    goto resume;
                }
                stk.Pop();
                continue;
            case BT_LB: {
                int cand = e.b, target = e.a;
                if (e.b > e.c) --e.b; else stk.Pop();
                if (IsMidPair(s, n, cand)) continue;   /* the body cannot start inside a surrogate pair */
                pc = target;
                pos = cand;
                goto resume;
            }
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
    if (m_exact) return Run(p);   /* only the search start is tried */
    for (;;) {
        if (m_prog.firstChar >= 0) {
            while (p < m_n && (Cp)m_s[p] != (Cp)m_prog.firstChar) ++p;
            if (p >= m_n) return false;
        }
        if (p == from || !IsMidPair(m_s, m_n, p)) {   /* a match never starts inside a surrogate pair */
            if (Run(p)) return true;
            if (m_verb == VERB_COMMIT || m_prog.anchored) return false;
        }
        if (m_verb == VERB_SKIP && m_verbPos > p) {
            p = m_verbPos;
        } else if (p < m_n) {
            int len;
            DecodeAt(m_s, m_n, p, len);
            p += len;
        } else {
            ++p;
        }
        if (p > m_n) return false;
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

int UcScript(Cp c)
{
    int lo = 0, hi = g_scriptRunsCount - 1;
    if (c > MAX_CP) return 0;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if ((g_scriptRuns[mid] >> 8) <= c) lo = mid; else hi = mid - 1;
    }
    return (int)(g_scriptRuns[lo] & 255u);
}

bool UcScriptExt(Cp c, int id)
{
    int lo = 0, hi = g_scxRangesCount - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (c < g_scxRanges[mid].lo) {
            hi = mid - 1;
        } else if (c > g_scxRanges[mid].hi) {
            lo = mid + 1;
        } else {
            const unsigned char* p = g_scxData + g_scxRanges[mid].off;
            for (; *p != 255; ++p) if (*p == id) return true;
            return false;
        }
    }
    return UcScript(c) == id;
}

int UcGcb(Cp c)
{
    int lo = 0, hi = g_gcbRunsCount - 1;
    if (c > MAX_CP) return 0;
    while (lo < hi) {
        int mid = (lo + hi + 1) / 2;
        if ((g_gcbRuns[mid] >> 4) <= c) lo = mid; else hi = mid - 1;
    }
    return (int)(g_gcbRuns[lo] & 15u);
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

// Script of every code point: (first code point << 8) | script id.  Script id 0 is Unknown.
const unsigned int g_scriptRuns[] = {
    0x19,0x4148,0x5B19,0x6148,0x7B19,0xAA48,0xAB19,0xBA48,
    0xBB19,0xC048,0xD719,0xD848,0xF719,0xF848,0x2B919,0x2E048,
    0x2E519,0x2EA0D,0x2EC19,0x30038,0x3702C,0x37419,0x3752C,0x37800,
    0x37A2C,0x37E19,0x37F2C,0x38000,0x3842C,0x38519,0x3862C,0x38719,
    0x3882C,0x38B00,0x38C2C,0x38D00,0x38E2C,0x3A200,0x3A32C,0x3E21A,
    0x3F02C,0x4001E,0x48538,0x4871E,0x53000,0x53105,0x55700,0x55905,
    0x58B00,0x58D05,0x59000,0x59135,0x5C800,0x5D035,0x5EB00,0x5EF35,
    0x5F500,0x60004,0x60519,0x60604,0x60C19,0x60D04,0x61B19,0x61C04,
    0x61F19,0x62004,0x64019,0x64104,0x64B38,0x65604,0x67038,0x67104,
    0x6DD19,0x6DE04,0x7008C,0x70E00,0x70F8C,0x74B00,0x74D8C,0x75004,
    0x78097,0x7B200,0x7C067,0x7FB00,0x7FD67,0x80080,0x82E00,0x83080,
    0x83F00,0x84053,0x85C00,0x85E53,0x85F00,0x8608C,0x86B00,0x87004,
    0x88F00,0x89004,0x89200,0x89804,0x8E219,0x8E304,0x90020,0x95138,
    0x95520,0x96419,0x96620,0x9800B,0x98400,0x9850B,0x98D00,0x98F0B,
    0x99100,0x9930B,0x9A900,0x9AA0B,0x9B100,0x9B20B,0x9B300,0x9B60B,
    0x9BA00,0x9BC0B,0x9C500,0x9C70B,0x9C900,0x9CB0B,0x9CF00,0x9D70B,
    0x9D800,0x9DC0B,0x9DE00,0x9DF0B,0x9E400,0x9E60B,0x9FF00,0xA012F,
    0xA0400,0xA052F,0xA0B00,0xA0F2F,0xA1100,0xA132F,0xA2900,0xA2A2F,
    0xA3100,0xA322F,0xA3400,0xA352F,0xA3700,0xA382F,0xA3A00,0xA3C2F,
    0xA3D00,0xA3E2F,0xA4300,0xA472F,0xA4900,0xA4B2F,0xA4E00,0xA512F,
    0xA5200,0xA592F,0xA5D00,0xA5E2F,0xA5F00,0xA662F,0xA7700,0xA812D,
    0xA8400,0xA852D,0xA8E00,0xA8F2D,0xA9200,0xA932D,0xAA900,0xAAA2D,
    0xAB100,0xAB22D,0xAB400,0xAB52D,0xABA00,0xABC2D,0xAC600,0xAC72D,
    0xACA00,0xACB2D,0xACE00,0xAD02D,0xAD100,0xAE02D,0xAE400,0xAE62D,
    0xAF200,0xAF92D,0xB0000,0xB0175,0xB0400,0xB0575,0xB0D00,0xB0F75,
    0xB1100,0xB1375,0xB2900,0xB2A75,0xB3100,0xB3275,0xB3400,0xB3575,
    0xB3A00,0xB3C75,0xB4500,0xB4775,0xB4900,0xB4B75,0xB4E00,0xB5575,
    0xB5800,0xB5C75,0xB5E00,0xB5F75,0xB6400,0xB6675,0xB7800,0xB8293,
    0xB8400,0xB8593,0xB8B00,0xB8E93,0xB9100,0xB9293,0xB9600,0xB9993,
    0xB9B00,0xB9C93,0xB9D00,0xB9E93,0xBA000,0xBA393,0xBA500,0xBA893,
    0xBAB00,0xBAE93,0xBBA00,0xBBE93,0xBC300,0xBC693,0xBC900,0xBCA93,
    0xBCE00,0xBD093,0xBD100,0xBD793,0xBD800,0xBE693,0xBFB00,0xC0096,
    0xC0D00,0xC0E96,0xC1100,0xC1296,0xC2900,0xC2A96,0xC3A00,0xC3C96,
    0xC4500,0xC4696,0xC4900,0xC4A96,0xC4E00,0xC5596,0xC5700,0xC5896,
    0xC5B00,0xC5D96,0xC5E00,0xC6096,0xC6400,0xC6696,0xC7000,0xC7796,
    0xC803D,0xC8D00,0xC8E3D,0xC9100,0xC923D,0xCA900,0xCAA3D,0xCB400,
    0xCB53D,0xCBA00,0xCBC3D,0xCC500,0xCC63D,0xCC900,0xCCA3D,0xCCE00,
    0xCD53D,0xCD700,0xCDD3D,0xCDF00,0xCE03D,0xCE400,0xCE63D,0xCF000,
    0xCF13D,0xCF400,0xD0052,0xD0D00,0xD0E52,0xD1100,0xD1252,0xD4500,
    0xD4652,0xD4900,0xD4A52,0xD5000,0xD5452,0xD6400,0xD6652,0xD8000,
    0xD8186,0xD8400,0xD8586,0xD9700,0xD9A86,0xDB200,0xDB386,0xDBC00,
    0xDBD86,0xDBE00,0xDC086,0xDC700,0xDCA86,0xDCB00,0xDCF86,0xDD500,
    0xDD686,0xDD700,0xDD886,0xDE000,0xDE686,0xDF000,0xDF286,0xDF500,
    0xE0198,0xE3B00,0xE3F19,0xE4098,0xE5C00,0xE8147,0xE8300,0xE8447,
    0xE8500,0xE8647,0xE8B00,0xE8C47,0xEA400,0xEA547,0xEA600,0xEA747,
    0xEBE00,0xEC047,0xEC500,0xEC647,0xEC700,0xEC847,0xECF00,0xED047,
    0xEDA00,0xEDC47,0xEE000,0xF0099,0xF4800,0xF4999,0xF6D00,0xF7199,
    0xF9800,0xF9999,0xFBD00,0xFBE99,0xFCD00,0xFCE99,0xFD519,0xFD999,
    0xFDB00,0x100061,0x10A028,0x10C600,0x10C728,0x10C800,0x10CD28,0x10CE00,
    0x10D028,0x10FB19,0x10FC28,0x110031,0x120027,0x124900,0x124A27,0x124E00,
    0x125027,0x125700,0x125827,0x125900,0x125A27,0x125E00,0x126027,0x128900,
    0x128A27,0x128E00,0x129027,0x12B100,0x12B227,0x12B600,0x12B827,0x12BF00,
    0x12C027,0x12C100,0x12C227,0x12C600,0x12C827,0x12D700,0x12D827,0x131100,
    0x131227,0x131600,0x131827,0x135B00,0x135D27,0x137D00,0x138027,0x139A00,
    0x13A017,0x13F600,0x13F817,0x13FE00,0x140012,0x16806A,0x169D00,0x16A07F,
    0x16EB19,0x16EE7F,0x16F900,0x17008D,0x171600,0x171F8D,0x172033,0x173519,
    0x173700,0x174011,0x175400,0x17608E,0x176D00,0x176E8E,0x177100,0x17728E,
    0x177400,0x178044,0x17DE00,0x17E044,0x17EA00,0x17F044,0x17FA00,0x18005E,
    0x180219,0x18045E,0x180519,0x18065E,0x181A00,0x18205E,0x187900,0x18805E,
    0x18AB00,0x18B012,0x18F600,0x19004A,0x191F00,0x19204A,0x192C00,0x19304A,
    0x193C00,0x19404A,0x194100,0x19444A,0x19508F,0x196E00,0x19708F,0x197500,
    0x198065,0x19AC00,0x19B065,0x19CA00,0x19D065,0x19DB00,0x19DE65,0x19E044,
    0x1A0010,0x1A1C00,0x1A1E10,0x1A2090,0x1A5F00,0x1A6090,0x1A7D00,0x1A7F90,
    0x1A8A00,0x1A9090,0x1A9A00,0x1AA090,0x1AAE00,0x1AB038,0x1ACF00,0x1B0007,
    0x1B4D00,0x1B5007,0x1B7F00,0x1B808A,0x1BC00A,0x1BF400,0x1BFC0A,0x1C0049,
    0x1C3800,0x1C3B49,0x1C4A00,0x1C4D49,0x1C506B,0x1C801E,0x1C8900,0x1C9028,
    0x1CBB00,0x1CBD28,0x1CC08A,0x1CC800,0x1CD038,0x1CD319,0x1CD438,0x1CE119,
    0x1CE238,0x1CE919,0x1CED38,0x1CEE19,0x1CF438,0x1CF519,0x1CF838,0x1CFA19,
    0x1CFB00,0x1D0048,0x1D262C,0x1D2B1E,0x1D2C48,0x1D5D2C,0x1D6248,0x1D662C,
    0x1D6B48,0x1D781E,0x1D7948,0x1DBF2C,0x1DC038,0x1E0048,0x1F002C,0x1F1600,
    0x1F182C,0x1F1E00,0x1F202C,0x1F4600,0x1F482C,0x1F4E00,0x1F502C,0x1F5800,
    0x1F592C,0x1F5A00,0x1F5B2C,0x1F5C00,0x1F5D2C,0x1F5E00,0x1F5F2C,0x1F7E00,
    0x1F802C,0x1FB500,0x1FB62C,0x1FC500,0x1FC62C,0x1FD400,0x1FD62C,0x1FDC00,
    0x1FDD2C,0x1FF000,0x1FF22C,0x1FF500,0x1FF62C,0x1FFF00,0x200019,0x200C38,
    0x200E19,0x206500,0x206619,0x207148,0x207200,0x207419,0x207F48,0x208019,
    0x208F00,0x209048,0x209D00,0x20A019,0x20C100,0x20D038,0x20F100,0x210019,
    0x21262C,0x212719,0x212A48,0x212C19,0x213248,0x213319,0x214E48,0x214F19,
    0x216048,0x218919,0x218C00,0x219019,0x242700,0x244019,0x244B00,0x246019,
    0x28000F,0x290019,0x2B7400,0x2B7619,0x2B9600,0x2B9719,0x2C0029,0x2C6048,
    0x2C801A,0x2CF400,0x2CF91A,0x2D0028,0x2D2600,0x2D2728,0x2D2800,0x2D2D28,
    0x2D2E00,0x2D309A,0x2D6800,0x2D6F9A,0x2D7100,0x2D7F9A,0x2D8027,0x2D9700,
    0x2DA027,0x2DA700,0x2DA827,0x2DAF00,0x2DB027,0x2DB700,0x2DB827,0x2DBF00,
    0x2DC027,0x2DC700,0x2DC827,0x2DCF00,0x2DD027,0x2DD700,0x2DD827,0x2DDF00,
    0x2DE01E,0x2E0019,0x2E5E00,0x2E8030,0x2E9A00,0x2E9B30,0x2EF400,0x2F0030,
    0x2FD600,0x2FF019,0x300530,0x300619,0x300730,0x300819,0x302130,0x302A38,
    0x302E31,0x303019,0x303830,0x303C19,0x304000,0x304136,0x309700,0x309938,
    0x309B19,0x309D36,0x30A019,0x30A13E,0x30FB19,0x30FD3E,0x310000,0x31050D,
    0x313000,0x313131,0x318F00,0x319019,0x31A00D,0x31C019,0x31E400,0x31EF19,
    0x31F03E,0x320031,0x321F00,0x322019,0x326031,0x327F19,0x32D03E,0x32FF19,
    0x33003E,0x335819,0x340030,0x4DC019,0x4E0030,0xA000A3,0xA48D00,0xA490A3,
    0xA4C700,0xA4D04D,0xA5009E,0xA62C00,0xA6401E,0xA6A008,0xA6F800,0xA70019,
    0xA72248,0xA78819,0xA78B48,0xA7CB00,0xA7D048,0xA7D200,0xA7D348,0xA7D400,
    0xA7D548,0xA7DA00,0xA7F248,0xA8008B,0xA82D00,0xA83019,0xA83A00,0xA8407B,
    0xA87800,0xA88081,0xA8C600,0xA8CE81,0xA8DA00,0xA8E020,0xA90041,0xA92E19,
    0xA92F41,0xA9307E,0xA95400,0xA95F7E,0xA96031,0xA97D00,0xA9803B,0xA9CE00,
    0xA9CF19,0xA9D03B,0xA9DA00,0xA9DE3B,0xA9E061,0xA9FF00,0xAA0016,0xAA3700,
    0xAA4016,0xAA4E00,0xAA5016,0xAA5A00,0xAA5C16,0xAA6061,0xAA8091,0xAAC300,
    0xAADB91,0xAAE058,0xAAF700,0xAB0127,0xAB0700,0xAB0927,0xAB0F00,0xAB1127,
    0xAB1700,0xAB2027,0xAB2700,0xAB2827,0xAB2F00,0xAB3048,0xAB5B19,0xAB5C48,
    0xAB652C,0xAB6648,0xAB6A19,0xAB6C00,0xAB7017,0xABC058,0xABEE00,0xABF058,
    0xABFA00,0xAC0031,0xD7A400,0xD7B031,0xD7C700,0xD7CB31,0xD7FC00,0xF90030,
    0xFA6E00,0xFA7030,0xFADA00,0xFB0048,0xFB0700,0xFB1305,0xFB1800,0xFB1D35,
    0xFB3700,0xFB3835,0xFB3D00,0xFB3E35,0xFB3F00,0xFB4035,0xFB4200,0xFB4335,
    0xFB4500,0xFB4635,0xFB5004,0xFBC300,0xFBD304,0xFD3E19,0xFD4004,0xFD9000,
    0xFD9204,0xFDC800,0xFDCF04,0xFDD000,0xFDF004,0xFE0038,0xFE1019,0xFE1A00,
    0xFE2038,0xFE2E1E,0xFE3019,0xFE5300,0xFE5419,0xFE6700,0xFE6819,0xFE6C00,
    0xFE7004,0xFE7500,0xFE7604,0xFEFD00,0xFEFF19,0xFF0000,0xFF0119,0xFF2148,
    0xFF3B19,0xFF4148,0xFF5B19,0xFF663E,0xFF7019,0xFF713E,0xFF9E19,0xFFA031,
    0xFFBF00,0xFFC231,0xFFC800,0xFFCA31,0xFFD000,0xFFD231,0xFFD800,0xFFDA31,
    0xFFDD00,0xFFE019,0xFFE700,0xFFE819,0xFFEF00,0xFFF919,0xFFFE00,0x100004C,
    0x1000C00,0x1000D4C,0x1002700,0x100284C,0x1003B00,0x1003C4C,0x1003E00,0x1003F4C,
    0x1004E00,0x100504C,0x1005E00,0x100804C,0x100FB00,0x1010019,0x1010300,0x1010719,
    0x1013400,0x1013719,0x101402C,0x1018F00,0x1019019,0x1019D00,0x101A02C,0x101A100,
    0x101D019,0x101FD38,0x101FE00,0x102804E,0x1029D00,0x102A013,0x102D100,0x102E038,
    0x102E119,0x102FC00,0x103006D,0x1032400,0x1032D6D,0x103302A,0x1034B00,0x103506F,
    0x1037B00,0x103809D,0x1039E00,0x1039F9D,0x103A070,0x103C400,0x103C870,0x103D600,
    0x104001F,0x1045083,0x1048077,0x1049E00,0x104A077,0x104AA00,0x104B076,0x104D400,
    0x104D876,0x104FC00,0x1050025,0x1052800,0x1053014,0x1056400,0x1056F14,0x105709F,
    0x1057B00,0x1057C9F,0x1058B00,0x1058C9F,0x1059300,0x105949F,0x1059600,0x105979F,
    0x105A200,0x105A39F,0x105B200,0x105B39F,0x105BA00,0x105BB9F,0x105BD00,0x106004B,
    0x1073700,0x107404B,0x1075600,0x107604B,0x1076800,0x1078048,0x1078600,0x1078748,
    0x107B100,0x107B248,0x107BB00,0x108001C,0x1080600,0x108081C,0x1080900,0x1080A1C,
    0x1083600,0x108371C,0x1083900,0x1083C1C,0x1083D00,0x1083F1C,0x1084037,0x1085600,
    0x1085737,0x1086079,0x1088062,0x1089F00,0x108A762,0x108B000,0x108E034,0x108F300,
    0x108F434,0x108F600,0x108FB34,0x109007C,0x1091C00,0x1091F7C,0x109204F,0x1093A00,
    0x1093F4F,0x1094000,0x109805B,0x109A05A,0x109B800,0x109BC5A,0x109D000,0x109D25A,
    0x10A0042,0x10A0400,0x10A0542,0x10A0700,0x10A0C42,0x10A1400,0x10A1542,0x10A1800,
    0x10A1942,0x10A3600,0x10A3842,0x10A3B00,0x10A3F42,0x10A4900,0x10A5042,0x10A5900,
    0x10A6072,0x10A806E,0x10AA000,0x10AC054,0x10AE700,0x10AEB54,0x10AF700,0x10B0006,
    0x10B3600,0x10B3906,0x10B403A,0x10B5600,0x10B583A,0x10B6039,0x10B7300,0x10B7839,
    0x10B807D,0x10B9200,0x10B997D,0x10B9D00,0x10BA97D,0x10BB000,0x10C0073,0x10C4900,
    0x10C806C,0x10CB300,0x10CC06C,0x10CF300,0x10CFA6C,0x10D0032,0x10D2800,0x10D3032,
    0x10D3A00,0x10E6004,0x10E7F00,0x10E80A2,0x10EAA00,0x10EABA2,0x10EAE00,0x10EB0A2,
    0x10EB200,0x10EFD04,0x10F0071,0x10F2800,0x10F3087,0x10F5A00,0x10F7074,0x10F8A00,
    0x10FB018,0x10FCC00,0x10FE026,0x10FF700,0x110000E,0x1104E00,0x110520E,0x1107600,
    0x1107F0E,0x110803C,0x110C300,0x110CD3C,0x110CE00,0x110D088,0x110E900,0x110F088,
    0x110FA00,0x1110015,0x1113500,0x1113615,0x1114800,0x1115050,0x1117700,0x1118082,
    0x111E000,0x111E186,0x111F500,0x1120045,0x1121200,0x1121345,0x1124200,0x1128060,
    0x1128700,0x1128860,0x1128900,0x1128A60,0x1128E00,0x1128F60,0x1129E00,0x1129F60,
    0x112AA00,0x112B046,0x112EB00,0x112F046,0x112FA00,0x113002B,0x1130400,0x113052B,
    0x1130D00,0x1130F2B,0x1131100,0x113132B,0x1132900,0x1132A2B,0x1133100,0x113322B,
    0x1133400,0x113352B,0x1133A00,0x1133B38,0x1133C2B,0x1134500,0x113472B,0x1134900,
    0x1134B2B,0x1134E00,0x113502B,0x1135100,0x113572B,0x1135800,0x1135D2B,0x1136400,
    0x113662B,0x1136D00,0x113702B,0x1137500,0x1140066,0x1145C00,0x1145D66,0x1146200,
    0x114809B,0x114C800,0x114D09B,0x114DA00,0x1158084,0x115B600,0x115B884,0x115DE00,
    0x116005D,0x1164500,0x116505D,0x1165A00,0x116605E,0x1166D00,0x1168092,0x116BA00,
    0x116C092,0x116CA00,0x1170002,0x1171B00,0x1171D02,0x1172C00,0x1173002,0x1174700,
    0x1180022,0x1183C00,0x118A0A1,0x118F300,0x118FFA1,0x1190021,0x1190700,0x1190921,
    0x1190A00,0x1190C21,0x1191400,0x1191521,0x1191700,0x1191821,0x1193600,0x1193721,
    0x1193900,0x1193B21,0x1194700,0x1195021,0x1195A00,0x119A064,0x119A800,0x119AA64,
    0x119D800,0x119DA64,0x119E500,0x11A00A4,0x11A4800,0x11A5089,0x11AA300,0x11AB012,
    0x11AC07A,0x11AF900,0x11B0020,0x11B0A00,0x11C000C,0x11C0900,0x11C0A0C,0x11C3700,
    0x11C380C,0x11C4600,0x11C500C,0x11C6D00,0x11C7055,0x11C9000,0x11C9255,0x11CA800,
    0x11CA955,0x11CB700,0x11D0056,0x11D0700,0x11D0856,0x11D0A00,0x11D0B56,0x11D3700,
    0x11D3A56,0x11D3B00,0x11D3C56,0x11D3E00,0x11D3F56,0x11D4800,0x11D5056,0x11D5A00,
    0x11D602E,0x11D6600,0x11D672E,0x11D6900,0x11D6A2E,0x11D8F00,0x11D902E,0x11D9200,
    0x11D932E,0x11D9900,0x11DA02E,0x11DAA00,0x11EE051,0x11EF900,0x11F0040,0x11F1100,
    0x11F1240,0x11F3B00,0x11F3E40,0x11F5A00,0x11FB04D,0x11FB100,0x11FC093,0x11FF200,
    0x11FFF93,0x120001B,0x1239A00,0x124001B,0x1246F00,0x124701B,0x1247500,0x124801B,
    0x1254400,0x12F901D,0x12FF300,0x1300024,0x1345600,0x1440003,0x1464700,0x1680008,
    0x16A3900,0x16A405F,0x16A5F00,0x16A605F,0x16A6A00,0x16A6E5F,0x16A7094,0x16ABF00,
    0x16AC094,0x16ACA00,0x16AD009,0x16AEE00,0x16AF009,0x16AF600,0x16B0078,0x16B4600,
    0x16B5078,0x16B5A00,0x16B5B78,0x16B6200,0x16B6378,0x16B7800,0x16B7D78,0x16B9000,
    0x16E4057,0x16E9B00,0x16F005C,0x16F4B00,0x16F4F5C,0x16F8800,0x16F8F5C,0x16FA000,
    0x16FE095,0x16FE168,0x16FE230,0x16FE443,0x16FE500,0x16FF030,0x16FF200,0x1700095,
    0x187F800,0x1880095,0x18B0043,0x18CD600,0x18D0095,0x18D0900,0x1AFF03E,0x1AFF400,
    0x1AFF53E,0x1AFFC00,0x1AFFD3E,0x1AFFF00,0x1B0003E,0x1B00136,0x1B1203E,0x1B12300,
    0x1B13236,0x1B13300,0x1B15036,0x1B15300,0x1B1553E,0x1B15600,0x1B1643E,0x1B16800,
    0x1B17068,0x1B2FC00,0x1BC0023,0x1BC6B00,0x1BC7023,0x1BC7D00,0x1BC8023,0x1BC8900,
    0x1BC9023,0x1BC9A00,0x1BC9C23,0x1BCA019,0x1BCA400,0x1CF0038,0x1CF2E00,0x1CF3038,
    0x1CF4700,0x1CF5019,0x1CFC400,0x1D00019,0x1D0F600,0x1D10019,0x1D12700,0x1D12919,
    0x1D16738,0x1D16A19,0x1D17B38,0x1D18319,0x1D18538,0x1D18C19,0x1D1AA38,0x1D1AE19,
    0x1D1EB00,0x1D2002C,0x1D24600,0x1D2C019,0x1D2D400,0x1D2E019,0x1D2F400,0x1D30019,
    0x1D35700,0x1D36019,0x1D37900,0x1D40019,0x1D45500,0x1D45619,0x1D49D00,0x1D49E19,
    0x1D4A000,0x1D4A219,0x1D4A300,0x1D4A519,0x1D4A700,0x1D4A919,0x1D4AD00,0x1D4AE19,
    0x1D4BA00,0x1D4BB19,0x1D4BC00,0x1D4BD19,0x1D4C400,0x1D4C519,0x1D50600,0x1D50719,
    0x1D50B00,0x1D50D19,0x1D51500,0x1D51619,0x1D51D00,0x1D51E19,0x1D53A00,0x1D53B19,
    0x1D53F00,0x1D54019,0x1D54500,0x1D54619,0x1D54700,0x1D54A19,0x1D55100,0x1D55219,
    0x1D6A600,0x1D6A819,0x1D7CC00,0x1D7CE19,0x1D80085,0x1DA8C00,0x1DA9B85,0x1DAA000,
    0x1DAA185,0x1DAB000,0x1DF0048,0x1DF1F00,0x1DF2548,0x1DF2B00,0x1E00029,0x1E00700,
    0x1E00829,0x1E01900,0x1E01B29,0x1E02200,0x1E02329,0x1E02500,0x1E02629,0x1E02B00,
    0x1E0301E,0x1E06E00,0x1E08F1E,0x1E09000,0x1E10069,0x1E12D00,0x1E13069,0x1E13E00,
    0x1E14069,0x1E14A00,0x1E14E69,0x1E15000,0x1E2909C,0x1E2AF00,0x1E2C0A0,0x1E2FA00,
    0x1E2FFA0,0x1E30000,0x1E4D063,0x1E4FA00,0x1E7E027,0x1E7E700,0x1E7E827,0x1E7EC00,
    0x1E7ED27,0x1E7EF00,0x1E7F027,0x1E7FF00,0x1E80059,0x1E8C500,0x1E8C759,0x1E8D700,
    0x1E90001,0x1E94C00,0x1E95001,0x1E95A00,0x1E95E01,0x1E96000,0x1EC7119,0x1ECB500,
    0x1ED0119,0x1ED3E00,0x1EE0004,0x1EE0400,0x1EE0504,0x1EE2000,0x1EE2104,0x1EE2300,
    0x1EE2404,0x1EE2500,0x1EE2704,0x1EE2800,0x1EE2904,0x1EE3300,0x1EE3404,0x1EE3800,
    0x1EE3904,0x1EE3A00,0x1EE3B04,0x1EE3C00,0x1EE4204,0x1EE4300,0x1EE4704,0x1EE4800,
    0x1EE4904,0x1EE4A00,0x1EE4B04,0x1EE4C00,0x1EE4D04,0x1EE5000,0x1EE5104,0x1EE5300,
    0x1EE5404,0x1EE5500,0x1EE5704,0x1EE5800,0x1EE5904,0x1EE5A00,0x1EE5B04,0x1EE5C00,
    0x1EE5D04,0x1EE5E00,0x1EE5F04,0x1EE6000,0x1EE6104,0x1EE6300,0x1EE6404,0x1EE6500,
    0x1EE6704,0x1EE6B00,0x1EE6C04,0x1EE7300,0x1EE7404,0x1EE7800,0x1EE7904,0x1EE7D00,
    0x1EE7E04,0x1EE7F00,0x1EE8004,0x1EE8A00,0x1EE8B04,0x1EE9C00,0x1EEA104,0x1EEA400,
    0x1EEA504,0x1EEAA00,0x1EEAB04,0x1EEBC00,0x1EEF004,0x1EEF200,0x1F00019,0x1F02C00,
    0x1F03019,0x1F09400,0x1F0A019,0x1F0AF00,0x1F0B119,0x1F0C000,0x1F0C119,0x1F0D000,
    0x1F0D119,0x1F0F600,0x1F10019,0x1F1AE00,0x1F1E619,0x1F20036,0x1F20119,0x1F20300,
    0x1F21019,0x1F23C00,0x1F24019,0x1F24900,0x1F25019,0x1F25200,0x1F26019,0x1F26600,
    0x1F30019,0x1F6D800,0x1F6DC19,0x1F6ED00,0x1F6F019,0x1F6FD00,0x1F70019,0x1F77700,
    0x1F77B19,0x1F7DA00,0x1F7E019,0x1F7EC00,0x1F7F019,0x1F7F100,0x1F80019,0x1F80C00,
    0x1F81019,0x1F84800,0x1F85019,0x1F85A00,0x1F86019,0x1F88800,0x1F89019,0x1F8AE00,
    0x1F8B019,0x1F8B200,0x1F90019,0x1FA5400,0x1FA6019,0x1FA6E00,0x1FA7019,0x1FA7D00,
    0x1FA8019,0x1FA8900,0x1FA9019,0x1FABE00,0x1FABF19,0x1FAC600,0x1FACE19,0x1FADC00,
    0x1FAE019,0x1FAE900,0x1FAF019,0x1FAF900,0x1FB0019,0x1FB9300,0x1FB9419,0x1FBCB00,
    0x1FBF019,0x1FBFA00,0x2000030,0x2A6E000,0x2A70030,0x2B73A00,0x2B74030,0x2B81E00,
    0x2B82030,0x2CEA200,0x2CEB030,0x2EBE100,0x2EBF030,0x2EE5E00,0x2F80030,0x2FA1E00,
    0x3000030,0x3134B00,0x3135030,0x323B000,0xE000119,0xE000200,0xE002019,0xE008000,
    0xE010038,0xE01F000,
};
const int g_scriptRunsCount = (int)(sizeof(g_scriptRuns) / sizeof(g_scriptRuns[0]));

// Script names (full and short ISO 15924 names) and their ids.
const ScriptName g_scriptNames[] = {
    {"Zzzz",0},
    {"Unknown",0},
    {"Adlm",1},
    {"Adlam",1},
    {"Ahom",2},
    {"Ahom",2},
    {"Hluw",3},
    {"Anatolian_Hieroglyphs",3},
    {"Arab",4},
    {"Arabic",4},
    {"Armn",5},
    {"Armenian",5},
    {"Avst",6},
    {"Avestan",6},
    {"Bali",7},
    {"Balinese",7},
    {"Bamu",8},
    {"Bamum",8},
    {"Bass",9},
    {"Bassa_Vah",9},
    {"Batk",10},
    {"Batak",10},
    {"Beng",11},
    {"Bengali",11},
    {"Bhks",12},
    {"Bhaiksuki",12},
    {"Bopo",13},
    {"Bopomofo",13},
    {"Brah",14},
    {"Brahmi",14},
    {"Brai",15},
    {"Braille",15},
    {"Bugi",16},
    {"Buginese",16},
    {"Buhd",17},
    {"Buhid",17},
    {"Cans",18},
    {"Canadian_Aboriginal",18},
    {"Cari",19},
    {"Carian",19},
    {"Aghb",20},
    {"Caucasian_Albanian",20},
    {"Cakm",21},
    {"Chakma",21},
    {"Cham",22},
    {"Cham",22},
    {"Cher",23},
    {"Cherokee",23},
    {"Chrs",24},
    {"Chorasmian",24},
    {"Zyyy",25},
    {"Common",25},
    {"Copt",26},
    {"Coptic",26},
    {"Qaac",26},
    {"Xsux",27},
    {"Cuneiform",27},
    {"Cprt",28},
    {"Cypriot",28},
    {"Cpmn",29},
    {"Cypro_Minoan",29},
    {"Cyrl",30},
    {"Cyrillic",30},
    {"Dsrt",31},
    {"Deseret",31},
    {"Deva",32},
    {"Devanagari",32},
    {"Diak",33},
    {"Dives_Akuru",33},
    {"Dogr",34},
    {"Dogra",34},
    {"Dupl",35},
    {"Duployan",35},
    {"Egyp",36},
    {"Egyptian_Hieroglyphs",36},
    {"Elba",37},
    {"Elbasan",37},
    {"Elym",38},
    {"Elymaic",38},
    {"Ethi",39},
    {"Ethiopic",39},
    {"Geor",40},
    {"Georgian",40},
    {"Glag",41},
    {"Glagolitic",41},
    {"Goth",42},
    {"Gothic",42},
    {"Gran",43},
    {"Grantha",43},
    {"Grek",44},
    {"Greek",44},
    {"Gujr",45},
    {"Gujarati",45},
    {"Gong",46},
    {"Gunjala_Gondi",46},
    {"Guru",47},
    {"Gurmukhi",47},
    {"Hani",48},
    {"Han",48},
    {"Hang",49},
    {"Hangul",49},
    {"Rohg",50},
    {"Hanifi_Rohingya",50},
    {"Hano",51},
    {"Hanunoo",51},
    {"Hatr",52},
    {"Hatran",52},
    {"Hebr",53},
    {"Hebrew",53},
    {"Hira",54},
    {"Hiragana",54},
    {"Armi",55},
    {"Imperial_Aramaic",55},
    {"Zinh",56},
    {"Inherited",56},
    {"Qaai",56},
    {"Phli",57},
    {"Inscriptional_Pahlavi",57},
    {"Prti",58},
    {"Inscriptional_Parthian",58},
    {"Java",59},
    {"Javanese",59},
    {"Kthi",60},
    {"Kaithi",60},
    {"Knda",61},
    {"Kannada",61},
    {"Kana",62},
    {"Katakana",62},
    {"Hrkt",63},
    {"Katakana_Or_Hiragana",63},
    {"Kawi",64},
    {"Kawi",64},
    {"Kali",65},
    {"Kayah_Li",65},
    {"Khar",66},
    {"Kharoshthi",66},
    {"Kits",67},
    {"Khitan_Small_Script",67},
    {"Khmr",68},
    {"Khmer",68},
    {"Khoj",69},
    {"Khojki",69},
    {"Sind",70},
    {"Khudawadi",70},
    {"Laoo",71},
    {"Lao",71},
    {"Latn",72},
    {"Latin",72},
    {"Lepc",73},
    {"Lepcha",73},
    {"Limb",74},
    {"Limbu",74},
    {"Lina",75},
    {"Linear_A",75},
    {"Linb",76},
    {"Linear_B",76},
    {"Lisu",77},
    {"Lisu",77},
    {"Lyci",78},
    {"Lycian",78},
    {"Lydi",79},
    {"Lydian",79},
    {"Mahj",80},
    {"Mahajani",80},
    {"Maka",81},
    {"Makasar",81},
    {"Mlym",82},
    {"Malayalam",82},
    {"Mand",83},
    {"Mandaic",83},
    {"Mani",84},
    {"Manichaean",84},
    {"Marc",85},
    {"Marchen",85},
    {"Gonm",86},
    {"Masaram_Gondi",86},
    {"Medf",87},
    {"Medefaidrin",87},
    {"Mtei",88},
    {"Meetei_Mayek",88},
    {"Mend",89},
    {"Mende_Kikakui",89},
    {"Merc",90},
    {"Meroitic_Cursive",90},
    {"Mero",91},
    {"Meroitic_Hieroglyphs",91},
    {"Plrd",92},
    {"Miao",92},
    {"Modi",93},
    {"Modi",93},
    {"Mong",94},
    {"Mongolian",94},
    {"Mroo",95},
    {"Mro",95},
    {"Mult",96},
    {"Multani",96},
    {"Mymr",97},
    {"Myanmar",97},
    {"Nbat",98},
    {"Nabataean",98},
    {"Nagm",99},
    {"Nag_Mundari",99},
    {"Nand",100},
    {"Nandinagari",100},
    {"Talu",101},
    {"New_Tai_Lue",101},
    {"Newa",102},
    {"Newa",102},
    {"Nkoo",103},
    {"Nko",103},
    {"Nshu",104},
    {"Nushu",104},
    {"Hmnp",105},
    {"Nyiakeng_Puachue_Hmong",105},
    {"Ogam",106},
    {"Ogham",106},
    {"Olck",107},
    {"Ol_Chiki",107},
    {"Hung",108},
    {"Old_Hungarian",108},
    {"Ital",109},
    {"Old_Italic",109},
    {"Narb",110},
    {"Old_North_Arabian",110},
    {"Perm",111},
    {"Old_Permic",111},
    {"Xpeo",112},
    {"Old_Persian",112},
    {"Sogo",113},
    {"Old_Sogdian",113},
    {"Sarb",114},
    {"Old_South_Arabian",114},
    {"Orkh",115},
    {"Old_Turkic",115},
    {"Ougr",116},
    {"Old_Uyghur",116},
    {"Orya",117},
    {"Oriya",117},
    {"Osge",118},
    {"Osage",118},
    {"Osma",119},
    {"Osmanya",119},
    {"Hmng",120},
    {"Pahawh_Hmong",120},
    {"Palm",121},
    {"Palmyrene",121},
    {"Pauc",122},
    {"Pau_Cin_Hau",122},
    {"Phag",123},
    {"Phags_Pa",123},
    {"Phnx",124},
    {"Phoenician",124},
    {"Phlp",125},
    {"Psalter_Pahlavi",125},
    {"Rjng",126},
    {"Rejang",126},
    {"Runr",127},
    {"Runic",127},
    {"Samr",128},
    {"Samaritan",128},
    {"Saur",129},
    {"Saurashtra",129},
    {"Shrd",130},
    {"Sharada",130},
    {"Shaw",131},
    {"Shavian",131},
    {"Sidd",132},
    {"Siddham",132},
    {"Sgnw",133},
    {"SignWriting",133},
    {"Sinh",134},
    {"Sinhala",134},
    {"Sogd",135},
    {"Sogdian",135},
    {"Sora",136},
    {"Sora_Sompeng",136},
    {"Soyo",137},
    {"Soyombo",137},
    {"Sund",138},
    {"Sundanese",138},
    {"Sylo",139},
    {"Syloti_Nagri",139},
    {"Syrc",140},
    {"Syriac",140},
    {"Tglg",141},
    {"Tagalog",141},
    {"Tagb",142},
    {"Tagbanwa",142},
    {"Tale",143},
    {"Tai_Le",143},
    {"Lana",144},
    {"Tai_Tham",144},
    {"Tavt",145},
    {"Tai_Viet",145},
    {"Takr",146},
    {"Takri",146},
    {"Taml",147},
    {"Tamil",147},
    {"Tnsa",148},
    {"Tangsa",148},
    {"Tang",149},
    {"Tangut",149},
    {"Telu",150},
    {"Telugu",150},
    {"Thaa",151},
    {"Thaana",151},
    {"Thai",152},
    {"Thai",152},
    {"Tibt",153},
    {"Tibetan",153},
    {"Tfng",154},
    {"Tifinagh",154},
    {"Tirh",155},
    {"Tirhuta",155},
    {"Toto",156},
    {"Toto",156},
    {"Ugar",157},
    {"Ugaritic",157},
    {"Vaii",158},
    {"Vai",158},
    {"Vith",159},
    {"Vithkuqi",159},
    {"Wcho",160},
    {"Wancho",160},
    {"Wara",161},
    {"Warang_Citi",161},
    {"Yezi",162},
    {"Yezidi",162},
    {"Yiii",163},
    {"Yi",163},
    {"Zanb",164},
    {"Zanabazar_Square",164},
};
const int g_scriptNamesCount = (int)(sizeof(g_scriptNames) / sizeof(g_scriptNames[0]));

// Script_Extensions where it differs from Script: ranges with an offset into g_scxData
// (script ids, terminated by 255).
const ScxRange g_scxRanges[] = {
    {0x342,0x342,0},{0x345,0x345,0},{0x363,0x36F,2},{0x483,0x483,4},{0x484,0x484,7},
    {0x485,0x486,10},{0x487,0x487,7},{0x60C,0x60C,13},{0x61B,0x61B,13},{0x61C,0x61C,20},
    {0x61F,0x61F,24},{0x640,0x640,32},{0x64B,0x655,42},{0x660,0x669,45},{0x670,0x670,42},
    {0x6D4,0x6D4,49},{0x951,0x951,52},{0x952,0x952,66},{0x964,0x964,79},{0x965,0x965,100},
    {0x966,0x96F,122},{0x9E6,0x9EF,127},{0xA66,0xA6F,131},{0xAE6,0xAEF,134},{0xBE6,0xBEF,137},
    {0xBF0,0xBF2,137},{0xBF3,0xBF3,137},{0xCE6,0xCEF,140},{0x1040,0x1049,143},{0x10FB,0x10FB,147},
    {0x1735,0x1736,150},{0x1802,0x1803,155},{0x1805,0x1805,155},{0x1CD0,0x1CD0,158},{0x1CD1,0x1CD1,163},
    {0x1CD2,0x1CD2,158},{0x1CD3,0x1CD3,165},{0x1CD4,0x1CD4,163},{0x1CD5,0x1CD6,168},{0x1CD7,0x1CD7,171},
    {0x1CD8,0x1CD8,168},{0x1CD9,0x1CD9,171},{0x1CDA,0x1CDA,174},{0x1CDB,0x1CDB,163},{0x1CDC,0x1CDD,171},
    {0x1CDE,0x1CDF,163},{0x1CE0,0x1CE0,171},{0x1CE1,0x1CE1,168},{0x1CE2,0x1CE8,163},{0x1CE9,0x1CE9,181},
    {0x1CEA,0x1CEA,168},{0x1CEB,0x1CEC,163},{0x1CED,0x1CED,168},{0x1CEE,0x1CF1,163},{0x1CF2,0x1CF2,184},
    {0x1CF3,0x1CF3,165},{0x1CF4,0x1CF4,195},{0x1CF5,0x1CF6,168},{0x1CF7,0x1CF7,199},{0x1CF8,0x1CF9,165},
    {0x1CFA,0x1CFA,201},{0x1DC0,0x1DC1,0},{0x1DF8,0x1DF8,203},{0x1DFA,0x1DFA,206},{0x202F,0x202F,208},
    {0x20F0,0x20F0,211},{0x2E43,0x2E43,7},{0x3001,0x3002,215},{0x3003,0x3003,222},{0x3006,0x3006,228},
    {0x3008,0x3008,215},{0x3009,0x3009,215},{0x300A,0x300A,215},{0x300B,0x300B,215},{0x300C,0x300C,215},
    {0x300D,0x300D,215},{0x300E,0x300E,215},{0x300F,0x300F,215},{0x3010,0x3010,215},{0x3011,0x3011,215},
    {0x3013,0x3013,222},{0x3014,0x3014,215},{0x3015,0x3015,215},{0x3016,0x3016,215},{0x3017,0x3017,215},
    {0x3018,0x3018,215},{0x3019,0x3019,215},{0x301A,0x301A,215},{0x301B,0x301B,215},{0x301C,0x301C,222},
    {0x301D,0x301D,222},{0x301E,0x301F,222},{0x302A,0x302D,230},{0x3030,0x3030,222},{0x3031,0x3035,233},
    {0x3037,0x3037,222},{0x303C,0x303C,236},{0x303D,0x303D,236},{0x303E,0x303F,228},{0x3099,0x309A,233},
    {0x309B,0x309C,233},{0x30A0,0x30A0,233},{0x30FB,0x30FB,215},{0x30FC,0x30FC,233},{0x3190,0x3191,228},
    {0x3192,0x3195,228},{0x3196,0x319F,228},{0x31C0,0x31E3,228},{0x3220,0x3229,228},{0x322A,0x3247,228},
    {0x3280,0x3289,228},{0x328A,0x32B0,228},{0x32C0,0x32CB,228},{0x32FF,0x32FF,228},{0x3358,0x3370,228},
    {0x337B,0x337F,228},{0x33E0,0x33FE,228},{0xA66F,0xA66F,7},{0xA700,0xA707,240},{0xA830,0xA832,243},
    {0xA833,0xA835,259},{0xA836,0xA837,274},{0xA838,0xA838,286},{0xA839,0xA839,274},{0xA8F1,0xA8F1,168},
    {0xA8F3,0xA8F3,299},{0xA92E,0xA92E,302},{0xA9CF,0xA9CF,306},{0xFD3E,0xFD3E,309},{0xFD3F,0xFD3F,309},
    {0xFDF2,0xFDF2,312},{0xFDFD,0xFDFD,312},{0xFE45,0xFE46,222},{0xFF61,0xFF61,215},{0xFF62,0xFF62,215},
    {0xFF63,0xFF63,215},{0xFF64,0xFF65,215},{0xFF70,0xFF70,233},{0xFF9E,0xFF9F,233},{0x10100,0x10101,315},
    {0x10102,0x10102,319},{0x10107,0x10133,322},{0x10137,0x1013F,319},{0x102E0,0x102E0,326},{0x102E1,0x102FB,326},
    {0x10AF2,0x10AF2,329},{0x11301,0x11301,137},{0x11303,0x11303,137},{0x1133B,0x1133C,137},{0x11FD0,0x11FD1,137},
    {0x11FD3,0x11FD3,137},{0x1BCA0,0x1BCA3,332},{0x1D360,0x1D371,228},{0x1F250,0x1F251,228},
};
const int g_scxRangesCount = (int)(sizeof(g_scxRanges) / sizeof(g_scxRanges[0]));
const unsigned char g_scxData[] = {
    44,255,72,255,30,111,255,30,41,255,30,72,255,4,50,103,
    140,151,162,255,4,140,151,255,1,4,50,103,140,151,162,255,
    1,4,50,83,84,116,125,135,140,255,4,140,255,4,151,162,
    255,4,50,255,11,32,43,45,47,61,72,82,117,130,147,150,
    155,255,11,32,43,45,47,61,72,82,117,147,150,155,255,11,
    32,34,43,45,46,47,61,70,80,82,86,100,117,134,139,146,
    147,150,155,255,11,32,34,43,45,46,47,61,70,74,80,82,
    86,100,117,134,139,146,147,150,155,255,32,34,60,80,255,11,
    21,139,255,47,96,255,45,69,255,43,147,255,61,100,255,21,
    97,143,255,40,72,255,17,51,141,142,255,94,123,255,11,32,
    43,61,255,32,255,32,43,255,11,32,255,32,130,255,32,61,
    82,117,147,150,255,32,100,255,11,32,43,61,82,100,117,134,
    150,155,255,32,43,61,255,11,255,100,255,30,140,255,140,255,
    72,94,255,32,43,72,255,13,48,49,54,62,163,255,13,48,
    49,54,62,255,48,255,13,48,255,54,62,255,48,54,62,255,
    48,72,255,32,34,45,47,60,61,69,70,80,82,93,100,130,
    146,155,255,32,34,45,47,60,61,69,70,80,93,100,130,146,
    155,255,32,34,45,47,60,69,70,80,93,146,155,255,32,34,
    45,47,60,69,70,80,93,130,146,155,255,32,147,255,65,72,
    97,255,16,59,255,4,103,255,4,151,255,28,29,76,255,28,
    76,255,28,75,76,255,4,26,255,84,116,255,35,255,
};

// Grapheme_Cluster_Break: (first code point << 4) | value; values: 0=Other, 1=CR, 2=LF, 3=Control, 4=Extend, 5=ZWJ, 6=Regional_Indicator, 7=Prepend, 8=SpacingMark, 9=L, 10=V, 11=T, 12=LV, 13=LVT
const unsigned int g_gcbRuns[] = {
    0x3,0xA2,0xB3,0xD1,0xE3,0x200,0x7F3,0xA00,
    0xAD3,0xAE0,0x3004,0x3700,0x4834,0x48A0,0x5914,0x5BE0,
    0x5BF4,0x5C00,0x5C14,0x5C30,0x5C44,0x5C60,0x5C74,0x5C80,
    0x6007,0x6060,0x6104,0x61B0,0x61C3,0x61D0,0x64B4,0x6600,
    0x6704,0x6710,0x6D64,0x6DD7,0x6DE0,0x6DF4,0x6E50,0x6E74,
    0x6E90,0x6EA4,0x6EE0,0x70F7,0x7100,0x7114,0x7120,0x7304,
    0x74B0,0x7A64,0x7B10,0x7EB4,0x7F40,0x7FD4,0x7FE0,0x8164,
    0x81A0,0x81B4,0x8240,0x8254,0x8280,0x8294,0x82E0,0x8594,
    0x85C0,0x8907,0x8920,0x8984,0x8A00,0x8CA4,0x8E27,0x8E34,
    0x9038,0x9040,0x93A4,0x93B8,0x93C4,0x93D0,0x93E8,0x9414,
    0x9498,0x94D4,0x94E8,0x9500,0x9514,0x9580,0x9624,0x9640,
    0x9814,0x9828,0x9840,0x9BC4,0x9BD0,0x9BE4,0x9BF8,0x9C14,
    0x9C50,0x9C78,0x9C90,0x9CB8,0x9CD4,0x9CE0,0x9D74,0x9D80,
    0x9E24,0x9E40,0x9FE4,0x9FF0,0xA014,0xA038,0xA040,0xA3C4,
    0xA3D0,0xA3E8,0xA414,0xA430,0xA474,0xA490,0xA4B4,0xA4E0,
    0xA514,0xA520,0xA704,0xA720,0xA754,0xA760,0xA814,0xA838,
    0xA840,0xABC4,0xABD0,0xABE8,0xAC14,0xAC60,0xAC74,0xAC98,
    0xACA0,0xACB8,0xACD4,0xACE0,0xAE24,0xAE40,0xAFA4,0xB000,
    0xB014,0xB028,0xB040,0xB3C4,0xB3D0,0xB3E4,0xB408,0xB414,
    0xB450,0xB478,0xB490,0xB4B8,0xB4D4,0xB4E0,0xB554,0xB580,
    0xB624,0xB640,0xB824,0xB830,0xBBE4,0xBBF8,0xBC04,0xBC18,
    0xBC30,0xBC68,0xBC90,0xBCA8,0xBCD4,0xBCE0,0xBD74,0xBD80,
    0xC004,0xC018,0xC044,0xC050,0xC3C4,0xC3D0,0xC3E4,0xC418,
    0xC450,0xC464,0xC490,0xC4A4,0xC4E0,0xC554,0xC570,0xC624,
    0xC640,0xC814,0xC828,0xC840,0xCBC4,0xCBD0,0xCBE8,0xCBF4,
    0xCC08,0xCC24,0xCC38,0xCC50,0xCC64,0xCC78,0xCC90,0xCCA8,
    0xCCC4,0xCCE0,0xCD54,0xCD70,0xCE24,0xCE40,0xCF38,0xCF40,
    0xD004,0xD028,0xD040,0xD3B4,0xD3D0,0xD3E4,0xD3F8,0xD414,
    0xD450,0xD468,0xD490,0xD4A8,0xD4D4,0xD4E7,0xD4F0,0xD574,
    0xD580,0xD624,0xD640,0xD814,0xD828,0xD840,0xDCA4,0xDCB0,
    0xDCF4,0xDD08,0xDD24,0xDD50,0xDD64,0xDD70,0xDD88,0xDDF4,
    0xDE00,0xDF28,0xDF40,0xE314,0xE320,0xE338,0xE344,0xE3B0,
    0xE474,0xE4F0,0xEB14,0xEB20,0xEB38,0xEB44,0xEBD0,0xEC84,
    0xECF0,0xF184,0xF1A0,0xF354,0xF360,0xF374,0xF380,0xF394,
    0xF3A0,0xF3E8,0xF400,0xF714,0xF7F8,0xF804,0xF850,0xF864,
    0xF880,0xF8D4,0xF980,0xF994,0xFBD0,0xFC64,0xFC70,0x102D4,
    0x10318,0x10324,0x10380,0x10394,0x103B8,0x103D4,0x103F0,0x10568,
    0x10584,0x105A0,0x105E4,0x10610,0x10714,0x10750,0x10824,0x10830,
    0x10848,0x10854,0x10870,0x108D4,0x108E0,0x109D4,0x109E0,0x11009,
    0x1160A,0x11A8B,0x12000,0x135D4,0x13600,0x17124,0x17158,0x17160,
    0x17324,0x17348,0x17350,0x17524,0x17540,0x17724,0x17740,0x17B44,
    0x17B68,0x17B74,0x17BE8,0x17C64,0x17C78,0x17C94,0x17D40,0x17DD4,
    0x17DE0,0x180B4,0x180E3,0x180F4,0x18100,0x18854,0x18870,0x18A94,
    0x18AA0,0x19204,0x19238,0x19274,0x19298,0x192C0,0x19308,0x19324,
    0x19338,0x19394,0x193C0,0x1A174,0x1A198,0x1A1B4,0x1A1C0,0x1A558,
    0x1A564,0x1A578,0x1A584,0x1A5F0,0x1A604,0x1A610,0x1A624,0x1A630,
    0x1A654,0x1A6D8,0x1A734,0x1A7D0,0x1A7F4,0x1A800,0x1AB04,0x1ACF0,
    0x1B004,0x1B048,0x1B050,0x1B344,0x1B3B8,0x1B3C4,0x1B3D8,0x1B424,
    0x1B438,0x1B450,0x1B6B4,0x1B740,0x1B804,0x1B828,0x1B830,0x1BA18,
    0x1BA24,0x1BA68,0x1BA84,0x1BAA8,0x1BAB4,0x1BAE0,0x1BE64,0x1BE78,
    0x1BE84,0x1BEA8,0x1BED4,0x1BEE8,0x1BEF4,0x1BF28,0x1BF40,0x1C248,
    0x1C2C4,0x1C348,0x1C364,0x1C380,0x1CD04,0x1CD30,0x1CD44,0x1CE18,
    0x1CE24,0x1CE90,0x1CED4,0x1CEE0,0x1CF44,0x1CF50,0x1CF78,0x1CF84,
    0x1CFA0,0x1DC04,0x1E000,0x200B3,0x200C4,0x200D5,0x200E3,0x20100,
    0x20283,0x202F0,0x20603,0x20700,0x20D04,0x20F10,0x2CEF4,0x2CF20,
    0x2D7F4,0x2D800,0x2DE04,0x2E000,0x302A4,0x30300,0x30994,0x309B0,
    0xA66F4,0xA6730,0xA6744,0xA67E0,0xA69E4,0xA6A00,0xA6F04,0xA6F20,
    0xA8024,0xA8030,0xA8064,0xA8070,0xA80B4,0xA80C0,0xA8238,0xA8254,
    0xA8278,0xA8280,0xA82C4,0xA82D0,0xA8808,0xA8820,0xA8B48,0xA8C44,
    0xA8C60,0xA8E04,0xA8F20,0xA8FF4,0xA9000,0xA9264,0xA92E0,0xA9474,
    0xA9528,0xA9540,0xA9609,0xA97D0,0xA9804,0xA9838,0xA9840,0xA9B34,
    0xA9B48,0xA9B64,0xA9BA8,0xA9BC4,0xA9BE8,0xA9C10,0xA9E54,0xA9E60,
    0xAA294,0xAA2F8,0xAA314,0xAA338,0xAA354,0xAA370,0xAA434,0xAA440,
    0xAA4C4,0xAA4D8,0xAA4E0,0xAA7C4,0xAA7D0,0xAAB04,0xAAB10,0xAAB24,
    0xAAB50,0xAAB74,0xAAB90,0xAABE4,0xAAC00,0xAAC14,0xAAC20,0xAAEB8,
    0xAAEC4,0xAAEE8,0xAAF00,0xAAF58,0xAAF64,0xAAF70,0xABE38,0xABE54,
    0xABE68,0xABE84,0xABE98,0xABEB0,0xABEC8,0xABED4,0xABEE0,0xAC00C,
    0xAC01D,0xAC1CC,0xAC1DD,0xAC38C,0xAC39D,0xAC54C,0xAC55D,0xAC70C,
    0xAC71D,0xAC8CC,0xAC8DD,0xACA8C,0xACA9D,0xACC4C,0xACC5D,0xACE0C,
    0xACE1D,0xACFCC,0xACFDD,0xAD18C,0xAD19D,0xAD34C,0xAD35D,0xAD50C,
    0xAD51D,0xAD6CC,0xAD6DD,0xAD88C,0xAD89D,0xADA4C,0xADA5D,0xADC0C,
    0xADC1D,0xADDCC,0xADDDD,0xADF8C,0xADF9D,0xAE14C,0xAE15D,0xAE30C,
    0xAE31D,0xAE4CC,0xAE4DD,0xAE68C,0xAE69D,0xAE84C,0xAE85D,0xAEA0C,
    0xAEA1D,0xAEBCC,0xAEBDD,0xAED8C,0xAED9D,0xAEF4C,0xAEF5D,0xAF10C,
    0xAF11D,0xAF2CC,0xAF2DD,0xAF48C,0xAF49D,0xAF64C,0xAF65D,0xAF80C,
    0xAF81D,0xAF9CC,0xAF9DD,0xAFB8C,0xAFB9D,0xAFD4C,0xAFD5D,0xAFF0C,
    0xAFF1D,0xB00CC,0xB00DD,0xB028C,0xB029D,0xB044C,0xB045D,0xB060C,
    0xB061D,0xB07CC,0xB07DD,0xB098C,0xB099D,0xB0B4C,0xB0B5D,0xB0D0C,
    0xB0D1D,0xB0ECC,0xB0EDD,0xB108C,0xB109D,0xB124C,0xB125D,0xB140C,
    0xB141D,0xB15CC,0xB15DD,0xB178C,0xB179D,0xB194C,0xB195D,0xB1B0C,
    0xB1B1D,0xB1CCC,0xB1CDD,0xB1E8C,0xB1E9D,0xB204C,0xB205D,0xB220C,
    0xB221D,0xB23CC,0xB23DD,0xB258C,0xB259D,0xB274C,0xB275D,0xB290C,
    0xB291D,0xB2ACC,0xB2ADD,0xB2C8C,0xB2C9D,0xB2E4C,0xB2E5D,0xB300C,
    0xB301D,0xB31CC,0xB31DD,0xB338C,0xB339D,0xB354C,0xB355D,0xB370C,
    0xB371D,0xB38CC,0xB38DD,0xB3A8C,0xB3A9D,0xB3C4C,0xB3C5D,0xB3E0C,
    0xB3E1D,0xB3FCC,0xB3FDD,0xB418C,0xB419D,0xB434C,0xB435D,0xB450C,
    0xB451D,0xB46CC,0xB46DD,0xB488C,0xB489D,0xB4A4C,0xB4A5D,0xB4C0C,
    0xB4C1D,0xB4DCC,0xB4DDD,0xB4F8C,0xB4F9D,0xB514C,0xB515D,0xB530C,
    0xB531D,0xB54CC,0xB54DD,0xB568C,0xB569D,0xB584C,0xB585D,0xB5A0C,
    0xB5A1D,0xB5BCC,0xB5BDD,0xB5D8C,0xB5D9D,0xB5F4C,0xB5F5D,0xB610C,
    0xB611D,0xB62CC,0xB62DD,0xB648C,0xB649D,0xB664C,0xB665D,0xB680C,
    0xB681D,0xB69CC,0xB69DD,0xB6B8C,0xB6B9D,0xB6D4C,0xB6D5D,0xB6F0C,
    0xB6F1D,0xB70CC,0xB70DD,0xB728C,0xB729D,0xB744C,0xB745D,0xB760C,
    0xB761D,0xB77CC,0xB77DD,0xB798C,0xB799D,0xB7B4C,0xB7B5D,0xB7D0C,
    0xB7D1D,0xB7ECC,0xB7EDD,0xB808C,0xB809D,0xB824C,0xB825D,0xB840C,
    0xB841D,0xB85CC,0xB85DD,0xB878C,0xB879D,0xB894C,0xB895D,0xB8B0C,
    0xB8B1D,0xB8CCC,0xB8CDD,0xB8E8C,0xB8E9D,0xB904C,0xB905D,0xB920C,
    0xB921D,0xB93CC,0xB93DD,0xB958C,0xB959D,0xB974C,0xB975D,0xB990C,
    0xB991D,0xB9ACC,0xB9ADD,0xB9C8C,0xB9C9D,0xB9E4C,0xB9E5D,0xBA00C,
    0xBA01D,0xBA1CC,0xBA1DD,0xBA38C,0xBA39D,0xBA54C,0xBA55D,0xBA70C,
    0xBA71D,0xBA8CC,0xBA8DD,0xBAA8C,0xBAA9D,0xBAC4C,0xBAC5D,0xBAE0C,
    0xBAE1D,0xBAFCC,0xBAFDD,0xBB18C,0xBB19D,0xBB34C,0xBB35D,0xBB50C,
    0xBB51D,0xBB6CC,0xBB6DD,0xBB88C,0xBB89D,0xBBA4C,0xBBA5D,0xBBC0C,
    0xBBC1D,0xBBDCC,0xBBDDD,0xBBF8C,0xBBF9D,0xBC14C,0xBC15D,0xBC30C,
    0xBC31D,0xBC4CC,0xBC4DD,0xBC68C,0xBC69D,0xBC84C,0xBC85D,0xBCA0C,
    0xBCA1D,0xBCBCC,0xBCBDD,0xBCD8C,0xBCD9D,0xBCF4C,0xBCF5D,0xBD10C,
    0xBD11D,0xBD2CC,0xBD2DD,0xBD48C,0xBD49D,0xBD64C,0xBD65D,0xBD80C,
    0xBD81D,0xBD9CC,0xBD9DD,0xBDB8C,0xBDB9D,0xBDD4C,0xBDD5D,0xBDF0C,
    0xBDF1D,0xBE0CC,0xBE0DD,0xBE28C,0xBE29D,0xBE44C,0xBE45D,0xBE60C,
    0xBE61D,0xBE7CC,0xBE7DD,0xBE98C,0xBE99D,0xBEB4C,0xBEB5D,0xBED0C,
    0xBED1D,0xBEECC,0xBEEDD,0xBF08C,0xBF09D,0xBF24C,0xBF25D,0xBF40C,
    0xBF41D,0xBF5CC,0xBF5DD,0xBF78C,0xBF79D,0xBF94C,0xBF95D,0xBFB0C,
    0xBFB1D,0xBFCCC,0xBFCDD,0xBFE8C,0xBFE9D,0xC004C,0xC005D,0xC020C,
    0xC021D,0xC03CC,0xC03DD,0xC058C,0xC059D,0xC074C,0xC075D,0xC090C,
    0xC091D,0xC0ACC,0xC0ADD,0xC0C8C,0xC0C9D,0xC0E4C,0xC0E5D,0xC100C,
    0xC101D,0xC11CC,0xC11DD,0xC138C,0xC139D,0xC154C,0xC155D,0xC170C,
    0xC171D,0xC18CC,0xC18DD,0xC1A8C,0xC1A9D,0xC1C4C,0xC1C5D,0xC1E0C,
    0xC1E1D,0xC1FCC,0xC1FDD,0xC218C,0xC219D,0xC234C,0xC235D,0xC250C,
    0xC251D,0xC26CC,0xC26DD,0xC288C,0xC289D,0xC2A4C,0xC2A5D,0xC2C0C,
    0xC2C1D,0xC2DCC,0xC2DDD,0xC2F8C,0xC2F9D,0xC314C,0xC315D,0xC330C,
    0xC331D,0xC34CC,0xC34DD,0xC368C,0xC369D,0xC384C,0xC385D,0xC3A0C,
    0xC3A1D,0xC3BCC,0xC3BDD,0xC3D8C,0xC3D9D,0xC3F4C,0xC3F5D,0xC410C,
    0xC411D,0xC42CC,0xC42DD,0xC448C,0xC449D,0xC464C,0xC465D,0xC480C,
    0xC481D,0xC49CC,0xC49DD,0xC4B8C,0xC4B9D,0xC4D4C,0xC4D5D,0xC4F0C,
    0xC4F1D,0xC50CC,0xC50DD,0xC528C,0xC529D,0xC544C,0xC545D,0xC560C,
    0xC561D,0xC57CC,0xC57DD,0xC598C,0xC599D,0xC5B4C,0xC5B5D,0xC5D0C,
    0xC5D1D,0xC5ECC,0xC5EDD,0xC608C,0xC609D,0xC624C,0xC625D,0xC640C,
    0xC641D,0xC65CC,0xC65DD,0xC678C,0xC679D,0xC694C,0xC695D,0xC6B0C,
    0xC6B1D,0xC6CCC,0xC6CDD,0xC6E8C,0xC6E9D,0xC704C,0xC705D,0xC720C,
    0xC721D,0xC73CC,0xC73DD,0xC758C,0xC759D,0xC774C,0xC775D,0xC790C,
    0xC791D,0xC7ACC,0xC7ADD,0xC7C8C,0xC7C9D,0xC7E4C,0xC7E5D,0xC800C,
    0xC801D,0xC81CC,0xC81DD,0xC838C,0xC839D,0xC854C,0xC855D,0xC870C,
    0xC871D,0xC88CC,0xC88DD,0xC8A8C,0xC8A9D,0xC8C4C,0xC8C5D,0xC8E0C,
    0xC8E1D,0xC8FCC,0xC8FDD,0xC918C,0xC919D,0xC934C,0xC935D,0xC950C,
    0xC951D,0xC96CC,0xC96DD,0xC988C,0xC989D,0xC9A4C,0xC9A5D,0xC9C0C,
    0xC9C1D,0xC9DCC,0xC9DDD,0xC9F8C,0xC9F9D,0xCA14C,0xCA15D,0xCA30C,
    0xCA31D,0xCA4CC,0xCA4DD,0xCA68C,0xCA69D,0xCA84C,0xCA85D,0xCAA0C,
    0xCAA1D,0xCABCC,0xCABDD,0xCAD8C,0xCAD9D,0xCAF4C,0xCAF5D,0xCB10C,
    0xCB11D,0xCB2CC,0xCB2DD,0xCB48C,0xCB49D,0xCB64C,0xCB65D,0xCB80C,
    0xCB81D,0xCB9CC,0xCB9DD,0xCBB8C,0xCBB9D,0xCBD4C,0xCBD5D,0xCBF0C,
    0xCBF1D,0xCC0CC,0xCC0DD,0xCC28C,0xCC29D,0xCC44C,0xCC45D,0xCC60C,
    0xCC61D,0xCC7CC,0xCC7DD,0xCC98C,0xCC99D,0xCCB4C,0xCCB5D,0xCCD0C,
    0xCCD1D,0xCCECC,0xCCEDD,0xCD08C,0xCD09D,0xCD24C,0xCD25D,0xCD40C,
    0xCD41D,0xCD5CC,0xCD5DD,0xCD78C,0xCD79D,0xCD94C,0xCD95D,0xCDB0C,
    0xCDB1D,0xCDCCC,0xCDCDD,0xCDE8C,0xCDE9D,0xCE04C,0xCE05D,0xCE20C,
    0xCE21D,0xCE3CC,0xCE3DD,0xCE58C,0xCE59D,0xCE74C,0xCE75D,0xCE90C,
    0xCE91D,0xCEACC,0xCEADD,0xCEC8C,0xCEC9D,0xCEE4C,0xCEE5D,0xCF00C,
    0xCF01D,0xCF1CC,0xCF1DD,0xCF38C,0xCF39D,0xCF54C,0xCF55D,0xCF70C,
    0xCF71D,0xCF8CC,0xCF8DD,0xCFA8C,0xCFA9D,0xCFC4C,0xCFC5D,0xCFE0C,
    0xCFE1D,0xCFFCC,0xCFFDD,0xD018C,0xD019D,0xD034C,0xD035D,0xD050C,
    0xD051D,0xD06CC,0xD06DD,0xD088C,0xD089D,0xD0A4C,0xD0A5D,0xD0C0C,
    0xD0C1D,0xD0DCC,0xD0DDD,0xD0F8C,0xD0F9D,0xD114C,0xD115D,0xD130C,
    0xD131D,0xD14CC,0xD14DD,0xD168C,0xD169D,0xD184C,0xD185D,0xD1A0C,
    0xD1A1D,0xD1BCC,0xD1BDD,0xD1D8C,0xD1D9D,0xD1F4C,0xD1F5D,0xD210C,
    0xD211D,0xD22CC,0xD22DD,0xD248C,0xD249D,0xD264C,0xD265D,0xD280C,
    0xD281D,0xD29CC,0xD29DD,0xD2B8C,0xD2B9D,0xD2D4C,0xD2D5D,0xD2F0C,
    0xD2F1D,0xD30CC,0xD30DD,0xD328C,0xD329D,0xD344C,0xD345D,0xD360C,
    0xD361D,0xD37CC,0xD37DD,0xD398C,0xD399D,0xD3B4C,0xD3B5D,0xD3D0C,
    0xD3D1D,0xD3ECC,0xD3EDD,0xD408C,0xD409D,0xD424C,0xD425D,0xD440C,
    0xD441D,0xD45CC,0xD45DD,0xD478C,0xD479D,0xD494C,0xD495D,0xD4B0C,
    0xD4B1D,0xD4CCC,0xD4CDD,0xD4E8C,0xD4E9D,0xD504C,0xD505D,0xD520C,
    0xD521D,0xD53CC,0xD53DD,0xD558C,0xD559D,0xD574C,0xD575D,0xD590C,
    0xD591D,0xD5ACC,0xD5ADD,0xD5C8C,0xD5C9D,0xD5E4C,0xD5E5D,0xD600C,
    0xD601D,0xD61CC,0xD61DD,0xD638C,0xD639D,0xD654C,0xD655D,0xD670C,
    0xD671D,0xD68CC,0xD68DD,0xD6A8C,0xD6A9D,0xD6C4C,0xD6C5D,0xD6E0C,
    0xD6E1D,0xD6FCC,0xD6FDD,0xD718C,0xD719D,0xD734C,0xD735D,0xD750C,
    0xD751D,0xD76CC,0xD76DD,0xD788C,0xD789D,0xD7A40,0xD7B0A,0xD7C70,
    0xD7CBB,0xD7FC0,0xFB1E4,0xFB1F0,0xFE004,0xFE100,0xFE204,0xFE300,
    0xFEFF3,0xFF000,0xFF9E4,0xFFA00,0xFFF03,0xFFFC0,0x101FD4,0x101FE0,
    0x102E04,0x102E10,0x103764,0x1037B0,0x10A014,0x10A040,0x10A054,0x10A070,
    0x10A0C4,0x10A100,0x10A384,0x10A3B0,0x10A3F4,0x10A400,0x10AE54,0x10AE70,
    0x10D244,0x10D280,0x10EAB4,0x10EAD0,0x10EFD4,0x10F000,0x10F464,0x10F510,
    0x10F824,0x10F860,0x110008,0x110014,0x110028,0x110030,0x110384,0x110470,
    0x110704,0x110710,0x110734,0x110750,0x1107F4,0x110828,0x110830,0x110B08,
    0x110B34,0x110B78,0x110B94,0x110BB0,0x110BD7,0x110BE0,0x110C24,0x110C30,
    0x110CD7,0x110CE0,0x111004,0x111030,0x111274,0x1112C8,0x1112D4,0x111350,
    0x111458,0x111470,0x111734,0x111740,0x111804,0x111828,0x111830,0x111B38,
    0x111B64,0x111BF8,0x111C10,0x111C27,0x111C40,0x111C94,0x111CD0,0x111CE8,
    0x111CF4,0x111D00,0x1122C8,0x1122F4,0x112328,0x112344,0x112358,0x112364,
    0x112380,0x1123E4,0x1123F0,0x112414,0x112420,0x112DF4,0x112E08,0x112E34,
    0x112EB0,0x113004,0x113028,0x113040,0x1133B4,0x1133D0,0x1133E4,0x1133F8,
    0x113404,0x113418,0x113450,0x113478,0x113490,0x1134B8,0x1134E0,0x113574,
    0x113580,0x113628,0x113640,0x113664,0x1136D0,0x113704,0x113750,0x114358,
    0x114384,0x114408,0x114424,0x114458,0x114464,0x114470,0x1145E4,0x1145F0,
    0x114B04,0x114B18,0x114B34,0x114B98,0x114BA4,0x114BB8,0x114BD4,0x114BE8,
    0x114BF4,0x114C18,0x114C24,0x114C40,0x115AF4,0x115B08,0x115B24,0x115B60,
    0x115B88,0x115BC4,0x115BE8,0x115BF4,0x115C10,0x115DC4,0x115DE0,0x116308,
    0x116334,0x1163B8,0x1163D4,0x1163E8,0x1163F4,0x116410,0x116AB4,0x116AC8,
    0x116AD4,0x116AE8,0x116B04,0x116B68,0x116B74,0x116B80,0x1171D4,0x117200,
    0x117224,0x117268,0x117274,0x1172C0,0x1182C8,0x1182F4,0x118388,0x118394,
    0x1183B0,0x119304,0x119318,0x119360,0x119378,0x119390,0x1193B4,0x1193D8,
    0x1193E4,0x1193F7,0x119408,0x119417,0x119428,0x119434,0x119440,0x119D18,
    0x119D44,0x119D80,0x119DA4,0x119DC8,0x119E04,0x119E10,0x119E48,0x119E50,
    0x11A014,0x11A0B0,0x11A334,0x11A398,0x11A3A7,0x11A3B4,0x11A3F0,0x11A474,
    0x11A480,0x11A514,0x11A578,0x11A594,0x11A5C0,0x11A847,0x11A8A4,0x11A978,
    0x11A984,0x11A9A0,0x11C2F8,0x11C304,0x11C370,0x11C384,0x11C3E8,0x11C3F4,
    0x11C400,0x11C924,0x11CA80,0x11CA98,0x11CAA4,0x11CB18,0x11CB24,0x11CB48,
    0x11CB54,0x11CB70,0x11D314,0x11D370,0x11D3A4,0x11D3B0,0x11D3C4,0x11D3E0,
    0x11D3F4,0x11D467,0x11D474,0x11D480,0x11D8A8,0x11D8F0,0x11D904,0x11D920,
    0x11D938,0x11D954,0x11D968,0x11D974,0x11D980,0x11EF34,0x11EF58,0x11EF70,
    0x11F004,0x11F027,0x11F038,0x11F040,0x11F348,0x11F364,0x11F3B0,0x11F3E8,
    0x11F404,0x11F418,0x11F424,0x11F430,0x134303,0x134404,0x134410,0x134474,
    0x134560,0x16AF04,0x16AF50,0x16B304,0x16B370,0x16F4F4,0x16F500,0x16F518,
    0x16F880,0x16F8F4,0x16F930,0x16FE44,0x16FE50,0x16FF08,0x16FF20,0x1BC9D4,
    0x1BC9F0,0x1BCA03,0x1BCA40,0x1CF004,0x1CF2E0,0x1CF304,0x1CF470,0x1D1654,
    0x1D1668,0x1D1674,0x1D16A0,0x1D16D8,0x1D16E4,0x1D1733,0x1D17B4,0x1D1830,
    0x1D1854,0x1D18C0,0x1D1AA4,0x1D1AE0,0x1D2424,0x1D2450,0x1DA004,0x1DA370,
    0x1DA3B4,0x1DA6D0,0x1DA754,0x1DA760,0x1DA844,0x1DA850,0x1DA9B4,0x1DAA00,
    0x1DAA14,0x1DAB00,0x1E0004,0x1E0070,0x1E0084,0x1E0190,0x1E01B4,0x1E0220,
    0x1E0234,0x1E0250,0x1E0264,0x1E02B0,0x1E08F4,0x1E0900,0x1E1304,0x1E1370,
    0x1E2AE4,0x1E2AF0,0x1E2EC4,0x1E2F00,0x1E4EC4,0x1E4F00,0x1E8D04,0x1E8D70,
    0x1E9444,0x1E94B0,0x1F1E66,0x1F2000,0x1F3FB4,0x1F4000,0xE00003,0xE00204,
    0xE00803,0xE01004,0xE01F03,0xE10000,
};
const int g_gcbRunsCount = (int)(sizeof(g_gcbRuns) / sizeof(g_gcbRuns[0]));

// Indic_Conjunct_Break values used by the grapheme cluster rules
const Range g_incbConsonant[] = {
    {0x915,0x939},{0x958,0x95F},{0x978,0x97F},{0x995,0x9A8},{0x9AA,0x9B0},{0x9B2,0x9B2},
    {0x9B6,0x9B9},{0x9DC,0x9DD},{0x9DF,0x9DF},{0x9F0,0x9F1},{0xA95,0xAA8},{0xAAA,0xAB0},
    {0xAB2,0xAB3},{0xAB5,0xAB9},{0xAF9,0xAF9},{0xB15,0xB28},{0xB2A,0xB30},{0xB32,0xB33},
    {0xB35,0xB39},{0xB5C,0xB5D},{0xB5F,0xB5F},{0xB71,0xB71},{0xC15,0xC28},{0xC2A,0xC39},
    {0xC58,0xC5A},{0xD15,0xD3A},
};
const int g_incbConsonantCount = (int)(sizeof(g_incbConsonant) / sizeof(g_incbConsonant[0]));
const Range g_incbLinker[] = {
    {0x94D,0x94D},{0x9CD,0x9CD},{0xACD,0xACD},{0xB4D,0xB4D},{0xC4D,0xC4D},{0xD4D,0xD4D},
};
const int g_incbLinkerCount = (int)(sizeof(g_incbLinker) / sizeof(g_incbLinker[0]));
const Range g_incbExtend[] = {
    {0x300,0x34E},{0x350,0x36F},{0x483,0x487},{0x591,0x5BD},{0x5BF,0x5BF},{0x5C1,0x5C2},
    {0x5C4,0x5C5},{0x5C7,0x5C7},{0x610,0x61A},{0x64B,0x65F},{0x670,0x670},{0x6D6,0x6DC},
    {0x6DF,0x6E4},{0x6E7,0x6E8},{0x6EA,0x6ED},{0x711,0x711},{0x730,0x74A},{0x7EB,0x7F3},
    {0x7FD,0x7FD},{0x816,0x819},{0x81B,0x823},{0x825,0x827},{0x829,0x82D},{0x859,0x85B},
    {0x898,0x89F},{0x8CA,0x8E1},{0x8E3,0x8FF},{0x93C,0x93C},{0x951,0x954},{0x9BC,0x9BC},
    {0x9FE,0x9FE},{0xA3C,0xA3C},{0xABC,0xABC},{0xB3C,0xB3C},{0xC3C,0xC3C},{0xC55,0xC56},
    {0xCBC,0xCBC},{0xD3B,0xD3C},{0xE38,0xE3A},{0xE48,0xE4B},{0xEB8,0xEBA},{0xEC8,0xECB},
    {0xF18,0xF19},{0xF35,0xF35},{0xF37,0xF37},{0xF39,0xF39},{0xF71,0xF72},{0xF74,0xF74},
    {0xF7A,0xF7D},{0xF80,0xF80},{0xF82,0xF84},{0xF86,0xF87},{0xFC6,0xFC6},{0x1037,0x1037},
    {0x1039,0x103A},{0x108D,0x108D},{0x135D,0x135F},{0x1714,0x1714},{0x17D2,0x17D2},{0x17DD,0x17DD},
    {0x18A9,0x18A9},{0x1939,0x193B},{0x1A17,0x1A18},{0x1A60,0x1A60},{0x1A75,0x1A7C},{0x1A7F,0x1A7F},
    {0x1AB0,0x1ABD},{0x1ABF,0x1ACE},{0x1B34,0x1B34},{0x1B6B,0x1B73},{0x1BAB,0x1BAB},{0x1BE6,0x1BE6},
    {0x1C37,0x1C37},{0x1CD0,0x1CD2},{0x1CD4,0x1CE0},{0x1CE2,0x1CE8},{0x1CED,0x1CED},{0x1CF4,0x1CF4},
    {0x1CF8,0x1CF9},{0x1DC0,0x1DFF},{0x200D,0x200D},{0x20D0,0x20DC},{0x20E1,0x20E1},{0x20E5,0x20F0},
    {0x2CEF,0x2CF1},{0x2D7F,0x2D7F},{0x2DE0,0x2DFF},{0x302A,0x302F},{0x3099,0x309A},{0xA66F,0xA66F},
    {0xA674,0xA67D},{0xA69E,0xA69F},{0xA6F0,0xA6F1},{0xA82C,0xA82C},{0xA8E0,0xA8F1},{0xA92B,0xA92D},
    {0xA9B3,0xA9B3},{0xAAB0,0xAAB0},{0xAAB2,0xAAB4},{0xAAB7,0xAAB8},{0xAABE,0xAABF},{0xAAC1,0xAAC1},
    {0xAAF6,0xAAF6},{0xABED,0xABED},{0xFB1E,0xFB1E},{0xFE20,0xFE2F},{0x101FD,0x101FD},{0x102E0,0x102E0},
    {0x10376,0x1037A},{0x10A0D,0x10A0D},{0x10A0F,0x10A0F},{0x10A38,0x10A3A},{0x10A3F,0x10A3F},{0x10AE5,0x10AE6},
    {0x10D24,0x10D27},{0x10EAB,0x10EAC},{0x10EFD,0x10EFF},{0x10F46,0x10F50},{0x10F82,0x10F85},{0x11070,0x11070},
    {0x1107F,0x1107F},{0x110BA,0x110BA},{0x11100,0x11102},{0x11133,0x11134},{0x11173,0x11173},{0x111CA,0x111CA},
    {0x11236,0x11236},{0x112E9,0x112EA},{0x1133B,0x1133C},{0x11366,0x1136C},{0x11370,0x11374},{0x11446,0x11446},
    {0x1145E,0x1145E},{0x114C3,0x114C3},{0x115C0,0x115C0},{0x116B7,0x116B7},{0x1172B,0x1172B},{0x1183A,0x1183A},
    {0x1193E,0x1193E},{0x11943,0x11943},{0x11A34,0x11A34},{0x11A47,0x11A47},{0x11A99,0x11A99},{0x11D42,0x11D42},
    {0x11D44,0x11D45},{0x11D97,0x11D97},{0x11F42,0x11F42},{0x16AF0,0x16AF4},{0x16B30,0x16B36},{0x1BC9E,0x1BC9E},
    {0x1D165,0x1D165},{0x1D167,0x1D169},{0x1D16E,0x1D172},{0x1D17B,0x1D182},{0x1D185,0x1D18B},{0x1D1AA,0x1D1AD},
    {0x1D242,0x1D244},{0x1E000,0x1E006},{0x1E008,0x1E018},{0x1E01B,0x1E021},{0x1E023,0x1E024},{0x1E026,0x1E02A},
    {0x1E08F,0x1E08F},{0x1E130,0x1E136},{0x1E2AE,0x1E2AE},{0x1E2EC,0x1E2EF},{0x1E4EC,0x1E4EF},{0x1E8D0,0x1E8D6},
    {0x1E944,0x1E94A},
};
const int g_incbExtendCount = (int)(sizeof(g_incbExtend) / sizeof(g_incbExtend[0]));

const Range g_binAlphabetic[] = {
    {0x41,0x5A},{0x61,0x7A},{0xAA,0xAA},{0xB5,0xB5},{0xBA,0xBA},{0xC0,0xD6},
    {0xD8,0xF6},{0xF8,0x2C1},{0x2C6,0x2D1},{0x2E0,0x2E4},{0x2EC,0x2EC},{0x2EE,0x2EE},
    {0x345,0x345},{0x370,0x374},{0x376,0x377},{0x37A,0x37D},{0x37F,0x37F},{0x386,0x386},
    {0x388,0x38A},{0x38C,0x38C},{0x38E,0x3A1},{0x3A3,0x3F5},{0x3F7,0x481},{0x48A,0x52F},
    {0x531,0x556},{0x559,0x559},{0x560,0x588},{0x5B0,0x5BD},{0x5BF,0x5BF},{0x5C1,0x5C2},
    {0x5C4,0x5C5},{0x5C7,0x5C7},{0x5D0,0x5EA},{0x5EF,0x5F2},{0x610,0x61A},{0x620,0x657},
    {0x659,0x65F},{0x66E,0x6D3},{0x6D5,0x6DC},{0x6E1,0x6E8},{0x6ED,0x6EF},{0x6FA,0x6FC},
    {0x6FF,0x6FF},{0x710,0x73F},{0x74D,0x7B1},{0x7CA,0x7EA},{0x7F4,0x7F5},{0x7FA,0x7FA},
    {0x800,0x817},{0x81A,0x82C},{0x840,0x858},{0x860,0x86A},{0x870,0x887},{0x889,0x88E},
    {0x8A0,0x8C9},{0x8D4,0x8DF},{0x8E3,0x8E9},{0x8F0,0x93B},{0x93D,0x94C},{0x94E,0x950},
    {0x955,0x963},{0x971,0x983},{0x985,0x98C},{0x98F,0x990},{0x993,0x9A8},{0x9AA,0x9B0},
    {0x9B2,0x9B2},{0x9B6,0x9B9},{0x9BD,0x9C4},{0x9C7,0x9C8},{0x9CB,0x9CC},{0x9CE,0x9CE},
    {0x9D7,0x9D7},{0x9DC,0x9DD},{0x9DF,0x9E3},{0x9F0,0x9F1},{0x9FC,0x9FC},{0xA01,0xA03},
    {0xA05,0xA0A},{0xA0F,0xA10},{0xA13,0xA28},{0xA2A,0xA30},{0xA32,0xA33},{0xA35,0xA36},
    {0xA38,0xA39},{0xA3E,0xA42},{0xA47,0xA48},{0xA4B,0xA4C},{0xA51,0xA51},{0xA59,0xA5C},
    {0xA5E,0xA5E},{0xA70,0xA75},{0xA81,0xA83},{0xA85,0xA8D},{0xA8F,0xA91},{0xA93,0xAA8},
    {0xAAA,0xAB0},{0xAB2,0xAB3},{0xAB5,0xAB9},{0xABD,0xAC5},{0xAC7,0xAC9},{0xACB,0xACC},
    {0xAD0,0xAD0},{0xAE0,0xAE3},{0xAF9,0xAFC},{0xB01,0xB03},{0xB05,0xB0C},{0xB0F,0xB10},
    {0xB13,0xB28},{0xB2A,0xB30},{0xB32,0xB33},{0xB35,0xB39},{0xB3D,0xB44},{0xB47,0xB48},
    {0xB4B,0xB4C},{0xB56,0xB57},{0xB5C,0xB5D},{0xB5F,0xB63},{0xB71,0xB71},{0xB82,0xB83},
    {0xB85,0xB8A},{0xB8E,0xB90},{0xB92,0xB95},{0xB99,0xB9A},{0xB9C,0xB9C},{0xB9E,0xB9F},
    {0xBA3,0xBA4},{0xBA8,0xBAA},{0xBAE,0xBB9},{0xBBE,0xBC2},{0xBC6,0xBC8},{0xBCA,0xBCC},
    {0xBD0,0xBD0},{0xBD7,0xBD7},{0xC00,0xC0C},{0xC0E,0xC10},{0xC12,0xC28},{0xC2A,0xC39},
    {0xC3D,0xC44},{0xC46,0xC48},{0xC4A,0xC4C},{0xC55,0xC56},{0xC58,0xC5A},{0xC5D,0xC5D},
    {0xC60,0xC63},{0xC80,0xC83},{0xC85,0xC8C},{0xC8E,0xC90},{0xC92,0xCA8},{0xCAA,0xCB3},
    {0xCB5,0xCB9},{0xCBD,0xCC4},{0xCC6,0xCC8},{0xCCA,0xCCC},{0xCD5,0xCD6},{0xCDD,0xCDE},
    {0xCE0,0xCE3},{0xCF1,0xCF3},{0xD00,0xD0C},{0xD0E,0xD10},{0xD12,0xD3A},{0xD3D,0xD44},
    {0xD46,0xD48},{0xD4A,0xD4C},{0xD4E,0xD4E},{0xD54,0xD57},{0xD5F,0xD63},{0xD7A,0xD7F},
    {0xD81,0xD83},{0xD85,0xD96},{0xD9A,0xDB1},{0xDB3,0xDBB},{0xDBD,0xDBD},{0xDC0,0xDC6},
    {0xDCF,0xDD4},{0xDD6,0xDD6},{0xDD8,0xDDF},{0xDF2,0xDF3},{0xE01,0xE3A},{0xE40,0xE46},
    {0xE4D,0xE4D},{0xE81,0xE82},{0xE84,0xE84},{0xE86,0xE8A},{0xE8C,0xEA3},{0xEA5,0xEA5},
    {0xEA7,0xEB9},{0xEBB,0xEBD},{0xEC0,0xEC4},{0xEC6,0xEC6},{0xECD,0xECD},{0xEDC,0xEDF},
    {0xF00,0xF00},{0xF40,0xF47},{0xF49,0xF6C},{0xF71,0xF83},{0xF88,0xF97},{0xF99,0xFBC},
    {0x1000,0x1036},{0x1038,0x1038},{0x103B,0x103F},{0x1050,0x108F},{0x109A,0x109D},{0x10A0,0x10C5},
    {0x10C7,0x10C7},{0x10CD,0x10CD},{0x10D0,0x10FA},{0x10FC,0x1248},{0x124A,0x124D},{0x1250,0x1256},
    {0x1258,0x1258},{0x125A,0x125D},{0x1260,0x1288},{0x128A,0x128D},{0x1290,0x12B0},{0x12B2,0x12B5},
    {0x12B8,0x12BE},{0x12C0,0x12C0},{0x12C2,0x12C5},{0x12C8,0x12D6},{0x12D8,0x1310},{0x1312,0x1315},
    {0x1318,0x135A},{0x1380,0x138F},{0x13A0,0x13F5},{0x13F8,0x13FD},{0x1401,0x166C},{0x166F,0x167F},
    {0x1681,0x169A},{0x16A0,0x16EA},{0x16EE,0x16F8},{0x1700,0x1713},{0x171F,0x1733},{0x1740,0x1753},
    {0x1760,0x176C},{0x176E,0x1770},{0x1772,0x1773},{0x1780,0x17B3},{0x17B6,0x17C8},{0x17D7,0x17D7},
    {0x17DC,0x17DC},{0x1820,0x1878},{0x1880,0x18AA},{0x18B0,0x18F5},{0x1900,0x191E},{0x1920,0x192B},
    {0x1930,0x1938},{0x1950,0x196D},{0x1970,0x1974},{0x1980,0x19AB},{0x19B0,0x19C9},{0x1A00,0x1A1B},
    {0x1A20,0x1A5E},{0x1A61,0x1A74},{0x1AA7,0x1AA7},{0x1ABF,0x1AC0},{0x1ACC,0x1ACE},{0x1B00,0x1B33},
    {0x1B35,0x1B43},{0x1B45,0x1B4C},{0x1B80,0x1BA9},{0x1BAC,0x1BAF},{0x1BBA,0x1BE5},{0x1BE7,0x1BF1},
    {0x1C00,0x1C36},{0x1C4D,0x1C4F},{0x1C5A,0x1C7D},{0x1C80,0x1C88},{0x1C90,0x1CBA},{0x1CBD,0x1CBF},
    {0x1CE9,0x1CEC},{0x1CEE,0x1CF3},{0x1CF5,0x1CF6},{0x1CFA,0x1CFA},{0x1D00,0x1DBF},{0x1DE7,0x1DF4},
    {0x1E00,0x1F15},{0x1F18,0x1F1D},{0x1F20,0x1F45},{0x1F48,0x1F4D},{0x1F50,0x1F57},{0x1F59,0x1F59},
    {0x1F5B,0x1F5B},{0x1F5D,0x1F5D},{0x1F5F,0x1F7D},{0x1F80,0x1FB4},{0x1FB6,0x1FBC},{0x1FBE,0x1FBE},
    {0x1FC2,0x1FC4},{0x1FC6,0x1FCC},{0x1FD0,0x1FD3},{0x1FD6,0x1FDB},{0x1FE0,0x1FEC},{0x1FF2,0x1FF4},
    {0x1FF6,0x1FFC},{0x2071,0x2071},{0x207F,0x207F},{0x2090,0x209C},{0x2102,0x2102},{0x2107,0x2107},
    {0x210A,0x2113},{0x2115,0x2115},{0x2119,0x211D},{0x2124,0x2124},{0x2126,0x2126},{0x2128,0x2128},
    {0x212A,0x212D},{0x212F,0x2139},{0x213C,0x213F},{0x2145,0x2149},{0x214E,0x214E},{0x2160,0x2188},
    {0x24B6,0x24E9},{0x2C00,0x2CE4},{0x2CEB,0x2CEE},{0x2CF2,0x2CF3},{0x2D00,0x2D25},{0x2D27,0x2D27},
    {0x2D2D,0x2D2D},{0x2D30,0x2D67},{0x2D6F,0x2D6F},{0x2D80,0x2D96},{0x2DA0,0x2DA6},{0x2DA8,0x2DAE},
    {0x2DB0,0x2DB6},{0x2DB8,0x2DBE},{0x2DC0,0x2DC6},{0x2DC8,0x2DCE},{0x2DD0,0x2DD6},{0x2DD8,0x2DDE},
    {0x2DE0,0x2DFF},{0x2E2F,0x2E2F},{0x3005,0x3007},{0x3021,0x3029},{0x3031,0x3035},{0x3038,0x303C},
    {0x3041,0x3096},{0x309D,0x309F},{0x30A1,0x30FA},{0x30FC,0x30FF},{0x3105,0x312F},{0x3131,0x318E},
    {0x31A0,0x31BF},{0x31F0,0x31FF},{0x3400,0x4DBF},{0x4E00,0xA48C},{0xA4D0,0xA4FD},{0xA500,0xA60C},
    {0xA610,0xA61F},{0xA62A,0xA62B},{0xA640,0xA66E},{0xA674,0xA67B},{0xA67F,0xA6EF},{0xA717,0xA71F},
    {0xA722,0xA788},{0xA78B,0xA7CA},{0xA7D0,0xA7D1},{0xA7D3,0xA7D3},{0xA7D5,0xA7D9},{0xA7F2,0xA805},
    {0xA807,0xA827},{0xA840,0xA873},{0xA880,0xA8C3},{0xA8C5,0xA8C5},{0xA8F2,0xA8F7},{0xA8FB,0xA8FB},
    {0xA8FD,0xA8FF},{0xA90A,0xA92A},{0xA930,0xA952},{0xA960,0xA97C},{0xA980,0xA9B2},{0xA9B4,0xA9BF},
    {0xA9CF,0xA9CF},{0xA9E0,0xA9EF},{0xA9FA,0xA9FE},{0xAA00,0xAA36},{0xAA40,0xAA4D},{0xAA60,0xAA76},
    {0xAA7A,0xAABE},{0xAAC0,0xAAC0},{0xAAC2,0xAAC2},{0xAADB,0xAADD},{0xAAE0,0xAAEF},{0xAAF2,0xAAF5},
    {0xAB01,0xAB06},{0xAB09,0xAB0E},{0xAB11,0xAB16},{0xAB20,0xAB26},{0xAB28,0xAB2E},{0xAB30,0xAB5A},
    {0xAB5C,0xAB69},{0xAB70,0xABEA},{0xAC00,0xD7A3},{0xD7B0,0xD7C6},{0xD7CB,0xD7FB},{0xF900,0xFA6D},
    {0xFA70,0xFAD9},{0xFB00,0xFB06},{0xFB13,0xFB17},{0xFB1D,0xFB28},{0xFB2A,0xFB36},{0xFB38,0xFB3C},
    {0xFB3E,0xFB3E},{0xFB40,0xFB41},{0xFB43,0xFB44},{0xFB46,0xFBB1},{0xFBD3,0xFD3D},{0xFD50,0xFD8F},
    {0xFD92,0xFDC7},{0xFDF0,0xFDFB},{0xFE70,0xFE74},{0xFE76,0xFEFC},{0xFF21,0xFF3A},{0xFF41,0xFF5A},
    {0xFF66,0xFFBE},{0xFFC2,0xFFC7},{0xFFCA,0xFFCF},{0xFFD2,0xFFD7},{0xFFDA,0xFFDC},{0x10000,0x1000B},
    {0x1000D,0x10026},{0x10028,0x1003A},{0x1003C,0x1003D},{0x1003F,0x1004D},{0x10050,0x1005D},{0x10080,0x100FA},
    {0x10140,0x10174},{0x10280,0x1029C},{0x102A0,0x102D0},{0x10300,0x1031F},{0x1032D,0x1034A},{0x10350,0x1037A},
    {0x10380,0x1039D},{0x103A0,0x103C3},{0x103C8,0x103CF},{0x103D1,0x103D5},{0x10400,0x1049D},{0x104B0,0x104D3},
    {0x104D8,0x104FB},{0x10500,0x10527},{0x10530,0x10563},{0x10570,0x1057A},{0x1057C,0x1058A},{0x1058C,0x10592},
    {0x10594,0x10595},{0x10597,0x105A1},{0x105A3,0x105B1},{0x105B3,0x105B9},{0x105BB,0x105BC},{0x10600,0x10736},
    {0x10740,0x10755},{0x10760,0x10767},{0x10780,0x10785},{0x10787,0x107B0},{0x107B2,0x107BA},{0x10800,0x10805},
    {0x10808,0x10808},{0x1080A,0x10835},{0x10837,0x10838},{0x1083C,0x1083C},{0x1083F,0x10855},{0x10860,0x10876},
    {0x10880,0x1089E},{0x108E0,0x108F2},{0x108F4,0x108F5},{0x10900,0x10915},{0x10920,0x10939},{0x10980,0x109B7},
    {0x109BE,0x109BF},{0x10A00,0x10A03},{0x10A05,0x10A06},{0x10A0C,0x10A13},{0x10A15,0x10A17},{0x10A19,0x10A35},
    {0x10A60,0x10A7C},{0x10A80,0x10A9C},{0x10AC0,0x10AC7},{0x10AC9,0x10AE4},{0x10B00,0x10B35},{0x10B40,0x10B55},
    {0x10B60,0x10B72},{0x10B80,0x10B91},{0x10C00,0x10C48},{0x10C80,0x10CB2},{0x10CC0,0x10CF2},{0x10D00,0x10D27},
    {0x10E80,0x10EA9},{0x10EAB,0x10EAC},{0x10EB0,0x10EB1},{0x10F00,0x10F1C},{0x10F27,0x10F27},{0x10F30,0x10F45},
    {0x10F70,0x10F81},{0x10FB0,0x10FC4},{0x10FE0,0x10FF6},{0x11000,0x11045},{0x11071,0x11075},{0x11080,0x110B8},
    {0x110C2,0x110C2},{0x110D0,0x110E8},{0x11100,0x11132},{0x11144,0x11147},{0x11150,0x11172},{0x11176,0x11176},
    {0x11180,0x111BF},{0x111C1,0x111C4},{0x111CE,0x111CF},{0x111DA,0x111DA},{0x111DC,0x111DC},{0x11200,0x11211},
    {0x11213,0x11234},{0x11237,0x11237},{0x1123E,0x11241},{0x11280,0x11286},{0x11288,0x11288},{0x1128A,0x1128D},
    {0x1128F,0x1129D},{0x1129F,0x112A8},{0x112B0,0x112E8},{0x11300,0x11303},{0x11305,0x1130C},{0x1130F,0x11310},
    {0x11313,0x11328},{0x1132A,0x11330},{0x11332,0x11333},{0x11335,0x11339},{0x1133D,0x11344},{0x11347,0x11348},
    {0x1134B,0x1134C},{0x11350,0x11350},{0x11357,0x11357},{0x1135D,0x11363},{0x11400,0x11441},{0x11443,0x11445},
    {0x11447,0x1144A},{0x1145F,0x11461},{0x11480,0x114C1},{0x114C4,0x114C5},{0x114C7,0x114C7},{0x11580,0x115B5},
    {0x115B8,0x115BE},{0x115D8,0x115DD},{0x11600,0x1163E},{0x11640,0x11640},{0x11644,0x11644},{0x11680,0x116B5},
    {0x116B8,0x116B8},{0x11700,0x1171A},{0x1171D,0x1172A},{0x11740,0x11746},{0x11800,0x11838},{0x118A0,0x118DF},
    {0x118FF,0x11906},{0x11909,0x11909},{0x1190C,0x11913},{0x11915,0x11916},{0x11918,0x11935},{0x11937,0x11938},
    {0x1193B,0x1193C},{0x1193F,0x11942},{0x119A0,0x119A7},{0x119AA,0x119D7},{0x119DA,0x119DF},{0x119E1,0x119E1},
    {0x119E3,0x119E4},{0x11A00,0x11A32},{0x11A35,0x11A3E},{0x11A50,0x11A97},{0x11A9D,0x11A9D},{0x11AB0,0x11AF8},
    {0x11C00,0x11C08},{0x11C0A,0x11C36},{0x11C38,0x11C3E},{0x11C40,0x11C40},{0x11C72,0x11C8F},{0x11C92,0x11CA7},
    {0x11CA9,0x11CB6},{0x11D00,0x11D06},{0x11D08,0x11D09},{0x11D0B,0x11D36},{0x11D3A,0x11D3A},{0x11D3C,0x11D3D},
    {0x11D3F,0x11D41},{0x11D43,0x11D43},{0x11D46,0x11D47},{0x11D60,0x11D65},{0x11D67,0x11D68},{0x11D6A,0x11D8E},
    {0x11D90,0x11D91},{0x11D93,0x11D96},{0x11D98,0x11D98},{0x11EE0,0x11EF6},{0x11F00,0x11F10},{0x11F12,0x11F3A},
    {0x11F3E,0x11F40},{0x11FB0,0x11FB0},{0x12000,0x12399},{0x12400,0x1246E},{0x12480,0x12543},{0x12F90,0x12FF0},
    {0x13000,0x1342F},{0x13441,0x13446},{0x14400,0x14646},{0x16800,0x16A38},{0x16A40,0x16A5E},{0x16A70,0x16ABE},
    {0x16AD0,0x16AED},{0x16B00,0x16B2F},{0x16B40,0x16B43},{0x16B63,0x16B77},{0x16B7D,0x16B8F},{0x16E40,0x16E7F},
    {0x16F00,0x16F4A},{0x16F4F,0x16F87},{0x16F8F,0x16F9F},{0x16FE0,0x16FE1},{0x16FE3,0x16FE3},{0x16FF0,0x16FF1},
    {0x17000,0x187F7},{0x18800,0x18CD5},{0x18D00,0x18D08},{0x1AFF0,0x1AFF3},{0x1AFF5,0x1AFFB},{0x1AFFD,0x1AFFE},
    {0x1B000,0x1B122},{0x1B132,0x1B132},{0x1B150,0x1B152},{0x1B155,0x1B155},{0x1B164,0x1B167},{0x1B170,0x1B2FB},
    {0x1BC00,0x1BC6A},{0x1BC70,0x1BC7C},{0x1BC80,0x1BC88},{0x1BC90,0x1BC99},{0x1BC9E,0x1BC9E},{0x1D400,0x1D454},
    {0x1D456,0x1D49C},{0x1D49E,0x1D49F},{0x1D4A2,0x1D4A2},{0x1D4A5,0x1D4A6},{0x1D4A9,0x1D4AC},{0x1D4AE,0x1D4B9},
    {0x1D4BB,0x1D4BB},{0x1D4BD,0x1D4C3},{0x1D4C5,0x1D505},{0x1D507,0x1D50A},{0x1D50D,0x1D514},{0x1D516,0x1D51C},
    {0x1D51E,0x1D539},{0x1D53B,0x1D53E},{0x1D540,0x1D544},{0x1D546,0x1D546},{0x1D54A,0x1D550},{0x1D552,0x1D6A5},
    {0x1D6A8,0x1D6C0},{0x1D6C2,0x1D6DA},{0x1D6DC,0x1D6FA},{0x1D6FC,0x1D714},{0x1D716,0x1D734},{0x1D736,0x1D74E},
    {0x1D750,0x1D76E},{0x1D770,0x1D788},{0x1D78A,0x1D7A8},{0x1D7AA,0x1D7C2},{0x1D7C4,0x1D7CB},{0x1DF00,0x1DF1E},
    {0x1DF25,0x1DF2A},{0x1E000,0x1E006},{0x1E008,0x1E018},{0x1E01B,0x1E021},{0x1E023,0x1E024},{0x1E026,0x1E02A},
    {0x1E030,0x1E06D},{0x1E08F,0x1E08F},{0x1E100,0x1E12C},{0x1E137,0x1E13D},{0x1E14E,0x1E14E},{0x1E290,0x1E2AD},
    {0x1E2C0,0x1E2EB},{0x1E4D0,0x1E4EB},{0x1E7E0,0x1E7E6},{0x1E7E8,0x1E7EB},{0x1E7ED,0x1E7EE},{0x1E7F0,0x1E7FE},
    {0x1E800,0x1E8C4},{0x1E900,0x1E943},{0x1E947,0x1E947},{0x1E94B,0x1E94B},{0x1EE00,0x1EE03},{0x1EE05,0x1EE1F},
    {0x1EE21,0x1EE22},{0x1EE24,0x1EE24},{0x1EE27,0x1EE27},{0x1EE29,0x1EE32},{0x1EE34,0x1EE37},{0x1EE39,0x1EE39},
    {0x1EE3B,0x1EE3B},{0x1EE42,0x1EE42},{0x1EE47,0x1EE47},{0x1EE49,0x1EE49},{0x1EE4B,0x1EE4B},{0x1EE4D,0x1EE4F},
    {0x1EE51,0x1EE52},{0x1EE54,0x1EE54},{0x1EE57,0x1EE57},{0x1EE59,0x1EE59},{0x1EE5B,0x1EE5B},{0x1EE5D,0x1EE5D},
    {0x1EE5F,0x1EE5F},{0x1EE61,0x1EE62},{0x1EE64,0x1EE64},{0x1EE67,0x1EE6A},{0x1EE6C,0x1EE72},{0x1EE74,0x1EE77},
    {0x1EE79,0x1EE7C},{0x1EE7E,0x1EE7E},{0x1EE80,0x1EE89},{0x1EE8B,0x1EE9B},{0x1EEA1,0x1EEA3},{0x1EEA5,0x1EEA9},
    {0x1EEAB,0x1EEBB},{0x1F130,0x1F149},{0x1F150,0x1F169},{0x1F170,0x1F189},{0x20000,0x2A6DF},{0x2A700,0x2B739},
    {0x2B740,0x2B81D},{0x2B820,0x2CEA1},{0x2CEB0,0x2EBE0},{0x2EBF0,0x2EE5D},{0x2F800,0x2FA1D},{0x30000,0x3134A},
    {0x31350,0x323AF},
};
const Range g_binEmoji[] = {
    {0x23,0x23},{0x2A,0x2A},{0x30,0x39},{0xA9,0xA9},{0xAE,0xAE},{0x203C,0x203C},
    {0x2049,0x2049},{0x2122,0x2122},{0x2139,0x2139},{0x2194,0x2199},{0x21A9,0x21AA},{0x231A,0x231B},
    {0x2328,0x2328},{0x23CF,0x23CF},{0x23E9,0x23F3},{0x23F8,0x23FA},{0x24C2,0x24C2},{0x25AA,0x25AB},
    {0x25B6,0x25B6},{0x25C0,0x25C0},{0x25FB,0x25FE},{0x2600,0x2604},{0x260E,0x260E},{0x2611,0x2611},
    {0x2614,0x2615},{0x2618,0x2618},{0x261D,0x261D},{0x2620,0x2620},{0x2622,0x2623},{0x2626,0x2626},
    {0x262A,0x262A},{0x262E,0x262F},{0x2638,0x263A},{0x2640,0x2640},{0x2642,0x2642},{0x2648,0x2653},
    {0x265F,0x2660},{0x2663,0x2663},{0x2665,0x2666},{0x2668,0x2668},{0x267B,0x267B},{0x267E,0x267F},
    {0x2692,0x2697},{0x2699,0x2699},{0x269B,0x269C},{0x26A0,0x26A1},{0x26A7,0x26A7},{0x26AA,0x26AB},
    {0x26B0,0x26B1},{0x26BD,0x26BE},{0x26C4,0x26C5},{0x26C8,0x26C8},{0x26CE,0x26CF},{0x26D1,0x26D1},
    {0x26D3,0x26D4},{0x26E9,0x26EA},{0x26F0,0x26F5},{0x26F7,0x26FA},{0x26FD,0x26FD},{0x2702,0x2702},
    {0x2705,0x2705},{0x2708,0x270D},{0x270F,0x270F},{0x2712,0x2712},{0x2714,0x2714},{0x2716,0x2716},
    {0x271D,0x271D},{0x2721,0x2721},{0x2728,0x2728},{0x2733,0x2734},{0x2744,0x2744},{0x2747,0x2747},
    {0x274C,0x274C},{0x274E,0x274E},{0x2753,0x2755},{0x2757,0x2757},{0x2763,0x2764},{0x2795,0x2797},
    {0x27A1,0x27A1},{0x27B0,0x27B0},{0x27BF,0x27BF},{0x2934,0x2935},{0x2B05,0x2B07},{0x2B1B,0x2B1C},
    {0x2B50,0x2B50},{0x2B55,0x2B55},{0x3030,0x3030},{0x303D,0x303D},{0x3297,0x3297},{0x3299,0x3299},
    {0x1F004,0x1F004},{0x1F0CF,0x1F0CF},{0x1F170,0x1F171},{0x1F17E,0x1F17F},{0x1F18E,0x1F18E},{0x1F191,0x1F19A},
    {0x1F1E6,0x1F1FF},{0x1F201,0x1F202},{0x1F21A,0x1F21A},{0x1F22F,0x1F22F},{0x1F232,0x1F23A},{0x1F250,0x1F251},
    {0x1F300,0x1F321},{0x1F324,0x1F393},{0x1F396,0x1F397},{0x1F399,0x1F39B},{0x1F39E,0x1F3F0},{0x1F3F3,0x1F3F5},
    {0x1F3F7,0x1F4FD},{0x1F4FF,0x1F53D},{0x1F549,0x1F54E},{0x1F550,0x1F567},{0x1F56F,0x1F570},{0x1F573,0x1F57A},
    {0x1F587,0x1F587},{0x1F58A,0x1F58D},{0x1F590,0x1F590},{0x1F595,0x1F596},{0x1F5A4,0x1F5A5},{0x1F5A8,0x1F5A8},
    {0x1F5B1,0x1F5B2},{0x1F5BC,0x1F5BC},{0x1F5C2,0x1F5C4},{0x1F5D1,0x1F5D3},{0x1F5DC,0x1F5DE},{0x1F5E1,0x1F5E1},
    {0x1F5E3,0x1F5E3},{0x1F5E8,0x1F5E8},{0x1F5EF,0x1F5EF},{0x1F5F3,0x1F5F3},{0x1F5FA,0x1F64F},{0x1F680,0x1F6C5},
    {0x1F6CB,0x1F6D2},{0x1F6D5,0x1F6D7},{0x1F6DC,0x1F6E5},{0x1F6E9,0x1F6E9},{0x1F6EB,0x1F6EC},{0x1F6F0,0x1F6F0},
    {0x1F6F3,0x1F6FC},{0x1F7E0,0x1F7EB},{0x1F7F0,0x1F7F0},{0x1F90C,0x1F93A},{0x1F93C,0x1F945},{0x1F947,0x1F9FF},
    {0x1FA70,0x1FA7C},{0x1FA80,0x1FA88},{0x1FA90,0x1FABD},{0x1FABF,0x1FAC5},{0x1FACE,0x1FADB},{0x1FAE0,0x1FAE8},
    {0x1FAF0,0x1FAF8},
};
const Range g_binEmojiPresentation[] = {
    {0x231A,0x231B},{0x23E9,0x23EC},{0x23F0,0x23F0},{0x23F3,0x23F3},{0x25FD,0x25FE},{0x2614,0x2615},
    {0x2648,0x2653},{0x267F,0x267F},{0x2693,0x2693},{0x26A1,0x26A1},{0x26AA,0x26AB},{0x26BD,0x26BE},
    {0x26C4,0x26C5},{0x26CE,0x26CE},{0x26D4,0x26D4},{0x26EA,0x26EA},{0x26F2,0x26F3},{0x26F5,0x26F5},
    {0x26FA,0x26FA},{0x26FD,0x26FD},{0x2705,0x2705},{0x270A,0x270B},{0x2728,0x2728},{0x274C,0x274C},
    {0x274E,0x274E},{0x2753,0x2755},{0x2757,0x2757},{0x2795,0x2797},{0x27B0,0x27B0},{0x27BF,0x27BF},
    {0x2B1B,0x2B1C},{0x2B50,0x2B50},{0x2B55,0x2B55},{0x1F004,0x1F004},{0x1F0CF,0x1F0CF},{0x1F18E,0x1F18E},
    {0x1F191,0x1F19A},{0x1F1E6,0x1F1FF},{0x1F201,0x1F201},{0x1F21A,0x1F21A},{0x1F22F,0x1F22F},{0x1F232,0x1F236},
    {0x1F238,0x1F23A},{0x1F250,0x1F251},{0x1F300,0x1F320},{0x1F32D,0x1F335},{0x1F337,0x1F37C},{0x1F37E,0x1F393},
    {0x1F3A0,0x1F3CA},{0x1F3CF,0x1F3D3},{0x1F3E0,0x1F3F0},{0x1F3F4,0x1F3F4},{0x1F3F8,0x1F43E},{0x1F440,0x1F440},
    {0x1F442,0x1F4FC},{0x1F4FF,0x1F53D},{0x1F54B,0x1F54E},{0x1F550,0x1F567},{0x1F57A,0x1F57A},{0x1F595,0x1F596},
    {0x1F5A4,0x1F5A4},{0x1F5FB,0x1F64F},{0x1F680,0x1F6C5},{0x1F6CC,0x1F6CC},{0x1F6D0,0x1F6D2},{0x1F6D5,0x1F6D7},
    {0x1F6DC,0x1F6DF},{0x1F6EB,0x1F6EC},{0x1F6F4,0x1F6FC},{0x1F7E0,0x1F7EB},{0x1F7F0,0x1F7F0},{0x1F90C,0x1F93A},
    {0x1F93C,0x1F945},{0x1F947,0x1F9FF},{0x1FA70,0x1FA7C},{0x1FA80,0x1FA88},{0x1FA90,0x1FABD},{0x1FABF,0x1FAC5},
    {0x1FACE,0x1FADB},{0x1FAE0,0x1FAE8},{0x1FAF0,0x1FAF8},
};
const Range g_binEmojiModifier[] = {
    {0x1F3FB,0x1F3FF},
};
const Range g_binEmojiModifierBase[] = {
    {0x261D,0x261D},{0x26F9,0x26F9},{0x270A,0x270D},{0x1F385,0x1F385},{0x1F3C2,0x1F3C4},{0x1F3C7,0x1F3C7},
    {0x1F3CA,0x1F3CC},{0x1F442,0x1F443},{0x1F446,0x1F450},{0x1F466,0x1F478},{0x1F47C,0x1F47C},{0x1F481,0x1F483},
    {0x1F485,0x1F487},{0x1F48F,0x1F48F},{0x1F491,0x1F491},{0x1F4AA,0x1F4AA},{0x1F574,0x1F575},{0x1F57A,0x1F57A},
    {0x1F590,0x1F590},{0x1F595,0x1F596},{0x1F645,0x1F647},{0x1F64B,0x1F64F},{0x1F6A3,0x1F6A3},{0x1F6B4,0x1F6B6},
    {0x1F6C0,0x1F6C0},{0x1F6CC,0x1F6CC},{0x1F90C,0x1F90C},{0x1F90F,0x1F90F},{0x1F918,0x1F91F},{0x1F926,0x1F926},
    {0x1F930,0x1F939},{0x1F93C,0x1F93E},{0x1F977,0x1F977},{0x1F9B5,0x1F9B6},{0x1F9B8,0x1F9B9},{0x1F9BB,0x1F9BB},
    {0x1F9CD,0x1F9CF},{0x1F9D1,0x1F9DD},{0x1FAC3,0x1FAC5},{0x1FAF0,0x1FAF8},
};
const Range g_binEmojiComponent[] = {
    {0x23,0x23},{0x2A,0x2A},{0x30,0x39},{0x200D,0x200D},{0x20E3,0x20E3},{0xFE0F,0xFE0F},
    {0x1F1E6,0x1F1FF},{0x1F3FB,0x1F3FF},{0x1F9B0,0x1F9B3},{0xE0020,0xE007F},
};
const Range g_binExtendedPictographic[] = {
    {0xA9,0xA9},{0xAE,0xAE},{0x203C,0x203C},{0x2049,0x2049},{0x2122,0x2122},{0x2139,0x2139},
    {0x2194,0x2199},{0x21A9,0x21AA},{0x231A,0x231B},{0x2328,0x2328},{0x2388,0x2388},{0x23CF,0x23CF},
    {0x23E9,0x23F3},{0x23F8,0x23FA},{0x24C2,0x24C2},{0x25AA,0x25AB},{0x25B6,0x25B6},{0x25C0,0x25C0},
    {0x25FB,0x25FE},{0x2600,0x2605},{0x2607,0x2612},{0x2614,0x2685},{0x2690,0x2705},{0x2708,0x2712},
    {0x2714,0x2714},{0x2716,0x2716},{0x271D,0x271D},{0x2721,0x2721},{0x2728,0x2728},{0x2733,0x2734},
    {0x2744,0x2744},{0x2747,0x2747},{0x274C,0x274C},{0x274E,0x274E},{0x2753,0x2755},{0x2757,0x2757},
    {0x2763,0x2767},{0x2795,0x2797},{0x27A1,0x27A1},{0x27B0,0x27B0},{0x27BF,0x27BF},{0x2934,0x2935},
    {0x2B05,0x2B07},{0x2B1B,0x2B1C},{0x2B50,0x2B50},{0x2B55,0x2B55},{0x3030,0x3030},{0x303D,0x303D},
    {0x3297,0x3297},{0x3299,0x3299},{0x1F000,0x1F0FF},{0x1F10D,0x1F10F},{0x1F12F,0x1F12F},{0x1F16C,0x1F171},
    {0x1F17E,0x1F17F},{0x1F18E,0x1F18E},{0x1F191,0x1F19A},{0x1F1AD,0x1F1E5},{0x1F201,0x1F20F},{0x1F21A,0x1F21A},
    {0x1F22F,0x1F22F},{0x1F232,0x1F23A},{0x1F23C,0x1F23F},{0x1F249,0x1F3FA},{0x1F400,0x1F53D},{0x1F546,0x1F64F},
    {0x1F680,0x1F6FF},{0x1F774,0x1F77F},{0x1F7D5,0x1F7FF},{0x1F80C,0x1F80F},{0x1F848,0x1F84F},{0x1F85A,0x1F85F},
    {0x1F888,0x1F88F},{0x1F8AE,0x1F8FF},{0x1F90C,0x1F93A},{0x1F93C,0x1F945},{0x1F947,0x1FAFF},{0x1FC00,0x1FFFD},
};
const int g_binExtendedPictographicCount = (int)(sizeof(g_binExtendedPictographic) / sizeof(g_binExtendedPictographic[0]));

// Binary properties usable as \p{Name}
const BinPropDef g_binProps[] = {
    {"Alphabetic","Alpha",g_binAlphabetic,(int)(sizeof(g_binAlphabetic) / sizeof(g_binAlphabetic[0]))},
    {"Emoji","",g_binEmoji,(int)(sizeof(g_binEmoji) / sizeof(g_binEmoji[0]))},
    {"Emoji_Presentation","EPres",g_binEmojiPresentation,(int)(sizeof(g_binEmojiPresentation) / sizeof(g_binEmojiPresentation[0]))},
    {"Emoji_Modifier","EMod",g_binEmojiModifier,(int)(sizeof(g_binEmojiModifier) / sizeof(g_binEmojiModifier[0]))},
    {"Emoji_Modifier_Base","EBase",g_binEmojiModifierBase,(int)(sizeof(g_binEmojiModifierBase) / sizeof(g_binEmojiModifierBase[0]))},
    {"Emoji_Component","EComp",g_binEmojiComponent,(int)(sizeof(g_binEmojiComponent) / sizeof(g_binEmojiComponent[0]))},
    {"Extended_Pictographic","ExtPict",g_binExtendedPictographic,(int)(sizeof(g_binExtendedPictographic) / sizeof(g_binExtendedPictographic[0]))},
};
const int g_binPropsCount = (int)(sizeof(g_binProps) / sizeof(g_binProps[0]));

// General category long names / aliases and the short name they stand for
const StrPair g_gcAliases[] = {
    {"Other","C"},
    {"Control","Cc"},
    {"cntrl","Cc"},
    {"Format","Cf"},
    {"Unassigned","Cn"},
    {"Private_Use","Co"},
    {"Surrogate","Cs"},
    {"Letter","L"},
    {"Cased_Letter","LC"},
    {"Lowercase_Letter","Ll"},
    {"Modifier_Letter","Lm"},
    {"Other_Letter","Lo"},
    {"Titlecase_Letter","Lt"},
    {"Uppercase_Letter","Lu"},
    {"Mark","M"},
    {"Combining_Mark","M"},
    {"Spacing_Mark","Mc"},
    {"Enclosing_Mark","Me"},
    {"Nonspacing_Mark","Mn"},
    {"Number","N"},
    {"Decimal_Number","Nd"},
    {"digit","Nd"},
    {"Letter_Number","Nl"},
    {"Other_Number","No"},
    {"Punctuation","P"},
    {"punct","P"},
    {"Connector_Punctuation","Pc"},
    {"Dash_Punctuation","Pd"},
    {"Close_Punctuation","Pe"},
    {"Final_Punctuation","Pf"},
    {"Initial_Punctuation","Pi"},
    {"Other_Punctuation","Po"},
    {"Open_Punctuation","Ps"},
    {"Symbol","S"},
    {"Currency_Symbol","Sc"},
    {"Modifier_Symbol","Sk"},
    {"Math_Symbol","Sm"},
    {"Other_Symbol","So"},
    {"Separator","Z"},
    {"Line_Separator","Zl"},
    {"Paragraph_Separator","Zp"},
    {"Space_Separator","Zs"},
};
const int g_gcAliasesCount = (int)(sizeof(g_gcAliases) / sizeof(g_gcAliases[0]));
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
    Compile(pattern, flags, 0, 0);
}

CRegexpW::CRegexpW(const wchar_t* pattern, unsigned int flags, CRegexpResolveProc resolver, void* user)
    : m_prog(0), m_stepBase(1000000UL), m_stepPer(256UL)
{
    Compile(pattern, flags, resolver, user);
}

CRegexpW::~CRegexpW() { delete m_prog; }

void CRegexpW::Compile(const wchar_t* pattern, unsigned int flags)
{
    Compile(pattern, flags, 0, 0);
}

void CRegexpW::Compile(const wchar_t* pattern, unsigned int flags, CRegexpResolveProc resolver, void* user)
{
    Program* prog = new Program;
    if (!prog) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
    try {
        Compiler c(*prog, pattern, WLen(pattern), flags, resolver, user);
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
    return MatchImpl(str, len, ctx, start, false, false);
}

bool CRegexpW::MatchExact(const wchar_t* str, CRegexpContext& ctx) const
{
    return MatchImpl(str, -1, ctx, 0, true, false);
}

bool CRegexpW::MatchExact(const wchar_t* str, int len, CRegexpContext& ctx) const
{
    return MatchImpl(str, len, ctx, 0, true, false);
}

/* exact: the match must span from start to the end of the subject.
   forceGlobal: continue after the previous match in ctx even if GLOBAL is not set */
bool CRegexpW::MatchImpl(const wchar_t* str, int len, CRegexpContext& ctx, int start, bool exact, bool forceGlobal) const
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
        if (m_prog->global || forceGlobal) {
            from = ctx.m_next;
            if (ctx.m_lastEmpty) notEmpty = from;
        }
    }
    ctx.m_next = 0;
    ctx.m_lastEmpty = 0;
    if (from > len) return false;
    if (m_prog->notEmpty == 2 && notEmpty < 0) notEmpty = from;   /* (*NOTEMPTY_ATSTART) */

    if (len > (int)((0xFFFFFFFFUL - m_stepBase) / (m_stepPer ? m_stepPer : 1UL))) limit = 0xFFFFFFFFUL;
    else limit = m_stepBase + m_stepPer * (unsigned long)len;
    if (m_prog->limitMatch && m_prog->limitMatch < limit) limit = m_prog->limitMatch;   /* (*LIMIT_MATCH=n) */

    if (!ctx.m_work) {
        ctx.m_work = new Work;
        if (!ctx.m_work) throw CRegexpException(CRegexpException::ERR_MEMORY, -1, "out of memory");
    }
    {
        Matcher m(*m_prog, *ctx.m_work, str, len, from, notEmpty, limit);
        if (exact) m.SetExact();
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
    return ReplaceImpl(str, len, repl, out, m_prog && m_prog->global, -1, 0, 0);
}

int CRegexpW::Replace(const wchar_t* str, int len, const wchar_t* repl, CRegexpString& out,
                      int maxCount, int* lastStart, int* lastEnd) const
{
    return ReplaceImpl(str, len, repl, out, true, maxCount, lastStart, lastEnd);
}

int CRegexpW::ReplaceImpl(const wchar_t* str, int len, const wchar_t* repl, CRegexpString& out,
                          bool all, int maxCount, int* lastStart, int* lastEnd) const
{
    CRegexpContext ctx;
    int last = 0, count = 0;
    if (lastStart) *lastStart = -1;
    if (lastEnd) *lastEnd = -1;
    if (!m_prog) throw CRegexpException(CRegexpException::ERR_NOT_COMPILED, -1, "pattern is not compiled");
    if (len < 0) len = WLen(str);
    out.clear();
    while (maxCount < 0 || count < maxCount) {
        int ms, me, rs;
        bool ok = MatchImpl(str, len, ctx, all ? -1 : 0, false, all);
        if (!ok) break;
        ms = ctx.GetStart(0);
        me = ctx.GetEnd(0);
        if (ms < last) ms = last;
        if (me < ms) me = ms;
        out.append(str + last, ms - last);
        rs = out.size();
        ExpandTemplate(out, repl, str, len, ctx, *this);
        if (lastStart) *lastStart = rs;
        if (lastEnd) *lastEnd = out.size();
        last = me;
        ++count;
        if (!all) break;
    }
    out.append(str + last, len - last);
    return count;
}
