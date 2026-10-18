/*
 * uka_regexp.h - a small backtracking regular expression engine for wchar_t strings.
 *
 * Two files only (uka_regexp.h / uka_regexp.cpp), no external libraries, no STL.
 * Written in plain C++98 so that it builds with Visual C++ 6.0 and old GCC as well as
 * current compilers.  Exceptions must be enabled (/GX on VC6).
 *
 * Quick tour:
 *
 *     CRegexpW re(L"(\\d+)-(\\d+)");          // throws CRegexpException on a bad pattern
 *     CRegexpContext ctx;                    // one per thread; holds the match result
 *     if (re.Match(L"tel 03-1234", ctx)) {
 *         int s = ctx.GetStart(1), e = ctx.GetEnd(1);   // offsets of group 1
 *     }
 *
 *     CRegexpString out;
 *     re.Replace(L"03-1234", L"$2-$1", out);           // out.c_str() == L"1234-03"
 *
 * See README.md for the supported syntax.
 */
#ifndef UKA_REGEXP_H
#define UKA_REGEXP_H

#include <stddef.h>

namespace UkaRegexpImpl {
struct Program;
struct Work;
}

/* Thrown when a pattern cannot be compiled or when the backtracking step limit is hit. */
class CRegexpException {
public:
    enum {
        ERR_SYNTAX = 1,       /* bad pattern; GetPosition() is the offset in the pattern */
        ERR_STEP_LIMIT = 2,   /* too many backtracks while matching */
        ERR_NOT_COMPILED = 3, /* Match() called before a successful Compile() */
        ERR_MEMORY = 4
    };
    CRegexpException(int code, int position, const char* message);
    int GetCode() const { return m_code; }
    int GetPosition() const { return m_pos; }     /* -1 when not applicable */
    const char* what() const { return m_msg; }    /* English description */
private:
    int m_code;
    int m_pos;
    char m_msg[96];
};

/* Minimal growable wide string used for the output of Replace(). Always NUL terminated. */
class CRegexpString {
public:
    CRegexpString();
    ~CRegexpString();
    const wchar_t* c_str() const;
    int size() const { return m_len; }
    void clear();
    void append(const wchar_t* s, int n);
    void push_back(wchar_t c);
private:
    CRegexpString(const CRegexpString&);
    CRegexpString& operator=(const CRegexpString&);
    void Reserve(int n);
    wchar_t* m_buf;
    int m_len;
    int m_cap;
};

/*
 * Holds the result of the last Match() and the working memory of the matcher.
 * A compiled CRegexpW can be shared by several threads as long as every thread
 * uses its own CRegexpContext.
 */
class CRegexpContext {
public:
    CRegexpContext();
    ~CRegexpContext();

    int GetGroupCount() const;           /* number of groups (not counting group 0) of the last match; 0 if none */
    bool IsMatched(int group) const;     /* did the group take part in the last match? (0 = whole match) */
    int GetStart(int group) const;       /* offset of the first character, or -1 */
    int GetEnd(int group) const;         /* offset after the last character, or -1 */
    void Reset();                        /* forget the previous match (restarts a GLOBAL scan at offset 0) */

private:
    friend class CRegexpW;
    CRegexpContext(const CRegexpContext&);
    CRegexpContext& operator=(const CRegexpContext&);
    void SetResult(int ngroups, const int* caps);
    void Clear();

    int* m_caps;        /* start,end pairs for groups 0..m_ngroups */
    int m_ngroups;      /* -1: no match */
    int m_capsCap;
    int m_next;         /* GLOBAL: where the next search starts */
    int m_lastEmpty;    /* GLOBAL: the previous match was empty */
    UkaRegexpImpl::Work* m_work;
};

class CRegexpW {
public:
    enum {
        IGNORECASE = 1,   /* (?i) */
        MULTILINE  = 2,   /* (?m) ^ and $ match at line boundaries */
        SINGLELINE = 4,   /* (?s) . matches a newline too */
        EXTENDED   = 8,   /* (?x) ignore white space and #comments in the pattern */
        GLOBAL     = 16,  /* (?g) Match() continues after the previous match, Replace() replaces all */

        /* what counts as a newline for . ^ $ \Z (like PCRE2_NEWLINE_*); the default is LF only.
           A (*CRLF)-style verb at the start of the pattern overrides this. */
        NEWLINE_CR      = 32,
        NEWLINE_CRLF    = 64,
        NEWLINE_ANYCRLF = 96,   /* CR, LF or CRLF */
        NEWLINE_ANY     = 128,  /* CR, LF, CRLF, VT, FF, NEL, LS, PS */
        BSR_ANYCRLF     = 256   /* \R matches only CR, LF and CRLF (default: all Unicode line breaks) */
    };

    CRegexpW();
    explicit CRegexpW(const wchar_t* pattern, unsigned int flags = 0);   /* may throw CRegexpException */
    ~CRegexpW();

    /* Compile a pattern. Throws CRegexpException(ERR_SYNTAX) on failure; the object is left unchanged then. */
    void Compile(const wchar_t* pattern, unsigned int flags = 0);
    bool IsCompiled() const { return m_prog != 0; }

    int GetGroupCount() const;                        /* number of capture groups, group 0 not counted */
    int GetGroupNumber(const wchar_t* name) const;    /* number of a named group, or -1 */

    /*
     * Search for the first match.  The result is stored in ctx.
     *   start < 0 : search from offset 0, or - when GLOBAL is set - from where the previous
     *               match in this ctx ended (an empty match is never repeated at the same place).
     *   start >= 0: search from this offset.
     * \G matches at the offset the search started from.
     * Throws CRegexpException(ERR_STEP_LIMIT) when the backtrack limit is exceeded.
     */
    bool Match(const wchar_t* str, CRegexpContext& ctx) const;                         /* str is NUL terminated */
    bool Match(const wchar_t* str, int len, CRegexpContext& ctx, int start = -1) const;

    /*
     * Replace the first match (all matches when GLOBAL is set) by repl, which may contain
     * $1 ${name} $& $` $' $+ $_ $$ .  The result replaces the contents of out.
     * Returns the number of replacements.
     */
    int Replace(const wchar_t* str, const wchar_t* repl, CRegexpString& out) const;
    int Replace(const wchar_t* str, int len, const wchar_t* repl, CRegexpString& out) const;

    /*
     * Backtrack limit per Match() call: base + perChar * length of the subject.
     * Defaults: 1000000 + 256 * length.
     */
    void SetStepLimit(unsigned long base, unsigned long perChar);

private:
    CRegexpW(const CRegexpW&);
    CRegexpW& operator=(const CRegexpW&);

    UkaRegexpImpl::Program* m_prog;
    unsigned long m_stepBase;
    unsigned long m_stepPer;
};

#endif /* UKA_REGEXP_H */
