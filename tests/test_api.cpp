// API level tests: Replace(), contexts, GLOBAL iteration, limits, exceptions, big inputs.
#include "../uka_regexp.h"
#include <stdio.h>
#include <string.h>
#include <wchar.h>

static int g_failed = 0, g_total = 0;

#define CHECK(cond) do { ++g_total; if (!(cond)) { ++g_failed; printf("FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond); } } while (0)

static bool Repl(const wchar_t* pat, unsigned int flags, const wchar_t* str, const wchar_t* repl, const wchar_t* expected, int count = -1)
{
    CRegexpW re(pat, flags);
    CRegexpString out;
    int n = re.Replace(str, repl, out);
    bool ok = wcscmp(out.c_str(), expected) == 0 && (count < 0 || n == count);
    if (!ok) printf("  Replace(/%ls/, \"%ls\", \"%ls\") = \"%ls\" (%d), expected \"%ls\"\n", pat, str, repl, out.c_str(), n, expected);
    return ok;
}

static void TestReplace()
{
    CHECK(Repl(L"(\\d+)-(\\d+)", 0, L"tel 03-1234!", L"$2-$1", L"tel 1234-03!", 1));
    CHECK(Repl(L"a", 0, L"aaa", L"b", L"baa", 1));
    CHECK(Repl(L"a", CRegexpW::GLOBAL, L"aaa", L"b", L"bbb", 3));
    CHECK(Repl(L"x", 0, L"abc", L"y", L"abc", 0));
    CHECK(Repl(L"x*", CRegexpW::GLOBAL, L"abc", L"-", L"-a-b-c-"));
    CHECK(Repl(L"", CRegexpW::GLOBAL, L"ab", L"-", L"-a-b-"));
    CHECK(Repl(L"\\d*", CRegexpW::GLOBAL, L"a12b", L"<$&>", L"<>a<12><>b<>"));
    CHECK(Repl(L"(?<y>\\d{4})-(?<m>\\d\\d)", 0, L"2024-05", L"${m}/${y}", L"05/2024"));
    CHECK(Repl(L"(?<y>\\d{4})-(?<m>\\d\\d)", 0, L"2024-05", L"${2}/${1}", L"05/2024"));
    CHECK(Repl(L"b", 0, L"abc", L"[$`|$&|$']", L"a[a|b|c]c"));
    CHECK(Repl(L"b", 0, L"abc", L"[$_]", L"a[abc]c"));
    CHECK(Repl(L"b", 0, L"abc", L"$$1", L"a$1c"));
    CHECK(Repl(L"(a)|(b)", CRegexpW::GLOBAL, L"ab", L"<$+>", L"<a><b>"));
    CHECK(Repl(L"(a)(b)?", 0, L"a", L"[$2]", L"[]"));
    CHECK(Repl(L"(a)", 0, L"a", L"$10", L"a0"));        // $1 followed by '0'
    CHECK(Repl(L"(a)", 0, L"a", L"$5", L"$5"));         // no such group: kept
    CHECK(Repl(L"(a)", 0, L"a", L"${x}", L"${x}"));
    CHECK(Repl(L"(a)", 0, L"a", L"$", L"$"));
    CHECK(Repl(L"(a)", 0, L"a", L"$0$0", L"aa"));
    CHECK(Repl(L"foo\\Kbar", 0, L"foobar", L"X", L"fooX"));
    CHECK(Repl(L"(?<=a)b", CRegexpW::GLOBAL, L"abab", L"X", L"aXaX"));
    CHECK(Repl(L"\\s+", CRegexpW::GLOBAL, L"a  b\t\nc", L" ", L"a b c"));
    CHECK(Repl(L"あ", CRegexpW::GLOBAL, L"あいあ", L"ア", L"アいア"));
    CHECK(Repl(L"(?g)a", 0, L"aa", L"b", L"bb"));   // (?g) turns the global mode on
    CHECK(Repl(L"^", CRegexpW::GLOBAL | CRegexpW::MULTILINE, L"a\nb", L"> ", L"> a\n> b"));
}

static void TestMatchApi()
{
    CRegexpW re(L"(a)(b)?");
    CRegexpContext ctx;
    CHECK(re.GetGroupCount() == 2);
    CHECK(re.Match(L"xxac", ctx));
    CHECK(ctx.GetGroupCount() == 2);
    CHECK(ctx.GetStart(0) == 2 && ctx.GetEnd(0) == 3);
    CHECK(ctx.IsMatched(1) && ctx.GetStart(1) == 2 && ctx.GetEnd(1) == 3);
    CHECK(!ctx.IsMatched(2) && ctx.GetStart(2) == -1 && ctx.GetEnd(2) == -1);
    CHECK(ctx.GetStart(3) == -1 && ctx.GetStart(-1) == -1);
    CHECK(!re.Match(L"xyz", ctx));
    CHECK(!ctx.IsMatched(0) && ctx.GetGroupCount() == 0);

    // explicit start offset and length
    CRegexpW re2(L"a");
    CHECK(re2.Match(L"aXa", 3, ctx, 1) && ctx.GetStart(0) == 2);
    CHECK(!re2.Match(L"aXa", 3, ctx, 3));
    CHECK(!re2.Match(L"aXa", 3, ctx, 4));
    CHECK(re2.Match(L"aXa", 1, ctx) && ctx.GetEnd(0) == 1);          // length given: the rest is invisible
    CHECK(!re2.Match(L"bXa", 2, ctx));
    CHECK(CRegexpW(L"a$").Match(L"ab", 1, ctx));                      // $ sees the length, not the NUL

    // \b and ^ use the whole string even when starting in the middle
    CRegexpW re3(L"^b");
    CHECK(!re3.Match(L"ab", 2, ctx, 1));
    CRegexpW re4(L"\\bb");
    CHECK(!re4.Match(L"ab", 2, ctx, 1));

    // \G without GLOBAL: where the search starts
    CRegexpW re5(L"\\Gb");
    CHECK(re5.Match(L"abb", 3, ctx, 1) && ctx.GetStart(0) == 1);
    CHECK(!re5.Match(L"abb", 3, ctx, 0));

    // GLOBAL: the context remembers where the previous match ended
    CRegexpW g(L"\\d+", CRegexpW::GLOBAL);
    CRegexpContext gc;
    const wchar_t* s = L"a1b22c333";
    int starts[8], n = 0;
    while (g.Match(s, gc) && n < 8) starts[n++] = gc.GetStart(0);
    CHECK(n == 3 && starts[0] == 1 && starts[1] == 3 && starts[2] == 6);
    CHECK(g.Match(s, gc) && gc.GetStart(0) == 1);                      // after a failure it starts over
    gc.Reset();
    CHECK(g.Match(s, gc) && gc.GetStart(0) == 1);
    CHECK(g.Match(s, gc) && gc.GetStart(0) == 3);

    // named groups
    CRegexpW named(L"(?<year>\\d+)-(?'mon'\\d+)-(?P<day>\\d+)");
    CHECK(named.GetGroupNumber(L"year") == 1 && named.GetGroupNumber(L"mon") == 2 && named.GetGroupNumber(L"day") == 3);
    CHECK(named.GetGroupNumber(L"nope") == -1);
    CRegexpW jp(L"(?<名前>\\p{L}+)");
    CHECK(jp.GetGroupNumber(L"名前") == 1);

    // flags
    CHECK(CRegexpW(L"abc", CRegexpW::IGNORECASE).Match(L"xABCx", ctx));
    CHECK(CRegexpW(L"^b", CRegexpW::MULTILINE).Match(L"a\nb", ctx));
    CHECK(CRegexpW(L"a.b", CRegexpW::SINGLELINE).Match(L"a\nb", ctx));
    CHECK(!CRegexpW(L"a.b").Match(L"a\nb", ctx));
    CHECK(CRegexpW(L"a b", CRegexpW::EXTENDED).Match(L"ab", ctx));

    // embedded NUL: only with an explicit length
    wchar_t nul[4] = { L'a', 0, L'b', 0 };
    CHECK(CRegexpW(L"a.b", CRegexpW::SINGLELINE).Match(nul, 3, ctx));
    CRegexpString out;
    CHECK(CRegexpW(L"b").Replace(nul, 3, L"X", out) == 1 && out.size() == 3 && out.c_str()[2] == L'X');
}

static void TestNewlineFlags()
{
    CRegexpContext ctx;
    // default: LF only
    CHECK(CRegexpW(L"^b", CRegexpW::MULTILINE).Match(L"a\nb", ctx) && ctx.GetStart(0) == 2);
    CHECK(!CRegexpW(L"^b", CRegexpW::MULTILINE).Match(L"a\rb", ctx));   // a lone CR is no line break
    CHECK(CRegexpW(L"a.b").Match(L"a\rb", ctx));

    // CRLF text: $ and ^ see the CRLF pair, . does not swallow the CR of a CRLF
    CRegexpW crlf(L"^(.*)$", CRegexpW::MULTILINE | CRegexpW::NEWLINE_CRLF | CRegexpW::GLOBAL);
    CRegexpContext c2;
    const wchar_t* text = L"one\r\ntwo\r\nthree";
    int ends[8], n = 0;
    while (crlf.Match(text, c2) && n < 8) ends[n++] = c2.GetEnd(1);
    CHECK(n == 3 && ends[0] == 3 && ends[1] == 8 && ends[2] == 15);

    CRegexpString out;
    CHECK(CRegexpW(L"^", CRegexpW::MULTILINE | CRegexpW::NEWLINE_ANYCRLF | CRegexpW::GLOBAL).Replace(L"a\rb\r\nc\nd", L"> ", out) == 4);
    CHECK(wcscmp(out.c_str(), L"> a\r> b\r\n> c\n> d") == 0);

    CHECK(CRegexpW(L"a$", CRegexpW::MULTILINE | CRegexpW::NEWLINE_ANY).Match(L"a\x2028" L"b", ctx));
    CHECK(!CRegexpW(L"a.b", CRegexpW::NEWLINE_ANY).Match(L"a\x85" L"b", ctx));
    CHECK(!CRegexpW(L"a.b", CRegexpW::NEWLINE_CR).Match(L"a\rb", ctx));
    CHECK(CRegexpW(L"a.b", CRegexpW::NEWLINE_CR).Match(L"a\nb", ctx));
    CHECK(CRegexpW(L"(*LF)a.b", CRegexpW::NEWLINE_CRLF).Match(L"a\rb", ctx) == true);   // the verb wins over the flag
    CHECK(CRegexpW(L"\\R").Match(L"\x2028", ctx));
    CHECK(!CRegexpW(L"\\R", CRegexpW::BSR_ANYCRLF).Match(L"\x2028", ctx));
    CHECK(CRegexpW(L"\\R", CRegexpW::BSR_ANYCRLF).Match(L"a\r\nb", ctx) && ctx.GetEnd(0) == 3);
}

struct ResolveLog { int calls; };

static const wchar_t* ResolverText(const wchar_t* name)
{
    if (wcscmp(name, L"d4") == 0) return L"\\d{4}";
    if (wcscmp(name, L"d2") == 0) return L"\\d\\d";
    if (wcscmp(name, L"date") == 0) return L"(?&d4)-(?&d2)-(?&d2)";
    if (wcscmp(name, L"paren") == 0) return L"\\((?:[^()]++|(?&paren))*\\)";
    if (wcscmp(name, L"loop") == 0) return L"a(?&loop)?";
    if (wcscmp(name, L"w") == 0) return L"abc";
    if (wcscmp(name, L"bad") == 0) return L"(";
    if (wcscmp(name, L"empty") == 0) return L"";
    return 0;
}

static bool TestResolver(const wchar_t* name, CRegexpString& pattern, void* user)
{
    const wchar_t* text = ResolverText(name);
    ((ResolveLog*)user)->calls++;
    if (!text) return false;
    pattern.append(text, (int)wcslen(text));
    return true;
}

struct ThrowingResolver { static bool Proc(const wchar_t*, CRegexpString&, void*) { throw 42; } };

static bool CompileFails(const wchar_t* pat, CRegexpResolveProc proc, ResolveLog* log, int* pos = 0, char* msg = 0)
{
    try {
        CRegexpW re(pat, 0, proc, log);
    } catch (CRegexpException& e) {
        if (pos) *pos = e.GetPosition();
        if (msg) { const char* w = e.what(); int k; for (k = 0; k < 95 && w[k]; ++k) msg[k] = w[k]; msg[k] = 0; }
        return e.GetCode() == CRegexpException::ERR_SYNTAX;
    }
    return false;
}

static void TestResolver()
{
    ResolveLog log = { 0 };
    CRegexpContext ctx;
    CRegexpW date(L"^(?&date)$", 0, TestResolver, &log);
    CHECK(log.calls == 3);                                   // date, d4, d2: each name once
    CHECK(date.Match(L"2024-05-17", ctx) && ctx.GetEnd(0) == 10);
    CHECK(!date.Match(L"2024-5-17", ctx));
    CHECK(date.GetGroupNumber(L"date") == 1 && date.GetGroupNumber(L"d4") == 2 && date.GetGroupCount() == 3);
    CHECK(!ctx.IsMatched(1));                                // groups of a subroutine call are restored on return

    log.calls = 0;
    CRegexpW paren(L"x(?&paren)y", 0, TestResolver, &log);
    CHECK(paren.Match(L"..x(a(b)c)y", ctx) && ctx.GetStart(0) == 2 && ctx.GetEnd(0) == 11);
    CHECK(!paren.Match(L"x(a(b)cy", ctx));
    CHECK(log.calls == 1);

    CHECK(CRegexpW(L"^(?P>d2)-(?R<d2>)$", 0, TestResolver, &log).Match(L"12-34", ctx));
    CHECK(CRegexpW(L"^(?&loop)$", 0, TestResolver, &log).Match(L"aaa", ctx));

    // \g<name> and \g'name' are subroutine calls too, \g{name} is a back reference and is never resolved
    log.calls = 0;
    CHECK(CRegexpW(L"^\\g<d2>-\\g'd2'$", 0, TestResolver, &log).Match(L"12-34", ctx) && log.calls == 1);
    CHECK(CompileFails(L"\\g{d2}", TestResolver, &log));

    // a name the pattern defines itself is not asked for
    log.calls = 0;
    CHECK(CRegexpW(L"(?<d4>\\d\\d)(?&d4)", 0, TestResolver, &log).Match(L"1234", ctx) && log.calls == 0);

    // flags given to Compile() apply to the resolved pattern; inline options of the caller do not
    CHECK(CRegexpW(L"^(?&w)$", CRegexpW::IGNORECASE, TestResolver, &log).Match(L"ABC", ctx));
    CHECK(!CRegexpW(L"^(?i)(?&w)$", 0, TestResolver, &log).Match(L"ABC", ctx));

    // without a resolver, or when it does not know the name, or when its pattern is bad: a syntax error
    int pos = 0;
    char msg[96] = "";
    CHECK(CompileFails(L"(?&date)", 0, 0));
    CHECK(CompileFails(L"(?&nope)", TestResolver, &log, &pos, msg) && pos == 0 && strstr(msg, "nope") != 0);   // the message names it
    CHECK(CompileFails(L"a(?&bad)", TestResolver, &log, &pos, msg) && pos == -1 && strstr(msg, "bad") != 0);
    CHECK(CompileFails(L"(?1)", TestResolver, &log));         // only names are resolved
    CHECK(CompileFails(L"\\k<date>", TestResolver, &log));    // not a subroutine call
    CRegexpW plain;
    bool thrown = false;
    try { plain.Compile(L"(?&date)"); } catch (CRegexpException&) { thrown = true; }
    CHECK(thrown && !plain.IsCompiled());

    // an empty pattern is a valid (empty) subroutine
    CHECK(CRegexpW(L"^a(?&empty)b$", 0, TestResolver, &log).Match(L"ab", ctx));

    // an exception thrown by the resolver propagates and leaves the object as it was
    CRegexpW keep(L"a+");
    int caught = 0;
    try { keep.Compile(L"(?&x)", 0, ThrowingResolver::Proc, 0); } catch (int v) { caught = v; }
    CHECK(caught == 42 && keep.IsCompiled() && keep.Match(L"caab", ctx) && ctx.GetEnd(0) == 3);
}

static void TestDollar()
{
    CRegexpContext ctx;
    CHECK(CRegexpW(L"a$").Match(L"a\n", ctx));                                    // like PCRE: before the final newline
    CHECK(!CRegexpW(L"a$").Match(L"a\n\n", ctx));
    CHECK(!CRegexpW(L"a$", CRegexpW::DOLLAR_ENDONLY).Match(L"a\n", ctx));
    CHECK(CRegexpW(L"a$", CRegexpW::DOLLAR_ENDONLY).Match(L"a", ctx));
    CHECK(CRegexpW(L"a$", CRegexpW::DOLLAR_ENDONLY | CRegexpW::MULTILINE).Match(L"a\nb", ctx));   // ignored with MULTILINE
    CHECK(CRegexpW(L"a\\z").Match(L"a", ctx) && !CRegexpW(L"a\\z").Match(L"a\n", ctx));
    CHECK(CRegexpW(L"a$", CRegexpW::NEWLINE_CRLF).Match(L"a\r\n", ctx));
    CHECK(!CRegexpW(L"a$", CRegexpW::NEWLINE_CRLF).Match(L"a\n", ctx));
}

static void TestErrors()
{
    CRegexpW re;
    CRegexpContext ctx;
    CHECK(!re.IsCompiled());
    bool thrown = false;
    try { re.Match(L"a", ctx); } catch (CRegexpException& e) { thrown = e.GetCode() == CRegexpException::ERR_NOT_COMPILED; }
    CHECK(thrown);

    thrown = false;
    try { re.Compile(L"ab(cd"); } catch (CRegexpException& e) {
        thrown = e.GetCode() == CRegexpException::ERR_SYNTAX && e.GetPosition() == 2 && e.what()[0] != 0;
    }
    CHECK(thrown);
    CHECK(!re.IsCompiled());

    re.Compile(L"a+");
    CHECK(re.IsCompiled() && re.Match(L"caab", ctx) && ctx.GetEnd(0) == 3);
    thrown = false;
    try { re.Compile(L"("); } catch (CRegexpException&) { thrown = true; }
    CHECK(thrown && re.IsCompiled() && re.Match(L"aa", ctx));          // the old pattern survives a failed Compile

    thrown = false;
    try { CRegexpW bad(L"[a"); } catch (CRegexpException&) { thrown = true; }
    CHECK(thrown);

    // deep nesting is rejected instead of overflowing the C stack
    wchar_t deep[3001];
    int i;
    for (i = 0; i < 1500; ++i) { deep[i] = L'('; deep[3000 - i - 1] = L')'; }
    deep[3000] = 0;
    thrown = false;
    try { CRegexpW d(deep); } catch (CRegexpException&) { thrown = true; }
    CHECK(thrown);
}

static void TestLimits()
{
    CRegexpContext ctx;
    CRegexpW bad(L"(.*a){12}c");
    bool limit = false;
    try { bad.Match(L"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", ctx); }
    catch (CRegexpException& e) { limit = e.GetCode() == CRegexpException::ERR_STEP_LIMIT; }
    CHECK(limit);

    // the limit can be changed
    CRegexpW quad(L"\\w+@");
    static wchar_t big[60001];
    int i;
    for (i = 0; i < 60000; ++i) big[i] = L'a';
    big[60000] = 0;
    limit = false;
    try { quad.Match(big, ctx); } catch (CRegexpException&) { limit = true; }
    CHECK(limit);
    quad.SetStepLimit(0xFFFFFFFFUL, 0);
    for (i = 0; i < 3000; ++i) big[i] = L'a';
    big[3000] = 0;
    limit = false;
    try { CHECK(!quad.Match(big, ctx)); } catch (CRegexpException&) { limit = true; }
    CHECK(!limit);

    // normal patterns have plenty of room
    CRegexpW ok(L"\\w+@");
    for (i = 0; i < 2000; ++i) big[i] = L'a';
    big[2000] = L'@';
    big[2001] = 0;
    CHECK(ok.Match(big, ctx) && ctx.GetEnd(0) == 2001);
}

// long subjects must not overflow the C stack (the matcher uses its own stack)
static void TestLongInput()
{
    const int N = 2000000;
    wchar_t* s = new wchar_t[N + 2];
    int i;
    for (i = 0; i < N; ++i) s[i] = (i & 1) ? L'b' : L'a';
    s[N] = L'!';
    s[N + 1] = 0;
    CRegexpContext ctx;
    CHECK(CRegexpW(L"(?:a|b)*").Match(s, ctx) && ctx.GetEnd(0) == N);
    CHECK(CRegexpW(L"(a|b)+!").Match(s, ctx) && ctx.GetEnd(0) == N + 1);
    CHECK(CRegexpW(L"[ab]*!").Match(s, ctx) && ctx.GetEnd(0) == N + 1);
    CHECK(CRegexpW(L".*!").Match(s, ctx) && ctx.GetEnd(0) == N + 1);
    CHECK(CRegexpW(L"(?:ab)*?!").Match(s, ctx) && ctx.GetEnd(0) == N + 1);
    CHECK(CRegexpW(L"(?:ab){0,}!").Match(s, ctx) && ctx.GetEnd(0) == N + 1);
    CHECK(CRegexpW(L"\\bz|!").Match(s, ctx) && ctx.GetStart(0) == N);
    CHECK(CRegexpW(L"(?<=b)!").Match(s, ctx) && ctx.GetStart(0) == N);
    CHECK(CRegexpW(L"(?<=a+)!").Match(s, N + 1, ctx, N) == false);   // starts at the end: one lookbehind
    delete[] s;
}

static void TestMatchExact()
{
    CRegexpContext ctx;
    CHECK(CRegexpW(L"a+").MatchExact(L"aaa", ctx) && ctx.GetStart(0) == 0 && ctx.GetEnd(0) == 3);
    CHECK(!CRegexpW(L"a+").MatchExact(L"aaab", ctx));
    CHECK(!CRegexpW(L"a+").MatchExact(L"baaa", ctx));          // not searched: must start at 0
    CHECK(CRegexpW(L"a|ab").MatchExact(L"ab", ctx));           // backtracks to the alternative that reaches the end
    CHECK(CRegexpW(L"(a+)(b*)").MatchExact(L"aab", ctx) && ctx.GetEnd(1) == 2 && ctx.GetEnd(2) == 3);
    CHECK(CRegexpW(L"x*").MatchExact(L"", ctx) && ctx.GetEnd(0) == 0);
    CHECK(!CRegexpW(L"x*").MatchExact(L"y", ctx));
    CHECK(CRegexpW(L"a.c", CRegexpW::GLOBAL).MatchExact(L"abc", ctx));   // GLOBAL is ignored
    CHECK(CRegexpW(L"a.c", CRegexpW::GLOBAL).MatchExact(L"abc", ctx));   // ... also for the second call
    CHECK(CRegexpW(L"b").MatchExact(L"abc", 3, ctx) == false);
    CHECK(CRegexpW(L"abc").MatchExact(L"abcdef", 3, ctx));               // length given: the subject ends at 3
}

static void TestReplaceCount()
{
    CRegexpString out;
    int rs, re;
    CRegexpW a(L"a");
    CHECK(a.Replace(L"aaaa", -1, L"b", out, 2) == 2 && wcscmp(out.c_str(), L"bbaa") == 0);   // not GLOBAL, but 2 are replaced
    CHECK(a.Replace(L"aaaa", -1, L"b", out, -1) == 4 && wcscmp(out.c_str(), L"bbbb") == 0);
    CHECK(a.Replace(L"aaaa", -1, L"b", out, 0) == 0 && wcscmp(out.c_str(), L"aaaa") == 0);
    CHECK(a.Replace(L"xyz", -1, L"b", out, 3, &rs, &re) == 0 && rs == -1 && re == -1);
    CHECK(a.Replace(L"xaay", -1, L"[$&]", out, -1, &rs, &re) == 2 && wcscmp(out.c_str(), L"x[a][a]y") == 0 && rs == 4 && re == 7);
    CHECK(a.Replace(L"xaay", -1, L"Q", out, 1, &rs, &re) == 1 && wcscmp(out.c_str(), L"xQay") == 0 && rs == 1 && re == 2);
    CHECK(CRegexpW(L"x*").Replace(L"abc", -1, L"-", out, 2) == 2 && wcscmp(out.c_str(), L"-a-bc") == 0);   // empty matches advance
}

// \K inside an assertion is an error (as PCRE2 10.38+); one reached through a subroutine call
// must still give start <= end so that GLOBAL iteration advances
static void TestKeepInAssertion()
{
    static const wchar_t* const bad[] = { L"(?=a\\K)", L"(?<=a\\K)", L"(?!a\\K)", L"(?<!a\\K)", L"(*pla:a\\K)" };
    int i, count = 0, prevEnd = 0;
    bool thrown;
    for (i = 0; i < (int)(sizeof(bad) / sizeof(bad[0])); ++i) {
        thrown = false;
        try { CRegexpW re(bad[i]); } catch (CRegexpException& e) { thrown = e.GetCode() == CRegexpException::ERR_SYNTAX; }
        CHECK(thrown);
    }

    CRegexpW re(L"(?=(?&k))a(?(DEFINE)(?<k>a\\K))", CRegexpW::GLOBAL);
    CRegexpContext ctx;
    while (count < 10 && re.Match(L"aa", 2, ctx)) {
        CHECK(ctx.GetStart(0) <= ctx.GetEnd(0) && ctx.GetStart(0) >= prevEnd);
        prevEnd = ctx.GetEnd(0);
        ++count;
    }
    CHECK(count > 0 && count < 10);
}

#define RUN(t) do { try { t(); } catch (CRegexpException& e) { ++g_failed; printf("FAIL: %s threw: %s\n", #t, e.what()); } } while (0)

static void TestUnicodeFlag()
{
    CRegexpContext ctx;
    {
        CRegexpW off(L"\\d+\\w+");   // off by default: ASCII only
        CHECK(!off.Match(L"１２あ", ctx));
    }
    {
        CRegexpW on(L"\\d+\\w+", CRegexpW::UCP);
        CHECK(on.Match(L"１２あ", ctx) && ctx.GetStart(0) == 0 && ctx.GetEnd(0) == 3);
    }
    {
        CRegexpW verb(L"(*UCP)\\bx\\u3042");
        CHECK(!verb.Match(L"あxあ", ctx));
        CHECK(verb.Match(L"あ xあ", ctx));
    }
    CHECK(Repl(L"\\s", CRegexpW::UCP | CRegexpW::GLOBAL, L"a　b c", L"_", L"a_b_c", 2));
    CHECK(Repl(L"\\s", CRegexpW::GLOBAL, L"a　b c", L"_", L"a　b_c", 1));
    CHECK(Repl(L"a{,2}", CRegexpW::GLOBAL, L"aaa", L"-", L"---", 3));   // a{,2} is a{0,2}
}

// a character beyond the BMP is one character: a surrogate pair where wchar_t is 16 bit
static int PutCp(wchar_t* d, unsigned long cp)
{
    if (sizeof(wchar_t) == 2 && cp > 0xFFFF) {
        cp -= 0x10000;
        d[0] = (wchar_t)(0xD800 + (cp >> 10));
        d[1] = (wchar_t)(0xDC00 + (cp & 0x3FF));
        return 2;
    }
    d[0] = (wchar_t)cp;
    return 1;
}

static void TestSurrogatePairs()
{
    wchar_t subj[16];
    int units = (int)(sizeof(wchar_t) == 2 ? 2 : 1);   // wchar_t units of one emoji
    int n = 0;
    CRegexpContext ctx;
    subj[n++] = L'a';
    n += PutCp(subj + n, 0x1F600);
    subj[n++] = L'b';
    subj[n] = 0;

    {
        CRegexpW re(L".", CRegexpW::GLOBAL);   // three characters, never half of the emoji
        int count = 0, expectStart[3];
        expectStart[0] = 0; expectStart[1] = 1; expectStart[2] = 1 + units;
        while (count < 5 && re.Match(subj, n, ctx)) {
            CHECK(count < 3 && ctx.GetStart(0) == expectStart[count]);
            CHECK(ctx.GetEnd(0) == (count == 1 ? 1 + units : expectStart[count] + 1));
            ++count;
        }
        CHECK(count == 3);
    }
    {
        CRegexpW re(L"x*", CRegexpW::GLOBAL);   // empty matches before a, before b ... but not inside the emoji
        CRegexpString out;
        CHECK(re.Replace(subj, n, L"-", out) == 4);
        CHECK(out.size() == 4 + n);
    }
    {
        CRegexpW re(L"a(.)b");
        CHECK(re.Match(subj, n, ctx));
        CHECK(ctx.GetStart(1) == 1 && ctx.GetEnd(1) == 1 + units);
        CHECK(re.MatchExact(subj, n, ctx));
    }
    {
        CRegexpW re(L"^.{3}$");
        CHECK(re.Match(subj, n, ctx));
        CRegexpW re2(L"(?<=a.)b");
        CHECK(re2.Match(subj, n, ctx) && ctx.GetStart(0) == 1 + units);
        CRegexpW re3(L"a.*?b");
        CHECK(re3.Match(subj, n, ctx) && ctx.GetEnd(0) == n);
    }
    {
        wchar_t pat[16];
        int m = 0;
        pat[m++] = L'[';
        m += PutCp(pat + m, 0x1F600);
        pat[m++] = L'-';
        m += PutCp(pat + m, 0x1F64F);
        pat[m++] = L']';
        pat[m++] = L'+';
        pat[m] = 0;
        CRegexpW re(pat);   // [<U+1F600>-<U+1F64F>]+ written with the characters themselves
        CHECK(re.Match(subj, n, ctx) && ctx.GetStart(0) == 1 && ctx.GetEnd(0) == 1 + units);
    }
    if (sizeof(wchar_t) == 2) {   // a lone surrogate is a character of its own
        wchar_t lone[3];
        lone[0] = 0xD83D;
        lone[1] = L'a';
        lone[2] = 0;
        CRegexpW re(L"^..$");
        CHECK(re.Match(lone, 2, ctx));
    }
}

int main()
{
    RUN(TestReplace);
    RUN(TestMatchApi);
    RUN(TestMatchExact);
    RUN(TestReplaceCount);
    RUN(TestNewlineFlags);
    RUN(TestDollar);
    RUN(TestResolver);
    RUN(TestErrors);
    RUN(TestKeepInAssertion);
    RUN(TestUnicodeFlag);
    RUN(TestSurrogatePairs);
    RUN(TestLimits);
    RUN(TestLongInput);
    printf("%d checks, %d failed\n", g_total, g_failed);
    return g_failed ? 1 : 0;
}
