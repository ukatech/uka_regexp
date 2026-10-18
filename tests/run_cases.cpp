// Data driven test runner.
//
//   run_cases FILE            print "<line number>\t<result>" for every case (used for the Perl comparison)
//   run_cases --verify FILE   compare with the 4th column of every case, report mismatches, exit 1 on any
//
// Case line (tab separated):  flags <TAB> pattern <TAB> subject [<TAB> expected]
//   flags   i m s x u = IGNORECASE MULTILINE SINGLELINE EXTENDED UNICODE, g = GLOBAL (report every match)
//   pattern the regular expression, "<LF>" stands for a line feed
//   subject the subject; \n \t \r \\ \xHH \x{H..} are decoded
//   result  per match "s-e" for every group (group 0 first, "-" if unmatched) separated by blanks;
//           matches separated by ";"; NOMATCH, ERR (bad pattern) or LIMIT (step limit)
// Lines starting with # and empty lines are ignored.
#include "../uka_regexp.h"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <string>
#include <vector>

static std::wstring Utf8ToWide(const std::string& s)
{
    std::wstring w;
    size_t i = 0;
    while (i < s.size()) {
        unsigned char c = (unsigned char)s[i];
        unsigned long cp;
        int extra;
        if (c < 0x80) { cp = c; extra = 0; }
        else if (c < 0xE0) { cp = c & 0x1F; extra = 1; }
        else if (c < 0xF0) { cp = c & 0x0F; extra = 2; }
        else { cp = c & 0x07; extra = 3; }
        ++i;
        while (extra-- > 0 && i < s.size()) { cp = (cp << 6) | ((unsigned char)s[i] & 0x3F); ++i; }
        if (sizeof(wchar_t) == 2 && cp > 0xFFFF) {
            cp -= 0x10000;
            w.push_back((wchar_t)(0xD800 + (cp >> 10)));
            w.push_back((wchar_t)(0xDC00 + (cp & 0x3FF)));
        } else {
            w.push_back((wchar_t)cp);
        }
    }
    return w;
}

static int Hex(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

// decode escapes of the subject (still UTF-8 text) into a wide string
static std::wstring DecodeSubject(const std::string& s)
{
    std::string out;
    size_t i = 0;
    while (i < s.size()) {
        if (s[i] == '\\' && i + 1 < s.size()) {
            char c = s[i + 1];
            i += 2;
            if (c == 'n') out += '\n';
            else if (c == 't') out += '\t';
            else if (c == 'r') out += '\r';
            else if (c == '\\') out += '\\';
            else if (c == 'x') {
                unsigned long v = 0;
                if (i < s.size() && s[i] == '{') {
                    ++i;
                    while (i < s.size() && s[i] != '}') { v = v * 16 + Hex(s[i]); ++i; }
                    ++i;
                } else {
                    int n = 0;
                    while (n < 2 && i < s.size() && Hex(s[i]) >= 0) { v = v * 16 + Hex(s[i]); ++i; ++n; }
                }
                // encode as UTF-8 so that Utf8ToWide can finish the job
                if (v < 0x80) out += (char)v;
                else if (v < 0x800) { out += (char)(0xC0 | (v >> 6)); out += (char)(0x80 | (v & 0x3F)); }
                else if (v < 0x10000) { out += (char)(0xE0 | (v >> 12)); out += (char)(0x80 | ((v >> 6) & 0x3F)); out += (char)(0x80 | (v & 0x3F)); }
                else { out += (char)(0xF0 | (v >> 18)); out += (char)(0x80 | ((v >> 12) & 0x3F)); out += (char)(0x80 | ((v >> 6) & 0x3F)); out += (char)(0x80 | (v & 0x3F)); }
            } else { out += '\\'; out += c; }
        } else {
            out += s[i++];
        }
    }
    return Utf8ToWide(out);
}

static std::string FormatMatch(const CRegexpW& re, const CRegexpContext& ctx)
{
    std::string r;
    int n = re.GetGroupCount(), g;
    for (g = 0; g <= n; ++g) {
        char buf[64];
        if (g) r += ' ';
        if (ctx.IsMatched(g)) sprintf(buf, "%d-%d", ctx.GetStart(g), ctx.GetEnd(g));
        else strcpy(buf, "-");
        r += buf;
    }
    return r;
}

static std::string RunCase(const std::string& flags, const std::string& pat, const std::string& subj)
{
    unsigned int f = 0;
    bool all = false;
    size_t i;
    for (i = 0; i < flags.size(); ++i) {
        switch (flags[i]) {
        case 'i': f |= CRegexpW::IGNORECASE; break;
        case 'm': f |= CRegexpW::MULTILINE; break;
        case 's': f |= CRegexpW::SINGLELINE; break;
        case 'x': f |= CRegexpW::EXTENDED; break;
        case 'u': f |= CRegexpW::UNICODE; break;
        case 'g': all = true; f |= CRegexpW::GLOBAL; break;
        default: break;
        }
    }
    std::string p2 = pat;
    size_t k;
    while ((k = p2.find("<LF>")) != std::string::npos) p2.replace(k, 4, "\n");
    std::wstring wp = Utf8ToWide(p2), ws = DecodeSubject(subj);
    try {
        CRegexpW re(wp.c_str(), f);
        CRegexpContext ctx;
        std::string res;
        int count = 0;
        while (re.Match(ws.c_str(), (int)ws.size(), ctx)) {
            if (count++) res += ';';
            res += FormatMatch(re, ctx);
            if (!all || count > 1000) break;
        }
        return count ? res : std::string("NOMATCH");
    } catch (CRegexpException& e) {
        return e.GetCode() == CRegexpException::ERR_STEP_LIMIT ? "LIMIT" : "ERR";
    }
}

int main(int argc, char** argv)
{
    bool verify = false;
    const char* path = 0;
    int a;
    for (a = 1; a < argc; ++a) {
        if (strcmp(argv[a], "--verify") == 0) verify = true;
        else path = argv[a];
    }
    if (!path) { fprintf(stderr, "usage: run_cases [--verify] FILE\n"); return 2; }
    FILE* fp = fopen(path, "rb");
    if (!fp) { perror(path); return 2; }
    char line[65536];
    int lineNo = 0, failed = 0, total = 0;
    while (fgets(line, sizeof(line), fp)) {
        ++lineNo;
        std::string l = line;
        while (!l.empty() && (l[l.size() - 1] == '\n' || l[l.size() - 1] == '\r')) l.erase(l.size() - 1);
        if (l.empty() || l[0] == '#') continue;
        std::vector<std::string> col;
        size_t b = 0;
        for (;;) {
            size_t t = l.find('\t', b);
            if (t == std::string::npos) { col.push_back(l.substr(b)); break; }
            col.push_back(l.substr(b, t - b));
            b = t + 1;
        }
        if (col.size() < 3) { fprintf(stderr, "line %d: need 3 columns\n", lineNo); continue; }
        std::string res = RunCase(col[0], col[1], col[2]);
        ++total;
        if (verify) {
            if (col.size() >= 4 && col[3] != res) {
                printf("FAIL line %d: /%s/%s on \"%s\"\n   expected: %s\n   actual:   %s\n",
                       lineNo, col[1].c_str(), col[0].c_str(), col[2].c_str(), col[3].c_str(), res.c_str());
                ++failed;
            }
        } else {
            printf("%d\t%s\n", lineNo, res.c_str());
        }
    }
    fclose(fp);
    if (verify) {
        printf("%d cases, %d failed\n", total, failed);
        return failed ? 1 : 0;
    }
    return 0;
}
