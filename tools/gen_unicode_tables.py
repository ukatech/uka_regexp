#!/usr/bin/env python3
"""Generate the Unicode tables embedded at the end of uka_regexp.cpp.

Usage:  python3 tools/gen_unicode_tables.py            (rewrites the generated block in place)

The block between the BEGIN/END GENERATED markers in uka_regexp.cpp is replaced.
Data comes from Python's unicodedata module (see the version printed in the block header).
"""
import os
import sys
import unicodedata

CATS = ['Cn', 'Cc', 'Cf', 'Co', 'Cs', 'Ll', 'Lm', 'Lo', 'Lt', 'Lu', 'Mc', 'Me', 'Mn', 'Nd', 'Nl',
        'No', 'Pc', 'Pd', 'Pe', 'Pf', 'Pi', 'Po', 'Ps', 'Sc', 'Sk', 'Sm', 'So', 'Zl', 'Zp', 'Zs']
CAT_INDEX = dict((c, i) for i, c in enumerate(CATS))

BEGIN = "// ==== BEGIN GENERATED TABLES (tools/gen_unicode_tables.py) ===="
END = "// ==== END GENERATED TABLES ===="


def category_runs():
    runs = []
    prev = -1
    for cp in range(0x110000):
        i = CAT_INDEX[unicodedata.category(chr(cp))]
        if i != prev:
            runs.append((cp << 5) | i)
            prev = i
    return runs


def case_maps():
    upper, lower, fold = {}, {}, {}
    for cp in range(0x110000):
        ch = chr(cp)
        u = ch.upper()
        if len(u) == 1 and u != ch:
            upper[cp] = ord(u)
        l = ch.lower()
        if len(l) == 1 and l != ch:
            lower[cp] = ord(l)
        f = ch.casefold()
        if len(f) == 1:
            if f != ch:
                fold[cp] = ord(f)
        elif len(l) == 1 and l != ch:
            fold[cp] = ord(l)          # simple (S) folding
    return upper, lower, fold


def to_ranges(m):
    keys = sorted(m)
    out = []
    i = 0
    while i < len(keys):
        k = keys[i]
        d = m[k] - k
        step = None
        if i + 1 < len(keys):
            k2 = keys[i + 1]
            if m[k2] - k2 == d and k2 - k in (1, 2):
                step = k2 - k
        if step is None:
            out.append((k, k, 1, d))
            i += 1
            continue
        j = i + 1
        while j + 1 < len(keys) and keys[j + 1] - keys[j] == step and m[keys[j + 1]] - keys[j + 1] == d:
            j += 1
        out.append((k, keys[j], step, d))
        i = j + 1
    return out


def fmt_numbers(vals, per_line, fmt):
    lines = []
    for i in range(0, len(vals), per_line):
        lines.append("    " + ",".join(fmt % v for v in vals[i:i + per_line]) + ",")
    return "\n".join(lines)


def fmt_ranges(name, rs):
    lines = ["const CaseRange %s[] = {" % name]
    for (lo, hi, step, d) in rs:
        lines.append("    {0x%X,0x%X,%d,%d}," % (lo, hi, step, d))
    lines.append("};")
    lines.append("const int %sCount = (int)(sizeof(%s) / sizeof(%s[0]));" % (name, name, name))
    return "\n".join(lines)


def main():
    runs = category_runs()
    upper, lower, fold = case_maps()
    out = []
    out.append(BEGIN)
    out.append("// Unicode %s. Do not edit by hand." % unicodedata.unidata_version)
    out.append("// General category runs: (first code point << 5) | category index (see CAT_* enum).")
    out.append("const unsigned int g_catRuns[] = {")
    out.append(fmt_numbers(runs, 8, "0x%X"))
    out.append("};")
    out.append("const int g_catRunsCount = (int)(sizeof(g_catRuns) / sizeof(g_catRuns[0]));")
    out.append("")
    out.append("// Simple case mappings: code points lo, lo+step, ... <= hi map to code point + delta.")
    out.append(fmt_ranges("g_foldTable", to_ranges(fold)))
    out.append(fmt_ranges("g_upperTable", to_ranges(upper)))
    out.append(fmt_ranges("g_lowerTable", to_ranges(lower)))
    out.append(END)
    block = "\n".join(out) + "\n"

    here = os.path.dirname(os.path.abspath(__file__))
    target = os.path.join(here, "..", "uka_regexp.cpp")
    with open(target, encoding="utf-8") as f:
        src = f.read()
    b = src.index(BEGIN)
    e = src.index(END) + len(END) + 1
    src = src[:b] + block + src[e:]
    with open(target, "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    print("runs=%d fold=%d upper=%d lower=%d" % (len(runs), len(to_ranges(fold)),
                                                 len(to_ranges(upper)), len(to_ranges(lower))))


if __name__ == "__main__":
    main()
