#!/usr/bin/env python3
"""Generate the Unicode tables embedded at the end of uka_regexp.cpp.

Usage:  python3 tools/gen_unicode_tables.py [UCD_DIR]    (rewrites the generated block in place)

The block between the BEGIN/END GENERATED markers in uka_regexp.cpp is replaced.
General categories and case mappings come from Python's unicodedata module (its Unicode version is
printed in the block header).  Scripts, Script_Extensions, grapheme cluster break data and the
binary properties are read from the Unicode Character Database files of the same version, which are
downloaded into tools/ucd/ (not committed) unless UCD_DIR is given.
"""
import os
import re
import subprocess
import sys
import unicodedata

CATS = ['Cn', 'Cc', 'Cf', 'Co', 'Cs', 'Ll', 'Lm', 'Lo', 'Lt', 'Lu', 'Mc', 'Me', 'Mn', 'Nd', 'Nl',
        'No', 'Pc', 'Pd', 'Pe', 'Pf', 'Pi', 'Po', 'Ps', 'Sc', 'Sk', 'Sm', 'So', 'Zl', 'Zp', 'Zs']
CAT_INDEX = dict((c, i) for i, c in enumerate(CATS))

UCD_FILES = {
    "Scripts.txt": "ucd/Scripts.txt",
    "ScriptExtensions.txt": "ucd/ScriptExtensions.txt",
    "PropertyValueAliases.txt": "ucd/PropertyValueAliases.txt",
    "DerivedCoreProperties.txt": "ucd/DerivedCoreProperties.txt",
    "GraphemeBreakProperty.txt": "ucd/auxiliary/GraphemeBreakProperty.txt",
    "emoji-data.txt": "ucd/emoji/emoji-data.txt",
}


def ucd_path(name, ucd_dir):
    if ucd_dir:
        return os.path.join(ucd_dir, name)
    here = os.path.dirname(os.path.abspath(__file__))
    cache = os.path.join(here, "ucd")
    os.makedirs(cache, exist_ok=True)
    path = os.path.join(cache, name)
    if not os.path.exists(path):
        version = unicodedata.unidata_version
        url = "https://www.unicode.org/Public/%s/ucd/%s" % (version, UCD_FILES[name][4:])
        print("downloading", url, file=sys.stderr)
        subprocess.check_call(["curl", "-sSf", "-o", path, url])
    return path


def read_property_file(path):
    """yield (lo, hi, [fields]) for every data line of a UCD file"""
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
            parts = [x.strip() for x in line.split(";")]
            rng = parts[0].split("..")
            lo = int(rng[0], 16)
            hi = int(rng[-1], 16)
            yield lo, hi, parts[1:]


def merge_ranges(rs):
    rs = sorted(rs)
    out = []
    for lo, hi in rs:
        if out and lo <= out[-1][1] + 1:
            if hi > out[-1][1]:
                out[-1] = (out[-1][0], hi)
        else:
            out.append((lo, hi))
    return out


def fmt_range_array(name, rs, with_count=False):
    rs = merge_ranges(rs)
    lines = ["const Range %s[] = {" % name]
    row = []
    for lo, hi in rs:
        row.append("{0x%X,0x%X}" % (lo, hi))
        if len(row) == 6:
            lines.append("    " + ",".join(row) + ",")
            row = []
    if row:
        lines.append("    " + ",".join(row) + ",")
    lines.append("};")
    if with_count:
        lines.append("const int %sCount = (int)(sizeof(%s) / sizeof(%s[0]));" % (name, name, name))
    return "\n".join(lines)


def script_tables(ucd_dir):
    """returns the C++ text for the Script / Script_Extensions tables"""
    # script names: sc ; short ; long [; alias...]
    scripts = []   # (long name, [all names])
    for line in open(ucd_path("PropertyValueAliases.txt", ucd_dir), encoding="utf-8"):
        line = line.split("#", 1)[0].strip()
        if not line.startswith("sc "):
            continue
        parts = [x.strip() for x in line.split(";")]
        scripts.append((parts[2], parts[1:]))
    scripts.sort()
    # id 0 is "Unknown" (also the value of unassigned code points)
    scripts.sort(key=lambda x: (x[0] != "Unknown", x[0]))
    by_name = {}
    for i, (long_name, names) in enumerate(scripts):
        for n in names:
            by_name[n] = i
    assert len(scripts) < 255

    script_of = [0] * 0x110000
    for lo, hi, f in read_property_file(ucd_path("Scripts.txt", ucd_dir)):
        sid = by_name[f[0]]
        for cp in range(lo, hi + 1):
            script_of[cp] = sid
    runs = []
    prev = -1
    for cp in range(0x110000):
        if script_of[cp] != prev:
            runs.append((cp << 8) | script_of[cp])
            prev = script_of[cp]

    scx = []   # (lo, hi, [ids])
    for lo, hi, f in read_property_file(ucd_path("ScriptExtensions.txt", ucd_dir)):
        scx.append((lo, hi, sorted(set(by_name[n] for n in f[0].split()))))
    scx.sort()
    data = []
    ranges = []
    cache = {}
    for lo, hi, ids in scx:
        key = tuple(ids)
        if key not in cache:
            cache[key] = len(data)
            data.extend(ids)
            data.append(255)
        ranges.append((lo, hi, cache[key]))

    out = []
    out.append("// Script of every code point: (first code point << 8) | script id.  Script id 0 is Unknown.")
    out.append("const unsigned int g_scriptRuns[] = {")
    out.append(fmt_numbers(runs, 8, "0x%X"))
    out.append("};")
    out.append("const int g_scriptRunsCount = (int)(sizeof(g_scriptRuns) / sizeof(g_scriptRuns[0]));")
    out.append("")
    out.append("// Script names (full and short ISO 15924 names) and their ids.")
    out.append("const ScriptName g_scriptNames[] = {")
    for i, (long_name, names) in enumerate(scripts):
        for n in names:
            out.append('    {"%s",%d},' % (n, i))
    out.append("};")
    out.append("const int g_scriptNamesCount = (int)(sizeof(g_scriptNames) / sizeof(g_scriptNames[0]));")
    out.append("")
    out.append("// Script_Extensions where it differs from Script: ranges with an offset into g_scxData")
    out.append("// (script ids, terminated by 255).")
    out.append("const ScxRange g_scxRanges[] = {")
    row = []
    for lo, hi, off in ranges:
        row.append("{0x%X,0x%X,%d}" % (lo, hi, off))
        if len(row) == 5:
            out.append("    " + ",".join(row) + ",")
            row = []
    if row:
        out.append("    " + ",".join(row) + ",")
    out.append("};")
    out.append("const int g_scxRangesCount = (int)(sizeof(g_scxRanges) / sizeof(g_scxRanges[0]));")
    out.append("const unsigned char g_scxData[] = {")
    out.append(fmt_numbers(data, 16, "%d"))
    out.append("};")
    return "\n".join(out), len(runs), len(ranges)


GCB_VALUES = ["Other", "CR", "LF", "Control", "Extend", "ZWJ", "Regional_Indicator", "Prepend",
              "SpacingMark", "L", "V", "T", "LV", "LVT"]


def segmentation_tables(ucd_dir):
    gcb = [0] * 0x110000
    for lo, hi, f in read_property_file(ucd_path("GraphemeBreakProperty.txt", ucd_dir)):
        v = GCB_VALUES.index(f[0])
        for cp in range(lo, hi + 1):
            gcb[cp] = v
    runs = []
    prev = -1
    for cp in range(0x110000):
        if gcb[cp] != prev:
            runs.append((cp << 4) | gcb[cp])
            prev = gcb[cp]

    emoji = {}
    for lo, hi, f in read_property_file(ucd_path("emoji-data.txt", ucd_dir)):
        emoji.setdefault(f[0], []).append((lo, hi))
    incb = {}
    alphabetic = []
    for lo, hi, f in read_property_file(ucd_path("DerivedCoreProperties.txt", ucd_dir)):
        if f[0] == "InCB":
            incb.setdefault(f[1], []).append((lo, hi))
        elif f[0] == "Alphabetic":
            alphabetic.append((lo, hi))

    out = []
    out.append("// Grapheme_Cluster_Break: (first code point << 4) | value; values: " + ", ".join(
        "%d=%s" % (i, n) for i, n in enumerate(GCB_VALUES)))
    out.append("const unsigned int g_gcbRuns[] = {")
    out.append(fmt_numbers(runs, 8, "0x%X"))
    out.append("};")
    out.append("const int g_gcbRunsCount = (int)(sizeof(g_gcbRuns) / sizeof(g_gcbRuns[0]));")
    out.append("")
    out.append("// Indic_Conjunct_Break values used by the grapheme cluster rules")
    for name in ("Consonant", "Linker", "Extend"):
        out.append(fmt_range_array("g_incb" + name, incb[name], True))
    out.append("")
    props = [("Alphabetic", "Alpha", alphabetic),
             ("Emoji", "", emoji["Emoji"]),
             ("Emoji_Presentation", "EPres", emoji["Emoji_Presentation"]),
             ("Emoji_Modifier", "EMod", emoji["Emoji_Modifier"]),
             ("Emoji_Modifier_Base", "EBase", emoji["Emoji_Modifier_Base"]),
             ("Emoji_Component", "EComp", emoji["Emoji_Component"]),
             ("Extended_Pictographic", "ExtPict", emoji["Extended_Pictographic"])]
    for name, alias, rs in props:
        out.append(fmt_range_array("g_bin" + name.replace("_", ""), rs, name == "Extended_Pictographic"))
    out.append("")
    out.append("// Binary properties usable as \\p{Name}")
    out.append("const BinPropDef g_binProps[] = {")
    for name, alias, rs in props:
        arr = "g_bin" + name.replace("_", "")
        out.append('    {"%s","%s",%s,(int)(sizeof(%s) / sizeof(%s[0]))},' % (name, alias, arr, arr, arr))
    out.append("};")
    out.append("const int g_binPropsCount = (int)(sizeof(g_binProps) / sizeof(g_binProps[0]));")

    # general category long names -> short names
    out.append("")
    out.append("// General category long names / aliases and the short name they stand for")
    out.append("const StrPair g_gcAliases[] = {")
    for line in open(ucd_path("PropertyValueAliases.txt", ucd_dir), encoding="utf-8"):
        line = line.split("#", 1)[0].strip()
        if not line.startswith("gc "):
            continue
        parts = [x.strip() for x in line.split(";")]
        for alias in parts[2:]:
            out.append('    {"%s","%s"},' % (alias, parts[1]))
    out.append("};")
    out.append("const int g_gcAliasesCount = (int)(sizeof(g_gcAliases) / sizeof(g_gcAliases[0]));")
    return "\n".join(out), len(runs)


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
    ucd_dir = sys.argv[1] if len(sys.argv) > 1 else None
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
    out.append("")
    script_text, nscript_runs, nscx = script_tables(ucd_dir)
    out.append(script_text)
    out.append("")
    seg_text, ngcb = segmentation_tables(ucd_dir)
    out.append(seg_text)
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
    print("runs=%d fold=%d upper=%d lower=%d script runs=%d scx=%d gcb runs=%d" % (
        len(runs), len(to_ranges(fold)), len(to_ranges(upper)), len(to_ranges(lower)), nscript_runs, nscx, ngcb))


if __name__ == "__main__":
    main()
