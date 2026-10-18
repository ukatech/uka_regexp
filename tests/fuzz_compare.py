#!/usr/bin/env python3
"""Compare run_cases with Perl on a (random) case file, tolerating patterns that make Perl run forever.

usage: fuzz_compare.py PATH_TO_run_cases CASES_FILE

Only the span of group 0 of every match is compared: Perl keeps captures that were set inside a
negative lookahead, this engine (like PCRE) does not.  Cases for which this engine reports LIMIT,
and cases Perl does not finish within the time limit, are skipped.
"""
import os
import subprocess
import sys

run_cases, cases_file = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
perl_script = os.path.join(here, "perl_cases.pl")

lines = open(cases_file, encoding="utf-8").read().split("\n")
if lines and lines[-1] == "":
    lines.pop()

mine = {}
out = subprocess.run([run_cases, cases_file], stdout=subprocess.PIPE, universal_newlines=True,
                     encoding="utf-8").stdout
for l in out.split("\n"):
    if l:
        a, b = l.split("\t", 1)
        mine[int(a)] = b

perl = {}
skipped = 0


def run_perl(start, end):
    """run lines [start, end) in a temporary file; returns False on timeout"""
    tmp = cases_file + ".chunk"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write("\n".join(lines[start:end]) + "\n")
    try:
        res = subprocess.run(["perl", perl_script, tmp], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                             universal_newlines=True, encoding="utf-8", timeout=10)
    except subprocess.TimeoutExpired:
        return False
    for l in res.stdout.split("\n"):
        if l:
            a, b = l.split("\t", 1)
            perl[start + int(a)] = b
    return True


def run_range(start, end):
    global skipped
    if start >= end:
        return
    if run_perl(start, end):
        return
    if end - start <= 1:
        skipped += 1
        return
    mid = (start + end) // 2
    run_range(start, mid)
    run_range(mid, end)


CHUNK = 500
for s in range(0, len(lines), CHUNK):
    run_range(s, min(s + CHUNK, len(lines)))
if os.path.exists(cases_file + ".chunk"):
    os.remove(cases_file + ".chunk")


def span0(x):
    return ";".join(a.split(" ")[0] for a in x.split(";"))


bad = 0
compared = 0
for n in range(1, len(lines) + 1):
    if n not in perl or n not in mine:
        continue
    if mine[n] == "LIMIT" or perl[n] == "LIMIT":
        continue
    compared += 1
    if span0(perl[n]) != span0(mine[n]):
        bad += 1
        c = lines[n - 1].split("\t")
        print("line %d: /%s/%s on %r\n   perl=%s\n   mine=%s" % (n, c[1][:300], c[0], c[2], perl[n][:120], mine[n][:120]))
print("compared %d cases, %d differ in group 0 (%d skipped: Perl did not finish)" % (compared, bad, skipped))
