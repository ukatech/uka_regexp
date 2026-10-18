#!/bin/sh
# usage: compare_perl.sh PATH_TO_run_cases [CASES_FILE]
# Runs the cases with the engine and with Perl and reports differences that are not listed in
# perl_known_diffs.txt (those are intentional: {,n} literal, \u, \Q\U\L, $ = end only, ...).
RUN="$1"
CASES="${2:-tests/cases_perl.txt}"
T=$(mktemp -d)
"$RUN" "$CASES" > "$T/mine" || exit 2
perl tests/perl_cases.pl "$CASES" > "$T/perl" 2>/dev/null || exit 2
awk -F'\t' 'NR==FNR { p[$1] = $2; next } p[$1] != $2 { print $1 }' "$T/perl" "$T/mine" > "$T/diff"
if [ "$CASES" = "tests/cases_perl.txt" ]; then
    if diff "$T/diff" tests/perl_known_diffs.txt > "$T/delta"; then
        echo "perl comparison: only the known differences ($(wc -l < "$T/diff") cases)"
    else
        echo "perl comparison: unexpected change in the set of differing lines:"; cat "$T/delta"; rm -rf "$T"; exit 1
    fi
else
    echo "perl comparison: $(wc -l < "$T/diff") differing cases (line numbers):"; cat "$T/diff"
fi
rm -rf "$T"
