#!/bin/sh
# usage: memo_compare.sh [CXX [SEEDS]]
# Remembering the states that already failed (Program::memoSlots) must never change a result.  Builds the
# test runner twice - with the memo used from the very first step (UKA_REGEXP_MEMO_START=0) and with it
# never used - and compares them on random patterns.  A case where the run without the memo hit the step
# limit may differ (that is what the memo is for); anything else is reported.
CXX="${1:-g++}"
SEEDS="${2:-5}"
PYTHON="${PYTHON:-python3}"
T=$(mktemp -d)
FLAGS="-std=c++98 -O2"
$CXX $FLAGS -DUKA_REGEXP_MEMO_START=0 -o "$T/on" tests/run_cases.cpp uka_regexp.cpp || exit 2
$CXX $FLAGS -DUKA_REGEXP_MEMO_START=4000000000UL -o "$T/off" tests/run_cases.cpp uka_regexp.cpp || exit 2
bad=0
seed=1
while [ "$seed" -le "$SEEDS" ]; do
    for gen in fuzz_memo_gen.py fuzz_gen.py; do
        "$PYTHON" "tests/$gen" "$seed" 3000 > "$T/cases" || exit 2
        "$T/off" "$T/cases" > "$T/r_off" || exit 2
        "$T/on" "$T/cases" > "$T/r_on" || exit 2
        awk -F'\t' -v g="$gen" -v s="$seed" 'NR==FNR { off[$1] = $2; next }
            off[$1] != $2 && off[$1] != "LIMIT" { print g " seed " s " line " $1 ": without memo " off[$1] ", with memo " $2; bad = 1 }
            END { exit bad }' "$T/r_off" "$T/r_on" || bad=1
    done
    seed=$((seed + 1))
done
rm -rf "$T"
if [ "$bad" = 0 ]; then echo "memo comparison: no differences"; else exit 1; fi
