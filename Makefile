# Builds and runs the tests with g++.  The engine itself is just uka_regexp.h + uka_regexp.cpp.
CXX      ?= g++
CXXFLAGS ?= -std=c++98 -Wall -Wextra -pedantic -O2
BUILD    = build

all: test

$(BUILD):
	mkdir -p $(BUILD)

$(BUILD)/run_cases: tests/run_cases.cpp uka_regexp.cpp uka_regexp.h | $(BUILD)
	$(CXX) $(CXXFLAGS) -o $@ tests/run_cases.cpp uka_regexp.cpp

$(BUILD)/test_api: tests/test_api.cpp uka_regexp.cpp uka_regexp.h | $(BUILD)
	$(CXX) $(CXXFLAGS) -o $@ tests/test_api.cpp uka_regexp.cpp

test: $(BUILD)/run_cases $(BUILD)/test_api
	$(BUILD)/run_cases --verify tests/cases_manual.txt
	$(BUILD)/test_api

# needs perl (5.30 or newer): compares tests/cases_perl.txt with Perl's results
compare-perl: $(BUILD)/run_cases
	sh tests/compare_perl.sh $(BUILD)/run_cases

# results must not depend on remembering failed states: memo used from the first step vs never (needs python3)
compare-memo:
	sh tests/memo_compare.sh $(CXX)

# rebuild the Unicode tables inside uka_regexp.cpp (needs python3)
unicode-tables:
	python3 tools/gen_unicode_tables.py

clean:
	rm -rf $(BUILD)

.PHONY: all test compare-perl compare-memo unicode-tables clean
