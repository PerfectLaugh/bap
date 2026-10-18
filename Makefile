build:
	dune build

# the API reference, rendered by odoc into _build/default/_doc/_html/<package>
.PHONY: doc
doc:
	dune tools install odoc
	dune build @doc

# the website (manuals, plugin pages, Primus Lisp docs, and the API
# reference) in doc/; needs man2html and emacs. It runs under dune exec,
# so that it documents bap and the plugins built in this tree.
.PHONY: website
website: doc
	dune build ./tools/bapdoc.exe
	dune exec -- $(MAKE) -C doc

# dune refuses to install when the dune.lock package management is
# active, so these targets expect the dependencies from an opam switch
install:
	dune install --pkg=disabled

uninstall:
	dune uninstall --pkg=disabled

clean:
	dune clean

.PHONY: build install uninstall clean

.PHONY: test test-instructions

.PHONY: check

test:
	dune test

# the lifter tests of the instructions of x86, ARM, MIPS and PowerPC,
# which are slow and do not run with dune test
test-instructions:
	dune build --force @instruction-tests

TESTSUITE_URL = https://github.com/PerfectLaugh/bap-testsuite.git
TESTSUITE_REV = 4e3ef9f8965b9c589a20a73c288c017d3c2e2d82

testsuite:
	git clone $(TESTSUITE_URL) testsuite

# the number of test files of the testsuite that run in parallel
TESTSUITE_JOBS ?= 8

# runs under dune exec, so that it tests bap and the plugins built in
# this tree instead of whatever bap is first on PATH, and with TERM=dumb,
# so that the output the tests match doesn't depend on the terminal
check: testsuite
	git -C testsuite cat-file -e $(TESTSUITE_REV)^{commit} 2>/dev/null || \
	  git -C testsuite fetch $(TESTSUITE_URL)
	git -C testsuite checkout -q $(TESTSUITE_REV)
	TERM=dumb dune exec -- bash tools/run-testsuite.sh $(TESTSUITE_JOBS)

# runs the micro-benchmarks in benchmarks/. Pass core_bench options in
# BENCH_ARGS (e.g., BENCH_ARGS="-quota 1" or BENCH_ARGS=-help) and set
# BAP_BENCH_BINARY to choose the binary whose functions are analyzed
.PHONY: bench
bench: testsuite
	dune exec -- ./benchmarks/run_benchmarks.exe $(BENCH_ARGS)

.PHONY: indent check-style status-clean

indent:
	dune fmt

status-clean:
	git diff --quiet --exit-code

check-style:
	dune build @fmt
