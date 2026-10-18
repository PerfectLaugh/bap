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

# the functional tests, see tools/testsuite/dune; TESTS selects the cases
# whose names contain one of its words, e.g., make check TESTS="taint mc/"
check:
	BAP_TESTS="$(TESTS)" dune build @testsuite

# checks out the testsuite at the revision of tools/testsuite/REVISION
.PHONY: testsuite
testsuite:
	dune exec -- ./tools/testsuite/run.exe --fetch-only

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
