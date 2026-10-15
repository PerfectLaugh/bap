build:
	dune build

.PHONY: doc
doc:
	@ocamlfind ocamlopt -linkpkg -package bap-plugins,core_kernel,core_kernel.caml_unix tools/bapdoc.ml -o bapdoc.native
	make -C doc

# dune refuses to install when the dune.lock package management is
# active, so these targets expect the dependencies from an opam switch
install:
	dune install --pkg=disabled

uninstall:
	dune uninstall --pkg=disabled

clean:
	dune clean

.PHONY: build install uninstall clean

.PHONY: test

.PHONY: check

test:
	dune test

testsuite:
	git clone https://github.com/BinaryAnalysisPlatform/bap-testsuite.git testsuite

check: testsuite
	make REVISION=5c65cc07c48ff738e843c0fc6dfb16a0eeb572c3 -C testsuite

.PHONY: indent check-style status-clean

indent:
	sh tools/ocp-indent-all.sh

status-clean:
	git diff --quiet --exit-code

check-style: status-clean indent
	git diff --exit-code
