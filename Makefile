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

.PHONY: test

.PHONY: check

test:
	dune test

testsuite:
	git clone https://github.com/BinaryAnalysisPlatform/bap-testsuite.git testsuite

check: testsuite
	$(MAKE) REVISION=5c65cc07c48ff738e843c0fc6dfb16a0eeb572c3 -C testsuite

.PHONY: indent check-style status-clean

indent:
	dune fmt

status-clean:
	git diff --quiet --exit-code

check-style:
	dune build @fmt
