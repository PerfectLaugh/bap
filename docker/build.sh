#!/bin/sh
# Builds BAP with dune package management and saves the environment
# in which the built programs can find their plugins and libraries.
#
# Dune doesn't install packages that are built with package management,
# so BAP is run from the build tree, with the same environment that
# `dune exec` provides, see entrypoint.sh.

set -eu

dune build @install

dune exec --no-build -- env |
    grep -E '^(PATH|OCAMLPATH|OCAMLFIND_IGNORE_DUPS_IN|CAML_LD_LIBRARY_PATH|DUNE_DIR_LOCATIONS|DUNE_OCAML_HARDCODED|DUNE_OCAML_STDLIB)=' |
    sed -e "s/'/'\\\\''/g" -e "s/^\([^=]*\)=\(.*\)$/export \1='\2'/" \
        > "$HOME/.bap-env"
