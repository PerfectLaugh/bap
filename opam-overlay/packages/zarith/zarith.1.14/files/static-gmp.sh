#!/bin/sh
# Builds GMP from its sources as a static library with position
# independent code, which zarith links into its stubs and its shared
# library, so that the programs of BAP don't depend on the libgmp of the
# system, then configures and builds zarith with this GMP, installed into
# ./gmp. The tests of the configure of GMP 6.3.0 aren't valid C23, the
# default of GCC 15, hence the standard. GMP needs m4, which is required
# from the system instead of with conf-m4, which on macOS links
# Homebrew's gm4 into its package, which the sandbox of dune can't link.
#
# The compilers find this GMP in the paths of the environment, instead of
# the flags of pkg-config, which zarith would record in its libraries,
# and the linkers of the programs would warn about the directory, which
# doesn't exist after the build. The libgmp.a is installed with zarith.

set -eu

src=gmp-6.3.0
prefix="$(pwd)/gmp"

tar xf "$src.tar.xz"
(cd "$src" &&
    ./configure --prefix="$prefix" --disable-shared --enable-static \
        --with-pic CC="$(ocamlc -config-var c_compiler) -std=gnu17" &&
    make -j"${1:-1}" &&
    make install)

C_INCLUDE_PATH="$prefix/include${C_INCLUDE_PATH:+:$C_INCLUDE_PATH}"
LIBRARY_PATH="$prefix/lib${LIBRARY_PATH:+:$LIBRARY_PATH}"
# no pkg-config files, so that the configure of zarith doesn't find the
# GMP of the system
PKG_CONFIG_LIBDIR="$prefix/none"
PKG_CONFIG_PATH=
export C_INCLUDE_PATH LIBRARY_PATH PKG_CONFIG_LIBDIR PKG_CONFIG_PATH
./configure -gmp
make
