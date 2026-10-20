#!/bin/sh
# Builds GMP from its sources as a static library with position
# independent code, which zarith links into its stubs and its shared
# library, so that the programs of BAP don't depend on the libgmp of the
# system, then configures zarith, which sees only the pkg-config file of
# this GMP, installed into ./gmp. The tests of the configure of GMP
# 6.3.0 aren't valid C23, the default of GCC 15, hence the standard.

set -eu

src=gmp-6.3.0
prefix="$(pwd)/gmp"

tar xf "$src.tar.xz"
(cd "$src" &&
    ./configure --prefix="$prefix" --disable-shared --enable-static \
        --with-pic CC="$(ocamlc -config-var c_compiler) -std=gnu17" &&
    make -j"${1:-1}" &&
    make install)
PKG_CONFIG_LIBDIR="$prefix/lib/pkgconfig" ./configure
