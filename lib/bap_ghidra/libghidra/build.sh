#!/bin/sh
# Builds the Ghidra decompiler library and Sleigh processor specifications.
#
# usage: build.sh [TARBALL]
#
# Produces in the current directory:
#   libdecomp.a, dlldecomp.so - the decompiler library
#   include/ghidra/           - its headers
#   Processors/               - the compiled processor specifications
#
# The Ghidra sources are taken from TARBALL, if it is specified (e.g.,
# when opam has already fetched it as an extra-source), otherwise they
# are downloaded from GitHub. In both cases the checksum is verified.

set -eu

GHIDRA_VERSION=12.1.4
GHIDRA_BASENAME=Ghidra_${GHIDRA_VERSION}_build
GHIDRA_URL=https://github.com/NationalSecurityAgency/ghidra/archive/refs/tags/${GHIDRA_BASENAME}.tar.gz
GHIDRA_SHA256=2a858300c350f05ae2e729dff86b4f584d0b9a6b398879c55025574e67696cec
GHIDRA_ROOT=ghidra-${GHIDRA_BASENAME}
DECOMPILER=${GHIDRA_ROOT}/Ghidra/Features/Decompiler/src/decompile/cpp

CXX=${CXX:-c++}
JOBS=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
OUT=$(pwd)
TARBALL=${1:-}

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

if [ -n "$TARBALL" ]; then
    cp "$TARBALL" "$WORK/ghidra.tar.gz"
else
    curl -sS -f -L -o "$WORK/ghidra.tar.gz" "$GHIDRA_URL"
fi

if command -v sha256sum >/dev/null 2>&1; then
    SUM=$(sha256sum "$WORK/ghidra.tar.gz" | cut -d' ' -f1)
else
    SUM=$(shasum -a 256 "$WORK/ghidra.tar.gz" | cut -d' ' -f1)
fi
if [ "$SUM" != "$GHIDRA_SHA256" ]; then
    echo "checksum mismatch for $GHIDRA_URL: got $SUM" >&2
    exit 1
fi

# runs the command quietly, but shows its output if it fails
quietly() {
    if ! "$@" >"$WORK/log" 2>&1; then
        cat "$WORK/log" >&2
        exit 1
    fi
}

cd "$WORK"
tar xzf ghidra.tar.gz \
    "${DECOMPILER}" \
    "${GHIDRA_ROOT}/Ghidra/Processors"

# the generated parsers are shipped with the sources, make sure that
# make doesn't try to regenerate them (and require bison and flex)
for f in xml grammar slghparse slghscan pcodeparse; do
    touch "${DECOMPILER}/$f.cc"
done
for f in xml grammar slghparse pcodeparse; do
    touch "${DECOMPILER}/$f.hh"
done

# the modules that depend on the GNU BFD library, they are only used by
# the command-line decompiler, so they are left out to avoid requiring
# the binutils development files
NO_BFD='analyzesigs bfd_arch codedata loadimage_bfd'

# the two targets share object directories, so they can't be built
# in the same parallel make invocation
quietly make -s -j"$JOBS" -C "${DECOMPILER}" \
        OPT_CXXFLAGS="-O2 -std=c++11 -fPIC" \
        EXTRA="\$(filter-out \$(CORE) \$(DECCORE) \$(SLEIGH) \$(GHIDRA) \$(SLACOMP) \$(SPECIAL) $NO_BFD,\$(ALL_NAMES))" \
        libdecomp.a
quietly make -s -j"$JOBS" -C "${DECOMPILER}" sleigh_opt
quietly "${DECOMPILER}/sleigh_opt" -a "${GHIDRA_ROOT}/Ghidra"

cp "${DECOMPILER}/libdecomp.a" "$OUT/libdecomp.a"
case $(uname -s) in
    Darwin)
        "$CXX" -shared -o "$OUT/dlldecomp.so" \
               -Wl,-all_load "$OUT/libdecomp.a" -undefined dynamic_lookup ;;
    *)
        "$CXX" -shared -o "$OUT/dlldecomp.so" \
               -Wl,--whole-archive "$OUT/libdecomp.a" -Wl,--no-whole-archive ;;
esac

mkdir -p "$OUT/include/ghidra"
cp "${DECOMPILER}"/*.h "${DECOMPILER}"/*.hh "$OUT/include/ghidra/"
cp -R "${GHIDRA_ROOT}/Ghidra/Processors" "$OUT/Processors"
