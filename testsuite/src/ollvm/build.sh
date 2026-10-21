#!/bin/sh
# Builds the flattening pass of Obfuscator-LLVM, see flattening.cpp, and
# flattens the functions of collatz.c with it, as Obfuscator-LLVM does,
# without the optimizations, so that the state is on the stack, to
# ../../bin/x86_64-linux-gnu-ollvm-fla
set -e
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
clang++ -shared -fPIC -O2 $(llvm-config --cxxflags) flattening.cpp \
    -o "$work/flattening.so"
clang -O0 -Xclang -disable-O0-optnone -S -emit-llvm collatz.c \
    -o "$work/collatz.ll"
opt -load-pass-plugin="$work/flattening.so" \
    -passes='function(lower-switch,ollvm-fla)' "$work/collatz.ll" -S \
    -o "$work/collatz-fla.ll"
clang -O0 -w -no-pie -fno-pie -fcf-protection=none "$work/collatz-fla.ll" \
    -o ../../bin/x86_64-linux-gnu-ollvm-fla
