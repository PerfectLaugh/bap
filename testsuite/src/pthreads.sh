#!/bin/sh
# builds pthreads.c, with clang and lld, and the stand-in libc of
# stub-libc.c, whose functions of the threads the emulator replaces
set -e
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

build() {
    target=$1 loader=$2
    shift 2
    T="--target=$target -fuse-ld=lld -nostdlib -O1 -fno-builtin \
       -fno-unwind-tables -fno-asynchronous-unwind-tables $*"
    clang $T -DPTHREAD -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c \
        -o $work/libc.so.6
    clang $T -fno-pie -no-pie -Wl,-e,_start -Wl,--dynamic-linker=$loader \
        pthreads.c $work/libc.so.6 -o ../bin/$target-pthreads
    echo "$target: done"
}

build x86_64-linux-gnu /lib64/ld-linux-x86-64.so.2
# the stand-in libc has no atomics
build aarch64-linux-gnu /lib/ld-linux-aarch64.so.1 -mno-outline-atomics
