#!/bin/sh
# builds threads-weird.c, see threads-arch.h, for the targets of Linux,
# with clang and lld, and the stand-in libc of stub-libc.c
set -e
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

build() {
    target=$1 loader=$2
    shift 2
    T="--target=$target -fuse-ld=lld -nostdlib -O1 -fno-builtin \
       -fno-unwind-tables -fno-asynchronous-unwind-tables $*"
    if [ "$loader" = static ]; then
        clang $T -static -Wl,-e,_start threads-weird.c stub-libc.c \
            -o ../bin/$target-threads-weird
    else
        clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c \
            -o $work/libc.so.6
        clang $T -fno-pie -no-pie -Wl,-e,_start -Wl,--dynamic-linker=$loader \
            threads-weird.c $work/libc.so.6 -o ../bin/$target-threads-weird
    fi
    echo "$target: done"
}

build x86_64-linux-gnu /lib64/ld-linux-x86-64.so.2
# the stand-in libc has no atomics
build aarch64-linux-gnu /lib/ld-linux-aarch64.so.1 -mno-outline-atomics
build i686-linux-gnu /lib/ld-linux.so.2
build arm-linux-gnueabihf /lib/ld-linux-armhf.so.3 -marm -march=armv7-a
build mips-linux-gnu /lib/ld.so.1
# static, without the PIC code of n64, which computes GP from T9, that
# the stubs, which call main, don't set, and its small data, whose stubs
# replace the functions of the stand-in libc by their names
build mips64-linux-gnuabi64 static -mno-abicalls -G0
build powerpc-linux-gnu /lib/ld.so.1
build riscv64-linux-gnu /lib/ld-linux-riscv64-lp64d.so.1
