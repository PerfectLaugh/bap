#!/bin/sh
# builds spawn.c, as threads.sh builds threads-weird.c
set -e
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

build() {
    target=$1 loader=$2
    shift 2
    T="--target=$target -fuse-ld=lld -nostdlib -O1 -fno-builtin -w \
       -fno-unwind-tables -fno-asynchronous-unwind-tables $*"
    clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c \
        -o $work/libc.so.6
    clang $T -fno-pie -no-pie -Wl,-e,_start -Wl,--dynamic-linker=$loader \
        spawn.c $work/libc.so.6 -o ../bin/$target-spawn
    echo "$target: done"
}

build x86_64-linux-gnu /lib64/ld-linux-x86-64.so.2
build aarch64-linux-gnu /lib/ld-linux-aarch64.so.1 -mno-outline-atomics
build i686-linux-gnu /lib/ld-linux.so.2
build arm-linux-gnueabihf /lib/ld-linux-armhf.so.3 -mthumb -march=armv7-a
build mips-linux-gnu /lib/ld.so.1
build powerpc-linux-gnu /lib/ld.so.1
build riscv64-linux-gnu /lib/ld-linux-riscv64-lp64d.so.1
