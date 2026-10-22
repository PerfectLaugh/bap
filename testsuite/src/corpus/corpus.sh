#!/bin/sh
# builds the parts of corpus.c for each target and its variants, e.g.,
# the levels of the optimizations, and the extensions of the
# instructions, as the objects in DIR, whose instructions without
# semantics bap prints:
#
#   corpus.sh DIR
#   bap DIR/aarch64-linux-gnu-O2-VECTOR.o --print-missing
set -e
cd "$(dirname "$0")"
out=${1:?usage: corpus.sh DIR}
mkdir -p "$out"

parts="INT BITS FLOAT VECTOR ATOMIC MEMORY"

build() {
    target=$1 name=$2
    shift 2
    for part in $parts; do
        clang --target=$target -c -w -ffreestanding -fno-builtin-memcpy \
            -fno-stack-protector -DPART_$part "$@" corpus.c \
            -o "$out/$target-$name-$part.o" ||
            echo "$target-$name-$part: FAILED"
    done
}

for o in O0 O1 O2 O3 Os; do
    build x86_64-linux-gnu $o -$o
    build i686-linux-gnu $o -$o
    build aarch64-linux-gnu $o -$o
    build arm-linux-gnueabihf $o -$o -marm -march=armv7-a -mfpu=neon-vfpv4
    build arm-linux-gnueabihf thumb-$o -$o -mthumb -march=armv7-a -mfpu=neon-vfpv4
    build mips-linux-gnu $o -$o
    build mipsel-linux-gnu $o -$o
    build mips64-linux-gnuabi64 $o -$o
    build mips64el-linux-gnuabi64 $o -$o
    build powerpc-linux-gnu $o -$o
    build powerpc64-linux-gnu $o -$o
    build powerpc64le-linux-gnu $o -$o
    build riscv64-linux-gnu $o -$o
    build riscv32-linux-gnu $o -$o
    build s390x-linux-gnu $o -$o
done

# the extensions
build x86_64-linux-gnu v2 -O2 -march=x86-64-v2
build x86_64-linux-gnu v3 -O2 -march=x86-64-v3
build x86_64-linux-gnu v4 -O2 -march=x86-64-v4
build i686-linux-gnu x87 -O2 -mno-sse
build i686-linux-gnu sse2 -O2 -msse2 -mfpmath=sse
build aarch64-linux-gnu lse -O2 -march=armv8.1-a
build aarch64-linux-gnu v8.2 -O2 -march=armv8.2-a+fp16+dotprod+rcpc
build aarch64-linux-gnu sve -O2 -march=armv8.2-a+sve
build arm-linux-gnueabihf v6 -O2 -marm -march=armv6 -mfpu=vfp
build arm-linux-gnueabi soft -O2 -marm -march=armv5te -mfloat-abi=soft
build arm-linux-gnueabihf v8 -O2 -marm -march=armv8-a -mfpu=crypto-neon-fp-armv8
build arm-linux-gnueabihf thumb-v8m -O2 -mthumb -march=armv8-m.main
build mips-linux-gnu r6 -O2 -march=mips32r6
build mips-linux-gnu r1 -O2 -march=mips32
build mips64-linux-gnuabi64 r6 -O2 -march=mips64r6
build powerpc-linux-gnu altivec -O2 -mcpu=7450 -maltivec
build powerpc64le-linux-gnu pwr9 -O2 -mcpu=pwr9
build powerpc64-linux-gnu pwr7 -O2 -mcpu=pwr7
build riscv64-linux-gnu v -O2 -march=rv64gcv
build riscv64-linux-gnu b -O2 -march=rv64gc_zba_zbb_zbs
build s390x-linux-gnu z13 -O2 -march=z13
