#!/bin/sh
# builds r6.c for the targets of the release 6 of MIPS, with clang and
# lld, as ../bin/TARGET-r6
set -e
cd "$(dirname "$0")"
for target in mipsisa32r6-linux-gnu mipsisa32r6el-linux-gnu \
              mipsisa64r6-linux-gnuabi64 mipsisa64r6el-linux-gnuabi64; do
    clang --target=$target -O1 -ffreestanding -fno-stack-protector \
        -fno-pic -mno-abicalls -fuse-ld=lld -nostdlib -static \
        -Wl,-e,_start r6.c -o ../bin/$target-r6
done
