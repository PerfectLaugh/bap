#!/bin/sh
# builds the programs, that test the loaders, for the targets, with clang
# and lld, without a libc: the static ones link stub.c, whose functions
# Primus replaces by their names, and the dynamic ones link libstub.so,
# whose functions Primus links, as it does the functions of libc
set -e
cd "$(dirname "$0")"
out=../../bin
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

entry="-Wl,-e,_start"
common="-O1 -ffreestanding -fno-builtin -fno-stack-protector -fno-asynchronous-unwind-tables -fuse-ld=lld -nostdlib -w"

flags() {
    case $1 in
        x86_64-linux-gnu) echo "--target=x86_64-linux-gnu -mstackrealign" ;;
        i686-linux-gnu) echo "--target=i686-linux-gnu -mstackrealign" ;;
        aarch64-linux-gnu) echo "--target=aarch64-linux-gnu" ;;
        arm-linux-gnueabi) echo "--target=armv7a-linux-gnueabi -marm -mfloat-abi=soft" ;;
        mips-linux-gnu) echo "--target=mips-linux-gnu -mabi=32 -G0" ;;
        riscv64-linux-gnu) echo "--target=riscv64-linux-gnu -march=rv64gc" ;;
    esac
}

# the code, which addresses the image at the top, is position-independent
# on x86-64, whose absolute addresses are 32 bits
high_pic() {
    case $1 in
        x86_64-*) echo -fPIE ;;
        riscv64-*) echo -mcmodel=medany ;;
    esac
}

high() {
    case $1 in
        x86_64-*|aarch64-*|riscv64-*) echo 0x7ffffff00000 ;;
        *) echo 0xffff0000 ;;
    esac
}

static_flags() {
    case $1 in
        mips-*) echo "-fno-pic -mno-abicalls" ;;
        *) echo "-fno-pic" ;;
    esac
}

static() {
    target=$1 name=$2 script=$3
    shift 3
    clang $(flags $target) $common $entry $(static_flags $target) -static \
        ${script:+-Wl,-T,$script} "$@" $name.c stub.c \
        -o $out/$target-loader-$name
}

dynamic() {
    target=$1 name=$2 pie=$3
    clang $(flags $target) $common -fPIC -shared stub.c -o $work/libstub.so
    clang $(flags $target) $common $entry $pie $name.c -L$work -lstub \
        -Wl,--dynamic-linker=/lib/ld.so.1 -Wl,--no-as-needed \
        -o $out/$target-loader-$name
}

# the entry at an odd address, of x86-64, and the delay slot of MIPS
odd_entry() { static x86_64-linux-gnu odd-entry ""; }
delay() { static mips-linux-gnu delay rwx.ld -Wl,--no-check-sections; }

for target in ${TARGETS:-x86_64-linux-gnu i686-linux-gnu aarch64-linux-gnu \
                arm-linux-gnueabi mips-linux-gnu riscv64-linux-gnu}; do
    static $target bss ""
    static $target packed packed.ld
    static $target rwx rwx.ld -Wl,--no-check-sections
    static $target high high.ld $(high_pic $target) -Wl,--defsym=high_base=$(high $target)
    static $target entry entry.ld
    static $target tls "" -ftls-model=local-exec
    dynamic $target weak -no-pie
    dynamic $target stdin "-fPIE -pie"
    llvm-objcopy --strip-sections $out/$target-loader-stdin \
        $out/$target-loader-stdin-stripped
    case $target in
        mips-*) ;;  # lld has no indirect functions of MIPS
        *) dynamic $target pie "-fPIE -pie" ;;
    esac
    echo "$target: done"
done

odd_entry
delay
