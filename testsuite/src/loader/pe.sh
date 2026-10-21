#!/bin/sh
# builds the programs of PE, that test the loaders, with clang and
# lld-link, without a libc, with the import libraries of the .def files
set -e
cd "$(dirname "$0")"
out=../../bin
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

build() {
    target=$1 machine=$2 name=$3 kernel=$4
    shift 4
    for def in msvcrt ordinal; do
        llvm-dlltool -m $machine -d $def.def -l $work/$def.lib
    done
    llvm-dlltool -m $machine -k -d $kernel.def -l $work/kernel32.lib
    clang --target=$target -O1 -ffreestanding -fno-builtin -fno-stack-protector \
        -w -c $name.c -o $work/$name.obj
    lld-link /nologo /entry:start /subsystem:console /nodefaultlib \
        $work/$name.obj $work/msvcrt.lib $work/kernel32.lib $work/ordinal.lib \
        "$@" /out:$out/$target-loader-$name.exe
    mv $out/$target-loader-$name.exe $out/$target-loader-$name
}

for target in ${TARGETS:-x86_64-pc-windows-msvc i686-pc-windows-msvc}; do
    case $target in
        x86_64-*) machine=i386:x86-64 kernel=kernel32 high=0x7ff000000000 ;;
        *) machine=i386 kernel=kernel32-x86 high=0x7f000000 ;;
    esac
    build $target $machine pe-basic $kernel
    # the .bss in .data, whose memory is larger than its contents
    cp pe-basic.c pe-merged.c
    build $target $machine pe-merged $kernel /merge:.bss=.data
    # the sections in the same pages, as the alignment is small
    cp pe-basic.c pe-packed.c
    build $target $machine pe-packed $kernel /align:16 /filealign:16
    # the image at the top of the address space, without relocations
    cp pe-basic.c pe-high.c
    build $target $machine pe-high $kernel /base:$high /fixed
    build $target $machine pe-ordinal $kernel
    rm -f pe-merged.c pe-packed.c pe-high.c
    echo "$target: done"
done
