#!/bin/sh
# builds threads-win.c, the program of PE, with clang and lld-link,
# without a libc, with the import libraries of the .def files
set -e
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

build() {
    target=$1 machine=$2 kernel=$3
    llvm-dlltool -m $machine -k -d $kernel.def -l $work/kernel32.lib
    llvm-dlltool -m $machine -d loader/msvcrt.def -l $work/msvcrt.lib
    clang --target=$target -O1 -ffreestanding -fno-builtin \
        -fno-stack-protector -w -c threads-win.c -o $work/threads-win.obj
    lld-link /nologo /entry:start /subsystem:console /nodefaultlib /debug:symtab \
        $work/threads-win.obj $work/kernel32.lib $work/msvcrt.lib \
        /out:$work/threads-win.exe
    mv $work/threads-win.exe ../bin/$target-threads-win
    echo "$target: done"
}

build x86_64-pc-windows-msvc i386:x86-64 threads-win
build i686-pc-windows-msvc i386 threads-win-x86
