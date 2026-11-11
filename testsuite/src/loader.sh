#!/bin/sh
# The libraries of testLinuxLoaderOrder, of AArch64 and without a libc, into OUTPUT-DIRECTORY, named as testsuite/bin has them:
#   loader.sh OUTPUT-DIRECTORY
# libbfsroot needs libbfsa and then libbfsb, and libbfsa needs libbfsc: breadth first, `which` is libbfsb's, 2, and depth first libbfsc's.
# libsn7 and libsn9 are both libsn.so by their SONAME, and libsnuser needs libsn.so: one that is loaded of that name is it.
# libwc is libwc.so of x86_64 and libwcarm of AArch64, which libwcuser needs: what is of another machine is passed over.
# libabs has `magic` of SHN_ABS, 0x1234, which libabsuse refers to: it is that, wherever libabs is.
# librp and librun need libpathv, which /rp has of 11 and /sp of 12: of DT_RPATH /rp is before what is asked, and of DT_RUNPATH after.
set -e
out=$1
cc="clang -shared -fPIC -nostdlib -O1 -fuse-ld=lld"
arm="$cc --target=aarch64-linux-musl"
tmp=$(mktemp -d)
build() { name=$1; shift; $arm "$@" -o "$tmp/$name.so"; cp "$tmp/$name.so" "$out/aarch64-linux-musl-$name"; }
build libbfsb -DVALUE=2 -Wl,-soname,libbfsb.so libwhich.c
build libbfsc -DVALUE=3 -Wl,-soname,libbfsc.so libwhich.c
build libbfsa -Wl,-soname,libbfsa.so libbfsa.c -L"$tmp" -lbfsc
build libbfsroot -Wl,-soname,libbfsroot.so libcallwhich.c -L"$tmp" -lbfsa -lbfsb
build libsn7 -DVALUE=7 -Wl,-soname,libsn.so libwhich.c
build libsn9 -DVALUE=9 -Wl,-soname,libsn.so libwhich.c
cp "$tmp/libsn7.so" "$tmp/libsn.so"
build libsnuser -Wl,-soname,libsnuser.so libcallwhich.c -L"$tmp" -lsn
$cc --target=x86_64-linux-musl -DVALUE=5 -Wl,-soname,libwc.so libwhich.c -o "$out/x86_64-linux-musl-libwc"
build libwcarm -DVALUE=6 -Wl,-soname,libwc.so libwhich.c
cp "$tmp/libwcarm.so" "$tmp/libwc.so"
build libwcuser -Wl,-soname,libwcuser.so libcallwhich.c -L"$tmp" -lwc
build libpathv11 -DVALUE=11 -Wl,-soname,libpathv.so libwhich.c
build libpathv12 -DVALUE=12 -Wl,-soname,libpathv.so libwhich.c
cp "$tmp/libpathv11.so" "$tmp/libpathv.so"
build librp -Wl,-soname,librp.so -Wl,--disable-new-dtags -Wl,-rpath,/rp libcallwhich.c -L"$tmp" -lpathv
build librun -Wl,-soname,librun.so -Wl,--enable-new-dtags -Wl,-rpath,/rp libcallwhich.c -L"$tmp" -lpathv
build libabs -Wl,-soname,libabs.so libabs.s
build libabsuse -Wl,-soname,libabsuse.so libabsuse.c -L"$tmp" -labs
rm -r "$tmp"
