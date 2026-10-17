let mode target encoding = Lifter_test.mode ~addr:0x20000 ~target ~encoding ()
let ppc32 = mode "powerpc" "llvm-powerpc32"
let ppc64eb = mode "powerpc64" "llvm-powerpc64"
let ppc64le = mode "powerpc64le" "llvm-powerpc64le"
