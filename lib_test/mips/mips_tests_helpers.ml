let mode target encoding = Lifter_test.mode ~addr:0x20000 ~target ~encoding ()
let mips32eb = mode "mips" "llvm-mips32"
let mips32le = mode "mipsel" "llvm-mips32le"
let mips64eb = mode "mips64" "llvm-mips64"
let mips64le = mode "mips64el" "llvm-mips64le"
