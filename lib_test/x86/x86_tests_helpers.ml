let x86_64 =
  Lifter_test.mode ~addr:0x20000 ~target:"x86_64" ~encoding:"llvm-x86_64" ()

let i686 = Lifter_test.mode ~addr:0x20000 ~target:"i686" ~encoding:"llvm-x86" ()
