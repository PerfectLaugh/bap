import BapTests.Core
import BapTests.Bil
import BapTests.Graph
import BapTests.Transform
import BapTests.Ssa
import BapTests.Optimize
import BapTests.Theory
import BapTests.Knowledge
import BapTests.Opinions
import BapTests.Persistence
import BapTests.IEEE754
import BapTests.Image
import BapTests.Elf
import BapTests.Macho
import BapTests.Pe
import BapTests.Coff
import BapTests.Disasm
import BapTests.AArch64
import BapTests.LLVM
import BapTests.Primus
import BapTests.Lifted
import BapTests.Lisp
import BapTests.Project
import BapTests.Scheduler
import BapTests.Symbolic
import BapTests.SymbolicMemory
import BapTests.Emu
import BapTests.Jni
import BapTests.Parity
import BapTests.Theorems

def main : IO Unit := do
  let tests : List (IO Unit) := [
    Bap.Tests.Core.run,
    Bap.Tests.Bil.run,
    Bap.Tests.Graph.run,
    Bap.Tests.Transform.run,
    Bap.Tests.Ssa.run,
    Bap.Tests.Optimize.run,
    Bap.Tests.Theory.run,
    Bap.Tests.Knowledge.run,
    Bap.Tests.Opinions.run,
    Bap.Tests.Persistence.run,
    Bap.Tests.IEEE754.run,
    Bap.Tests.Image.run,
    Bap.Tests.Elf.run,
    Bap.Tests.Macho.run,
    Bap.Tests.Pe.run,
    Bap.Tests.Coff.run,
    Bap.Tests.Disasm.run,
    Bap.Tests.AArch64.run,
    Bap.Tests.LLVM.run,
    Bap.Tests.Primus.run,
    Bap.Tests.Lifted.run,
    Bap.Tests.Lisp.run,
    Bap.Tests.Project.run,
    Bap.Tests.Scheduler.run,
    Bap.Tests.Symbolic.run,
    Bap.Tests.SymbolicMemory.run,
    Bap.Tests.Emu.run,
    Bap.Tests.Emu.testRealPthreads,
    Bap.Tests.Emu.testLinuxPrograms,
    -- Floating point is much the longest of each, so only one of each family runs it here: of ARM, x87, RISC-V, MIPS and PowerPC.
    -- The others were compared with qemu by hand.
    Bap.Tests.Emu.testLinuxMusl "aarch64",
    Bap.Tests.Emu.testLinuxMusl "riscv64" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "i686" (exclusive := false),
    Bap.Tests.Emu.testLinuxMusl "riscv32",
    Bap.Tests.Emu.testLinuxMusl "mips",
    Bap.Tests.Emu.testLinuxMusl "mipsel" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mips64" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mips64el" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "powerpc" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "powerpc64",
    Bap.Tests.Emu.testLinuxMusl "powerpc64le" (floats := false),
    Bap.Tests.Emu.testLinuxCheckpoints "aarch64",
    Bap.Tests.Emu.testLinuxCheckpoints "riscv64",
    Bap.Tests.Emu.testLinuxCheckpoints "i686",
    Bap.Tests.Emu.testLinuxCheckpoints "riscv32",
    Bap.Tests.Emu.testLinuxCheckpoints "mips",
    Bap.Tests.Emu.testLinuxCheckpoints "mips64el",
    Bap.Tests.Emu.testLinuxCheckpoints "powerpc",
    Bap.Tests.Emu.testLinuxCheckpoints "powerpc64le",
    Bap.Tests.Emu.testLinuxCheckpoints "x86_64",
    Bap.Tests.Jni.run
  ]
  Bap.Tests.Optimize.scaling
  -- More tests than the pool has threads would wait for each other, with processors to spare.
  let tasks ← tests.mapM fun test => liftM <| IO.asTask (prio := .dedicated) do
    try test catch error =>
      IO.eprintln s!"FAILED: {error}"
      throw error
  tasks.forM fun task =>
    match task.get with
    | .ok _ => pure ()
    | .error error => throw error
  IO.println "all BAP Lean tests passed"
