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
    Bap.Tests.Jni.run
  ]
  let tasks ← tests.mapM fun test => liftM (IO.asTask test)
  tasks.forM fun task =>
    match task.get with
    | .ok _ => pure ()
    | .error error => throw error
  IO.println "all BAP Lean tests passed"
