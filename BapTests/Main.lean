import BapTests.GraphScale
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
    Bap.Tests.Emu.testLinuxLayouts,
    Bap.Tests.Emu.testThumbIt,
    Bap.Tests.Emu.testRangeEntries,
    Bap.Tests.Emu.testLinuxRaises "aarch64-linux-musl-libc-raises",
    Bap.Tests.Emu.testLinuxRaises "aarch64-linux-musl-libc-controls",
    Bap.Tests.Emu.testLinuxRaises "arm-linux-musl-libc-controls",
    Bap.Tests.Emu.testArmV8 "vrint",
    Bap.Tests.Emu.testArmV8 "v8fp",
    Bap.Tests.Emu.testOptimizedRange,
    Bap.Tests.Emu.testLinuxAuxv "aarch64",
    Bap.Tests.Emu.testLinuxAuxv "mips",
    Bap.Tests.Emu.testPowerpcElfv1,
    Bap.Tests.Emu.testPowerpcPrefixed,
    Bap.Tests.Emu.testLinuxRound "aarch64",
    Bap.Tests.Emu.testLinuxRound "arm",
    Bap.Tests.Emu.testLinuxRound "powerpc64",
    Bap.Tests.Emu.testLinuxDynamic "arm",
    Bap.Tests.Emu.testLinuxExec "aarch64",
    Bap.Tests.Emu.testLinuxExec "i686",
    Bap.Tests.Emu.testLinuxExec "thumb",
    Bap.Tests.Emu.testLinuxExec "mips",
    Bap.Tests.Emu.testLinuxExec "powerpc64",
    Bap.Tests.GraphScale.run,
    -- Floating point is much the longest of each, so only one of each family runs it here: of AArch64, Thumb, x87, RISC-V, MIPS and PowerPC.
    -- The others were compared with qemu by hand.
    Bap.Tests.Emu.testLinuxMusl "aarch64",
    Bap.Tests.Emu.testLinuxMusl "riscv64" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "i686" (exclusive := false),
    Bap.Tests.Emu.testLinuxMusl "arm" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "thumb",
    Bap.Tests.Emu.testLinuxSelfModifying,
    Bap.Tests.Emu.testLinuxSyscallHandler "aarch64" 17,
    Bap.Tests.Emu.testLinuxSyscallHandler "mips" 4203,
    Bap.Tests.Emu.testLinuxInterworking "arm",
    Bap.Tests.Emu.testLinuxInterworking "thumb",
    Bap.Tests.Emu.testLinuxMusl "riscv32",
    Bap.Tests.Emu.testLinuxMusl "mips",
    Bap.Tests.Emu.testLinuxMusl "mipsel" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mips64" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mips64el" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mipsr6" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "mips64r6" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "powerpc" (floats := false),
    Bap.Tests.Emu.testLinuxMusl "powerpc64",
    Bap.Tests.Emu.testLinuxMusl "powerpc64le" (floats := false),
    Bap.Tests.Emu.testLinuxProc "aarch64",
    Bap.Tests.Emu.testLinuxProc "mips",
    Bap.Tests.Emu.testLinuxCheckpoints "aarch64" (cuts := [1, 12000]),
    Bap.Tests.Emu.testLinuxCheckpoints "riscv64",
    Bap.Tests.Emu.testLinuxCheckpoints "i686",
    Bap.Tests.Emu.testLinuxCheckpoints "thumb",
    Bap.Tests.Emu.testLinuxCheckpoints "riscv32",
    Bap.Tests.Emu.testLinuxCheckpoints "mips",
    Bap.Tests.Emu.testLinuxCheckpoints "mips64el",
    Bap.Tests.Emu.testLinuxCheckpoints "powerpc",
    Bap.Tests.Emu.testLinuxCheckpoints "powerpc64le",
    Bap.Tests.Emu.testLinuxCheckpoints "x86_64",
    Bap.Tests.Emu.testLinuxResumeTraces "aarch64",
    Bap.Tests.Emu.testLinuxResumeTraces "x86_64" (quanta := [100]) (names := ["libc-threads"]),
    Bap.Tests.Emu.testLinuxResumeTraces "thumb" (quanta := [13]) (names := ["libc-threads"]),
    Bap.Tests.Emu.testLinuxResumeTraces "mips" (quanta := [31]) (names := ["libc-fork"]),
    Bap.Tests.Emu.testLinuxRuntimeModels "aarch64" 17,
    Bap.Tests.Emu.testLinuxRuntimeModels "mips" 4203,
    Bap.Tests.Emu.testLinuxServedCheckpoint "aarch64" 17,
    Bap.Tests.Lifted.testNativeMemory,
    Bap.Tests.Lifted.testNativeMemoryModel,
    Bap.Tests.Emu.testLinuxSignals "x86_64",
    Bap.Tests.Emu.testLinuxSignals "aarch64",
    Bap.Tests.Emu.testLinuxSignals "riscv64",
    Bap.Tests.Emu.testLinuxSignals "riscv32",
    Bap.Tests.Emu.testLinuxSignals "arm",
    Bap.Tests.Emu.testLinuxSignals "thumb",
    Bap.Tests.Emu.testLinuxSignals "i686",
    Bap.Tests.Emu.testLinuxSignals "mips",
    Bap.Tests.Emu.testLinuxSignals "mipsel",
    Bap.Tests.Emu.testLinuxSignals "mips64",
    Bap.Tests.Emu.testLinuxSignals "mips64el",
    Bap.Tests.Emu.testLinuxSignals "powerpc",
    Bap.Tests.Emu.testLinuxSignals "powerpc64",
    Bap.Tests.Emu.testLinuxSignals "powerpc64le",
    Bap.Tests.Emu.testLinuxSignalCheckpoints "aarch64" 99991,
    Bap.Tests.Emu.testLinuxSignalCheckpoints "mips" 99991,
    Bap.Tests.Emu.testGuestHeap,
    Bap.Tests.Emu.testMachineMemory "aarch64",
    Bap.Tests.Emu.testMachineMemory "x86_64",
    Bap.Tests.Emu.testMachineMemory "mips",
    Bap.Tests.Emu.testMachineMemory "thumb",
    Bap.Tests.Emu.testMachineHeapExec "aarch64",
    Bap.Tests.Emu.testLinuxLibraries "x86_64" (ifunc := true),
    Bap.Tests.Emu.testLinuxLibraries "aarch64" (ifunc := true),
    Bap.Tests.Emu.testLinuxLibraries "riscv64",
    Bap.Tests.Emu.testLinuxLibraries "riscv32",
    Bap.Tests.Emu.testLinuxLibraries "arm",
    Bap.Tests.Emu.testLinuxLibraries "thumb",
    Bap.Tests.Emu.testLinuxLibraries "i686",
    Bap.Tests.Emu.testLinuxLibraries "mips",
    Bap.Tests.Emu.testLinuxLibraries "mipsel",
    Bap.Tests.Emu.testLinuxLibraries "mips64",
    Bap.Tests.Emu.testLinuxLibraries "mips64el",
    Bap.Tests.Emu.testLinuxLibraries "powerpc",
    Bap.Tests.Emu.testLinuxLibraries "powerpc64",
    Bap.Tests.Emu.testLinuxLibraries "powerpc64le",
    Bap.Tests.Emu.testLinuxLibraryProcesses "aarch64" "x86_64",
    Bap.Tests.Emu.testLinuxLibraryTls "x86_64",
    Bap.Tests.Emu.testLinuxLibraryTls "aarch64",
    Bap.Tests.Emu.testLinuxLibraryTls "riscv64",
    Bap.Tests.Emu.testLinuxLibraryTls "riscv32",
    Bap.Tests.Emu.testLinuxLibraryTls "arm",
    Bap.Tests.Emu.testLinuxLibraryTls "thumb",
    Bap.Tests.Emu.testLinuxLibraryTls "i686",
    Bap.Tests.Emu.testLinuxLibraryTls "mips",
    Bap.Tests.Emu.testLinuxLibraryTls "mipsel",
    Bap.Tests.Emu.testLinuxLibraryTls "mips64",
    Bap.Tests.Emu.testLinuxLibraryTls "mips64el",
    Bap.Tests.Emu.testLinuxLibraryTls "powerpc" (runsByModule := false),
    Bap.Tests.Emu.testLinuxLibraryTls "powerpc64",
    Bap.Tests.Emu.testLinuxLibraryTls "powerpc64le",
    Bap.Tests.Emu.testRollbackMemory,
    Bap.Tests.Emu.testCheckpointMoments,
    Bap.Tests.Emu.testParallelAtomics,
    Bap.Tests.Emu.testParallelTearing,
    Bap.Tests.Emu.testParallelFences,
    Bap.Tests.Emu.testParallelUnaligned,
    Bap.Tests.Jni.run,
    Bap.Tests.Jni.testState
  ]
  Bap.Tests.Optimize.scaling
  Bap.Tests.Lifted.invalidationScales
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
