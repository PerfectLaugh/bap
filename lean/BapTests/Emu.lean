import BapTests.Support

namespace Bap.Tests.Emu

open Bap

private def reg (name : String) : Var := ⟨name, .imm 64, 0, false⟩

private def shellStreams (commands : List String) : IO (IO.FS.Stream × IO.FS.Stream × IO.Ref String) := do
  let lines ← IO.mkRef commands
  let text ← IO.mkRef ""
  let input : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure ByteArray.empty
    write := fun _ => pure ()
    getLine := do
      match ← lines.get with
      | [] => pure ""
      | line :: rest =>
        lines.set rest
        pure (line ++ "\n")
    putStr := fun _ => pure ()
    isTty := pure false
  }
  let output : IO.FS.Stream := {
    flush := pure ()
    read := fun _ => pure ByteArray.empty
    write := fun _ => pure ()
    getLine := pure ""
    putStr := fun chunk => text.modify (· ++ chunk)
    isTty := pure false
  }
  pure (input, output, text)

private def testDiff : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let emu ← Bap.Emu.riscv64 code 0 0
  let saved ← Bap.Emu.snapshot emu
  Bap.Emu.save emu "native/build/emu-diff.sexp"
  Bap.Emu.write emu 0 (ByteArray.mk #[0, 0])
  Bap.Emu.write emu 4 (ByteArray.mk #[0])
  assertEqual "Emu snapshot diff coalesces changes" [(0, 2), (4, 1)] (← Bap.Emu.diff emu saved)
  assertEqual "Emu checkpoint diff matches snapshot" [(0, 2), (4, 1)] (← Bap.Emu.changedSince emu "native/build/emu-diff.sexp")
  Bap.Emu.restore emu saved
  assertEqual "Emu restored snapshot has no diff" [] (← Bap.Emu.diff emu saved)
  let memory := Bap.Memory.writeRegion (Bap.Memory.empty 64) 0xfe (ByteArray.mk #[1, 2, 3, 4])
  assertTrue "Memory bulk read crosses pages and preserves zeroes"
    (Bap.Memory.readRegion memory 0xfc 8 == ByteArray.mk #[0, 0, 1, 2, 3, 4, 0, 0])
  let persistent ← Jit.createMemory #[0] #[40]
  emu.engine.persistentMemory.set (some persistent)
  emu.engine.persistentVariable.set (some emu.config.memory)
  Bap.Emu.write emu 0 (ByteArray.mk #[41])
  assertEqual "Emu script write updates persistent memory in place" true
    ((← emu.engine.persistentMemory.get).isSome)
  let (_, synchronizedValues) ← Jit.dumpMemory persistent
  assertEqual "Emu persistent memory contains script-written byte" #[41] synchronizedValues

private def testLiveProject : IO Unit := do
  let original := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let emu ← Bap.Emu.riscv64 original 0 0
  Bap.Emu.map emu ⟨0x1000, ByteArray.mk #[1, 2, 3, 4], ⟨true, false, false⟩⟩
  let patched ← LLVM.assemble "riscv64" "addi a0, a0, 2"
  Bap.Emu.write emu 0 patched
  let project ← Bap.Emu.project emu [] [("entry", 0)]
  match project.image, project.disasm with
  | some image, some disasm =>
    assertEqual "Emu live project architecture" Image.Arch.riscv image.arch
    assertEqual "Emu live project includes code and data" 2 image.memory.entries.length
    assertEqual "Emu live project includes symbol" 1 image.symbols.length
    assertTrue "Emu live project uses patched bytes" (image.memory.readByte 0 == some patched[0]!)
    assertTrue "Emu live project preserves data bytes" (image.memory.readByte 0x1000 == some 1)
    assertEqual "Emu live project disassembles only code" 2 disasm.instructions.length
    match disasm.instructions.find? fun insn => insn.address == 0 with
    | some insn => assertTrue "Emu live project decodes patched instruction" ((insn.asm.splitOn "2").length > 1)
    | none => throw <| IO.userError "Emu live project lost patched instruction"
  | _, _ => throw <| IO.userError "Emu live project is incomplete"
  match Bap.Plugin.analyze Bap.Plugin.defaultRegistry project with
  | .error error => throw <| IO.userError s!"live project analysis failed: {repr error}"
  | .ok analyzed =>
    assertEqual "Emu live project analysis instruction count" (some "2") (analyzed.get "instructions")
    assertEqual "Emu live project analysis status" (some "analyzed") (analyzed.get "status")
    Bap.Project.save analyzed "native/build/emu-live-project.sexp"
    let restored ← Bap.Project.loadSaved "native/build/emu-live-project.sexp"
    assertEqual "Emu persisted project keeps analysis" (some "analyzed") (restored.get "status")
    assertEqual "Emu persisted project keeps pass history" analyzed.passed restored.passed
    match restored.image, restored.disasm with
    | some image, some disasm =>
      assertTrue "Emu persisted project keeps patched memory" (image.memory.readByte 0 == some patched[0]!)
      assertEqual "Emu persisted project keeps instructions" 2 disasm.instructions.length
      assertTrue "Emu persisted project keeps BIL" (disasm.instructions.all fun insn => !insn.bil.isEmpty)
    | _, _ => throw <| IO.userError "Emu persisted project is incomplete"

private def testDelaySlots : IO Unit := do
  let r2 := reg "R2"
  let r3 := reg "R3"
  let r4 := reg "R4"
  let r5 := reg "R5"
  let r6 := reg "R6"
  let code := (ByteArray.mk #[0x10, 0x43, 0x00, 0x02]) ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 1") ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 100") ++
    (← LLVM.assemble "mips64" "addiu $5, $5, 1") ++
    (← LLVM.assemble "mips64" "addiu $6, $6, 1")
  let slotInsn ← Target.LLVMLift.decodeMIPS 0 4 code
  assertEqual "Emu MIPS delay slot assembly" "addiu $4, $4, 0x1" slotInsn.asm
  let targetInsn ← Target.LLVMLift.decodeMIPS 0 12 code
  assertEqual "Emu MIPS branch target assembly" "addiu $5, $5, 0x1" targetInsn.asm
  let emu ← Bap.Emu.mips64 code 0 0
  Bap.Emu.setReg emu r2 (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg emu r3 (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg emu r4 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu r5 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu r6 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.traceStart emu
  let branchStep ← Bap.Emu.run emu 1
  assertEqual "Emu MIPS taken branch step" 1 branchStep
  assertEqual "Emu MIPS branch enters delay slot" 4 (← Bap.Emu.pc emu)
  assertBits "Emu MIPS branch leaves slot register unchanged" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.reg emu r4))
  let slotStep ← Bap.Emu.run emu 1
  assertEqual "Emu MIPS delay slot step" 1 slotStep
  assertEqual "Emu MIPS slot reaches branch target" 12 (← Bap.Emu.pc emu)
  assertBits "Emu MIPS delay slot result" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r4))
  let targetStep ← Bap.Emu.run emu 1
  assertEqual "Emu MIPS branch target step" 1 targetStep
  assertEqual "Emu MIPS taken branch execution trace" [0, 4, 12] (← Bap.Emu.tracePcs emu)
  assertEqual "Emu MIPS taken branch reaches target" 16 (← Bap.Emu.pc emu)
  assertBits "Emu MIPS taken branch skips fallthrough" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r4))
  assertBits "Emu MIPS taken branch executes target" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r5))

  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu r3 (.bits (BitVec.ofNat 64 2))
  Bap.Emu.setReg emu r4 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu r5 (.bits (BitVec.ofNat 64 0))
  let untakenSteps ← Bap.Emu.run emu 3
  assertEqual "Emu MIPS untaken branch and slot steps" 3 untakenSteps
  assertEqual "Emu MIPS untaken branch reaches fallthrough" 12 (← Bap.Emu.pc emu)
  assertBits "Emu MIPS untaken branch executes slot and fallthrough" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg emu r4))
  assertBits "Emu MIPS untaken branch skips target" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.reg emu r5))

  let likelyCode := (ByteArray.mk #[0x50, 0x43, 0x00, 0x02]) ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 1") ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 100") ++
    (← LLVM.assemble "mips64" "addiu $5, $5, 1")
  let likelyEmu ← Bap.Emu.mips64 likelyCode 0 0
  Bap.Emu.setReg likelyEmu r2 (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg likelyEmu r3 (.bits (BitVec.ofNat 64 2))
  Bap.Emu.setReg likelyEmu r4 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg likelyEmu r5 (.bits (BitVec.ofNat 64 0))
  let annulledSteps ← Bap.Emu.runUntil likelyEmu 12
  assertEqual "Emu MIPS likely untaken branch annuls slot" 2 annulledSteps
  assertBits "Emu MIPS likely untaken branch skips slot" (BitVec.ofNat 64 100)
    (.ok (← Bap.Emu.reg likelyEmu r4))
  Bap.Emu.setPc likelyEmu 0
  Bap.Emu.setReg likelyEmu r3 (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg likelyEmu r4 (.bits (BitVec.ofNat 64 0))
  let likelyTakenSteps ← Bap.Emu.runUntil likelyEmu 12
  assertEqual "Emu MIPS likely taken branch keeps slot" 2 likelyTakenSteps
  assertBits "Emu MIPS likely taken branch executes slot" (BitVec.ofNat 64 1)
    (.ok (← Bap.Emu.reg likelyEmu r4))

  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu r3 (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg emu r4 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu r5 (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.run emu 1
  assertEqual "Emu MIPS branch stops at delay slot" 4 (← Bap.Emu.pc emu)
  Bap.Emu.save emu "native/build/emu-delay-checkpoint.sexp"
  let pending ← Bap.Emu.snapshot emu
  let second ← Bap.Emu.spawnThread emu 16 7
  Bap.Emu.switchThread emu second
  let _ ← Bap.Emu.run emu 1
  Bap.Emu.switchThread emu 1
  let _ ← Bap.Emu.run emu 2
  assertEqual "Emu thread switch resumes pending target" 16 (← Bap.Emu.pc emu)
  assertBits "Emu thread switch preserves pending delay slot" (BitVec.ofNat 64 1)
    (.ok (← Bap.Emu.reg emu r4))
  assertBits "Emu thread switch preserves other thread" (BitVec.ofNat 64 1)
    (.ok (← Bap.Emu.threadReg emu second r6))
  Bap.Emu.setReg emu r5 (.bits (BitVec.ofNat 64 99))
  Bap.Emu.restore emu pending
  let _ ← Bap.Emu.run emu 2
  assertBits "Emu snapshot restores pending branch" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r5))
  Bap.Emu.restore emu pending
  Bap.Emu.load emu "native/build/emu-delay-checkpoint.sexp"
  let _ ← Bap.Emu.run emu 2
  assertBits "Emu checkpoint restores pending branch" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r5))

private def testThreads : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "sw a0, 0(a1)") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let emu ← Bap.Emu.riscv64 code 0 0
  Bap.Emu.map emu ⟨0x1000, ByteArray.mk (List.replicate 4 0).toArray, ⟨true, true, false⟩⟩
  let output := reg "X10"
  let pointer := reg "X11"
  Bap.Emu.setReg emu output (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu pointer (.bits (BitVec.ofNat 64 0x1000))
  let second ← Bap.Emu.spawnThread emu 0 10
  assertEqual "Emu allocates thread IDs" 2 second
  assertEqual "Emu enumerates threads" [⟨1, 0, false⟩, ⟨2, 0, false⟩] (← Bap.Emu.threads emu)
  Bap.Emu.setThreadReg emu second pointer (.bits (BitVec.ofNat 64 0x1000))
  Bap.Emu.switchThread emu second
  assertEqual "Emu switches current thread" 2 (← Bap.Emu.thread emu)
  let _ ← Bap.Emu.run emu 1
  assertBits "Emu thread argument register" (BitVec.ofNat 64 11)
    (.ok (← Bap.Emu.reg emu output))
  Bap.Emu.switchThread emu 1
  assertBits "Emu parked thread preserves result" (BitVec.ofNat 64 11)
    (.ok (← Bap.Emu.threadReg emu second output))
  assertBits "Emu current thread registers are independent" (BitVec.ofNat 64 0)
    (.ok (← Bap.Emu.reg emu output))
  let _ ← Bap.Emu.run emu 1
  Bap.Emu.switchThread emu second
  let _ ← Bap.Emu.run emu 1
  assertTrue "Emu threads share memory"
    ((ByteArray.mk #[11, 0, 0, 0]) == (← Bap.Emu.read emu 0x1000 4))
  Bap.Emu.setPc emu 0
  Bap.Emu.switchThread emu 1
  Bap.Emu.setPc emu 0
  let scheduled ← Bap.Emu.runPreemptive emu 1 2
  assertEqual "Emu preemptive scheduler executes both threads" 2 scheduled
  assertBits "Emu scheduler preserves first thread" (BitVec.ofNat 64 2)
    (.ok (← Bap.Emu.threadReg emu 1 output))
  assertBits "Emu scheduler preserves second thread" (BitVec.ofNat 64 12)
    (.ok (← Bap.Emu.threadReg emu second output))
  assertEqual "Emu scheduler stops on the quantum boundary" 2 (← Bap.Emu.thread emu)
  Bap.Emu.stopThread emu second
  Bap.Emu.switchThread emu 1
  Bap.Emu.resumeThread emu second
  assertEqual "Emu resumeThread reactivates the saved context" [⟨1, 4, false⟩, ⟨2, 4, false⟩]
    (← Bap.Emu.threads emu)
  Bap.Emu.stopThread emu 1
  let stoppedSteps ← Bap.Emu.runPreemptive emu 1 1
  assertEqual "Emu preemption yields a stopped thread to its caller" 0 stoppedSteps
  assertEqual "Emu preemption does not abandon a stopped thread" 1 (← Bap.Emu.thread emu)
  Bap.Emu.resumeThread emu 1

  let saved ← Bap.Emu.snapshot emu
  Bap.Emu.save emu "native/build/emu-threads-checkpoint.sexp"
  Bap.Emu.setThreadReg emu 1 output (.bits (BitVec.ofNat 64 99))
  Bap.Emu.setThreadReg emu second output (.bits (BitVec.ofNat 64 99))
  Bap.Emu.write emu 0x1000 (ByteArray.mk #[99, 99, 99, 99])
  Bap.Emu.restore emu saved
  assertBits "Emu snapshot restores first thread" (BitVec.ofNat 64 2)
    (.ok (← Bap.Emu.threadReg emu 1 output))
  assertBits "Emu snapshot restores second thread" (BitVec.ofNat 64 12)
    (.ok (← Bap.Emu.threadReg emu second output))
  Bap.Emu.setThreadReg emu 1 output (.bits (BitVec.ofNat 64 99))
  Bap.Emu.setThreadReg emu second output (.bits (BitVec.ofNat 64 99))
  Bap.Emu.load emu "native/build/emu-threads-checkpoint.sexp"
  assertBits "Emu checkpoint restores first thread" (BitVec.ofNat 64 2)
    (.ok (← Bap.Emu.threadReg emu 1 output))
  assertBits "Emu checkpoint restores second thread" (BitVec.ofNat 64 12)
    (.ok (← Bap.Emu.threadReg emu second output))
  assertTrue "Emu checkpoint restores shared memory"
    ((ByteArray.mk #[11, 0, 0, 0]) == (← Bap.Emu.read emu 0x1000 4))
  let third ← Bap.Emu.spawnThread emu 0 7
  assertEqual "Emu checkpoint preserves next thread ID" 3 third
  let parallelCode := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++ (← LLVM.assemble "riscv64" "jal 0")
  let parallelEmu ← Bap.Emu.riscv64 parallelCode 0 0
  Bap.Emu.setReg parallelEmu output (.bits (BitVec.ofNat 64 0))
  let parallelSecond ← Bap.Emu.spawnThread parallelEmu 0 10
  let parallelSteps ← Bap.Emu.runPreemptiveParallel parallelEmu 1
  assertEqual "Emu parallel scheduler executes both threads" 2 parallelSteps
  assertBits "Emu parallel scheduler preserves first thread" (BitVec.ofNat 64 1)
    (.ok (← Bap.Emu.threadReg parallelEmu 1 output))
  assertBits "Emu parallel scheduler preserves second thread" (BitVec.ofNat 64 11)
    (.ok (← Bap.Emu.threadReg parallelEmu parallelSecond output))
  let contextEmu ← Bap.Emu.riscv64 parallelCode 0 0
  Bap.Emu.setReg contextEmu output (.bits (BitVec.ofNat 64 0))
  let contextSecond ← Bap.Emu.spawnThread contextEmu 0 10
  let contextEvents ← IO.mkRef []
  let _ ← Bap.Emu.onCodeWith contextEmu (4, 4) fun current _ => do
    let tid ← Bap.Emu.thread current
    match ← Bap.Emu.reg current output with
    | .bits value => contextEvents.modify fun events => (tid, value.toNat) :: events
    | _ => throw <| IO.userError "context hook register is not a bit vector"
    Bap.Emu.stop current
  let _ ← Bap.Emu.runPreemptiveParallel contextEmu 10
  let sortedEvents := (← contextEvents.get).mergeSort fun left right => left.1 ≤ right.1
  assertEqual "Emu context hooks observe the active worker" [(1, 1), (contextSecond, 11)] sortedEvents
  assertTrue "Emu context hooks stop each active worker"
    ((← Bap.Emu.threads contextEmu).all fun thread => thread.stopped)
  let syscallContextEmu ← Bap.Emu.riscv64 ((← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "ecall")) 0 0
  Bap.Emu.setReg syscallContextEmu output (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg syscallContextEmu (reg "X17") (.bits (BitVec.ofNat 64 39))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg syscallContextEmu (reg s!"X{10 + index}") (.bits (BitVec.ofNat 64 0))
  let syscallContextSecond ← Bap.Emu.spawnThread syscallContextEmu 0 10
  let syscallContextEvents ← IO.mkRef []
  let _ ← Bap.Emu.onSyscallWith syscallContextEmu fun current _ _ => do
    let tid ← Bap.Emu.thread current
    match ← Bap.Emu.reg current output with
    | .bits value => syscallContextEvents.modify fun events => (tid, value.toNat) :: events
    | _ => throw <| IO.userError "context syscall register is not a bit vector"
    Bap.Emu.stop current
    pure (.returnValue 0)
  let _ ← Bap.Emu.runPreemptiveParallel syscallContextEmu 10
  let sortedSyscallEvents := (← syscallContextEvents.get).mergeSort fun left right => left.1 ≤ right.1
  assertEqual "Emu context syscalls observe the active worker"
    [(1, 1), (syscallContextSecond, 11)] sortedSyscallEvents
  assertTrue "Emu context syscalls stop each active worker"
    ((← Bap.Emu.threads syscallContextEmu).all fun thread => thread.stopped)
  let parallelMemoryCode := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "sw a0, 0(a1)") ++ (← LLVM.assemble "riscv64" "jal 0")
  let parallelMemoryEmu ← Bap.Emu.riscv64 parallelMemoryCode 0 0
  Bap.Emu.map parallelMemoryEmu ⟨0x1000, ByteArray.mk (List.replicate 8 0).toArray, ⟨true, true, false⟩⟩
  Bap.Emu.setReg parallelMemoryEmu output (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg parallelMemoryEmu pointer (.bits (BitVec.ofNat 64 0x1000))
  let parallelMemorySecond ← Bap.Emu.spawnThread parallelMemoryEmu 0 10
  Bap.Emu.setThreadReg parallelMemoryEmu parallelMemorySecond pointer (.bits (BitVec.ofNat 64 0x1004))
  let parallelMemorySteps ← Bap.Emu.runPreemptiveParallel parallelMemoryEmu 2
  assertEqual "Emu parallel scheduler counts memory workers" 4 parallelMemorySteps
  assertTrue "Emu parallel scheduler joins first memory output"
    ((ByteArray.mk #[1, 0, 0, 0]) == (← Bap.Emu.read parallelMemoryEmu 0x1000 4))
  assertTrue "Emu parallel scheduler joins second memory output"
    ((ByteArray.mk #[11, 0, 0, 0]) == (← Bap.Emu.read parallelMemoryEmu 0x1004 4))
  assertBits "Emu parallel scheduler preserves second memory worker" (BitVec.ofNat 64 11)
    (.ok (← Bap.Emu.threadReg parallelMemoryEmu parallelMemorySecond output))
  Bap.Emu.cloneProcessMemory parallelMemoryEmu parallelMemorySecond
  Bap.Emu.switchThread parallelMemoryEmu 1
  Bap.Emu.setPc parallelMemoryEmu 0
  Bap.Emu.switchThread parallelMemoryEmu parallelMemorySecond
  Bap.Emu.setPc parallelMemoryEmu 0
  let _ ← Bap.Emu.runPreemptiveParallel parallelMemoryEmu 4
  assertTrue "Emu fork memory is copy on write"
    ((ByteArray.mk #[2, 0, 0, 0]) == (← Bap.Emu.read parallelMemoryEmu 0x1000 4))
  let childMemory ← parallelMemoryEmu.processMemory.get
  let some childNativeMemory := childMemory.get? parallelMemorySecond
    | throw <| IO.userError "missing child memory"
  let childNative ← Jit.readMemory childNativeMemory 0x1004
  assertEqual "Emu fork memory preserves child bytes" 12 childNative.toNat
  Bap.Emu.save parallelMemoryEmu "native/build/emu-cow-checkpoint.sexp"
  Bap.Emu.load parallelMemoryEmu "native/build/emu-cow-checkpoint.sexp"
  Bap.Emu.switchThread parallelMemoryEmu 1
  Bap.Emu.setPc parallelMemoryEmu 0
  Bap.Emu.switchThread parallelMemoryEmu parallelMemorySecond
  Bap.Emu.setPc parallelMemoryEmu 0
  let _ ← Bap.Emu.runPreemptiveParallel parallelMemoryEmu 4
  assertTrue "Emu checkpoint restores parent memory"
    ((ByteArray.mk #[3, 0, 0, 0]) == (← Bap.Emu.read parallelMemoryEmu 0x1000 4))
  let restoredMemory ← parallelMemoryEmu.processMemory.get
  let some restoredNativeMemory := restoredMemory.get? parallelMemorySecond
    | throw <| IO.userError "missing restored child memory"
  let restoredNative ← Jit.readMemory restoredNativeMemory 0x1004
  assertEqual "Emu checkpoint restores child memory" 13 restoredNative.toNat

set_option maxRecDepth 8000 in
private def diffAndCodecRegressions : IO Unit := do
  let rw : Primus.Protection := ⟨true, true, false⟩
  let region (address : Nat) (bytes : List UInt8) : Bap.Emu.Region := ⟨address, ByteArray.mk bytes.toArray, rw⟩
  assertEqual "diff reports bytes of a grown region" [(0x12, 2)]
    (Bap.Emu.diffRanges [region 0x10 [1, 2]] [region 0x10 [1, 2, 3, 4]])
  assertEqual "diff reports bytes of a shrunk region" [(0x11, 1)]
    (Bap.Emu.diffRanges [region 0x10 [1, 2]] [region 0x10 [1]])
  assertEqual "diff reports overlapping tables once" [(0x12, 1)]
    (Bap.Emu.diffRanges [region 0x10 [1, 2, 3, 4]] [region 0x10 [1, 2], region 0x12 [9, 4]])
  assertEqual "diff merges adjacent regions" [(0x10, 4)]
    (Bap.Emu.diffRanges [region 0x10 [1, 2], region 0x12 [3, 4]] [region 0x10 [5, 6], region 0x12 [7, 8]])
  assertEqual "diff of identical tables is empty" []
    (Bap.Emu.diffRanges [region 0x10 [1, 2]] [region 0x10 [1, 2]])
  let register (name : String) : Bap.Var := ⟨name, .imm 256, 0, false⟩
  let snapshotOf (env : Bil.Env) (pc : Nat := 0x1000) : Bap.Emu.Snapshot :=
    ⟨{ env := env }, pc, [region 0x10 [1, 2]], false, [], 0, 0, none, []⟩
  let wide := BitVec.ofNat 256 (2 ^ 255 + 7)
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [(register "ymm", .bits wide)]) with
  | .error error => throw <| IO.userError error
  | .ok data =>
    match Bap.Emu.decodeBinarySnapshot data with
    | .error error => throw <| IO.userError error
    | .ok decoded =>
      assertBits "binary checkpoint keeps a 256-bit value" wide (Bil.lookup decoded.state.env (register "ymm"))
      assertEqual "binary checkpoint keeps the pc" 0x1000 decoded.pc
  let tooWide : Value := .bits (BitVec.ofNat 257 (2 ^ 256))
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [(register "zmm", tooWide)]) with
  | .error _ => IO.println "ok: binary checkpoint refuses a value over 256 bits"
  | .ok _ => throw <| IO.userError "binary checkpoint accepted a 257-bit value"
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [] (2 ^ 64)) with
  | .error _ => IO.println "ok: binary checkpoint refuses a pc over 64 bits"
  | .ok _ => throw <| IO.userError "binary checkpoint accepted a 65-bit pc"

set_option maxRecDepth 4000 in
private def runEmulator : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi a0, a1, 2") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++ (← LLVM.assemble "riscv64" "jal 4")
  assertEqual "Emu test code size" 12 code.size
  let thirdInsn ← Target.LLVMLift.decodeRISCV 8 8 (code.extract 8 12)
  assertEqual "Emu third instruction size" 4 thirdInsn.size
  let emu ← Bap.Emu.riscv64 code 0 0
  let input := reg "X11"
  let output := reg "X10"
  Bap.Emu.setReg emu input (.bits (BitVec.ofNat 64 4))
  let mapped ← Bap.Emu.regions emu
  assertEqual "Emu mapped region count" 1 mapped.length
  let regionSize ← match mapped with
    | [region] => pure region.2.1
    | _ => throw <| IO.userError "expected one Emu region"
  assertEqual "Emu mapped region size" code.size regionSize
  let steps ← Bap.Emu.runUntil emu 12
  assertEqual "Emu run-until steps" 3 steps
  assertEqual "Emu run-until PC" 12 (← Bap.Emu.pc emu)
  let result ← Bap.Emu.reg emu output
  assertBits "Emu register result" (BitVec.ofNat 64 7) (.ok result)
  let original ← Bap.Emu.read emu 0 4
  assertTrue "Emu instruction memory read" ((code.extract 0 4) == original)

  let replacement ← LLVM.assemble "riscv64" "addi a0, a1, 5"
  Bap.Emu.write emu 0 replacement
  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu input (.bits (BitVec.ofNat 64 1))
  let patchedSteps ← Bap.Emu.run emu 1
  assertEqual "Emu patched instruction steps" 1 patchedSteps
  let patchedResult ← Bap.Emu.reg emu output
  assertBits "Emu self-modifying code result" (BitVec.ofNat 64 6) (.ok patchedResult)
  let patchedBytes ← Bap.Emu.read emu 0 4
  assertTrue "Emu patched instruction bytes" (replacement == patchedBytes)

  let snapshot ← Bap.Emu.snapshot emu
  Bap.Emu.setReg emu output (.bits (BitVec.ofNat 64 99))
  let overwritten ← LLVM.assemble "riscv64" "addi a0, a1, 9"
  Bap.Emu.write emu 0 overwritten
  Bap.Emu.setPc emu 8
  Bap.Emu.restore emu snapshot
  assertEqual "Emu snapshot restores PC" 4 (← Bap.Emu.pc emu)
  let restoredResult ← Bap.Emu.reg emu output
  assertBits "Emu snapshot restores registers" (BitVec.ofNat 64 6) (.ok restoredResult)
  let restoredBytes ← Bap.Emu.read emu 0 4
  assertTrue "Emu snapshot restores code" (replacement == restoredBytes)
  assertTrue "Emu snapshot restores running state" !(← Bap.Emu.stopped emu)
  let resumedSteps ← Bap.Emu.run emu 1
  assertEqual "Emu resume after restore" 1 resumedSteps
  let resumedResult ← Bap.Emu.reg emu output
  assertBits "Emu restored execution result" (BitVec.ofNat 64 7) (.ok resumedResult)

  let previousPc ← Bap.Emu.pc emu
  let functionCode := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "jalr x0, 0(ra)")
  Bap.Emu.write emu 0 functionCode
  let returned ← Bap.Emu.call emu 0 0x1000 [41]
  assertBits "Emu call return value" (BitVec.ofNat 64 42) (.ok returned)
  assertEqual "Emu call restores PC" previousPc (← Bap.Emu.pc emu)
  let restoredCallResult ← Bap.Emu.reg emu output
  assertBits "Emu call restores registers" (BitVec.ofNat 64 7) (.ok restoredCallResult)
  let functionBytes ← Bap.Emu.read emu 0 functionCode.size
  assertTrue "Emu call preserves memory effects" (functionCode == functionBytes)

  let stubRegion : Bap.Emu.Region := ⟨0x1000, functionCode, ⟨true, true, true⟩⟩
  Bap.Emu.map emu stubRegion
  let stubResult ← Bap.Emu.stub emu 0x1000 0x2000 [41]
  assertBits "Emu native stub result" (BitVec.ofNat 64 42) (.ok stubResult)
  assertEqual "Emu native stub restores PC" previousPc (← Bap.Emu.pc emu)
  let stubRegions ← Bap.Emu.regions emu
  assertEqual "Emu native stub region persists" 2 stubRegions.length

  Bap.Emu.write emu 0 code
  Bap.Emu.setPc emu 0
  let codeHits ← IO.mkRef 0
  let codeHook ← Bap.Emu.onCode emu (0, 4) fun _ => codeHits.modify (· + 1)
  let hookedSteps ← Bap.Emu.run emu 2
  assertEqual "Emu code hooks allow execution" 2 hookedSteps
  assertEqual "Emu code hook range filtering" 2 (← codeHits.get)
  assertEqual "Emu two steps stop at PC 8" 8 (← Bap.Emu.pc emu)
  let stopHook ← Bap.Emu.onCode emu (8, 8) fun _ => Bap.Emu.stop emu
  let stoppedSteps ← Bap.Emu.run emu 10
  assertEqual "Emu code hook stops before instruction" 0 stoppedSteps
  assertTrue "Emu code hook stopped state" (← Bap.Emu.stopped emu)
  assertEqual "Emu code hook stop PC" 8 (← Bap.Emu.pc emu)
  Bap.Emu.removeHook emu stopHook
  Bap.Emu.resume emu
  let removedSteps ← Bap.Emu.run emu 1
  assertEqual "Emu removed hook allows execution" 1 removedSteps
  assertEqual "Emu removed hook does not refire" 2 (← codeHits.get)
  Bap.Emu.removeHook emu codeHook
  Bap.Emu.clearHooks emu

  Bap.Emu.traceStart emu
  Bap.Emu.setPc emu 0
  let _ ← Bap.Emu.run emu 2
  assertEqual "Emu trace records executed PCs" [0, 4] (← Bap.Emu.tracePcs emu)
  Bap.Emu.traceStart emu
  Bap.Emu.setPc emu 8
  Bap.Emu.stop emu
  assertTrue "Emu stopped instruction is not traced" !(← Bap.Emu.step emu)
  assertEqual "Emu trace reset excludes stopped instruction" [] (← Bap.Emu.traceStop emu)
  Bap.Emu.traceStart emu
  Bap.Emu.resume emu
  let _ ← Bap.Emu.run emu 1
  assertEqual "Emu trace stops in execution order" [8] (← Bap.Emu.traceStop emu)
  Bap.Emu.traceStartCapacity emu 2
  Bap.Emu.setPc emu 0
  let _ ← Bap.Emu.run emu 3
  assertEqual "Emu bounded PC trace retains newest blocks" [4, 8] (← Bap.Emu.tracePcs emu)
  assertEqual "Emu bounded PC trace reports evictions" 1 (← Bap.Emu.traceDroppedPcs emu)

  Bap.Emu.setPc emu 8
  let beforeCheckpoint ← Bap.Emu.reg emu output
  assertBits "Emu checkpoint input register" (BitVec.ofNat 64 4) (.ok beforeCheckpoint)
  Bap.Emu.save emu "native/build/emu-checkpoint.sexp"
  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu output (.bits (BitVec.ofNat 64 99))
  let checkpointOverwrite ← LLVM.assemble "riscv64" "addi a0, a1, 9"
  Bap.Emu.write emu 0 checkpointOverwrite
  Bap.Emu.load emu "native/build/emu-checkpoint.sexp"
  assertEqual "Emu checkpoint restores PC" 8 (← Bap.Emu.pc emu)
  let checkpointResult ← Bap.Emu.reg emu output
  assertBits "Emu checkpoint restores registers" (BitVec.ofNat 64 4) (.ok checkpointResult)
  let checkpointBytes ← Bap.Emu.read emu 0 4
  assertTrue "Emu checkpoint restores code" ((code.extract 0 4) == checkpointBytes)
  let checkpointSteps ← Bap.Emu.run emu 1
  assertEqual "Emu checkpoint resumes execution" 1 checkpointSteps

  let memoryCode := (← LLVM.assemble "riscv64" "addi a0, x0, 42") ++
    (← LLVM.assemble "riscv64" "sw a0, 0(a1)") ++
    (← LLVM.assemble "riscv64" "lw a2, 0(a1)")
  let memoryEmu ← Bap.Emu.riscv64 memoryCode 0 0
  Bap.Emu.map memoryEmu ⟨0x1000, ByteArray.mk (List.replicate 4 0).toArray, ⟨true, true, false⟩⟩
  Bap.Emu.setReg memoryEmu input (.bits (BitVec.ofNat 64 0x1000))
  let memoryEvents ← IO.mkRef []
  let writeHook ← Bap.Emu.onWrite memoryEmu (0x1000, 0x1003) fun address size value => do
    assertTrue "Emu write hook runs before store"
      ((ByteArray.mk #[0, 0, 0, 0]) == (← Bap.Emu.read memoryEmu 0x1000 4))
    memoryEvents.modify fun events => (true, address, size, value) :: events
  let readHook ← Bap.Emu.onRead memoryEmu (0x1000, 0x1003) fun address size => do
    memoryEvents.modify fun events => (false, address, size, 0) :: events
  let missedWrites ← IO.mkRef 0
  let _ ← Bap.Emu.onWrite memoryEmu (0x2000, 0x2000) fun _ _ _ => missedWrites.modify (· + 1)
  Bap.Emu.traceStartAccesses memoryEmu 4
  let memorySteps ← Bap.Emu.run memoryEmu 3
  assertEqual "Emu memory hook instruction count" 3 memorySteps
  assertEqual "Emu whole-access memory hook events"
    [(true, 0x1000, 4, 42), (false, 0x1000, 4, 0)]
    (← memoryEvents.get).reverse
  assertEqual "Emu memory hooks filter ranges" 0 (← missedWrites.get)
  assertBits "Emu hooked load result" (BitVec.ofNat 64 42) (.ok (← Bap.Emu.reg memoryEmu (reg "X12")))
  assertEqual "Emu memory hooks retain native execution" 3 (← Bap.Primus.Lifted.stats memoryEmu.engine).nativeRuns
  match ← Bap.Emu.traceAccesses memoryEmu with
  | [written, loaded] =>
    assertEqual "Emu memory trace write record"
      ({ insn := 1, pc := 4, address := 0x1000, size := 4, write := true, value := some 42, thread := 1 } : Bap.Emu.TraceAccess)
      written
    assertEqual "Emu memory trace read record"
      ({ insn := 2, pc := 8, address := 0x1000, size := 4, write := false, value := none, thread := 1 } : Bap.Emu.TraceAccess)
      loaded
  | _ => throw <| IO.userError "Emu memory trace expected two accesses"
  assertEqual "Emu memory trace access count" 2 (← Bap.Emu.traceAccessesCount memoryEmu)
  assertEqual "Emu memory trace has no evictions" 0 (← Bap.Emu.traceDroppedAccesses memoryEmu)
  assertEqual "Emu memory trace preserves PC history" [0, 4, 8] (← Bap.Emu.traceStop memoryEmu)
  Bap.Emu.removeHook memoryEmu readHook
  Bap.Emu.removeHook memoryEmu writeHook
  Bap.Emu.setPc memoryEmu 8
  let _ ← Bap.Emu.run memoryEmu 1
  assertEqual "Emu removed memory hooks do not refire" 2 (← memoryEvents.get).length

  let ringEmu ← Bap.Emu.riscv64 memoryCode 0 0
  Bap.Emu.map ringEmu ⟨0x1000, ByteArray.mk (List.replicate 4 0).toArray, ⟨true, true, false⟩⟩
  Bap.Emu.setReg ringEmu input (.bits (BitVec.ofNat 64 0x1000))
  Bap.Emu.traceStartAccesses ringEmu 1
  let _ ← Bap.Emu.run ringEmu 3
  match ← Bap.Emu.traceAccesses ringEmu with
  | [loaded] =>
    assertEqual "Emu bounded trace retains newest access" (8, false) (loaded.pc, loaded.write)
  | _ => throw <| IO.userError "Emu bounded trace expected one access"
  assertEqual "Emu bounded trace counts all accesses" 2 (← Bap.Emu.traceAccessesCount ringEmu)
  assertEqual "Emu bounded trace reports eviction" 1 (← Bap.Emu.traceDroppedAccesses ringEmu)
  Bap.Emu.setPc ringEmu 0
  Bap.Emu.traceStartWatch ringEmu (0x2000, 0x2000) 4
  let _ ← Bap.Emu.run ringEmu 3
  assertEqual "Emu watched trace filters accesses" [] (← Bap.Emu.traceAccesses ringEmu)
  assertEqual "Emu watched trace count excludes misses" 0 (← Bap.Emu.traceAccessesCount ringEmu)
  assertEqual "Emu watched trace still records PCs" [0, 4, 8] (← Bap.Emu.traceStop ringEmu)

  let readFaultEmu ← Bap.Emu.riscv64 (← LLVM.assemble "riscv64" "lw a0, 0(a1)") 0 0
  Bap.Emu.setReg readFaultEmu input (.bits (BitVec.ofNat 64 0x9000))
  Bap.Emu.setReg readFaultEmu output (.bits (BitVec.ofNat 64 7))
  let readFaulted ← try
    let _ ← Bap.Emu.step readFaultEmu
    pure false
  catch _ => pure true
  assertTrue "Emu unmapped guest read faults" readFaulted
  assertEqual "Emu read fault preserves PC" 0 (← Bap.Emu.pc readFaultEmu)
  assertBits "Emu read fault rolls back destination" (BitVec.ofNat 64 7)
    (.ok (← Bap.Emu.reg readFaultEmu output))
  match ← Bap.Emu.failure readFaultEmu with
  | some fault =>
      assertEqual "Emu guest read fault details"
        (0, 0x9000, Bap.Emu.MemoryOperation.read, 1) (fault.pc, fault.address, fault.operation, fault.thread)
  | none => throw <| IO.userError "Emu guest read fault was not recorded"

  let pushEmu ← Bap.Emu.x86_64 (← LLVM.assemble "x86_64" "pushq %rax") 0 0
  Bap.Emu.map pushEmu ⟨0x1ff0, ByteArray.mk (List.replicate 32 0).toArray, ⟨true, false, false⟩⟩
  Bap.Emu.setReg pushEmu (reg "RSP") (.bits (BitVec.ofNat 64 0x2004))
  Bap.Emu.setReg pushEmu (reg "RAX") (.bits (BitVec.ofNat 64 42))
  let writeFaulted ← try
    let _ ← Bap.Emu.step pushEmu
    pure false
  catch _ => pure true
  assertTrue "Emu read-only guest write faults" writeFaulted
  assertEqual "Emu write fault preserves PC" 0 (← Bap.Emu.pc pushEmu)
  assertBits "Emu write fault rolls back stack pointer" (BitVec.ofNat 64 0x2004)
    (.ok (← Bap.Emu.reg pushEmu (reg "RSP")))
  assertTrue "Emu write fault rolls back memory"
    ((ByteArray.mk (List.replicate 8 0).toArray) == (← Bap.Emu.read pushEmu 0x1ffc 8))
  match ← Bap.Emu.failure pushEmu with
  | some fault =>
      assertEqual "Emu guest write fault details"
        (0, 0x1ffc, Bap.Emu.MemoryOperation.write, 1) (fault.pc, fault.address, fault.operation, fault.thread)
  | none => throw <| IO.userError "Emu guest write fault was not recorded"

  let patched ← LLVM.assemble "riscv64" "addi a0, x0, 42"
  let patchWord := (List.range 4).foldl (init := 0) fun word index =>
    word + patched[index]!.toNat * 256 ^ index
  let smcCode := (← LLVM.assemble "riscv64" "addi a0, x0, 40") ++
    (← LLVM.assemble "riscv64" "sw a1, 0(a2)") ++ (← LLVM.assemble "riscv64" "jal -8")
  let smcEmu ← Bap.Emu.riscv64 smcCode 0 0
  Bap.Emu.setReg smcEmu input (.bits (BitVec.ofNat 64 patchWord))
  Bap.Emu.setReg smcEmu (reg "X12") (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.run smcEmu 2
  assertTrue "Emu guest store updates mapped code" (patched == (← Bap.Emu.read smcEmu 0 4))
  assertEqual "Emu guest code write preserves unrelated JIT blocks" 1 (← smcEmu.engine.cache.get).size
  let _ ← Bap.Emu.run smcEmu 1
  assertEqual "Emu self-modifying test returns to entry" 0 (← Bap.Emu.pc smcEmu)
  let _ ← Bap.Emu.run smcEmu 1
  assertBits "Emu guest code write invalidates native lift" (BitVec.ofNat 64 42)
    (.ok (← Bap.Emu.reg smcEmu output))
  assertEqual "Emu guest code write lifts the patched instruction again" 4
    (← Bap.Primus.Lifted.stats smcEmu.engine).lifts

  let x86Code := (← LLVM.assemble "x86_64" "movq $40, %rax") ++
    (← LLVM.assemble "x86_64" "addq $2, %rax")
  let x86Emu ← Bap.Emu.x86_64 x86Code 0 0
  let x86Steps ← Bap.Emu.run x86Emu 2
  assertEqual "Emu x86-64 instruction count" 2 x86Steps
  let x86Result ← Bap.Emu.reg x86Emu (reg "RAX")
  assertBits "Emu x86-64 result" (BitVec.ofNat 64 42) (.ok x86Result)

  let armCode := (← LLVM.assemble "aarch64" "movz x0, 40") ++
    (← LLVM.assemble "aarch64" "add x0, x0, 2")
  let armEmu ← Bap.Emu.aarch64 armCode 0 0
  let armSteps ← Bap.Emu.run armEmu 2
  assertEqual "Emu AArch64 instruction count" 2 armSteps
  let armResult ← Bap.Emu.reg armEmu (reg "X0")
  assertBits "Emu AArch64 result" (BitVec.ofNat 64 42) (.ok armResult)

  let syscallEmu ← Bap.Emu.riscv64 ((← LLVM.assemble "riscv64" "ecall") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")) 0 0
  Bap.Emu.setReg syscallEmu (reg "X17") (.bits (BitVec.ofNat 64 39))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg syscallEmu (reg s!"X{10 + index}") (.bits (BitVec.ofNat 64 (index + 1)))
  let syscallOrder ← IO.mkRef []
  let defaultSyscallHook ← Bap.Emu.onSyscall syscallEmu fun number args => do
    assertEqual "Emu RISC-V syscall number" 39 number
    assertEqual "Emu RISC-V syscall arguments" [1, 2, 3, 4, 5, 6] args
    syscallOrder.modify fun order => "default" :: order
    pure .default
  let returnSyscallHook ← Bap.Emu.onSyscall syscallEmu fun _ _ => do
    syscallOrder.modify fun order => "return" :: order
    pure (.returnValue 100)
  let syscallSteps ← Bap.Emu.run syscallEmu 2
  assertEqual "Emu handled RISC-V syscall continues" 2 syscallSteps
  assertEqual "Emu RISC-V syscall resumes at next PC" 8 (← Bap.Emu.pc syscallEmu)
  assertEqual "Emu syscall hooks run in registration order" ["default", "return"] (← syscallOrder.get).reverse
  assertBits "Emu RISC-V syscall return value" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg syscallEmu output))
  Bap.Emu.removeHook syscallEmu defaultSyscallHook
  Bap.Emu.removeHook syscallEmu returnSyscallHook
  Bap.Emu.setPc syscallEmu 0
  let defaultSyscallSteps ← Bap.Emu.run syscallEmu 1
  assertEqual "Emu unhandled syscall stops" 0 defaultSyscallSteps
  assertEqual "Emu unhandled syscall preserves PC" 0 (← Bap.Emu.pc syscallEmu)
  assertTrue "Emu unhandled syscall sets stopped state" (← Bap.Emu.stopped syscallEmu)

  let x86SyscallEmu ← Bap.Emu.x86_64 ((← LLVM.assemble "x86_64" "syscall") ++
    (← LLVM.assemble "x86_64" "addq $1, %rax")) 0 0
  Bap.Emu.setReg x86SyscallEmu (reg "RAX") (.bits (BitVec.ofNat 64 39))
  (["RDI", "RSI", "RDX", "R10", "R8", "R9"]).zip [1, 2, 3, 4, 5, 6] |>.forM fun binding =>
    Bap.Emu.setReg x86SyscallEmu (reg binding.1) (.bits (BitVec.ofNat 64 binding.2))
  let x86SyscallHook ← Bap.Emu.onSyscall x86SyscallEmu fun number args => do
    assertEqual "Emu x86-64 syscall number" 39 number
    assertEqual "Emu x86-64 syscall arguments" [1, 2, 3, 4, 5, 6] args
    pure (.returnValue 100)
  let x86SyscallSteps ← Bap.Emu.run x86SyscallEmu 2
  assertEqual "Emu handled x86-64 syscall continues" 2 x86SyscallSteps
  assertEqual "Emu x86-64 syscall resumes at next PC" 6 (← Bap.Emu.pc x86SyscallEmu)
  assertBits "Emu x86-64 syscall return value" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg x86SyscallEmu (reg "RAX")))
  Bap.Emu.removeHook x86SyscallEmu x86SyscallHook

  let armSyscallEmu ← Bap.Emu.aarch64 ((← LLVM.assemble "aarch64" "svc #0") ++
    (← LLVM.assemble "aarch64" "add x0, x0, 1")) 0 0
  Bap.Emu.setReg armSyscallEmu (reg "X8") (.bits (BitVec.ofNat 64 64))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg armSyscallEmu (reg s!"X{index}") (.bits (BitVec.ofNat 64 (index + 1)))
  let armSyscallHook ← Bap.Emu.onSyscall armSyscallEmu fun number args => do
    assertEqual "Emu AArch64 syscall number" 64 number
    assertEqual "Emu AArch64 syscall arguments" [1, 2, 3, 4, 5, 6] args
    pure (.returnValue 100)
  let armSyscallSteps ← Bap.Emu.run armSyscallEmu 2
  assertEqual "Emu handled AArch64 syscall continues" 2 armSyscallSteps
  assertEqual "Emu AArch64 syscall resumes at next PC" 8 (← Bap.Emu.pc armSyscallEmu)
  assertBits "Emu AArch64 syscall return value" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg armSyscallEmu (reg "X0")))
  Bap.Emu.removeHook armSyscallEmu armSyscallHook

  let intrinsicEmu ← Bap.Emu.x86_64 ((← LLVM.assemble "x86_64" "hlt") ++
    (← LLVM.assemble "x86_64" "addq $1, %rax")) 0 0
  Bap.Emu.setReg intrinsicEmu (reg "RAX") (.bits (BitVec.ofNat 64 40))
  let missedIntrinsics ← IO.mkRef 0
  let _ ← Bap.Emu.onIntrinsic intrinsicEmu "other" fun _ => do
    missedIntrinsics.modify (· + 1)
    pure .default
  let defaultIntrinsicHook ← Bap.Emu.onIntrinsic intrinsicEmu "hlt" fun address => do
    assertEqual "Emu intrinsic receives current PC" 0 address
    pure .default
  let proceedIntrinsicHook ← Bap.Emu.onIntrinsic intrinsicEmu "hlt" fun _ => do
    Bap.Emu.setReg intrinsicEmu (reg "RAX") (.bits (BitVec.ofNat 64 42))
    pure .proceed
  let intrinsicSteps ← Bap.Emu.run intrinsicEmu 2
  assertEqual "Emu handled intrinsic continues" 2 intrinsicSteps
  assertEqual "Emu intrinsic resumes at next PC" 5 (← Bap.Emu.pc intrinsicEmu)
  assertEqual "Emu intrinsic filters names" 0 (← missedIntrinsics.get)
  assertBits "Emu intrinsic models result registers" (BitVec.ofNat 64 43)
    (.ok (← Bap.Emu.reg intrinsicEmu (reg "RAX")))
  Bap.Emu.removeHook intrinsicEmu defaultIntrinsicHook
  Bap.Emu.removeHook intrinsicEmu proceedIntrinsicHook
  Bap.Emu.setPc intrinsicEmu 0
  let defaultIntrinsicSteps ← Bap.Emu.run intrinsicEmu 1
  assertEqual "Emu unhandled intrinsic stops" 0 defaultIntrinsicSteps
  assertEqual "Emu unhandled intrinsic preserves PC" 0 (← Bap.Emu.pc intrinsicEmu)

  let wildcardEmu ← Bap.Emu.riscv64 ((← LLVM.assemble "riscv64" "ecall") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")) 0 0
  let wildcardHook ← Bap.Emu.onIntrinsic wildcardEmu "*" fun _ => do
    Bap.Emu.setReg wildcardEmu output (.bits (BitVec.ofNat 64 100))
    pure .proceed
  let wildcardSteps ← Bap.Emu.run wildcardEmu 2
  assertEqual "Emu wildcard intrinsic handles syscall" 2 wildcardSteps
  assertBits "Emu wildcard intrinsic resumes execution" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg wildcardEmu output))
  Bap.Emu.removeHook wildcardEmu wildcardHook

  let breakEmu ← Bap.Emu.riscv64 ((← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")) 0 0
  Bap.Emu.setReg breakEmu output (.bits (BitVec.ofNat 64 40))
  let _ ← Bap.Emu.addBreakpoint breakEmu 4
  let breakSteps ← Bap.Emu.run breakEmu 10
  assertEqual "Emu breakpoint stops before instruction" 1 breakSteps
  assertEqual "Emu breakpoint preserves PC" 4 (← Bap.Emu.pc breakEmu)
  assertTrue "Emu breakpoint sets stopped state" (← Bap.Emu.stopped breakEmu)
  Bap.Emu.resume breakEmu
  let resumedBreakSteps ← Bap.Emu.run breakEmu 1
  assertEqual "Emu breakpoint does not replay on resume" 1 resumedBreakSteps
  assertEqual "Emu resumed breakpoint advances PC" 8 (← Bap.Emu.pc breakEmu)
  Bap.Emu.setPc breakEmu 4
  let revisitedBreakSteps ← Bap.Emu.run breakEmu 1
  assertEqual "Emu breakpoint fires on later visits" 0 revisitedBreakSteps
  Bap.Emu.removeBreakpoint breakEmu 4
  Bap.Emu.resume breakEmu
  let _ ← Bap.Emu.run breakEmu 1
  assertBits "Emu removed breakpoint allows execution" (BitVec.ofNat 64 43)
    (.ok (← Bap.Emu.reg breakEmu output))

  let shellCode := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let shellPatch ← LLVM.assemble "riscv64" "addi a0, a0, 2"
  let patchWords := shellPatch.toList.map fun byte =>
    let digits := String.ofList (Nat.toDigits 16 byte.toNat)
    if digits.length < 2 then "0" ++ digits else digits
  let patchText := String.intercalate " " patchWords
  let shellEmu ← Bap.Emu.riscv64 shellCode 0 0
  let (shellInput, shellOutput, shellText) ← shellStreams [
    "help", "pc", "set X10 40", "reg X10", "snap", "step", "restore", "reg X10",
    "write 0 " ++ patchText, "x 0 4", "save native/build/emu-shell-checkpoint.sexp",
    "break 4", "breaks", "continue", "delete 4", "continue 8", "q"
  ]
  Bap.Emu.shell shellEmu shellInput shellOutput
  let shellOutputText ← shellText.get
  assertTrue "Emu shell prints help" ((shellOutputText.splitOn "help pc regs").length > 1)
  assertTrue "Emu shell reads registers" ((shellOutputText.splitOn "X10=64:0x28").length > 1)
  assertTrue "Emu shell dumps memory" ((shellOutputText.splitOn patchText).length > 1)
  assertEqual "Emu shell continue reaches target" 8 (← Bap.Emu.pc shellEmu)
  assertBits "Emu shell edits and executes code" (BitVec.ofNat 64 43)
    (.ok (← Bap.Emu.reg shellEmu output))
  assertEqual "Emu shell deletes breakpoints" [] (← Bap.Emu.breakpoints shellEmu)
  assertTrue "Emu shell leaves resumed program running" !(← Bap.Emu.stopped shellEmu)

  testThreads
  testDelaySlots
  testLiveProject
  testDiff

  Bap.Emu.stop emu
  assertTrue "Emu stopped state" (← Bap.Emu.stopped emu)
  assertTrue "Emu stopped step does not execute" !(← Bap.Emu.step emu)
  Bap.Emu.resume emu
  assertTrue "Emu resumed state" !(← Bap.Emu.stopped emu)

def run : IO Unit := do
  diffAndCodecRegressions
  runEmulator

end Bap.Tests.Emu
