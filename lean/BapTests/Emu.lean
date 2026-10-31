import BapTests.Support

namespace Bap.Tests.Emu

open Bap

private def reg (name : String) : Var := ⟨name, .imm 64, 0, false⟩

/-- The configuration that the tests run under. All that they check of an emulator holds under each. -/
private initialize tuningRef : IO.Ref (Option (Nat × Nat × Nat)) ← IO.mkRef none

/-- The change to a configuration that makes it the one the tests run under. -/
private def tuned : IO (Bap.Emu.Config → Bap.Emu.Config) := do
  match ← tuningRef.get with
  | none => pure id
  | some (hotThreshold, cacheLimit, rangeLimit) =>
    pure fun config => { config with hotThreshold, cacheLimit, rangeLimit }

/-- Whether the tests run on the machine with neither ranges nor an interpreted start, whose counters some of them look at. -/
private initialize stepwise : IO.Ref Bool ← IO.mkRef false

namespace Tuned

def riscv64 (code : ByteArray) (base entry : Nat) : IO Bap.Emu.Emu := do Bap.Emu.riscv64 code base entry (adjust := ← tuned)
def riscv32 (code : ByteArray) (base entry : Nat) : IO Bap.Emu.Emu := do Bap.Emu.riscv32 code base entry (adjust := ← tuned)
def x86_64 (code : ByteArray) (base entry : Nat) : IO Bap.Emu.Emu := do Bap.Emu.x86_64 code base entry (adjust := ← tuned)
def aarch64 (code : ByteArray) (base entry : Nat) : IO Bap.Emu.Emu := do Bap.Emu.aarch64 code base entry (adjust := ← tuned)
def mips64 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) : IO Bap.Emu.Emu := do
  Bap.Emu.mips64 code base entry release6 (adjust := ← tuned)
def mips32 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) : IO Bap.Emu.Emu := do
  Bap.Emu.mips32 code base entry release6 (adjust := ← tuned)

end Tuned

/-- What a test says about the counters of the engine, which depend on how it is tuned. -/
private def onStepwise (check : IO Unit) : IO Unit := do
  if ← stepwise.get then check

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
  let emu ← Tuned.riscv64 code 0 0
  let saved ← Bap.Emu.snapshot emu
  Bap.Emu.save emu "native/build/emu-diff.bin"
  Bap.Emu.write emu 0 (ByteArray.mk #[0, 0])
  Bap.Emu.write emu 4 (ByteArray.mk #[0])
  assertEqual "Emu snapshot diff coalesces changes" [(0, 2), (4, 1)] (← Bap.Emu.diff emu saved)
  assertEqual "Emu checkpoint diff matches snapshot" [(0, 2), (4, 1)] (← Bap.Emu.changedSince emu "native/build/emu-diff.bin")
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
  let emu ← Tuned.riscv64 original 0 0
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
  let summarize : Bap.Project.Pass := {
    name := "summarize"
    run := fun project =>
      let instructions := project.disasm.map (fun disasm => disasm.instructions.length) |>.getD 0
      .ok (project.set "instructions" (toString instructions) |>.set "status" "analyzed")
  }
  match Bap.Project.runPasses [summarize] project with
  | .error error => throw <| IO.userError s!"live project analysis failed: {repr error}"
  | .ok analyzed =>
    assertEqual "Emu live project analysis instruction count" (some "2") (analyzed.get "instructions")
    assertEqual "Emu live project analysis status" (some "analyzed") (analyzed.get "status")
    Bap.Project.save analyzed "native/build/emu-live-project.bin"
    let restored ← Bap.Project.loadSaved "native/build/emu-live-project.bin"
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
  let emu ← Tuned.mips64 code 0 0
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
  let likelyEmu ← Tuned.mips64 likelyCode 0 0
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
  Bap.Emu.save emu "native/build/emu-delay-checkpoint.bin"
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
  Bap.Emu.load emu "native/build/emu-delay-checkpoint.bin"
  let _ ← Bap.Emu.run emu 2
  assertBits "Emu checkpoint restores pending branch" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu r5))

private def testThreads : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "sw a0, 0(a1)") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")
  let emu ← Tuned.riscv64 code 0 0
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
  Bap.Emu.save emu "native/build/emu-threads-checkpoint.bin"
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
  Bap.Emu.load emu "native/build/emu-threads-checkpoint.bin"
  assertBits "Emu checkpoint restores first thread" (BitVec.ofNat 64 2)
    (.ok (← Bap.Emu.threadReg emu 1 output))
  assertBits "Emu checkpoint restores second thread" (BitVec.ofNat 64 12)
    (.ok (← Bap.Emu.threadReg emu second output))
  assertTrue "Emu checkpoint restores shared memory"
    ((ByteArray.mk #[11, 0, 0, 0]) == (← Bap.Emu.read emu 0x1000 4))
  let third ← Bap.Emu.spawnThread emu 0 7
  assertEqual "Emu checkpoint preserves next thread ID" 3 third
  let parallelCode := (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++ (← LLVM.assemble "riscv64" "jal 0")
  let parallelEmu ← Tuned.riscv64 parallelCode 0 0
  Bap.Emu.setReg parallelEmu output (.bits (BitVec.ofNat 64 0))
  let parallelSecond ← Bap.Emu.spawnThread parallelEmu 0 10
  let parallelSteps ← Bap.Emu.runPreemptiveParallel parallelEmu 1
  assertEqual "Emu parallel scheduler executes both threads" 2 parallelSteps
  assertBits "Emu parallel scheduler preserves first thread" (BitVec.ofNat 64 1)
    (.ok (← Bap.Emu.threadReg parallelEmu 1 output))
  assertBits "Emu parallel scheduler preserves second thread" (BitVec.ofNat 64 11)
    (.ok (← Bap.Emu.threadReg parallelEmu parallelSecond output))
  let contextEmu ← Tuned.riscv64 parallelCode 0 0
  Bap.Emu.setReg contextEmu output (.bits (BitVec.ofNat 64 0))
  let contextSecond ← Bap.Emu.spawnThread contextEmu 0 10
  let contextEvents ← IO.mkRef []
  let _ ← Bap.Emu.onCode contextEmu (4, 4) fun current _ => do
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
  let syscallContextEmu ← Tuned.riscv64 ((← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
    (← LLVM.assemble "riscv64" "ecall")) 0 0
  Bap.Emu.setReg syscallContextEmu output (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg syscallContextEmu (reg "X17") (.bits (BitVec.ofNat 64 39))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg syscallContextEmu (reg s!"X{10 + index}") (.bits (BitVec.ofNat 64 0))
  let syscallContextSecond ← Bap.Emu.spawnThread syscallContextEmu 0 10
  let syscallContextEvents ← IO.mkRef []
  let _ ← Bap.Emu.onSyscall syscallContextEmu fun current _ _ => do
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
  let parallelMemoryEmu ← Tuned.riscv64 parallelMemoryCode 0 0
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
  Bap.Emu.save parallelMemoryEmu "native/build/emu-cow-checkpoint.bin"
  Bap.Emu.load parallelMemoryEmu "native/build/emu-cow-checkpoint.bin"
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
    ⟨{ env := env }, pc, [region 0x10 [1, 2]], false, [], 0, 0, none, [], none⟩
  let wide := BitVec.ofNat 256 (2 ^ 255 + 7)
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [(register "ymm", .bits wide)]) with
  | .error error => throw <| IO.userError error
  | .ok data =>
    match Bap.Emu.decodeBinarySnapshot data with
    | .error error => throw <| IO.userError error
    | .ok decoded =>
      assertBits "binary checkpoint keeps a 256-bit value" wide (Bil.lookup decoded.state.env (register "ymm"))
      assertEqual "binary checkpoint keeps the pc" 0x1000 decoded.pc
  -- Values take as many bytes as their width: nothing is too wide for the format any more.
  let zmm : Bap.Var := ⟨"zmm", .imm 512, 0, false⟩
  let widest := BitVec.ofNat 512 (2 ^ 511 + 3)
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [(zmm, .bits widest)]) with
  | .error error => throw <| IO.userError s!"binary checkpoint refused a 512-bit value: {error}"
  | .ok data =>
    match Bap.Emu.decodeBinarySnapshot data with
    | .error error => throw <| IO.userError error
    | .ok decoded => assertBits "binary checkpoint keeps a 512-bit value" widest (Bil.lookup decoded.state.env zmm)
  match Bap.Emu.encodeBinarySnapshot (snapshotOf [] (2 ^ 64)) with
  | .error _ => IO.println "ok: binary checkpoint refuses a pc over 64 bits"
  | .ok _ => throw <| IO.userError "binary checkpoint accepted a 65-bit pc"

private def riscvConfig : IO Bap.Emu.Config := do
  let disassembler ← Target.RISCV.disassembler 0
  pure {
    disassembler
    disassemblerAt := some (fun base => Target.RISCV.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
  }

private def expectThrow (name : String) (action : IO α) : IO Unit := do
  match ← action.toBaseIO with
  | .error _ => IO.println s!"ok: {name}"
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly succeeded"

private def regionAudit : IO Unit := do
  let rw : Primus.Protection := ⟨true, true, false⟩
  let ro : Primus.Protection := ⟨true, false, false⟩
  let zeros (size : Nat) := ByteArray.mk (List.replicate size 0).toArray
  let code ← LLVM.assemble "riscv64" "addi a0, a0, 1"
  let a0 : Bap.Var := ⟨"X10", .imm 64, 0, false⟩
  -- Instruction fetch needs execute permission only.
  let executeOnly ← Bap.Emu.create (← riscvConfig) [⟨0, code, ⟨false, false, true⟩⟩] { env := [(a0, .bits (BitVec.ofNat 64 0))] } 0
  assertTrue "Emu fetches execute-only memory" (← Bap.Emu.step executeOnly)
  assertBits "Emu runs execute-only code" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg executeOnly a0))
  expectThrow "Emu execute-only memory is not readable" (Bap.Emu.read executeOnly 0 4)
  -- Protection applies to the requested bytes only.
  let emu ← Tuned.riscv64 code 0 0
  Bap.Emu.map emu ⟨0x1000, zeros 0x30, rw⟩
  Bap.Emu.map emu ⟨0x1030, zeros 0x10, rw⟩
  Bap.Emu.write emu 0x1014 (ByteArray.mk #[7])
  Bap.Emu.protect emu 0x1010 0x10 ro
  expectThrow "Emu protect covers the requested bytes" (Bap.Emu.write emu 0x1010 (ByteArray.mk #[1]))
  Bap.Emu.write emu 0x100f (ByteArray.mk #[1])
  Bap.Emu.write emu 0x1020 (ByteArray.mk #[1])
  assertEqual "Emu protect keeps the bytes" #[7] (← Bap.Emu.read emu 0x1014 1).data
  Bap.Emu.protect emu 0x1028 0x10 ro
  expectThrow "Emu protect crosses adjacent regions" (Bap.Emu.write emu 0x1030 (ByteArray.mk #[1]))
  expectThrow "Emu protect refuses an unmapped range" (Bap.Emu.protect emu 0x1038 0x10 ro)
  -- Regions stay inside the address space.
  let narrow ← Tuned.riscv32 code 0 0
  expectThrow "Emu map refuses a region past the address space" (Bap.Emu.map narrow ⟨2 ^ 32 - 2, zeros 4, rw⟩)
  Bap.Emu.map narrow ⟨2 ^ 32 - 4, zeros 4, rw⟩
  -- An overlay replaces a region and nothing else.
  expectThrow "Emu overlay refuses to overlap another region" (Bap.Emu.overlay emu ⟨0x1038, zeros 0x10, rw⟩)
  Bap.Emu.overlay emu ⟨0x1030, ByteArray.mk (List.replicate 8 9).toArray, rw⟩
  -- Accesses that straddle a watched range are seen.
  let store ← LLVM.assemble "riscv64" "sw a1, 0(a0)"
  let watching ← Tuned.riscv64 store 0 0
  let wide := BitVec.ofNat 64 0x2000
  Bap.Emu.map watching ⟨0x2000, zeros 8, rw⟩
  Bap.Emu.setReg watching a0 (.bits wide)
  Bap.Emu.setReg watching ⟨"X11", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 1))
  let hits ← IO.mkRef 0
  let _ ← Bap.Emu.onWrite watching (0x2002, 0x2002) fun _ _ _ _ => hits.modify (· + 1)
  let _ ← Bap.Emu.step watching
  assertEqual "Emu write hook sees an access straddling its range" 1 (← hits.get)
  -- Every hook is told the thread that runs it, through the emulator it gets.
  let hookThreads ← IO.mkRef ([] : List Nat)
  let threaded ← Tuned.riscv64 store 0 0
  Bap.Emu.map threaded ⟨0x2000, zeros 8, rw⟩
  Bap.Emu.setReg threaded a0 (.bits wide)
  Bap.Emu.setReg threaded ⟨"X11", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 1))
  let _ ← Bap.Emu.onCode threaded (0, 0) fun current _ => do
    hookThreads.modify (· ++ [← Bap.Emu.thread current])
  let _ ← Bap.Emu.onWrite threaded (0x2002, 0x2002) fun current _ _ _ => do
    hookThreads.modify (· ++ [← Bap.Emu.thread current])
  let _ ← Bap.Emu.step threaded
  assertEqual "code and write hooks know their thread" [1, 1] (← hookThreads.get)
  -- A failed step leaves forked processes their memory.
  let forked ← Tuned.riscv64 store 0 0
  Bap.Emu.setReg forked a0 (.bits (BitVec.ofNat 64 0x9000))
  Bap.Emu.setReg forked ⟨"X11", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 1))
  let child ← Bap.Emu.forkThread forked 0
  Bap.Emu.cloneProcessMemory forked child
  expectThrow "Emu faulting store fails" (Bap.Emu.step forked)
  assertEqual "Emu fault keeps forked process memory" 1 (← forked.processMemory.get).size
  -- A call does not disturb a pending delay slot.
  let calling ← Tuned.riscv64 ((← LLVM.assemble "riscv64" "addi a0, a0, 1") ++ (← LLVM.assemble "riscv64" "ret")) 0 0
  Bap.Emu.setReg calling a0 (.bits (BitVec.ofNat 64 0))
  calling.pendingRef.set (some ⟨0x40, 0x44⟩)
  calling.skipCode.set (some 0x48)
  let _ ← Bap.Emu.call calling 0 0x1000 []
  assertEqual "Emu call preserves a pending branch" (some ⟨0x40, 0x44⟩) (← calling.pendingRef.get)
  assertEqual "Emu call preserves a skipped hook" (some 0x48) (← calling.skipCode.get)
  -- A failing parallel worker rolls the round back only after every worker has finished.
  let spinning ← LLVM.assemble "riscv64" "addi a0, a0, 1"
  let failing ← Tuned.riscv64 spinning 0 0
  Bap.Emu.setReg failing a0 (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.spawnThread failing 0x7000 0
  expectThrow "Emu parallel round reports a worker failure" (Bap.Emu.runPreemptiveParallel failing 1)
  assertBits "Emu parallel failure rolls the first worker back" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.threadReg failing 1 a0))

set_option maxRecDepth 8000 in
/-- Regressions of the bugs that the proofs of `Bap.Emu.CoreProofs` found. -/
private def coreRegressions : IO Unit := do
  let zeros (size : Nat) := ByteArray.mk (List.replicate size 0).toArray
  let rw : Primus.Protection := ⟨true, true, false⟩
  let bits (value : Nat) : Value := .bits (BitVec.ofNat 64 value)
  let rv (text : String) := LLVM.assemble "riscv64" text
  let a0 := reg "X10"
  let a1 := reg "X11"
  let a2 := reg "X12"
  -- An interpreted delayed branch enters its slot like a native one (advance_delayed).
  let branch := (ByteArray.mk #[0x10, 0x43, 0x00, 0x02]) ++ (← LLVM.assemble "mips64" "addiu $4, $4, 1") ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 100") ++ (← LLVM.assemble "mips64" "addiu $5, $5, 1")
  let mipsConfig : Bap.Emu.Config := {
    disassembler := ← Target.MIPS.disassembler 0
    disassemblerAt := some (fun base => Target.MIPS.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .big
    syscallAbi := .mips
    delayPolicy := .mips false
    hotThreshold := 5
  }
  let interpreted ← Bap.Emu.create mipsConfig [⟨0, branch, ⟨true, true, true⟩⟩] {} 0
  for name in ["R2", "R3"] do Bap.Emu.setReg interpreted (reg name) (bits 1)
  for name in ["R4", "R5"] do Bap.Emu.setReg interpreted (reg name) (bits 0)
  let _ ← Bap.Emu.run interpreted 1
  assertEqual "Emu interpreted delayed branch enters the slot" 4 (← Bap.Emu.pc interpreted)
  let _ ← Bap.Emu.run interpreted 1
  assertEqual "Emu interpreted delay slot reaches the target" 12 (← Bap.Emu.pc interpreted)
  assertBits "Emu interpreted delay slot runs" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg interpreted (reg "R4")))
  -- A compiled range would run past a delay slot, so that delay slots keep ranges off.
  let ranged ← Bap.Emu.create { mipsConfig with hotThreshold := 1, rangeLimit := 8 } [⟨0, branch, ⟨true, true, true⟩⟩] {} 0
  for name in ["R2", "R3"] do Bap.Emu.setReg ranged (reg name) (bits 1)
  for name in ["R4", "R5"] do Bap.Emu.setReg ranged (reg name) (bits 0)
  let _ ← Bap.Emu.run ranged 2
  assertEqual "Emu delay slots keep compiled ranges off" 12 (← Bap.Emu.pc ranged)
  assertEqual "Emu delayed code has no compiled range" 0 (← Bap.Primus.Lifted.stats ranged.engine).graphBlocks
  -- A special nobody serves in a slot is a precise exception (advance_unhandled).
  let slotCall := (ByteArray.mk #[0x10, 0x43, 0x00, 0x02]) ++ (← LLVM.assemble "mips64" "syscall") ++
    (← LLVM.assemble "mips64" "addiu $4, $4, 100") ++ (← LLVM.assemble "mips64" "addiu $5, $5, 1")
  let slotEmu ← Tuned.mips64 slotCall 0 0
  for name in ["R2", "R3"] do Bap.Emu.setReg slotEmu (reg name) (bits 1)
  for name in ["R4", "R5", "R6", "R7", "R8", "R9"] do Bap.Emu.setReg slotEmu (reg name) (bits 0)
  let _ ← Bap.Emu.run slotEmu 5
  assertEqual "Emu unhandled slot special keeps the pc" 4 (← Bap.Emu.pc slotEmu)
  let _ ← Bap.Emu.onSyscall slotEmu fun _ _ _ => pure (.returnValue 0)
  Bap.Emu.resume slotEmu
  let _ ← Bap.Emu.run slotEmu 1
  assertEqual "Emu served slot special completes the branch" 12 (← Bap.Emu.pc slotEmu)
  -- Faults name the thread that took them.
  let faulting ← Tuned.riscv64 (← rv "lw a0, 0(a1)") 0 0
  Bap.Emu.setReg faulting a1 (bits 0x9000)
  let second ← Bap.Emu.spawnThread faulting 0 0
  Bap.Emu.switchThread faulting second
  expectThrow "Emu second thread faults" (Bap.Emu.step faulting)
  assertEqual "Emu fault names its thread" (some second) ((← Bap.Emu.failure faulting).map (·.thread))
  -- A hook that moves the pc keeps the instruction from running (afterHooks_redirect).
  let moving ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "addi a0, a0, 2") ++ (← rv "addi a0, a0, 4")) 0 0
  Bap.Emu.setReg moving a0 (bits 0)
  let _ ← Bap.Emu.onCode moving (0, 0) fun current _ => Bap.Emu.setPc current 8
  let _ ← Bap.Emu.run moving 2
  assertEqual "Emu hook redirect reaches the new pc" 12 (← Bap.Emu.pc moving)
  assertBits "Emu hook redirect skips the instruction" (BitVec.ofNat 64 4) (.ok (← Bap.Emu.reg moving a0))
  -- So does a syscall hook that moves the pc (commit_redirect).
  let longjmp ← Tuned.riscv64 ((← rv "ecall") ++ (← rv "addi a0, a0, 2") ++ (← rv "addi a0, a0, 4")) 0 0
  Bap.Emu.setReg longjmp a0 (bits 0)
  (List.range 6).forM fun index => Bap.Emu.setReg longjmp (reg s!"X{11 + index}") (bits 0)
  Bap.Emu.setReg longjmp (reg "X17") (bits 1)
  let _ ← Bap.Emu.onIntrinsic longjmp "*" fun _ _ => do
    Bap.Emu.setPc longjmp 8
    pure .proceed
  let _ ← Bap.Emu.run longjmp 1
  assertEqual "Emu handler moves the pc" 8 (← Bap.Emu.pc longjmp)
  -- A thread that a hook creates during a parallel round survives it (mergeRound_new_thread).
  let spawning ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "jal 0")) 0 0
  Bap.Emu.setReg spawning a0 (bits 0)
  let _ ← Bap.Emu.spawnThread spawning 0 0
  let spawned ← IO.mkRef false
  let _ ← Bap.Emu.onCode spawning (4, 4) fun current _ => do
    if !(← spawned.get) then
      spawned.set true
      let _ ← Bap.Emu.spawnThread current 0 0
  let _ ← Bap.Emu.runPreemptiveParallel spawning 4
  assertEqual "Emu parallel round keeps a thread a hook spawned" [1, 2, 3] ((← Bap.Emu.threads spawning).map (·.id))
  -- Sequentially scheduled forks have memories of their own (SpaceMachine.isolation).
  let store := (← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a1)") ++ (← rv "jal -8")
  let forking ← Tuned.riscv64 store 0 0
  Bap.Emu.map forking ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg forking a0 (bits 0)
  Bap.Emu.setReg forking a1 (bits 0x1000)
  let child ← Bap.Emu.forkThread forking 0
  Bap.Emu.setThreadReg forking child a0 (bits 100)
  Bap.Emu.setThreadReg forking child a1 (bits 0x1000)
  Bap.Emu.resumeThread forking child
  Bap.Emu.cloneProcessMemory forking child
  let _ ← Bap.Emu.run forking 2
  Bap.Emu.switchThread forking child
  let _ ← Bap.Emu.run forking 2
  assertEqual "Emu fork stores to its own memory" 101 (← Bap.Emu.read forking 0x1000 1)[0]!.toNat
  Bap.Emu.switchThread forking 1
  assertEqual "Emu fork leaves the parent's memory" 1 (← Bap.Emu.read forking 0x1000 1)[0]!.toNat
  let _ ← Bap.Emu.runPreemptive forking 3 6
  assertEqual "Emu preemption stores to the fork's memory" 102 (← Bap.Emu.read forking 0x1000 1)[0]!.toNat
  Bap.Emu.switchThread forking 1
  assertEqual "Emu preemption stores to the parent's memory" 2 (← Bap.Emu.read forking 0x1000 1)[0]!.toNat
  -- The state of a thread of the shared address space follows it, also behind a process (parkShared).
  let sharing ← Tuned.riscv64 store 0 0
  Bap.Emu.map sharing ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg sharing a0 (bits 0)
  Bap.Emu.setReg sharing a1 (bits 0x1000)
  let sibling ← Bap.Emu.spawnThread sharing 0 0
  let process ← Bap.Emu.forkThread sharing 0
  Bap.Emu.resumeThread sharing process
  Bap.Emu.cloneProcessMemory sharing process
  let _ ← Bap.Emu.run sharing 2
  Bap.Emu.switchThread sharing process
  Bap.Emu.switchThread sharing sibling
  Bap.Emu.refreshRegions sharing
  assertEqual "Emu sibling state follows the shared memory" 1 (← Bap.Emu.read sharing 0x1000 1)[0]!.toNat
  match Bil.lookup (← sharing.state.get).env sharing.config.memory with
  | .ok (.memory memory) =>
    assertEqual "Emu state memory is exact after leaving a process" 1
      (Bap.Memory.readRegion memory 0x1000 1)[0]!.toNat
  | _ => throw <| IO.userError "memory variable is missing"
  -- A failed parallel round keeps what earlier rounds wrote (the exact rollback).
  let round ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a1)") ++ (← rv "lb a3, 0(a2)") ++ (← rv "jal -12")) 0 0
  Bap.Emu.map round ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg round a0 (bits 0)
  Bap.Emu.setReg round a1 (bits 0x1000)
  Bap.Emu.setReg round a2 (bits 0x1000)
  let roundSecond ← Bap.Emu.spawnThread round 0 0
  Bap.Emu.setThreadReg round roundSecond a1 (bits 0x1004)
  let _ ← Bap.Emu.runPreemptiveParallel round 4
  let written := (← Bap.Emu.read round 0x1000 1)[0]!
  assertEqual "Emu parallel round wrote" 1 written.toNat
  Bap.Emu.setThreadReg round roundSecond a2 (bits 0x9000)
  expectThrow "Emu parallel round fails" (Bap.Emu.runPreemptiveParallel round 4)
  assertEqual "Emu failed round keeps earlier writes" written.toNat (← Bap.Emu.read round 0x1000 1)[0]!.toNat
  assertEqual "Emu failed round reports the fault" (some 0x9000) ((← Bap.Emu.failure round).map (·.address))
  -- A breakpoint stops the worker that hits it.
  let breaking ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "addi a0, a0, 1") ++ (← rv "jal 0")) 0 0
  Bap.Emu.setReg breaking a0 (bits 0)
  let _ ← Bap.Emu.spawnThread breaking 0 0
  let _ ← Bap.Emu.addBreakpoint breaking 4
  let _ ← Bap.Emu.runPreemptiveParallel breaking 10
  assertEqual "Emu breakpoint stops parallel workers" [⟨1, 4, true⟩, ⟨2, 4, true⟩] (← Bap.Emu.threads breaking)
  -- A stopped current thread does not hold up the only active one of a parallel round.
  let blocked ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "jal 0")) 0 0
  Bap.Emu.setReg blocked a0 (bits 0)
  let blockedSecond ← Bap.Emu.spawnThread blocked 0 0
  Bap.Emu.stop blocked
  assertEqual "Emu parallel round runs past a stopped thread" 2 (← Bap.Emu.runPreemptiveParallel blocked 2)
  assertEqual "Emu parallel round switched to the active thread" blockedSecond (← Bap.Emu.thread blocked)
  -- No re-fires: hooks fire once per instruction, across all that may happen in between.
  let code := (← rv "addi a0, a0, 1") ++ (← rv "addi a0, a0, 1")
  let hits ← IO.mkRef 0
  let fresh : IO Bap.Emu.Emu := do
    let emu ← Tuned.riscv64 code 0 0
    Bap.Emu.setReg emu a0 (bits 0)
    hits.set 0
    let _ ← Bap.Emu.onCode emu (0, 0) fun _ _ => do
      hits.modify (· + 1)
      Bap.Emu.stop emu
    let _ ← Bap.Emu.step emu
    pure emu
  let afterSnapshot ← fresh
  let saved ← Bap.Emu.snapshot afterSnapshot
  Bap.Emu.restore afterSnapshot saved
  Bap.Emu.resume afterSnapshot
  let _ ← Bap.Emu.step afterSnapshot
  assertEqual "Emu snapshot and restore cause no re-fire" 1 (← hits.get)
  assertEqual "Emu restored breakpoint resumes" 4 (← Bap.Emu.pc afterSnapshot)
  let afterSwitch ← fresh
  let other ← Bap.Emu.spawnThread afterSwitch 4 0
  Bap.Emu.switchThread afterSwitch other
  Bap.Emu.switchThread afterSwitch 1
  Bap.Emu.resume afterSwitch
  let _ ← Bap.Emu.step afterSwitch
  assertEqual "Emu thread switches cause no re-fire" 1 (← hits.get)
  let afterSave ← fresh
  Bap.Emu.save afterSave "native/build/emu-refire-checkpoint.bin"
  Bap.Emu.load afterSave "native/build/emu-refire-checkpoint.bin"
  Bap.Emu.resume afterSave
  let _ ← Bap.Emu.step afterSave
  assertEqual "Emu checkpoints cause no re-fire" 1 (← hits.get)
  let afterParallel ← fresh
  let _ ← Bap.Emu.spawnThread afterParallel 4 0
  Bap.Emu.resume afterParallel
  let _ ← Bap.Emu.runPreemptiveParallel afterParallel 1
  assertEqual "Emu parallel workers cause no re-fire" 1 (← hits.get)
  -- A fault retries its instruction without firing its hooks again (rollback_no_pending).
  let retry ← Tuned.riscv64 (← rv "lw a0, 0(a1)") 0 0
  Bap.Emu.setReg retry a1 (bits 0x9000)
  let retries ← IO.mkRef 0
  let _ ← Bap.Emu.onCode retry (0, 0) fun _ _ => retries.modify (· + 1)
  expectThrow "Emu retried load faults" (Bap.Emu.step retry)
  Bap.Emu.map retry ⟨0x9000, zeros 8, rw⟩
  let _ ← Bap.Emu.step retry
  assertEqual "Emu retry after a fault causes no re-fire" 1 (← retries.get)
  assertEqual "Emu retry runs the instruction" 4 (← Bap.Emu.pc retry)
  -- An unhandled special stops once; resuming retries it without firing hooks again.
  let special ← Tuned.riscv64 (← rv "ecall") 0 0
  let specials ← IO.mkRef 0
  let _ ← Bap.Emu.onCode special (0, 0) fun _ _ => specials.modify (· + 1)
  let _ ← Bap.Emu.step special
  Bap.Emu.resume special
  let _ ← Bap.Emu.step special
  assertEqual "Emu unhandled special causes no re-fire" 1 (← specials.get)
  -- A rolled back trace holds only instructions that completed.
  let traced ← Tuned.riscv64 ((← rv "sw a0, 0(a2)") ++ (← rv "lw a0, 0(a1)")) 0 0
  Bap.Emu.map traced ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg traced a0 (bits 0)
  Bap.Emu.setReg traced a1 (bits 0x9000)
  Bap.Emu.setReg traced a2 (bits 0x1000)
  Bap.Emu.traceStartAccesses traced 8
  let _ ← Bap.Emu.step traced
  expectThrow "Emu traced load faults" (Bap.Emu.step traced)
  assertEqual "Emu trace excludes a failed instruction" [0] (← Bap.Emu.tracePcs traced)
  -- Compiled ranges: hooks fire once, the trace is in order, and a stop leaves the block unexecuted.
  let rangeConfig : Bap.Emu.Config := {
    disassembler := ← Target.RISCV.disassembler 0
    disassemblerAt := some (fun base => Target.RISCV.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    rangeLimit := 8
  }
  let rangeCode := (← rv "jal 4") ++ (← rv "jal 4") ++ (← rv "jal 4") ++ (← rv "jal 4") ++ (← rv "addi a0, a0, 1")
  let ranging ← Bap.Emu.create rangeConfig [⟨0, rangeCode, ⟨true, true, true⟩⟩] { env := [(a0, bits 0)] } 0
  Bap.Emu.traceStart ranging
  let rangeHits ← IO.mkRef 0
  let _ ← Bap.Emu.onCode ranging (8, 8) fun _ _ => do
    rangeHits.modify (· + 1)
    Bap.Emu.stop ranging
  let _ ← Bap.Emu.run ranging 10
  assertEqual "Emu compiled range stops at the hook" 8 (← Bap.Emu.pc ranging)
  assertEqual "Emu compiled range trace holds what ran" [0, 4] (← Bap.Emu.tracePcs ranging)
  Bap.Emu.resume ranging
  let _ ← Bap.Emu.step ranging
  assertEqual "Emu compiled range causes no re-fire" 1 (← rangeHits.get)
  assertEqual "Emu compiled range resumes" [0, 4, 8] ((← Bap.Emu.tracePcs ranging).take 3)
  -- A process that a hook forks in a parallel round has its memory in its state too.
  let forkingRound ← Tuned.riscv64 ((← rv "sb a0, 0(a1)") ++ (← rv "addi a0, a0, 1") ++ (← rv "jal -8")) 0 0
  Bap.Emu.map forkingRound ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg forkingRound a0 (bits 5)
  Bap.Emu.setReg forkingRound a1 (bits 0x1000)
  let _ ← Bap.Emu.spawnThread forkingRound 4 6
  let forkedRound ← IO.mkRef none
  let _ ← Bap.Emu.onCode forkingRound (4, 4) fun current _ => do
    if (← Bap.Emu.thread current) == 1 && (← forkedRound.get).isNone then
      let id ← Bap.Emu.forkThread current 4
      Bap.Emu.cloneProcessMemory current id
      forkedRound.set (some id)
  let _ ← Bap.Emu.runPreemptiveParallel forkingRound 2
  let some forkId := ← forkedRound.get | throw <| IO.userError "the hook did not fork"
  Bap.Emu.resumeThread forkingRound forkId
  Bap.Emu.switchThread forkingRound forkId
  match Bil.lookup (← forkingRound.state.get).env forkingRound.config.memory with
  | .ok (.memory memory) =>
    assertEqual "Emu fork in a round has its memory in its state" 5 (Bap.Memory.readRegion memory 0x1000 1)[0]!.toNat
  | _ => throw <| IO.userError "memory variable is missing"
  assertEqual "Emu fork in a round reads its native memory" 5 (← Bap.Emu.read forkingRound 0x1000 1)[0]!.toNat
  -- Hooks fire in the order of their registration, whatever their kind.
  let ordered ← Tuned.riscv64 (← rv "sw a0, 0(a1)") 0 0
  Bap.Emu.map ordered ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg ordered a0 (bits 0)
  Bap.Emu.setReg ordered a1 (bits 0x1000)
  let order ← IO.mkRef ([] : List Nat)
  let _ ← Bap.Emu.onCode ordered (0, 0) fun _ _ => order.modify (· ++ [1])
  let _ ← Bap.Emu.onCode ordered (0, 0) fun _ _ => order.modify (· ++ [2])
  let _ ← Bap.Emu.onWrite ordered (0x1000, 0x1003) fun _ _ _ _ => order.modify (· ++ [3])
  let _ ← Bap.Emu.onWrite ordered (0x1000, 0x1003) fun _ _ _ _ => order.modify (· ++ [4])
  let _ ← Bap.Emu.step ordered
  assertEqual "Emu hooks fire in registration order" [1, 2, 3, 4] (← order.get)
  -- A fork keeps its memory across a failed step of its own, and a checkpoint keeps both memories.
  let failing ← Tuned.riscv64 ((← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a1)") ++ (← rv "lb a3, 0(a2)") ++ (← rv "jal -12")) 0 0
  Bap.Emu.map failing ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg failing a0 (bits 0)
  Bap.Emu.setReg failing a1 (bits 0x1000)
  Bap.Emu.setReg failing a2 (bits 0x1000)
  let forked ← Bap.Emu.forkThread failing 0
  Bap.Emu.setThreadReg failing forked a0 (bits 100)
  Bap.Emu.resumeThread failing forked
  Bap.Emu.cloneProcessMemory failing forked
  Bap.Emu.switchThread failing forked
  let _ ← Bap.Emu.run failing 3
  Bap.Emu.setReg failing a2 (bits 0x9000)
  Bap.Emu.setPc failing 8
  expectThrow "Emu fork faults" (Bap.Emu.step failing)
  assertEqual "Emu fork keeps its memory across a fault" 101 (← Bap.Emu.read failing 0x1000 1)[0]!.toNat
  Bap.Emu.save failing "native/build/emu-fork-checkpoint.bin"
  Bap.Emu.write failing 0x1000 (ByteArray.mk #[7])
  Bap.Emu.load failing "native/build/emu-fork-checkpoint.bin"
  assertEqual "Emu checkpoint keeps a fork's memory" 101 (← Bap.Emu.read failing 0x1000 1)[0]!.toNat
  Bap.Emu.switchThread failing 1
  assertEqual "Emu checkpoint keeps the parent's memory" 0 (← Bap.Emu.read failing 0x1000 1)[0]!.toNat

set_option maxRecDepth 4000 in
private def runEmulator : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi a0, a1, 2") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1") ++ (← LLVM.assemble "riscv64" "jal 4")
  assertEqual "Emu test code size" 12 code.size
  let thirdInsn ← Target.LLVMLift.decodeRISCV 8 8 (code.extract 8 12)
  assertEqual "Emu third instruction size" 4 thirdInsn.size
  let emu ← Tuned.riscv64 code 0 0
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
  let codeHook ← Bap.Emu.onCode emu (0, 4) fun _ _ => codeHits.modify (· + 1)
  let hookedSteps ← Bap.Emu.run emu 2
  assertEqual "Emu code hooks allow execution" 2 hookedSteps
  assertEqual "Emu code hook range filtering" 2 (← codeHits.get)
  assertEqual "Emu two steps stop at PC 8" 8 (← Bap.Emu.pc emu)
  let stopHook ← Bap.Emu.onCode emu (8, 8) fun _ _ => Bap.Emu.stop emu
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
  Bap.Emu.save emu "native/build/emu-checkpoint.bin"
  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu output (.bits (BitVec.ofNat 64 99))
  let checkpointOverwrite ← LLVM.assemble "riscv64" "addi a0, a1, 9"
  Bap.Emu.write emu 0 checkpointOverwrite
  Bap.Emu.load emu "native/build/emu-checkpoint.bin"
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
  let memoryEmu ← Tuned.riscv64 memoryCode 0 0
  Bap.Emu.map memoryEmu ⟨0x1000, ByteArray.mk (List.replicate 4 0).toArray, ⟨true, true, false⟩⟩
  Bap.Emu.setReg memoryEmu input (.bits (BitVec.ofNat 64 0x1000))
  let memoryEvents ← IO.mkRef []
  let writeHook ← Bap.Emu.onWrite memoryEmu (0x1000, 0x1003) fun _ address size value => do
    assertTrue "Emu write hook runs before store"
      ((ByteArray.mk #[0, 0, 0, 0]) == (← Bap.Emu.read memoryEmu 0x1000 4))
    memoryEvents.modify fun events => (true, address, size, value) :: events
  let readHook ← Bap.Emu.onRead memoryEmu (0x1000, 0x1003) fun _ address size => do
    memoryEvents.modify fun events => (false, address, size, 0) :: events
  let missedWrites ← IO.mkRef 0
  let _ ← Bap.Emu.onWrite memoryEmu (0x2000, 0x2000) fun _ _ _ _ => missedWrites.modify (· + 1)
  Bap.Emu.traceStartAccesses memoryEmu 4
  let memorySteps ← Bap.Emu.run memoryEmu 3
  assertEqual "Emu memory hook instruction count" 3 memorySteps
  assertEqual "Emu whole-access memory hook events"
    [(true, 0x1000, 4, 42), (false, 0x1000, 4, 0)]
    (← memoryEvents.get).reverse
  assertEqual "Emu memory hooks filter ranges" 0 (← missedWrites.get)
  assertBits "Emu hooked load result" (BitVec.ofNat 64 42) (.ok (← Bap.Emu.reg memoryEmu (reg "X12")))
  onStepwise <| assertEqual "Emu memory hooks retain native execution" 3 (← Bap.Primus.Lifted.stats memoryEmu.engine).nativeRuns
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

  let ringEmu ← Tuned.riscv64 memoryCode 0 0
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

  let readFaultEmu ← Tuned.riscv64 (← LLVM.assemble "riscv64" "lw a0, 0(a1)") 0 0
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

  let pushEmu ← Tuned.x86_64 (← LLVM.assemble "x86_64" "pushq %rax") 0 0
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
  let smcEmu ← Tuned.riscv64 smcCode 0 0
  Bap.Emu.setReg smcEmu input (.bits (BitVec.ofNat 64 patchWord))
  Bap.Emu.setReg smcEmu (reg "X12") (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.run smcEmu 2
  assertTrue "Emu guest store updates mapped code" (patched == (← Bap.Emu.read smcEmu 0 4))
  onStepwise <| assertEqual "Emu guest code write preserves unrelated JIT blocks" 1 (← smcEmu.engine.cache.get).size
  let _ ← Bap.Emu.run smcEmu 1
  assertEqual "Emu self-modifying test returns to entry" 0 (← Bap.Emu.pc smcEmu)
  let _ ← Bap.Emu.run smcEmu 1
  assertBits "Emu guest code write invalidates native lift" (BitVec.ofNat 64 42)
    (.ok (← Bap.Emu.reg smcEmu output))
  onStepwise <| assertEqual "Emu guest code write lifts the patched instruction again" 4
    (← Bap.Primus.Lifted.stats smcEmu.engine).lifts

  let x86Code := (← LLVM.assemble "x86_64" "movq $40, %rax") ++
    (← LLVM.assemble "x86_64" "addq $2, %rax")
  let x86Emu ← Tuned.x86_64 x86Code 0 0
  let x86Steps ← Bap.Emu.run x86Emu 2
  assertEqual "Emu x86-64 instruction count" 2 x86Steps
  let x86Result ← Bap.Emu.reg x86Emu (reg "RAX")
  assertBits "Emu x86-64 result" (BitVec.ofNat 64 42) (.ok x86Result)

  let armCode := (← LLVM.assemble "aarch64" "movz x0, 40") ++
    (← LLVM.assemble "aarch64" "add x0, x0, 2")
  let armEmu ← Tuned.aarch64 armCode 0 0
  let armSteps ← Bap.Emu.run armEmu 2
  assertEqual "Emu AArch64 instruction count" 2 armSteps
  let armResult ← Bap.Emu.reg armEmu (reg "X0")
  assertBits "Emu AArch64 result" (BitVec.ofNat 64 42) (.ok armResult)

  let syscallEmu ← Tuned.riscv64 ((← LLVM.assemble "riscv64" "ecall") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")) 0 0
  Bap.Emu.setReg syscallEmu (reg "X17") (.bits (BitVec.ofNat 64 39))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg syscallEmu (reg s!"X{10 + index}") (.bits (BitVec.ofNat 64 (index + 1)))
  let syscallOrder ← IO.mkRef []
  let defaultSyscallHook ← Bap.Emu.onSyscall syscallEmu fun _ number args => do
    assertEqual "Emu RISC-V syscall number" 39 number
    assertEqual "Emu RISC-V syscall arguments" [1, 2, 3, 4, 5, 6] args
    syscallOrder.modify fun order => "default" :: order
    pure .default
  let returnSyscallHook ← Bap.Emu.onSyscall syscallEmu fun _ _ _ => do
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

  let x86SyscallEmu ← Tuned.x86_64 ((← LLVM.assemble "x86_64" "syscall") ++
    (← LLVM.assemble "x86_64" "addq $1, %rax")) 0 0
  Bap.Emu.setReg x86SyscallEmu (reg "RAX") (.bits (BitVec.ofNat 64 39))
  (["RDI", "RSI", "RDX", "R10", "R8", "R9"]).zip [1, 2, 3, 4, 5, 6] |>.forM fun binding =>
    Bap.Emu.setReg x86SyscallEmu (reg binding.1) (.bits (BitVec.ofNat 64 binding.2))
  let x86SyscallHook ← Bap.Emu.onSyscall x86SyscallEmu fun _ number args => do
    assertEqual "Emu x86-64 syscall number" 39 number
    assertEqual "Emu x86-64 syscall arguments" [1, 2, 3, 4, 5, 6] args
    pure (.returnValue 100)
  let x86SyscallSteps ← Bap.Emu.run x86SyscallEmu 2
  assertEqual "Emu handled x86-64 syscall continues" 2 x86SyscallSteps
  assertEqual "Emu x86-64 syscall resumes at next PC" 6 (← Bap.Emu.pc x86SyscallEmu)
  assertBits "Emu x86-64 syscall return value" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg x86SyscallEmu (reg "RAX")))
  Bap.Emu.removeHook x86SyscallEmu x86SyscallHook

  let armSyscallEmu ← Tuned.aarch64 ((← LLVM.assemble "aarch64" "svc #0") ++
    (← LLVM.assemble "aarch64" "add x0, x0, 1")) 0 0
  Bap.Emu.setReg armSyscallEmu (reg "X8") (.bits (BitVec.ofNat 64 64))
  (List.range 6).forM fun index =>
    Bap.Emu.setReg armSyscallEmu (reg s!"X{index}") (.bits (BitVec.ofNat 64 (index + 1)))
  let armSyscallHook ← Bap.Emu.onSyscall armSyscallEmu fun _ number args => do
    assertEqual "Emu AArch64 syscall number" 64 number
    assertEqual "Emu AArch64 syscall arguments" [1, 2, 3, 4, 5, 6] args
    pure (.returnValue 100)
  let armSyscallSteps ← Bap.Emu.run armSyscallEmu 2
  assertEqual "Emu handled AArch64 syscall continues" 2 armSyscallSteps
  assertEqual "Emu AArch64 syscall resumes at next PC" 8 (← Bap.Emu.pc armSyscallEmu)
  assertBits "Emu AArch64 syscall return value" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg armSyscallEmu (reg "X0")))
  Bap.Emu.removeHook armSyscallEmu armSyscallHook

  let intrinsicEmu ← Tuned.x86_64 ((← LLVM.assemble "x86_64" "hlt") ++
    (← LLVM.assemble "x86_64" "addq $1, %rax")) 0 0
  Bap.Emu.setReg intrinsicEmu (reg "RAX") (.bits (BitVec.ofNat 64 40))
  let missedIntrinsics ← IO.mkRef 0
  let _ ← Bap.Emu.onIntrinsic intrinsicEmu "other" fun _ _ => do
    missedIntrinsics.modify (· + 1)
    pure .default
  let defaultIntrinsicHook ← Bap.Emu.onIntrinsic intrinsicEmu "hlt" fun _ address => do
    assertEqual "Emu intrinsic receives current PC" 0 address
    pure .default
  let proceedIntrinsicHook ← Bap.Emu.onIntrinsic intrinsicEmu "hlt" fun _ _ => do
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

  let wildcardEmu ← Tuned.riscv64 ((← LLVM.assemble "riscv64" "ecall") ++
    (← LLVM.assemble "riscv64" "addi a0, a0, 1")) 0 0
  let wildcardHook ← Bap.Emu.onIntrinsic wildcardEmu "*" fun _ _ => do
    Bap.Emu.setReg wildcardEmu output (.bits (BitVec.ofNat 64 100))
    pure .proceed
  let wildcardSteps ← Bap.Emu.run wildcardEmu 2
  assertEqual "Emu wildcard intrinsic handles syscall" 2 wildcardSteps
  assertBits "Emu wildcard intrinsic resumes execution" (BitVec.ofNat 64 101)
    (.ok (← Bap.Emu.reg wildcardEmu output))
  Bap.Emu.removeHook wildcardEmu wildcardHook

  let breakEmu ← Tuned.riscv64 ((← LLVM.assemble "riscv64" "addi a0, a0, 1") ++
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
  let shellEmu ← Tuned.riscv64 shellCode 0 0
  let (shellInput, shellOutput, shellText) ← shellStreams [
    "help", "pc", "set X10 40", "reg X10", "snap", "step", "restore", "reg X10",
    "write 0 " ++ patchText, "x 0 4", "save native/build/emu-shell-checkpoint.bin",
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
  -- The registers of the debugger have the widths of their target, and values that do not fit are refused.
  let narrowShell ← Tuned.riscv32 shellCode 0 0
  let (narrowInput, narrowOutput, narrowText) ← shellStreams [
    "set X10 7", "reg X10", "set X10 0x1ffffffff", "reg X10", "x 0 99999999999", "x 0x 1", "set X11 0x", "regs", "q"
  ]
  Bap.Emu.shell narrowShell narrowInput narrowOutput
  let narrowOutputText ← narrowText.get
  assertTrue "Emu shell reads a 32-bit register" ((narrowOutputText.splitOn "X10=32:0x7").length == 3)
  assertTrue "Emu shell refuses a value that does not fit" ((narrowOutputText.splitOn "does not fit").length > 1)
  assertTrue "Emu shell fails on an absurd size" ((narrowOutputText.splitOn "unmapped Emu address in").length > 1)
  assertTrue "Emu shell refuses the bare prefix" ((narrowOutputText.splitOn "empty hexadecimal value").length == 3)
  assertEqual "Emu shell parses hexadecimal" (some (Bap.Emu.Command.breakAt 16))
    (Bap.Emu.parseCommand ["break", "0x10"]).toOption
  assertEqual "Emu shell parses decimal" (some (Bap.Emu.Command.examine 16 2))
    (Bap.Emu.parseCommand ["x", "16", "2"]).toOption

  testThreads
  testDelaySlots
  testLiveProject
  testDiff

  Bap.Emu.stop emu
  assertTrue "Emu stopped state" (← Bap.Emu.stopped emu)
  assertTrue "Emu stopped step does not execute" !(← Bap.Emu.step emu)
  Bap.Emu.resume emu
  assertTrue "Emu resumed state" !(← Bap.Emu.stopped emu)

/-- Compiled ranges: they form on what a lifter makes of a real loop, they run around it natively, and the
fuel, the hooks and the code they run stay exact. -/
private def rangeRegressions : IO Unit := do
  let rv (text : String) := LLVM.assemble "riscv64" text
  let bits (value : Nat) : Value := .bits (BitVec.ofNat 64 value)
  let a0 := reg "X10"
  let a1 := reg "X11"
  let a2 := reg "X12"
  let a3 := reg "X13"
  let rw : Primus.Protection := ⟨true, true, false⟩
  let zeros (size : Nat) := ByteArray.mk (List.replicate size 0).toArray
  let decoders ← Bap.Emu.riscv64Decoders
  let make (code : ByteArray) : IO Bap.Emu.Emu := do
    let emu ← Bap.Emu.create {
        disassembler := ← decoders 0
        disassemblerAt := some decoders
        memory := ⟨"mem", .mem 64 8, 0, false⟩
        rangeLimit := 8 } [⟨0, code, ⟨true, true, true⟩⟩] {} 0
    for index in [0:32] do Bap.Emu.setReg emu (reg s!"X{index}") (bits 0)
    pure emu
  let loop := (← rv "addi a0, a0, 1") ++ (← rv "addi a1, a1, 2") ++ (← rv "bne a0, a3, -8") ++ (← rv "addi a2, a2, 1")
  -- A pc-relative branch with no else, and blocks that fall through, chain into one native run.
  let chaining ← make loop
  Bap.Emu.setReg chaining a3 (bits 1000)
  assertEqual "Emu range runs what it is told to" 2500 (← Bap.Emu.run chaining 2500)
  let chainingStats ← Primus.Lifted.stats chaining.engine
  assertEqual "Emu range forms on a lifted loop" 4 chainingStats.graphBlocks
  assertEqual "Emu range goes around a loop in one native run" 1 chainingStats.nativeRuns
  assertBits "Emu range computes what the loop does" (BitVec.ofNat 64 834) (.ok (← Bap.Emu.reg chaining a0))
  assertBits "Emu range computes the rest of the loop" (BitVec.ofNat 64 1666) (.ok (← Bap.Emu.reg chaining a1))
  assertEqual "Emu range ends with the pc at the next instruction" 4 (← Bap.Emu.pc chaining)
  -- What a run of a range left says nothing of the next step: a hook that fails fires once, and one that moves the pc is one instruction.
  let failing ← make loop
  Bap.Emu.setReg failing a3 (bits 1000)
  let _ ← Bap.Emu.run failing 100
  let failedAt ← Bap.Emu.pc failing
  let fired ← IO.mkRef 0
  let _ ← Bap.Emu.onCode failing (failedAt, failedAt) fun _ _ => do
    fired.modify (· + 1)
    throw <| IO.userError "a hook that fails"
  let threw ← try
      let _ ← Bap.Emu.run failing 100
      pure false
    catch _ => pure true
  assertTrue "Emu a hook that fails fails the run" threw
  assertEqual "Emu a hook that fails after a range fires once" 1 (← fired.get)
  let movedRun (stepwise : Bool) : IO (Nat × Nat) := do
    let moved ← make loop
    Bap.Emu.setReg moved a3 (bits 1000)
    let _ ← Bap.Emu.run moved 100
    let at' ← Bap.Emu.pc moved
    let once ← IO.mkRef true
    let _ ← Bap.Emu.onCode moved (at', at') fun current _ => do
      if ← once.get then
        once.set false
        current.pc.set 0
    if stepwise then
      let mut stepped := 0
      for _ in [0:20] do
        if ← Bap.Emu.step moved then stepped := stepped + 1
      pure (stepped, ← Bap.Emu.pc moved)
    else
      pure (← Bap.Emu.run moved 20, ← Bap.Emu.pc moved)
  assertEqual "Emu a hook that moves the pc after a range counts as single steps do" (← movedRun true) (← movedRun false)
  -- The fuel counts instructions, wherever it runs out, and resuming goes on from there.
  for fuel in [1, 2, 3, 4, 5, 7, 11] do
    let exact ← make loop
    Bap.Emu.setReg exact a3 (bits 1000)
    let single ← make loop
    Bap.Emu.setReg single a3 (bits 1000)
    let mut stepped := 0
    for _ in [0:fuel] do
      if ← Bap.Emu.step single then stepped := stepped + 1
    assertEqual s!"Emu range fuel {fuel} is exact" stepped (← Bap.Emu.run exact fuel)
    assertEqual s!"Emu range fuel {fuel} stops at the pc of single steps" (← Bap.Emu.pc single) (← Bap.Emu.pc exact)
    assertEqual s!"Emu range fuel {fuel} has the registers of single steps"
      (repr (← Bap.Emu.reg single a0)).pretty
      (repr (← Bap.Emu.reg exact a0)).pretty
    assertEqual s!"Emu range fuel {fuel} has the other register of single steps"
      (repr (← Bap.Emu.reg single a1)).pretty (repr (← Bap.Emu.reg exact a1)).pretty
  -- A range that runs off its end has the pc of the block it ended in, and not the one after its seed.
  let ending ← make ((← rv "jal 4") ++ (← rv "jal 4") ++ (← rv "addi a0, a0, 7") ++ (← rv "ecall"))
  assertEqual "Emu range ending in a fall-through counts its instructions" 3 (← Bap.Emu.run ending 3)
  assertEqual "Emu range ending in a fall-through has its pc" 12 (← Bap.Emu.pc ending)
  assertBits "Emu range ending in a fall-through ran it" (BitVec.ofNat 64 7) (.ok (← Bap.Emu.reg ending a0))
  -- A block that needs the interpreter stays out of the range, and the range forms around it.
  let special ← make ((← rv "addi a0, a0, 1") ++ (← rv "ecall") ++ (← rv "jal -8"))
  let served ← IO.mkRef 0
  let _ ← Bap.Emu.onSyscall special fun _ _ _ => do
    served.modify (· + 1)
    pure (.returnValue 0)
  let _ ← Bap.Emu.run special 30
  assertEqual "Emu range leaves for a special" 10 (← served.get)
  -- Preemption is exact as well: each thread gets its quantum.
  let round ← make ((← rv "addi a0, a0, 1") ++ (← rv "jal -4"))
  let other ← Bap.Emu.spawnThread round 0 0
  assertEqual "Emu range preempts at its quantum" 100 (← Bap.Emu.runPreemptive round 10 100)
  assertBits "Emu range quantum: first thread" (BitVec.ofNat 64 25) (.ok (← Bap.Emu.threadReg round 1 a0))
  assertBits "Emu range quantum: second thread" (BitVec.ofNat 64 25) (.ok (← Bap.Emu.threadReg round other a0))
  -- A code hook sees every instruction it is on, and all stop where single steps do.
  let hooked ← make loop
  Bap.Emu.setReg hooked a3 (bits 1000)
  let hits ← IO.mkRef 0
  let _ ← Bap.Emu.onCode hooked (4, 4) fun _ _ => hits.modify (· + 1)
  let _ ← Bap.Emu.run hooked 300
  assertEqual "Emu range fires the hooks of its blocks" 100 (← hits.get)
  -- A hook that a write hook adds fires at the very next instruction, in a range that started with no hooks.
  let storing := (← rv "sb a0, 0(a2)") ++ (← rv "addi a0, a0, 1") ++ (← rv "addi a1, a1, 1") ++ (← rv "jal -12")
  let late ← make storing
  Bap.Emu.map late ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg late a2 (bits 0x1000)
  let lateHits ← IO.mkRef ([] : List Nat)
  let added ← IO.mkRef false
  let _ ← Bap.Emu.onWrite late (0x1000, 0x1000) fun _ _ _ _ => do
    if !(← added.get) then
      added.set true
      let _ ← Bap.Emu.onCode late (0, 12) fun _ pc => lateHits.modify (· ++ [pc])
  let _ ← Bap.Emu.run late 4
  assertEqual "Emu range fires a hook added on the way" [4, 8, 12] (← lateHits.get)
  -- A store into the code that a range runs next takes effect at the next instruction.
  let patching ← make ((← rv "sw a1, 0(a2)") ++ (← rv "addi a0, a0, 1") ++ (← rv "addi a3, a3, 5") ++ (← rv "jal -12"))
  Bap.Emu.setReg patching a2 (bits 8)
  let addi9 := (← rv "addi a3, a3, 9")
  let word := (List.range 4).foldl (init := 0) fun word index => word + addi9[index]!.toNat * 256 ^ index
  Bap.Emu.setReg patching a1 (bits word)
  let _ ← Bap.Emu.run patching 3
  assertBits "Emu range sees the code it wrote" (BitVec.ofNat 64 9) (.ok (← Bap.Emu.reg patching a3))
  -- A memory set through its variable is what the next access reads, native memory or not.
  let replaced ← Tuned.riscv64 (← rv "lb a0, 0(a1)") 0 0
  Bap.Emu.map replaced ⟨0x1000, zeros 8, rw⟩
  Bap.Emu.setReg replaced a1 (bits 0x1000)
  Bap.Emu.setReg replaced a0 (bits 0)
  let _ ← Bap.Emu.step replaced
  Bap.Emu.setPc replaced 0
  let fresh := Bap.Memory.writeRegion (Bap.Memory.writeRegion (Bap.Memory.empty 64) 0 (← rv "lb a0, 0(a1)")) 0x1000 (ByteArray.mk #[42])
  Bap.Emu.setReg replaced replaced.config.memory (.memory fresh)
  let _ ← Bap.Emu.step replaced
  assertBits "Emu reads the memory that was set" (BitVec.ofNat 64 42) (.ok (← Bap.Emu.reg replaced a0))
  -- A checkpoint brings back the code a compiled range has to forget.
  let rewinding ← make ((← rv "addi a0, a0, 1") ++ (← rv "addi a0, a0, 1") ++ (← rv "jal -8"))
  let start ← Bap.Emu.snapshot rewinding
  let _ ← Bap.Emu.run rewinding 3
  Bap.Emu.write rewinding 4 (← rv "addi a0, a0, 5")
  let _ ← Bap.Emu.run rewinding 3
  assertBits "Emu range runs written code" (BitVec.ofNat 64 8) (.ok (← Bap.Emu.reg rewinding a0))
  let _ ← Bap.Emu.restore rewinding start
  let _ ← Bap.Emu.run rewinding 3
  assertBits "Emu range after a restore runs the restored code" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg rewinding a0))
  -- A hook reads the state of its block, as in single steps, with the range around it.
  let readingCode := (← rv "addi a0, a0, 1") ++ (← rv "addi a1, a1, 2") ++ (← rv "addi a2, a2, 3") ++ (← rv "jal -12")
  let readings (emu : Bap.Emu.Emu) (steps : IO Unit) : IO (List String) := do
    let seen ← IO.mkRef ([] : List String)
    let _ ← Bap.Emu.onCode emu (8, 8) fun _ pc => do
      let values := [← Bap.Emu.reg emu a0, ← Bap.Emu.reg emu a1, ← Bap.Emu.reg emu a2]
      seen.modify (· ++ [s!"{pc} {(repr values).pretty}"])
    steps
    seen.get
  let hookedRange ← make readingCode
  let hookedSingle ← make readingCode
  let inRange ← readings hookedRange (do let _ ← Bap.Emu.run hookedRange 25)
  let inSteps ← readings hookedSingle (do for _ in [0:25] do let _ ← Bap.Emu.step hookedSingle)
  assertEqual "Emu code hook in a range reads what single steps have" inSteps inRange
  assertTrue "Emu range keeps chaining around a hook" ((← Primus.Lifted.stats hookedRange.engine).nativeRuns < 25)
  -- So does a hook of an access, which comes in the middle of a block.
  let accessCode := (← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a2)") ++ (← rv "jal -8")
  let watching (emu : Bap.Emu.Emu) (steps : IO Unit) : IO (List String) := do
    Bap.Emu.map emu ⟨0x1000, zeros 8, rw⟩
    Bap.Emu.setReg emu a2 (bits 0x1000)
    let seen ← IO.mkRef ([] : List String)
    let _ ← Bap.Emu.onWrite emu (0x1000, 0x1000) fun _ _ _ value => do
      seen.modify (· ++ [s!"{value} {(repr (← Bap.Emu.reg emu a0)).pretty}"])
    steps
    seen.get
  let watchedRange ← make accessCode
  let watchedSingle ← make accessCode
  let watched ← watching watchedRange (do let _ ← Bap.Emu.run watchedRange 16)
  assertEqual "Emu access hook in a run reads what single steps have"
    (← watching watchedSingle (do for _ in [0:16] do let _ ← Bap.Emu.step watchedSingle)) watched
  -- A budget that no slot can hold counts all the same.
  let huge ← make loop
  Bap.Emu.setReg huge a3 (bits 1000)
  let _ ← Bap.Emu.onCode huge (12, 12) fun _ _ => Bap.Emu.stop huge
  assertEqual "Emu range counts with any fuel" 3000 (← Bap.Emu.run huge (2 ^ 64 + 1))
  -- A fault in a range leaves the emulator as a fault in single steps does, on a table of ways to fault.
  let load := (← rv "addi a0, a0, 1") ++ (← rv "addi a1, a1, 1") ++ (← rv "lb a2, 0(a3)")
  let walk := (← rv "lb a0, 0(a1)") ++ (← rv "addi a1, a1, 1") ++ (← rv "addi a2, a2, 1") ++ (← rv "bne a2, a3, -12")
  let table : List (String × ByteArray × List (Var × Nat) × Bool) := [
    ("a load after two instructions", load, [(a3, 0x9000)], false),
    ("the first instruction", (← rv "lb a2, 0(a3)") ++ (← rv "addi a0, a0, 1"), [(a3, 0x9000)], false),
    ("a store after a store", (← rv "addi a0, a0, 7") ++ (← rv "sb a0, 0(a1)") ++ (← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a3)"),
      [(a1, 0x1000), (a3, 0x9000)], false),
    ("a pointer that walks off a region in a loop", walk, [(a1, 0x1000), (a3, 1000)], false),
    ("a store that walks off a region in a loop", (← rv "sb a2, 0(a1)") ++ (← rv "addi a1, a1, 1") ++ (← rv "addi a2, a2, 1") ++ (← rv "bne a2, a3, -12"),
      [(a1, 0x1000), (a3, 1000)], false),
    ("a store to read-only memory", (← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a1)") ++ (← rv "addi a0, a0, 1") ++ (← rv "sb a0, 0(a3)"),
      [(a1, 0x1000), (a3, 0x2000)], false),
    ("a load that passes the end of a region", (← rv "addi a0, a0, 1") ++ (← rv "lw a2, 0(a1)"), [(a1, 0x1000 + 14)], false),
    ("past jumps", (← rv "jal 8") ++ (← rv "addi a0, a0, 100") ++ (← rv "addi a1, a1, 1") ++ (← rv "lb a2, 0(a3)"), [(a3, 0x9000)], false),
    ("with a hook out of the way", load, [(a3, 0x9000)], true)
  ]
  for (name, code, registers, hook) in table do
    let setup : IO Bap.Emu.Emu := do
      let emu ← make code
      Bap.Emu.map emu ⟨0x1000, zeros 16, rw⟩
      Bap.Emu.map emu ⟨0x2000, zeros 16, ⟨true, false, false⟩⟩
      for (var, value) in registers do Bap.Emu.setReg emu var (bits value)
      if hook then
        let _ ← Bap.Emu.onCode emu (0x8000, 0x8000) fun _ _ => pure ()
      pure emu
    let ranged ← setup
    let single ← setup
    expectThrow s!"Emu range faults at {name}" (do let _ ← Bap.Emu.run ranged 100000)
    let mut count := 0
    let mut failed := false
    while !failed do
      try
        let _ ← Bap.Emu.step single
        count := count + 1
      catch _ =>
        failed := true
    let chained ← Primus.Lifted.stats ranged.engine
    if count > 1 then
      assertTrue s!"Emu range at {name} chained: {chained.nativeRuns} of {count + 2}" (chained.nativeRuns ≤ count + 2)
    let view (emu : Bap.Emu.Emu) : IO String := do
      let values ← [a0, a1, a2, a3].mapM (Bap.Emu.reg emu)
      let fault ← Bap.Emu.failure emu
      let bytes ← Bap.Emu.read emu 0x1000 16
      pure s!"{(repr values).pretty} {← Bap.Emu.pc emu} {repr fault} {bytes.toList} {← Bap.Emu.stopped emu}"
    assertEqual s!"Emu range fault at {name} has the state of single steps" (← view single) (← view ranged)
    -- And it goes on the same: it faults again where it was.
    expectThrow s!"Emu range fault at {name} recurs" (do let _ ← Bap.Emu.run ranged 100000)
    expectThrow s!"Emu single-step fault at {name} recurs" (do let _ ← Bap.Emu.step single)
    assertEqual s!"Emu range fault at {name} recurs the same way" (← view single) (← view ranged)
  -- What it is told in so many words: the two instructions before the fault have happened.
  let faulting ← make load
  Bap.Emu.setReg faulting a3 (bits 0x9000)
  expectThrow "Emu range faults" (do let _ ← Bap.Emu.run faulting 10)
  let some fault := ← Bap.Emu.failure faulting | throw <| IO.userError "the range recorded no fault"
  assertEqual "Emu range fault has the pc of the access" 8 fault.pc
  assertEqual "Emu range fault has the address of the access" 0x9000 fault.address
  assertEqual "Emu range fault leaves the pc at the access" 8 (← Bap.Emu.pc faulting)
  assertBits "Emu range fault has run what came before" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg faulting a0))
  assertBits "Emu range fault has run all that came before" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg faulting a1))

/-- A parallel worker reads what native code wrote in the same round, also in an instruction that it interprets. -/
private def parallelReadThrough : IO Unit := do
  let rv (text : String) := LLVM.assemble "riscv64" text
  let bits (value : Nat) : Value := .bits (BitVec.ofNat 64 value)
  let a0 := reg "X10"
  let a1 := reg "X11"
  let a2 := reg "X12"
  let a3 := reg "X13"
  let a4 := reg "X14"
  let decoders ← Bap.Emu.riscv64Decoders
  -- With a threshold of two, the second store runs natively, and the first load is interpreted.
  let code := (← rv "sb a0, 0(a1)") ++ (← rv "addi a0, a0, 1") ++ (← rv "addi a2, a2, 1") ++ (← rv "bne a2, a3, -12") ++
    (← rv "lb a4, 0(a1)") ++ (← rv "jal 0")
  let emu ← Bap.Emu.create {
      disassembler := ← decoders 0
      disassemblerAt := some decoders
      memory := ⟨"mem", .mem 64 8, 0, false⟩
      hotThreshold := 2 } [⟨0, code, ⟨true, true, true⟩⟩, ⟨0x1000, ByteArray.mk (List.replicate 16 0).toArray, ⟨true, true, false⟩⟩] {} 0
  for (var, value) in [(a0, 5), (a1, 0x1000), (a2, 0), (a3, 2), (a4, 0)] do Bap.Emu.setReg emu var (bits value)
  let second ← Bap.Emu.spawnThread emu 20 0
  let _ ← Bap.Emu.runPreemptiveParallel emu 9
  let stats ← Primus.Lifted.stats emu.engine
  assertTrue "the store runs natively and the load is interpreted" (stats.nativeRuns > 0 && stats.interpretedRuns > 0)
  assertBits "a parallel worker's interpreted load reads what its native store wrote" (BitVec.ofNat 64 6)
    (.ok (← Bap.Emu.threadReg emu 1 a4))
  assertEqual "the memory has what the native store wrote" 6 (← Bap.Emu.read emu 0x1000 1)[0]!.toNat
  let _ := second

/-- On a 32-bit space an access past the end faults, in the interpreter and in native code alike. -/
private def wrapRegressions : IO Unit := do
  let code := (← LLVM.assemble "riscv32" "lw a0, 0(a1)") ++ (← LLVM.assemble "riscv32" "jal 0")
  let a0 : Var := ⟨"X10", .imm 32, 0, false⟩
  let a1 : Var := ⟨"X11", .imm 32, 0, false⟩
  let bits (value : Nat) : Value := .bits (BitVec.ofNat 32 value)
  let emu ← Tuned.riscv32 code 0 0
  Bap.Emu.map emu ⟨0xfffff000, ByteArray.mk (List.replicate 4096 1).toArray, ⟨true, true, false⟩⟩
  Bap.Emu.setReg emu a0 (bits 0)
  Bap.Emu.setReg emu a1 (bits 0xffffff00)
  let _ ← Bap.Emu.step emu
  assertBits "Emu 32-bit load in range" (BitVec.ofNat 32 0x01010101) (.ok (← Bap.Emu.reg emu a0))
  onStepwise <| assertEqual "Emu 32-bit load runs natively" 1 (← Primus.Lifted.stats emu.engine).nativeRuns
  Bap.Emu.setPc emu 0
  Bap.Emu.setReg emu a1 (bits 0xfffffffe)
  expectThrow "Emu 32-bit load that passes the end faults" (Bap.Emu.step emu)
  let some fault := ← Bap.Emu.failure emu | throw <| IO.userError "the load recorded no fault"
  assertEqual "Emu 32-bit load faults at the end of the space" (2 ^ 32) fault.address

/-- A hook of an access inside a compiled range takes the step back, so that it sees and leaves exactly what single steps do,
at any fuel, and accesses that no hook watches do not slow the range down. -/
private def accessHookRanges : IO Unit := do
  let rv (source : String) : IO ByteArray := LLVM.assemble "riscv64" source
  let word (value : Nat) : Value := .bits (BitVec.ofNat 64 value)
  let code := (← rv "addi a0, a0, 1") ++ (← rv "sd a0, 0(a4)") ++ (← rv "ld a1, 8(a4)") ++ (← rv "add a2, a2, a1") ++
    (← rv "bne a0, a3, -16") ++ (← rv "ld a5, 0(a6)") ++ (← rv "jal 0")
  let fresh (hotThreshold rangeLimit : Nat) (faultAt : Nat) : IO Bap.Emu.Emu := do
    let emu ← Bap.Emu.riscv64 code 0 0
      (adjust := fun config => { config with hotThreshold, rangeLimit })
    Bap.Emu.map emu ⟨0x1000, ByteArray.mk (List.replicate 32 1).toArray, ⟨true, true, false⟩⟩
    for name in ["X10", "X11", "X12", "X15"] do Bap.Emu.setReg emu (reg name) (word 0)
    Bap.Emu.setReg emu (reg "X13") (word 12)
    Bap.Emu.setReg emu (reg "X14") (word 0x1000)
    Bap.Emu.setReg emu (reg "X16") (word faultAt)
    pure emu
  let regValue (emu : Bap.Emu.Emu) (name : String) : IO Nat := do
    match ← Bap.Emu.reg emu (reg name) with
    | .bits value => pure value.toNat
    | _ => throw <| IO.userError s!"{name} is not a word"
  /- What a run does, as hooks and afterwards see it. -/
  let trial (hotThreshold rangeLimit fuel faultAt : Nat) : IO (List (Nat × Nat × Nat) × List Nat × Bool) := do
    let emu ← fresh hotThreshold rangeLimit faultAt
    let log ← IO.mkRef ([] : List (Nat × Nat × Nat))
    let note (kind : Nat) : IO Unit := do
      let pc ← Bap.Emu.pc emu
      let value ← regValue emu "X10"
      log.modify ((kind, pc, value) :: ·)
    let _ ← Bap.Emu.onRead emu (0x1008, 0x100f) fun _ _ _ => note 0
    let _ ← Bap.Emu.onWrite emu (0x1000, 0x1007) fun _ _ _ _ => note 1
    let _ ← Bap.Emu.onCode emu (12, 12) fun _ _ => note 2
    let failed ← try
        let _ ← Bap.Emu.run emu fuel
        pure false
      catch _ => pure true
    let registers ← ["X10", "X11", "X12", "X15"].mapM (regValue emu)
    pure (← log.get, (← Bap.Emu.pc emu) :: registers, failed)
  for fuel in [1, 2, 3, 4, 5, 7, 11, 16, 26, 40, 59, 60, 61, 62, 70] do
    let expected ← trial 1 1 fuel 0x1000
    assertEqual s!"Emu hooks in a range see what single steps see, fuel {fuel}" expected (← trial 1 16 fuel 0x1000)
    assertEqual s!"Emu hooks past the threshold see what single steps see, fuel {fuel}" expected (← trial 16 16 fuel 0x1000)
  -- And a fault after them, in the same range.
  for fuel in [58, 61, 70] do
    let expected ← trial 1 1 fuel 0x9000
    assertEqual s!"Emu fault after hooks in a range is the same, fuel {fuel}" expected (← trial 1 16 fuel 0x9000)
  -- A step after a run that a hook stopped is one instruction.
  let halted ← fresh 1 16 0x1000
  let _ ← Bap.Emu.onCode halted (12, 12) fun _ _ => Bap.Emu.stop halted
  let _ ← Bap.Emu.run halted 40
  assertEqual "Emu run stops at the hook" 12 (← Bap.Emu.pc halted)
  Bap.Emu.resume halted
  let _ ← Bap.Emu.step halted
  assertEqual "Emu step after a stopped run is one instruction" 16 (← Bap.Emu.pc halted)
  -- Hooks that nothing touches leave the ranges alone.
  let far ← fresh 1 16 0x1000
  let farHits ← IO.mkRef 0
  let _ ← Bap.Emu.onRead far (0x1018, 0x101f) fun _ _ _ => farHits.modify (· + 1)
  let _ ← Bap.Emu.onWrite far (0x1018, 0x101f) fun _ _ _ _ => farHits.modify (· + 1)
  assertEqual "Emu range under hooks elsewhere runs all of it" 60 (← Bap.Emu.run far 60)
  assertEqual "Emu hooks elsewhere do not fire" 0 (← farHits.get)
  assertTrue "Emu range keeps chaining under hooks elsewhere" ((← Primus.Lifted.stats far.engine).nativeRuns < 10)
  -- A hook that is hit takes its steps out of the range, and removing it brings them back.
  let hit ← fresh 1 16 0x1000
  let hits ← IO.mkRef 0
  let hook ← Bap.Emu.onRead hit (0x1008, 0x100f) fun _ _ _ => hits.modify (· + 1)
  let _ ← Bap.Emu.run hit 30
  assertEqual "Emu hit hook fires once per load" 6 (← hits.get)
  assertTrue "Emu steps that met the hook are single steps" !(← hit.watchedSteps.get).isEmpty
  Bap.Emu.removeHook hit hook
  assertTrue "Emu removing a hook lets its steps chain again" (← hit.watchedSteps.get).isEmpty

private def allEmulatorTests : IO Unit := do
  accessHookRanges
  rangeRegressions
  parallelReadThrough
  wrapRegressions
  diffAndCodecRegressions
  regionAudit
  coreRegressions
  runEmulator

/-- A little-endian MIPS and its delay slots: the word of a branch is read in its byte order. -/
private def mipsLittle : IO Unit := do
  for (triple, bits, make) in [("mips64el", 64, Bap.Emu.mips64 (endian := .little)), ("mipsel", 32, Bap.Emu.mips32 (endian := .little))] do
    let code := (← LLVM.assemble triple "addiu $4, $4, 1") ++ ByteArray.mk #[0x02, 0, 0, 0x10] ++
      (← LLVM.assemble triple "addiu $4, $4, 10") ++ (← LLVM.assemble triple "addiu $4, $4, 100") ++
      (← LLVM.assemble triple "addiu $5, $5, 1")
    let a0 : Bap.Var := ⟨"R4", .imm bits, 0, false⟩
    let a1 : Bap.Var := ⟨"R5", .imm bits, 0, false⟩
    let emu ← make code 0 0
    Bap.Emu.setReg emu a0 (.bits (BitVec.ofNat bits 0))
    Bap.Emu.setReg emu a1 (.bits (BitVec.ofNat bits 0))
    let _ ← Bap.Emu.run emu 4
    match ← Bap.Emu.reg emu a0, ← Bap.Emu.reg emu a1 with
    | .bits first, .bits second =>
      assertEqual s!"{triple} runs its delay slot and skips what the branch skips" 11 first.toNat
      assertEqual s!"{triple} goes on at the target" 1 second.toNat
    | _, _ => throw <| IO.userError "no registers"

/-- A range runs on over an instruction that does nothing, and doesn't leave and come back at each pass of a loop. -/
private def nopInLoop : IO Unit := do
  let code ← LLVM.assemble "x86_64" "movl $0, %eax\nmovl $1000, %ecx\n1:\nnopw 0(%rax,%rax,1)\nsubl $1, %ecx\njne 1b\nhlt"
  let emu ← Bap.Emu.x86_64 code 0x1000 0x1000
  let steps ← Bap.Emu.run emu 3002
  assertEqual "a loop with a nop runs all of its instructions" 3002 steps
  match ← Bap.Emu.reg emu ⟨"RCX", .imm 64, 0, false⟩ with
  | .bits value => assertEqual "and counts down" 0 value.toNat
  | _ => throw <| IO.userError "no RCX"
  let statistics ← emu.engine.statistics.get
  assertTrue s!"and stays in a compiled range: {statistics.nativeRuns} runs" (statistics.nativeRuns < 100)

/-- The tests of the emulator, on the machine as it comes, on one that compiles everything at once, and on one that does not
chain, so that they say the same of native code, ranges and the interpreter. -/
def run : IO Unit := do
  nopInLoop
  mipsLittle
  allEmulatorTests
  tuningRef.set (some (1, 4096, 16))
  allEmulatorTests
  tuningRef.set (some (1, 128, 1))
  stepwise.set true
  allEmulatorTests

end Bap.Tests.Emu
