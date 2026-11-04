import BapTests.Support

namespace Bap.Tests.Emu

open Bap

private def expectThrow (name : String) (action : IO α) : IO Unit := do
  match ← action.toBaseIO with
  | .error _ => IO.println s!"ok: {name}"
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly succeeded"

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
  -- Where another thread goes on from, and where the one that runs does, which forgets the branch that it was in the middle of.
  Bap.Emu.restore emu pending
  let other ← Bap.Emu.spawnThread emu 16 7
  Bap.Emu.setThreadPc emu other 20
  assertEqual "Emu a thread goes on from where it is set to" 20 (← Bap.Emu.threadPc emu other)
  assertEqual "Emu and the thread that runs doesn't" 4 (← Bap.Emu.pc emu)
  Bap.Emu.switchThread emu other
  assertEqual "Emu switching to it, it is there" 20 (← Bap.Emu.pc emu)
  Bap.Emu.setThreadPc emu 1 8
  Bap.Emu.switchThread emu 1
  assertEqual "Emu a thread in a delay slot goes on from where it is set to" 8 (← Bap.Emu.pc emu)
  assertTrue "Emu and forgets the branch that it was in the middle of" (← emu.pendingRef.get).isNone
  Bap.Emu.restore emu pending
  assertTrue "Emu a thread in a delay slot has a branch to go to" (← emu.pendingRef.get).isSome
  Bap.Emu.setThreadPc emu 1 0
  assertEqual "Emu the thread that runs goes on from where it is set to" 0 (← Bap.Emu.pc emu)
  assertTrue "Emu and forgets its branch" (← emu.pendingRef.get).isNone
  expectThrow "Emu a thread that isn't there has no pc to set" (Bap.Emu.setThreadPc emu 99 0)

/-- Each thread pushes a value and reads it back after the other has pushed: with one stack it would read the other's. -/
private def testCloneThread : IO Unit := do
  let code := (← LLVM.assemble "riscv64" "addi sp, sp, -8") ++
    (← LLVM.assemble "riscv64" "sd a2, 0(sp)") ++
    (← LLVM.assemble "riscv64" "ld a3, 0(sp)")
  let emu ← Tuned.riscv64 code 0 0
  Bap.Emu.map emu ⟨0x1000, ByteArray.mk (List.replicate 64 0).toArray, ⟨true, true, false⟩⟩
  let bits (value : Nat) : Bap.Value := .bits (BitVec.ofNat 64 value)
  Bap.Emu.setReg emu (reg "X2") (bits 0x1010)
  Bap.Emu.setReg emu (reg "X4") (bits 0x77)
  Bap.Emu.setReg emu (reg "X10") (bits 5)
  Bap.Emu.setReg emu (reg "X12") (bits 1)
  let child ← Bap.Emu.clone emu { start := 0, stack := some 0x1030, threadPointer := some 0x88, shareMemory := true, sameGroup := true }
  assertBits "Emu clone runs on its stack" (BitVec.ofNat 64 0x1030) (.ok (← Bap.Emu.threadReg emu child (reg "X2")))
  assertBits "Emu clone returns 0" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.threadReg emu child (reg "X10")))
  assertBits "Emu clone has its thread pointer" (BitVec.ofNat 64 0x88) (.ok (← Bap.Emu.threadReg emu child (reg "X4")))
  assertBits "Emu clone copies the other registers" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.threadReg emu child (reg "X12")))
  assertBits "Emu clone leaves the parent's stack" (BitVec.ofNat 64 0x1010) (.ok (← Bap.Emu.reg emu (reg "X2")))
  assertBits "Emu clone leaves the parent's thread pointer" (BitVec.ofNat 64 0x77) (.ok (← Bap.Emu.reg emu (reg "X4")))
  let _ ← Bap.Emu.run emu 2
  Bap.Emu.switchThread emu child
  Bap.Emu.setReg emu (reg "X12") (bits 2)
  let _ ← Bap.Emu.run emu 3
  assertBits "Emu clone reads its own frame" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg emu (reg "X13")))
  Bap.Emu.switchThread emu 1
  let _ ← Bap.Emu.run emu 1
  assertBits "Emu parent of a clone reads its own frame" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu (reg "X13")))

/-- Processes, as programs see them, through system calls and `runProcesses`. -/
private def testProcesses : IO Unit := do
  let rv (text : String) := LLVM.assemble "riscv64" text
  let asm (lines : List String) : IO ByteArray := do
    lines.foldlM (fun code line => do pure (code ++ (← rv line))) ByteArray.empty
  let word (emu : Bap.Emu.Emu) (address : Nat) : IO Nat := do
    let bytes ← Bap.Emu.read emu address 4
    pure (bytes[0]!.toNat + bytes[1]!.toNat * 256 + bytes[2]!.toNat * 65536 + bytes[3]!.toNat * 16777216)
  let zeros := ByteArray.mk (List.replicate 64 (0 : UInt8)).toArray
  let clean (emu : Bap.Emu.Emu) : IO Bap.Emu.Emu := do
    for index in List.range 32 do
      Bap.Emu.setReg emu (reg s!"X{index}") (.bits (BitVec.ofNat 64 0))
    pure emu
  let rw : Primus.Protection := ⟨true, true, false⟩
  -- clone(SIGCHLD); the child writes, then exits with 7; the parent waits for it and then finds no child.
  let program ← asm [
    "addi a7, zero, 220", "addi a0, zero, 17", "addi a1, zero, 0", "ecall",
    "bne a0, zero, 28",
    "addi t0, zero, 9", "lui t1, 1", "sw t0, 8(t1)",
    "addi a0, zero, 7", "addi a7, zero, 93", "ecall",
    "addi s1, a0, 0",
    "addi a0, zero, -1", "lui a1, 1", "addi a2, zero, 0", "addi a3, zero, 0", "addi a7, zero, 260", "ecall",
    "addi s2, a0, 0",
    "lui t1, 1", "lw s3, 8(t1)",
    "addi a0, zero, -1", "addi a1, zero, 0", "addi a7, zero, 260", "ecall",
    "addi s4, a0, 0",
    "addi a7, zero, 172", "ecall", "addi s5, a0, 0",
    "addi a0, zero, 3", "addi a7, zero, 94", "ecall"]
  let emu ← clean (← Tuned.riscv64 program 0 0)
  Bap.Emu.map emu ⟨0x1000, zeros, rw⟩
  let _ ← Bap.Emu.serveTaskCalls emu
  assertEqual "Emu process finishes with its status" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 3))
    (← Bap.Emu.runProcesses emu 3 1000)
  assertBits "Emu waitpid returns the child" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg emu (reg "X18")))
  assertBits "Emu parent sees what fork returned" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg emu (reg "X9")))
  assertEqual "Emu waitpid writes the status" (Bap.Tasks.exitedStatus 7) (← word emu 0x1000)
  assertBits "Emu child's write stays in the child" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.reg emu (reg "X19")))
  assertBits "Emu second waitpid has no child" (BitVec.ofNat 64 (2 ^ 64 - 10)) (.ok (← Bap.Emu.reg emu (reg "X20")))
  assertBits "Emu getpid is the first process" (BitVec.ofNat 64 1) (.ok (← Bap.Emu.reg emu (reg "X21")))
  assertEqual "Emu a reported child is gone" [1] ((← Bap.Emu.tasks emu).map (·.tid))
  -- WNOHANG says 0 while the child runs.
  let polling ← asm [
    "addi a7, zero, 220", "addi a0, zero, 17", "addi a1, zero, 0", "ecall",
    "beq a0, zero, 32",
    "addi a0, zero, -1", "addi a1, zero, 0", "addi a2, zero, 1", "addi a3, zero, 0", "addi a7, zero, 260", "ecall",
    "beq zero, zero, 24",
    "addi a0, zero, 0", "addi a7, zero, 93", "ecall", "beq zero, zero, 0", "beq zero, zero, 0", "beq zero, zero, 0",
    "addi s1, a0, 0", "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  let nohang ← clean (← Tuned.riscv64 polling 0 0)
  let _ ← Bap.Emu.serveTaskCalls nohang
  let _ ← Bap.Emu.runProcesses nohang 100 1000
  assertBits "Emu WNOHANG returns 0 while the child runs" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.reg nohang (reg "X9")))
  -- The host side: a child that loops can be killed, and then waited for.
  let spinning ← clean (← Tuned.riscv64 (← rv "beq zero, zero, 0") 0 0)
  let spinner ← Bap.Emu.fork spinning 0
  assertEqual "Emu waitpid of a running child" Bap.Tasks.WaitResult.running (← Bap.Emu.waitpid spinning (some spinner))
  assertEqual "Emu parent of a fork" [(1, 0), (spinner, 1)] ((← Bap.Emu.tasks spinning).map fun task => (task.tid, task.parent))
  Bap.Emu.kill spinning spinner 9
  assertEqual "Emu waitpid of a killed child" (Bap.Tasks.WaitResult.exited spinner (Bap.Tasks.signaledStatus 9))
    (← Bap.Emu.waitpid spinning (some spinner))
  assertEqual "Emu waitpid after the report" Bap.Tasks.WaitResult.noChild (← Bap.Emu.waitpid spinning (some spinner))
  -- A child that faults ends with SIGSEGV, and its parent goes on.
  let faulting ← asm [
    "addi a7, zero, 220", "addi a0, zero, 17", "addi a1, zero, 0", "ecall",
    "bne a0, zero, 12", "lui t1, 16", "lw t0, 0(t1)",
    "addi a0, zero, -1", "lui a1, 1", "addi a2, zero, 0", "addi a3, zero, 0", "addi a7, zero, 260", "ecall",
    "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  let faults ← clean (← Tuned.riscv64 faulting 0 0)
  Bap.Emu.map faults ⟨0x1000, zeros, rw⟩
  let _ ← Bap.Emu.serveTaskCalls faults
  assertEqual "Emu parent of a child that faults finishes" (Bap.Tasks.ScheduleOutcome.finished 0) (← Bap.Emu.runProcesses faults 5 1000)
  assertEqual "Emu fault is SIGSEGV" (Bap.Tasks.signaledStatus 11) (← word faults 0x1000)
  -- Waiting for a child that is stopped for good is a deadlock.
  let waiting ← asm [
    "addi a7, zero, 220", "addi a0, zero, 17", "addi a1, zero, 0", "ecall",
    "addi a0, zero, -1", "addi a1, zero, 0", "addi a2, zero, 0", "addi a3, zero, 0", "addi a7, zero, 260", "ecall",
    "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  let blocked ← clean (← Tuned.riscv64 waiting 0 0)
  let _ ← Bap.Emu.serveTaskCalls blocked
  let stopChild ← IO.mkRef true
  let _ ← Bap.Emu.onCode blocked (16, 16) fun current _ => do
    if (← Bap.Emu.pid current) != 1 && (← stopChild.get) then
      stopChild.set false
      Bap.Emu.stopThread current (← Bap.Emu.thread current)
  match ← Bap.Emu.runProcesses blocked 1 100 with
  | .stopped id => assertEqual "Emu a hook stops the child" 2 id
  | outcome => throw <| IO.userError s!"expected a stopped child, got {repr outcome}"
  Bap.Emu.switchThread blocked 1
  assertEqual "Emu a child stopped for good is a deadlock" (Bap.Tasks.ScheduleOutcome.deadlock [1]) (← Bap.Emu.runProcesses blocked 1 100)
  -- A thread of a forked process shares that process's memory, and not its parent's. It is a task like any other.
  let threaded ← clean (← Tuned.riscv64 (← asm ["addi t0, t0, 1", "beq zero, zero, -4"]) 0 0)
  Bap.Emu.map threaded ⟨0x1000, zeros, rw⟩
  let forkedParent ← Bap.Emu.fork threaded 0
  Bap.Emu.switchThread threaded forkedParent
  let sibling ← Bap.Emu.clone threaded { start := 0, stack := some 0x1030, shareMemory := true, sameGroup := true }
  Bap.Emu.write threaded 0x1000 (ByteArray.mk #[42])
  assertEqual "Emu thread is in the group of its process" [(1, 1, 1), (forkedParent, forkedParent, forkedParent), (sibling, forkedParent, forkedParent)]
    ((← Bap.Emu.tasks threaded).map fun task => (task.tid, task.group, task.space))
  Bap.Emu.switchThread threaded sibling
  assertEqual "Emu thread of a fork sees what its process wrote" 42 (← Bap.Emu.read threaded 0x1000 1)[0]!.toNat
  Bap.Emu.write threaded 0x1001 (ByteArray.mk #[43])
  Bap.Emu.switchThread threaded 1
  assertEqual "Emu first process doesn't see it" 0 (← Bap.Emu.read threaded 0x1000 1)[0]!.toNat
  Bap.Emu.switchThread threaded forkedParent
  assertEqual "Emu process sees what its thread wrote" 43 (← Bap.Emu.read threaded 0x1001 1)[0]!.toNat
  Bap.Emu.switchThread threaded 1
  Bap.Emu.switchThread threaded sibling
  assertEqual "Emu memory of the thread survives the way through another" 43 (← Bap.Emu.read threaded 0x1001 1)[0]!.toNat
  -- What a process maps is its own, and what it unmaps is gone, and zeros if it comes back.
  let mapping ← clean (← Tuned.riscv64 (← rv "beq zero, zero, 0") 0 0)
  let mappingChild ← Bap.Emu.fork mapping 0
  Bap.Emu.map mapping ⟨0x5000, ByteArray.mk (List.replicate 0x2000 (9 : UInt8)).toArray, rw⟩
  assertEqual "Emu a mapping is there" 9 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  Bap.Emu.switchThread mapping mappingChild
  expectThrow "Emu a mapping of another process isn't" (Bap.Emu.read mapping 0x5000 1)
  Bap.Emu.map mapping ⟨0x5000, ByteArray.mk (List.replicate 0x1000 (7 : UInt8)).toArray, rw⟩
  assertEqual "Emu a process can map the same address" 7 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  Bap.Emu.switchThread mapping 1
  assertEqual "Emu each has its own bytes there" 9 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  let saved ← Bap.Emu.snapshot mapping
  Bap.Emu.unmap mapping 0x5000 0x1000
  expectThrow "Emu what is unmapped is gone" (Bap.Emu.read mapping 0x5000 1)
  assertEqual "Emu the rest of it is there" 9 (← Bap.Emu.read mapping 0x6000 1)[0]!.toNat
  Bap.Emu.map mapping ⟨0x5000, ByteArray.mk (List.replicate 0x1000 (0 : UInt8)).toArray, rw⟩
  assertEqual "Emu mapped again it is zeros" 0 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  Bap.Emu.restore mapping saved
  assertEqual "Emu a snapshot has the map of each process" 9 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  Bap.Emu.switchThread mapping mappingChild
  assertEqual "Emu a snapshot has the map of the other" 7 (← Bap.Emu.read mapping 0x5000 1)[0]!.toNat
  -- Sharing memory without being a thread is a process of its own in the same space.
  let spaced ← clean (← Tuned.riscv64 (← rv "beq zero, zero, 0") 0 0)
  Bap.Emu.map spaced ⟨0x1000, zeros, rw⟩
  let vmProcess ← Bap.Emu.clone spaced { start := 0, shareMemory := true }
  assertEqual "Emu clone with CLONE_VM alone is a process" [(1, 1, 0, 1), (vmProcess, vmProcess, 1, 1)]
    ((← Bap.Emu.tasks spaced).map fun task => (task.tid, task.group, task.parent, task.space))
  -- A process isn't over until its last thread is, whichever exits first.
  let leaderExits ← asm [
    "addi a7, zero, 220", "addi a0, zero, 17", "addi a1, zero, 0", "ecall",
    "bne a0, zero, 56",
    "lui a0, 0x10", "addi a0, a0, 0x100", "lui a1, 1", "addi a1, a1, 64", "addi a7, zero, 220", "ecall",
    "beq a0, zero, 16",
    "addi a0, zero, 5", "addi a7, zero, 93", "ecall",
    "addi a0, zero, 9", "addi a7, zero, 93", "ecall",
    "addi a0, zero, -1", "lui a1, 1", "addi a2, zero, 0", "addi a3, zero, 0", "addi a7, zero, 260", "ecall",
    "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  let lastThread ← clean (← Tuned.riscv64 leaderExits 0 0)
  Bap.Emu.map lastThread ⟨0x1000, zeros, rw⟩
  let _ ← Bap.Emu.serveTaskCalls lastThread
  assertEqual "Emu parent of a threaded child finishes" (Bap.Tasks.ScheduleOutcome.finished 0) (← Bap.Emu.runProcesses lastThread 2 2000)
  assertEqual "Emu the status of a process is its leader's" (Bap.Tasks.exitedStatus 5) (← word lastThread 0x1000)
  -- Tasks of a forked space in a parallel round: each writes its own byte. Both thread writes are in the space, and in the
  -- memory of the state of each, and the first process has neither.
  let rounds ← clean (← Tuned.riscv64 (← asm ["sb a0, 0(a1)", "beq zero, zero, 0"]) 0 0)
  Bap.Emu.map rounds ⟨0x1000, zeros, rw⟩
  Bap.Emu.setReg rounds (reg "X10") (.bits (BitVec.ofNat 64 1))
  Bap.Emu.setReg rounds (reg "X11") (.bits (BitVec.ofNat 64 0x1010))
  let forkedSpace ← Bap.Emu.fork rounds 0
  Bap.Emu.setThreadReg rounds forkedSpace (reg "X10") (.bits (BitVec.ofNat 64 2))
  Bap.Emu.setThreadReg rounds forkedSpace (reg "X11") (.bits (BitVec.ofNat 64 0x1000))
  Bap.Emu.switchThread rounds forkedSpace
  let inSpace ← Bap.Emu.clone rounds { start := 0, shareMemory := true, sameGroup := true }
  Bap.Emu.setThreadReg rounds inSpace (reg "X10") (.bits (BitVec.ofNat 64 3))
  Bap.Emu.setThreadReg rounds inSpace (reg "X11") (.bits (BitVec.ofNat 64 0x1001))
  Bap.Emu.switchThread rounds 1
  let _ ← Bap.Emu.runPreemptiveParallel rounds 2
  let byteIn (id : Nat) (address : Nat) : IO Nat := do
    Bap.Emu.switchThread rounds id
    let native := (← Bap.Emu.read rounds address 1)[0]!.toNat
    match Bil.lookup (← rounds.state.get).env rounds.config.memory with
    | .ok (.memory memory) => assertEqual "Emu state of a task in a round has its memory" native (Bap.Memory.readRegion memory address 1)[0]!.toNat
    | _ => throw <| IO.userError "memory variable is missing"
    pure native
  assertEqual "Emu round: the fork has its write" 2 (← byteIn forkedSpace 0x1000)
  assertEqual "Emu round: the fork has its thread's write" 3 (← byteIn forkedSpace 0x1001)
  assertEqual "Emu round: the thread has the fork's write" 2 (← byteIn inSpace 0x1000)
  assertEqual "Emu round: the thread has its write" 3 (← byteIn inSpace 0x1001)
  assertEqual "Emu round: the fork doesn't have the first's write" 0 (← byteIn inSpace 0x1010)
  assertEqual "Emu round: the first has its write" 1 (← byteIn 1 0x1010)
  assertEqual "Emu round: the first doesn't have the fork's" 0 (← byteIn 1 0x1000)
  -- pthread_create and pthread_join, as libc makes them of system calls: a stack from mmap, clone with the flags of a thread,
  -- and a futex on the word that the exit of the thread clears. In each order: the thread may be over before the join starts.
  let joining ← asm [
    "addi a7, zero, 222", "addi a0, zero, 0", "lui a1, 4", "addi a2, zero, 3", "addi a3, zero, 0x22", "addi a4, zero, -1",
    "addi a5, zero, 0", "ecall",
    "addi s1, a0, 0", "lui t0, 4", "add a1, s1, t0",
    "lui a0, 0x1210", "addi a0, a0, 0x100", "addi a2, zero, 0", "addi a3, zero, 0", "lui a4, 1", "addi a7, zero, 220", "ecall",
    "bne a0, zero, 32",
    "addi sp, sp, -8", "sd a2, 0(sp)", "addi t0, zero, 77", "lui t1, 1", "sw t0, 8(t1)", "addi a7, zero, 93", "ecall",
    "addi s2, a0, 0",
    "lui a0, 1", "lw a2, 0(a0)", "beq a2, zero, 24",
    "addi a1, zero, 128", "addi a3, zero, 0", "addi a7, zero, 98", "ecall", "beq zero, zero, -28",
    "lui t1, 1", "lw s3, 8(t1)", "lw s4, 0(t1)",
    "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  for quantum in [1, 2, 3, 5, 8, 13, 21, 100] do
    let pthreads ← clean (← Tuned.riscv64 joining 0 0)
    Bap.Emu.map pthreads ⟨0x1000, zeros, rw⟩
    let _ ← Bap.Emu.serveTaskCalls pthreads
    assertEqual s!"Emu pthread program finishes, quantum {quantum}" (Bap.Tasks.ScheduleOutcome.finished 0) (← Bap.Emu.runProcesses pthreads quantum 2000)
    assertBits s!"Emu clone returns the thread, quantum {quantum}" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg pthreads (reg "X18")))
    assertBits s!"Emu join sees what the thread wrote, quantum {quantum}" (BitVec.ofNat 64 77) (.ok (← Bap.Emu.reg pthreads (reg "X19")))
    assertBits s!"Emu the exit of a thread clears its id, quantum {quantum}" (BitVec.ofNat 64 0) (.ok (← Bap.Emu.reg pthreads (reg "X20")))
  -- A word that isn't what the caller thinks is EAGAIN, and a wait that nothing can end is a deadlock unless it has a timeout.
  let futexing (timeout : Nat) (expected : Nat) : IO ByteArray := asm [
    "lui a0, 1", "addi a1, zero, 128", s!"addi a2, zero, {expected}", s!"addi a3, zero, {timeout}", "addi a7, zero, 98", "ecall",
    "addi s1, a0, 0", "addi a0, zero, 0", "addi a7, zero, 94", "ecall"]
  let oneFutex (timeout expected : Nat) : IO (Bap.Emu.Emu × Bap.Tasks.ScheduleOutcome) := do
    let emu ← clean (← Tuned.riscv64 (← futexing timeout expected) 0 0)
    Bap.Emu.map emu ⟨0x1000, zeros, rw⟩
    let _ ← Bap.Emu.serveTaskCalls emu
    let outcome ← Bap.Emu.runProcesses emu 4 200
    pure (emu, outcome)
  let (changed, changedOutcome) ← oneFutex 0 5
  assertEqual "Emu futex of another value goes on" (Bap.Tasks.ScheduleOutcome.finished 0) changedOutcome
  assertBits "Emu futex of another value is EAGAIN" (BitVec.ofNat 64 (2 ^ 64 - 11)) (.ok (← Bap.Emu.reg changed (reg "X9")))
  let (_, stuck) ← oneFutex 0 0
  assertEqual "Emu futex that nothing wakes is a deadlock" (Bap.Tasks.ScheduleOutcome.deadlock [1]) stuck
  let (timedEmu, timed) ← oneFutex 16 0
  assertEqual "Emu futex with a timeout goes on" (Bap.Tasks.ScheduleOutcome.finished 0) timed
  assertBits "Emu futex with a timeout is ETIMEDOUT" (BitVec.ofNat 64 (2 ^ 64 - 110)) (.ok (← Bap.Emu.reg timedEmu (reg "X9")))
  -- The table: the first to wait wakes first, no more than asked, and only those of the word and of the space.
  let waiter (thread space address : Nat) : Bap.Tasks.FutexWaiter := { thread, space, address, bitset := 2 ^ 32 - 1 }
  let table : Bap.Tasks.TaskTable := { futexes := [waiter 3 1 0x10, waiter 4 2 0x10, waiter 5 1 0x20, waiter 6 1 0x10] }
  assertEqual "Emu futex wakes in order and no more than asked" [3] (table.futexWake 1 0x10 (2 ^ 32 - 1) 1).2
  assertEqual "Emu futex wakes only its word in its space" [3, 6] (table.futexWake 1 0x10 (2 ^ 32 - 1) 9).2
  let (requeued, woken, moved) := table.futexRequeue 1 0x10 0x20 1 1
  assertEqual "Emu futex requeue wakes one" [3] woken
  assertEqual "Emu futex requeue moves one" 1 moved
  assertEqual "Emu futex requeue leaves it on the other word" [5, 6] (requeued.futexWake 1 0x20 (2 ^ 32 - 1) 9).2
  -- A task that is blocked stays so across a checkpoint, with what it needs to wake.
  let (blockedEmu, _) ← oneFutex 0 0
  Bap.Emu.save blockedEmu "native/build/emu-task-checkpoint.bin"
  let restored ← clean (← Tuned.riscv64 (← futexing 0 0) 0 0)
  Bap.Emu.map restored ⟨0x1000, zeros, rw⟩
  Bap.Emu.load restored "native/build/emu-task-checkpoint.bin"
  assertEqual "Emu checkpoint keeps who waits on a futex" [1] ((← restored.taskTable.get).futexes.map (·.thread))
  -- x86-64: the child sees 0 in RAX, not RDI, and its parent the child.
  let x86 (text : String) := LLVM.assemble "x86_64" text
  let forking := (← x86 "movq $57, %rax") ++ (← x86 "movq $5, %rdi") ++ (← x86 "syscall") ++ (← x86 "movq %rax, %rbx") ++
    (← x86 "movq $231, %rax") ++ (← x86 "movq %rbx, %rdi") ++ (← x86 "syscall")
  let intel ← Bap.Emu.x86_64 forking 0 0
  for name in ["RAX", "RBX", "RDI", "RSI", "RDX", "R10", "R8", "R9"] do
    Bap.Emu.setReg intel ⟨name, .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.serveTaskCalls intel
  let exited ← Bap.Emu.runProcesses intel 2 100
  assertEqual "Emu x86-64 parent exits with the child's id" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 2)) exited
  let rbx : Bap.Var := ⟨"RBX", .imm 64, 0, false⟩
  assertBits "Emu x86-64 parent gets the child" (BitVec.ofNat 64 2) (.ok (← Bap.Emu.reg intel rbx))
  -- The child's side, stopped before anything else changes its registers.
  let intelChild ← Bap.Emu.x86_64 forking 0 0
  for name in ["RAX", "RBX", "RDI", "RSI", "RDX", "R10", "R8", "R9"] do
    Bap.Emu.setReg intelChild ⟨name, .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 7))
  let forkedIntel ← Bap.Emu.fork intelChild 0
  assertBits "Emu x86-64 child sees 0 in RAX" (BitVec.ofNat 64 0)
    (.ok (← Bap.Emu.threadReg intelChild forkedIntel ⟨"RAX", .imm 64, 0, false⟩))
  assertBits "Emu x86-64 child keeps RDI" (BitVec.ofNat 64 7)
    (.ok (← Bap.Emu.threadReg intelChild forkedIntel ⟨"RDI", .imm 64, 0, false⟩))

/-- A real pthread program under real libc, if there is a compiler to make one: threads, a mutex that they fight over, and
joins. It is 3 s, most of it compiling hot code. -/
def testRealPthreads : IO Unit := do
  let binary := "native/build/pthreads-test"
  -- What gcc makes elsewhere isn't a static x86-64 program for Linux.
  let compiled ← if System.Platform.isWindows || !System.Platform.target.startsWith "x86_64" then
      pure (.error (IO.userError "not here"))
    else
      (IO.Process.output
        { cmd := "gcc", args := #["-static", "-O1", "-pthread", "testsuite/src/libc-threads.c", "-o", binary] }).toBaseIO
  match compiled with
  | .ok { exitCode := 0, .. } =>
    let written ← IO.mkRef ByteArray.empty
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile binary)) "/test" ["/test"]
    let outcome ← machine.run fun data => written.modify (· ++ data)
    assertEqual "Emu runs a libc pthread program to its end" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    assertEqual "Emu threads of libc count to what they should" "y" (String.fromUTF8! (← written.get))
  | _ => IO.println "ok: skipped the libc pthread program, as nothing here compiles one statically"

/-- `blr x30` goes where X30 said, and X30 is then where to come back to. -/
private def testBlrLink : IO Unit := do
  let emu ← Bap.Emu.aarch64 ((← LLVM.assemble "aarch64" "blr x30") ++ (← LLVM.assemble "aarch64" "nop") ++ (← LLVM.assemble "aarch64" "nop")) 0 0
  let x30 : Bap.Var := ⟨"X30", .imm 64, 0, false⟩
  Bap.Emu.setReg emu x30 (.bits (BitVec.ofNat 64 8))
  let _ ← Bap.Emu.step emu
  assertEqual "Emu blr x30 goes where it said" 8 (← Bap.Emu.pc emu)
  assertBits "Emu blr x30 links" (BitVec.ofNat 64 4) (.ok (← Bap.Emu.reg emu x30))

/-- `wzr` is as wide as the 32 bits of what it is compared with: `0 - 0` has to set Z, which is how ld.so tells that hashes are
the same. -/
private def testZeroRegisterWidth : IO Unit := do
  let emu ← Bap.Emu.aarch64 (← LLVM.assemble "aarch64" "cmp wzr, w0, lsr #1") 0 0
  Bap.Emu.setReg emu ⟨"X0", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 1))
  let _ ← Bap.Emu.step emu
  assertBits "Emu cmp wzr is of 32 bits" (BitVec.ofNat 1 1) (.ok (← Bap.Emu.reg emu ⟨"ZF", .imm 1, 0, false⟩))

/-- Programs of other machines than this one, which need no compiler: static, with musl, from `testsuite/src`. What is printed is
what they print under qemu. -/
def testLinuxMusl (triple : String) (floats : Bool := true) (exclusive : Bool := true) : IO Unit := do
  let run (name : String) (quantum : Nat := 100000) : IO (Bap.Tasks.ScheduleOutcome × ByteArray) := do
    let path := s!"testsuite/bin/{triple}-linux-musl-{name}"
    let written ← IO.mkRef ByteArray.empty
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)) "/test" ["/test", "arg1"]
    let outcome ← machine.run (quantum := quantum) fun data => written.modify (· ++ data)
    pure (outcome, ← written.get)
  -- Turns so short that many end between an exclusive load and its store, which then has to fail.
  if exclusive then
    let (outcome, text) ← run "exclusive" 11
    assertEqual s!"Linux {triple} exclusive updates aren't lost" ((Bap.Tasks.ScheduleOutcome.finished 0), "y") (outcome, String.fromUTF8! text)
  let (outcome, text) ← run "libc-files"
  assertEqual s!"Linux {triple} a program has its status" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 5)) outcome
  assertEqual s!"Linux {triple} a program finds its files"
    "args 2 arg1\ncwd /\nread hello 42\nsize 9 dir 0\nseek yz\ndup x\nlink c\nentries 3\ngone -1\ntime 1\nmalloc 1\nnope 1\n"
    (String.fromUTF8! text)
  let (outcome, text) ← run "libc-threads"
  assertEqual s!"Linux {triple} threads end" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} threads count to what they should" "y" (String.fromUTF8! text)
  if floats then
    let (outcome, text) ← run "libc-floats"
    assertEqual s!"Linux {triple} a program of floating point ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    assertEqual s!"Linux {triple} floating point is what qemu does" (← IO.FS.readBinFile s!"testsuite/data/{triple}-libc-floats.out").toList text.toList

/-- Each condition and shape of an IT block under each of the flags, and `tbb` and `tbh`, as qemu runs them. -/
def testThumbIt : IO Unit := do
  let path := "testsuite/bin/thumb-linux-musl-it"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual "Thumb IT blocks end" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual "Thumb IT blocks are what qemu does" (String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/thumb-it.out"))
    (String.fromUTF8! (← written.get))

/-- A program that runs another, a script among them, in a child that had its memory before. -/
def testLinuxExec (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-exec"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" program).addFile "/script" "#!/test child\n".toUTF8
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} a program that runs others ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} programs run others"
    ("missing 2\ndescriptors 3 4\nchild: a bc env=NAME=value kept=1 closed=0\nstatus 7\n" ++
      "child: /script x env=none kept=1 closed=0\nscript 7\n")
    (String.fromUTF8! (← written.get))

/-- A program that its loader and libc load, which says what the same program does when it is static. -/
def testLinuxDynamic (triple : String) : IO Unit := do
  let run (kernel : Bap.Linux.Kernel) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let written ← IO.mkRef ByteArray.empty
    let machine ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
    let outcome ← machine.run fun data => written.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← written.get))
  let file (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let loader ← file "loader"
  let dynamic := ((Bap.Linux.Kernel.empty.addFile "/test" (← file "dynamic")).addFile "/lib/ld-musl.so.1" loader).addFile
    "/lib/libc_musl.so" loader
  let alone := Bap.Linux.Kernel.empty.addFile "/test" (← file "libc-files")
  let (dynamicOutcome, dynamicText) ← run dynamic
  let (staticOutcome, staticText) ← run alone
  assertEqual s!"Linux {triple} a dynamic program has the status of a static one" staticOutcome dynamicOutcome
  assertEqual s!"Linux {triple} a dynamic program does what a static one does" staticText dynamicText

/-- A position-independent program goes where it is asked to, 0 among them, and otherwise where Linux would put it; one that isn't can't be moved. -/
def testLinuxBase (triple : String) (linked : Nat) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-where"
  let run (base : Option Nat) : IO String := do
    let written ← IO.mkRef ByteArray.empty
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"] (base := base)
    let outcome ← machine.run fun data => written.modify (· ++ data)
    assertEqual s!"Linux {triple} a program at a base ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    pure (String.fromUTF8! (← written.get))
  let hex (value : Nat) : String :=
    let digits := String.ofList (Nat.toDigits 16 value)
    String.ofList (List.replicate (16 - digits.length) '0') ++ digits ++ "\n"
  assertEqual s!"Linux {triple} a program goes where Linux puts it" (hex (0x555555554000 + linked)) (← run none)
  assertEqual s!"Linux {triple} a program goes where it was linked" (hex linked) (← run (some 0))
  assertEqual s!"Linux {triple} a program goes at a base" (hex (0x10000000 + linked)) (← run (some 0x10000000))
  let failed ← try let _ ← run (some 0x1001); pure false catch _ => pure true
  assertTrue s!"Linux {triple} a base is a page" failed
  let fixed ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-files"
  let moved ← try let _ ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" fixed) "/test" ["/test"] (base := some 0x10000000); pure false
    catch _ => pure true
  assertTrue s!"Linux {triple} a program that isn't position-independent can't be moved" moved
  let _ ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" fixed) "/test" ["/test"] (base := some 0)

/-- A program of the older ABI of 64-bit PowerPC, that finds its data by what its function descriptor says. -/
def testPowerpcElfv1 : IO Unit := do
  let program ← IO.FS.readBinFile "testsuite/bin/powerpc64-linux-elfv1"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual "Linux ELFv1 a program ends with its status" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 7)) outcome
  assertEqual "Linux ELFv1 a program finds its data" "from a descriptor\n" (String.fromUTF8! (← written.get))

/-- Prefixed instructions of Power10, as qemu runs them. -/
def testPowerpcPrefixed : IO Unit := do
  let program ← IO.FS.readBinFile "testsuite/bin/powerpc64le-linux-musl-prefixed"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual "Linux PowerPC prefixed instructions end" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual "Linux PowerPC prefixed instructions are what qemu does"
    (String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/powerpc64le-prefixed.out")) (String.fromUTF8! (← written.get))

/-- What `/proc/self/auxv` says is what a program was started with. -/
def testLinuxAuxv (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-auxv"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} auxv ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} auxv is what it started with" "1 1 1\n" (String.fromUTF8! (← written.get))

/-- A loop that runs a lot is compiled again with optimization, in the middle of it, and comes to the same. -/
def testOptimizedRange : IO Unit := do
  let code ← LLVM.assemble "riscv64" "addi a0, a0, 3\naddi a1, a1, -1\nbnez a1, -8\nnop"
  let count := 200000
  let a0 : Bap.Var := ⟨"X10", .imm 64, 0, false⟩
  let emu ← Tuned.riscv64 code 0 0
  Bap.Emu.setReg emu a0 (.bits (BitVec.ofNat 64 0))
  Bap.Emu.setReg emu ⟨"X11", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 count))
  let _ ← Bap.Emu.runUntil emu 12 (fuel := 3 * count + 100)
  assertBits "A loop comes to the same when compiled again" (BitVec.ofNat 64 (3 * count)) (.ok (← Bap.Emu.reg emu a0))
  let stats ← Primus.Lifted.stats emu.engine
  assertTrue s!"A loop that runs a lot is compiled again ({stats.optimized})" (stats.optimized ≥ 1)

/-- Floating point of ARMv8, as qemu has it: VRINT under each of the rounding modes, and what else there is on its edges. -/
def testArmV8 (name : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/arm-linux-musl-{name}"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux ARM {name} ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux ARM {name} is what qemu does" (String.fromUTF8! (← IO.FS.readBinFile s!"testsuite/data/arm-{name}.out"))
    (String.fromUTF8! (← written.get))

/-- What sockets hold goes into a checkpoint and comes back: a listener with a connection to accept, and a pair with bytes, a name and
an open file on the way. -/
def testSocketImage : IO Unit := do
  let kernel := (Bap.Linux.Kernel.empty.addDirectories "/run").withConsole 1
  let (kernel, listener) := kernel.socket 1 1 0
  let some kernel := (kernel.bind 1 listener "/" "/run/listen.sock" fun _ => false).toOption | throw <| IO.userError "bind"
  let some kernel := (kernel.listen 1 listener).toOption | throw <| IO.userError "listen"
  let (kernel, client) := kernel.socket 1 1 0
  let some target := (kernel.socketNamed "/" "/run/listen.sock").toOption | throw <| IO.userError "named"
  let some kernel := (kernel.connect 1 client target fun _ => true).toOption | throw <| IO.userError "connect"
  let (kernel, one, _) := kernel.socketPair 1 5 0
  let some (kernel, _) := (kernel.send 1 one { data := "packet".toUTF8, rights := [0] } none fun _ => true).toOption
    | throw <| IO.userError "send"
  let encoded := Bap.Linux.Image.encode ByteArray.empty kernel.image
  let some (image, _) := (Bap.Linux.Image.decode encoded 0).toOption | throw <| IO.userError "decode"
  let some back := image.kernel.toOption | throw <| IO.userError "kernel"
  let sockets (kernel : Bap.Linux.Kernel) : List (Nat × ByteArray) :=
    ((kernel.inodes.toList.filterMap fun (number, _) => (kernel.socketAt number).map fun socket => (number, Bap.Linux.socketBytes socket)).toArray.qsort
      (fun left right => left.1 < right.1)).toList
  assertEqual "sockets of a checkpoint are those that there were" ((sockets kernel).map (·.1)) ((sockets back).map (·.1))
  assertTrue "and hold what they held" ((sockets kernel).map (·.2) == (sockets back).map (·.2))
  -- The listener, the client, the end of its connection that waits to be accepted, and the pair.
  assertEqual "five of them" 5 (sockets back).length
  assertEqual "the listener is at its path" (some target) (back.paths.get? "/run/listen.sock")

/-- A fault that a program ignores ends it, as Linux has it, or goes on past it when asked; and a handler that can't be entered is told
apart from a fault that nothing handles. -/
def testSignalFailures (triple : String) : IO Unit := do
  let label := s!"Signals {triple}"
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-fault"
  let runWith (mode : String) (skip : Bool) : IO (Bap.Tasks.ScheduleOutcome × String × List Bap.Linux.SignalFailure) := do
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test", mode]
    machine.setSkipIgnoredFaults skip
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => written.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← written.get), ← machine.signalFailures)
  let (outcome, _, failures) ← runWith "ignore" false
  assertEqual s!"{label} an ignored fault ends the process, as Linux has it" (Bap.Tasks.ScheduleOutcome.finished 11) outcome
  assertTrue s!"{label} as a fault that nothing handles: {repr failures}"
    (failures.any fun | .unhandled _ _ 16 "SIGSEGV is ignored" => true | _ => false)
  let (outcome, text, failures) ← runWith "ignore" true
  assertEqual s!"{label} or goes on past it when asked" (Bap.Tasks.ScheduleOutcome.finished 0, "went on\n") (outcome, text)
  assertTrue s!"{label} which is said" (failures.any fun | .skipped _ _ 16 => true | _ => false)
  let (outcome, _, failures) ← runWith "nostack" false
  assertEqual s!"{label} a handler with no stack ends the process" (Bap.Tasks.ScheduleOutcome.finished 11) outcome
  assertTrue s!"{label} as a handler that couldn't be entered, and not as a fault that nothing handles: {repr failures}"
    ((failures.any fun | .handlerEntry _ 11 _ => true | _ => false) && !(failures.any fun | .unhandled .. => true | _ => false))

/-- A routine that the host does instead, once it is found to do the same: SHA-512 checked against the program's own and put in place,
not checked again for the same code, and one that does something else refused. -/
def testAcceleration (triple : String) : IO Unit := do
  let label := s!"Acceleration {triple}"
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-sha"
  let image ← IO.ofExcept (Bap.Image.Elf.decode program)
  let symbol (name : String) : IO Bap.Image.Symbol := do
    match image.symbols.find? (·.name == name) with
    | some found => pure found
    | none => throw <| IO.userError s!"{label} has no {name}"
  let routine ← symbol "sha512"
  let broken ← symbol "broken_sha512"
  let expected := String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/libc-sha.out")
  let calls ← IO.mkRef 0
  let base := Bap.Linux.Accelerate.sha512
  let counted : Bap.Linux.Accelerate.Accelerator := { base with host := fun machine arguments => do
    calls.modify (· + 1)
    base.host machine arguments }
  let start : IO Bap.Linux.Machine := Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let runOn (machine : Bap.Linux.Machine) : IO String := do
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run (fuel := 2000000000) fun data => written.modify (· ++ data)
    assertEqual s!"{label} it ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    pure (String.fromUTF8! (← written.get))
  let refusing ← start
  match ← refusing.accelerate counted broken.addr broken.size with
  | .rejected _ why => assertTrue s!"{label} what does something else is refused: {why}" true
  | other => throw <| IO.userError s!"{label} accepted what does something else: {repr other}"
  let first ← start
  let outcome ← first.accelerate counted routine.addr routine.size
  assertTrue s!"{label} what does the same is checked and put in place: {repr outcome}" (outcome matches .validated _)
  calls.set 0
  assertEqual s!"{label} and the program does what it did" expected (← runOn first)
  assertEqual s!"{label} by the host each time" 20 (← calls.get)
  let second ← start
  let outcome ← second.accelerate counted routine.addr routine.size
  assertTrue s!"{label} the same code isn't checked again: {repr outcome}" (outcome matches .reused _)
  assertEqual s!"{label} and it does what it did there too" expected (← runOn second)
  assertTrue s!"{label} what was checked can be carried on"
    ((← Bap.Linux.Accelerate.trusted).any fun (name, _) => name == "sha512")

/-- What operations raise, on what their edges are, as qemu has it. -/
def testLinuxRaises (name : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{name}"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {name} ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {name} is what qemu does" (String.fromUTF8! (← IO.FS.readBinFile s!"testsuite/data/{name}.out"))
    (String.fromUTF8! (← written.get))

/-- A range from the middle: a loop of three blocks that goes on as a loop of the last two, whose first gets hot in a range that
it is in already. It comes to what it does without, and it is what happens. -/
def testRangeEntries : IO Unit := do
  let code ← LLVM.assemble "riscv64"
    "addi a2, a2, 1\nj 4\naddi a0, a0, 1\naddi a2, a2, 2\nj 4\naddi a1, a1, -1\nbeqz a1, 8\njr t0\nnop"
  let register (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let run (entries : Bool) : IO (Nat × Nat × Nat) := do
    let emu ← Bap.Emu.riscv64 code 0 0
      (adjust := fun config => { config with hotThreshold := 2, cacheLimit := 256, rangeLimit := 8, rangeEntries := entries })
    for (name, value) in [("X10", 0), ("X11", 2000), ("X12", 0), ("X5", 0)] do
      Bap.Emu.setReg emu (register name) (.bits (BitVec.ofNat 64 value))
    let value (name : String) : IO Nat := do
      match ← Bap.Emu.reg emu (register name) with
      | .bits bits => pure bits.toNat
      | _ => pure 0
    -- Not by steps: a step may enter no other block, and has no use for a range. Eight times round, of eight instructions, which is
    -- enough for the loop to have a range. It is at the top, and from the next time round it goes back to the second block.
    let _ ← Bap.Emu.run emu 64
    assertEqual "A loop has been round eight times" 0 (← Bap.Emu.pc emu)
    Bap.Emu.setReg emu (register "X5") (.bits (BitVec.ofNat 64 8))
    -- Almost to where it ends, which is past the code if it runs over: six instructions each time round, and it has more to come.
    let _ ← Bap.Emu.run emu (6 * ((← value "X11") - 2))
    let _ ← Bap.Emu.runUntil emu 32 (fuel := 100)
    let stats ← Primus.Lifted.stats emu.engine
    pure (← value "X10", ← value "X12", stats.entriesReused)
  let (plainFirst, plainSecond, plainReused) ← run false
  let (first, second, reused) ← run true
  assertEqual "A range is run from its middle only if asked" 0 plainReused
  assertTrue s!"A range is run from its middle ({reused})" (reused ≥ 1)
  assertEqual "A range from its middle comes to the same" (plainFirst, plainSecond) (first, second)
  assertTrue s!"A loop that ran ends with what it counted ({first})" (first > 1000)

/-- What changes what was compiled without changing its bytes, hooks that come to a thread where it stopped, and a profile of what ran. -/
def testCodeControl : IO Unit := do
  let code ← LLVM.assemble "riscv64" "addi a0, a0, 1\naddi a1, a1, -1\nbnez a1, -8\nnop\nnop"
  let emu ← Bap.Emu.riscv64 code 0 0 (adjust := fun config => { config with hotThreshold := 2, rangeLimit := 8 })
  let register (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let set (name : String) (value : Nat) : IO Unit := Bap.Emu.setReg emu (register name) (.bits (BitVec.ofNat 64 value))
  let value (name : String) : IO Nat := do
    match ← Bap.Emu.reg emu (register name) with
    | .bits bits => pure bits.toNat
    | _ => pure 0
  -- A hundred times round, of three instructions.
  let loop : IO Unit := do
    set "X10" 0
    set "X11" 100
    Bap.Emu.setPc emu 0
    let _ ← Bap.Emu.run emu 300
  Bap.Emu.startProfile emu
  loop
  let profile ← Bap.Emu.profile emu
  Bap.Emu.stopProfile emu
  assertEqual "A loop counts" (100, 12) (← value "X10", ← Bap.Emu.pc emu)
  assertEqual "A profile has all that ran" 300 (profile.foldl (fun total entry => total + entry.2.instructions) 0)
  assertTrue "of which some was compiled" (profile.any (·.2.nativeRuns > 0))
  assertTrue "and some wasn't, before it was" (profile.any (·.2.interpretedRuns > 0))
  assertTrue "and it took some time" (profile.any (·.2.nativeNanos > 0))
  -- What a write would drop comes back as it was, for the same bytes; what is invalidated is made again.
  let stats := Primus.Lifted.stats emu.engine
  Primus.Lifted.discardRange emu.engine 0 11
  let before ← stats
  loop
  assertTrue "What is discarded comes back as it was" ((← stats).versionHits > before.versionHits)
  Bap.Emu.invalidateCode emu 0 11
  let before ← stats
  loop
  let after ← stats
  assertEqual "What is invalidated doesn't" before.versionHits after.versionHits
  assertTrue "it is compiled again" (after.nativeCompilations > before.nativeCompilations)
  assertEqual "and does what it did" 100 (← value "X10")
  -- A thread that stopped where a hook comes afterwards: the hook fires when it goes on, and what stopped it doesn't again.
  set "X11" 100
  Bap.Emu.setPc emu 0
  let breakpoint ← Bap.Emu.addBreakpoint emu 4
  let _ ← Bap.Emu.run emu 10
  assertEqual "A breakpoint stops it" 4 (← Bap.Emu.pc emu)
  let fired ← IO.mkRef 0
  let hook ← Bap.Emu.onCode emu (4, 4) fun _ _ => fired.modify (· + 1)
  let another ← Bap.Emu.addBreakpoint emu 4
  Bap.Emu.resumeThread emu (← Bap.Emu.thread emu)
  let _ ← Bap.Emu.run emu 1
  assertEqual "A hook that came after it stopped fires when it goes on" 1 (← fired.get)
  assertEqual "and a breakpoint that came then stops it when it comes back" 8 (← Bap.Emu.pc emu)
  for id in [hook, another] do Bap.Emu.removeHook emu id
  -- And where it stopped, put back.
  set "X11" 100
  Bap.Emu.setPc emu 0
  let _ ← Bap.Emu.run emu 10
  let saved ← Bap.Emu.snapshot emu
  Bap.Emu.resumeThread emu (← Bap.Emu.thread emu)
  let _ ← Bap.Emu.run emu 5
  Bap.Emu.restore emu saved
  fired.set 0
  let _ ← Bap.Emu.onCode emu (4, 4) fun _ _ => fired.modify (· + 1)
  Bap.Emu.resumeThread emu (← Bap.Emu.thread emu)
  let _ ← Bap.Emu.run emu 1
  assertEqual "A hook that came after it was put back fires when it goes on" (1, 8) (← fired.get, ← Bap.Emu.pc emu)
  Bap.Emu.removeHook emu breakpoint

/-- What the rounding modes of a machine do, as qemu has it. -/
def testLinuxRound (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-round"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} a program that rounds ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} rounding is what qemu does" (String.fromUTF8! (← IO.FS.readBinFile s!"testsuite/data/{triple}-libc-round.out"))
    (String.fromUTF8! (← written.get))

/-- What a program finds in `/proc`, of itself and its child, and a file that a function makes, across a checkpoint. -/
def testLinuxProc (triple : String) : IO Unit := do
  let path := s!"testsuite/bin/{triple}-linux-musl-libc-proc"
  let custom : Bap.Linux.Generator := fun view => s!"made for {view.machine}\n".toUTF8
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)).addGenerated "/custom" custom
  let runOn (machine : Bap.Linux.Machine) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => written.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← written.get))
  let machineName := if triple == "mips" then "mips" else triple
  let expected (customLine : String) :=
    "cmdline 11 /test arg1\nexe /test\nmaps stack 1 exec 1\nstatus name test same 1\ncomm by pid test\nself is pid 1\nfd link /made\nfds 1\n" ++
    "cpuinfo size 0 read 1\nostype Linux\n" ++ customLine ++ "write refused 1\nchild seen 1\nchild 7 gone 1\n"
  let made := s!"made for {machineName}\n"
  let (outcome, text) ← runOn (← Bap.Linux.start kernel "/test" ["/test", "arg1"])
  assertEqual s!"Linux {triple} /proc says what a process is" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 4), expected s!"custom {made.utf8ByteSize} {made}") (outcome, text)
  -- A checkpoint has the name of what makes it, and goes on with the function that it is given again.
  let first ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
  let _ ← first.run (fuel := 1) fun _ => pure ()
  let data ← first.checkpoint
  let (_, again) ← runOn (← Bap.Linux.Machine.ofCheckpoint data (generators := [("/custom", custom)]))
  assertEqual s!"Linux {triple} a generated file goes on from a checkpoint" text again
  let (_, without) ← runOn (← Bap.Linux.Machine.ofCheckpoint data)
  assertTrue s!"Linux {triple} a generated file without what makes it fails to open: {without}" ((without.splitOn "custom -1").length > 1)
  -- What is put in over a file of /proc is what a program gets.
  let (_, mine) ← runOn (← Bap.Linux.start (kernel.addGenerated "/proc/sys/kernel/ostype" fun _ => "Mine\n".toUTF8) "/test" ["/test", "arg1"])
  assertTrue s!"Linux {triple} /proc can be replaced: {mine}" ((mine.splitOn "ostype Mine").length > 1)

/-- What a machine is given sees each system call before the kernel: it may answer one, with a result or an error on any architecture,
or hand it on. `getcwd` is the number that it answers. -/
def testLinuxSyscallHandler (triple : String) (getcwd : Nat) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-files")
  let seen ← IO.mkRef 0
  let handler : Bap.Linux.SyscallHandler := fun emu number _ => do
    seen.modify (· + 1)
    if number == getcwd then Bap.Emu.syscallReturn emu (.error 13) else pure .default
  let start := Bap.Linux.start kernel "/test" ["/test", "arg1"] (handler := some handler)
  let runOn (machine : Bap.Linux.Machine) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let console ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => console.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← console.get))
  let expected := "args 2 arg1\ncwd ?\nread hello 42\nsize 9 dir 0\nseek yz\ndup x\nlink c\nentries 3\ngone -1\ntime 1\nmalloc 1\nnope 1\n"
  assertEqual s!"Linux {triple} a handler goes before the kernel" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 5), expected) (← runOn (← start))
  assertTrue s!"Linux {triple} a handler sees the others too" ((← seen.get) > 10)
  -- After a checkpoint it is given again.
  let first ← start
  let _ ← first.run (fuel := 1) fun _ => pure ()
  assertEqual s!"Linux {triple} a handler goes on from a checkpoint" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 5), expected)
    (← runOn (← Bap.Linux.Machine.ofCheckpoint (← first.checkpoint) (handler := some handler)))

/-- Code that a program changes under itself once it is hot, as the machine that made this test does it. -/
def testLinuxSelfModifying : IO Unit := do
  let path := "testsuite/bin/x86_64-linux-musl-selfmodify"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual "Linux nothing of code that was changed stays" (Bap.Tasks.ScheduleOutcome.finished 0, "65650259506356\n65650259506398\n")
    (outcome, String.fromUTF8! (← written.get))

/-- Calls between ARM and Thumb, whichever a program starts in, and the helpers of the kernel, as qemu has them. -/
def testLinuxInterworking (triple : String) : IO Unit := do
  let path := s!"testsuite/bin/{triple}-linux-musl-interworking"
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)) "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} goes between ARM and Thumb" (Bap.Tasks.ScheduleOutcome.finished 0, "104 214 110\ntls 1\ncas 0 9\ncas 1 9\nversion 1\n")
    (outcome, String.fromUTF8! (← written.get))

/-- A wide instruction of an IT block that says that it sets the flags does, which a narrow one there doesn't. -/
private def testThumbItFlags : IO Unit := do
  -- cmp r0, #1; it ne; orrsne.w r3, r1, r2
  let code := ByteArray.mk #[0x01, 0x28, 0x18, 0xbf, 0x51, 0xea, 0x02, 0x03, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let emu ← Bap.Emu.arm32 code 0 0 (thumb := true)
  let word (name : String) : Bap.Var := ⟨name, .imm 32, 0, false⟩
  let flag (name : String) : Bap.Var := ⟨name, .imm 1, 0, false⟩
  for name in ["R0", "R1", "R2", "R3"] do Bap.Emu.setReg emu (word name) (.bits (BitVec.ofNat 32 0))
  for name in ["NF", "ZF", "CF", "VF"] do Bap.Emu.setReg emu (flag name) (.bits (BitVec.ofNat 1 0))
  let _ ← Bap.Emu.step emu
  let _ ← Bap.Emu.step emu
  assertBits "Emu orrs.w in an IT block sets Z" (BitVec.ofNat 1 1) (.ok (← Bap.Emu.reg emu (flag "ZF")))

/-- A machine stopped anywhere and saved goes on from the bytes alone, in a new machine, to the same end. -/
def testLinuxCheckpoints (triple : String) (cuts : List Nat := [12000]) : IO Unit := do
  let start (name : String) : IO Bap.Linux.Machine := do
    let path := s!"testsuite/bin/{triple}-linux-musl-{name}"
    Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile path)) "/test" ["/test", "arg1"]
  let runOn (machine : Bap.Linux.Machine) (fuel : Nat) : IO (Bap.Tasks.ScheduleOutcome × ByteArray) := do
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run (fuel := fuel) fun data => written.modify (· ++ data)
    pure (outcome, ← written.get)
  for name in ["libc-files", "libc-threads", "libc-fork"] do
    let (wholeOutcome, wholeText) ← runOn (← start name) 1000000000
    -- These end at some tens of thousands of instructions.
    let mut stops := 0
    for cut in cuts do
      let first ← start name
      let (outcome, before) ← runOn first cut
      if outcome == .outOfFuel then
        stops := stops + 1
        let data ← first.checkpoint
        let second ← Bap.Linux.Machine.ofCheckpoint data
        -- The file of the same state is the same file, so that nothing was lost or made up on the way.
        assertEqual s!"Linux {triple} {name} at {cut} saves again as it was" (data == (← second.checkpoint)) true
        let (outcome, after) ← runOn second 1000000000
        assertEqual s!"Linux {triple} {name} ends from {cut} as it would have" wholeOutcome outcome
        assertEqual s!"Linux {triple} {name} says from {cut} what it would have" wholeText.toList (before ++ after).toList
        -- What saves is still as it was, and goes on to the same end.
        let (outcome, after) ← runOn first 1000000000
        assertEqual s!"Linux {triple} {name} saving at {cut} changes nothing" (wholeOutcome, wholeText.toList) (outcome, (before ++ after).toList)
    assertTrue s!"Linux {triple} {name} was stopped at {stops} places" (stops == cuts.length)
    -- Going back in the same machine, past what it did to its files, its tasks and its memory.
    let machine ← start name
    let (_, before) ← runOn machine 12000
    let saved ← machine.save
    let (outcome, after) ← runOn machine 1000000000
    machine.restore saved
    let (again, afterAgain) ← runOn machine 1000000000
    assertEqual s!"Linux {triple} {name} goes back and does it again" (outcome, after.toList) (again, afterAgain.toList)
    assertEqual s!"Linux {triple} {name} from going back says what it would have" wholeText.toList (before ++ afterAgain).toList
  expectThrow s!"Linux what isn't a checkpoint is refused" (Bap.Linux.Machine.ofCheckpoint "BAPLINUX".toUTF8)
  expectThrow s!"Linux what isn't a checkpoint is refused" (Bap.Linux.Machine.ofCheckpoint "not one".toUTF8)

/-- What a run does to the last instruction: where each instruction was, in the order that they ran over all the threads, the system
calls, what it says, how it ends and the bytes of all that is left at the end. -/
private structure RunTrace where
  outcome : Bap.Tasks.ScheduleOutcome
  pcs : List Nat
  syscalls : List (Nat × List Nat)
  written : ByteArray
  final : ByteArray

/-- Runs a machine in pieces of `cuts`, and after each one goes on in a new machine from the bytes of a checkpoint. `.none` runs it whole. -/
private def tracedRun (start : (Nat → List Nat → IO Unit) → IO Bap.Linux.Machine)
    (resume : (Nat → List Nat → IO Unit) → ByteArray → IO Bap.Linux.Machine)
    (quantum : Nat) (cuts : Nat → Option Nat) : IO RunTrace := do
  let pcs ← IO.mkRef ([] : List (List Nat))
  let syscalls ← IO.mkRef ([] : List (Nat × List Nat))
  let written ← IO.mkRef ByteArray.empty
  let watch : Nat → List Nat → IO Unit := fun number args => syscalls.modify ((number, args) :: ·)
  let rec go : Nat → Nat → Bap.Linux.Machine → IO RunTrace
    | 0, _, _ => throw <| IO.userError "more pieces than a run should have"
    | fuel + 1, index, machine => do
      Bap.Emu.traceStartCapacity machine.emu 100000000
      let outcome ← machine.run (quantum := quantum) (fuel := (cuts index).getD 1000000000) fun data => written.modify (· ++ data)
      pcs.modify ((← Bap.Emu.traceStop machine.emu) :: ·)
      if outcome == .outOfFuel then
        go fuel (index + 1) (← resume watch (← machine.checkpoint))
      else
        pure { outcome, pcs := (← pcs.get).reverse.flatten, syscalls := (← syscalls.get).reverse, written := ← written.get, final := ← machine.checkpoint }
  go 2000 0 (← start watch)

/-- Going on from a checkpoint is the same run: the same instructions in the same order over all the threads, wherever it stops, however
often, in the middle of a turn, at its end or the first instruction of the run, to the same bytes at the end. -/
def testLinuxResumeTraces (triple : String) (quanta : List Nat := [100, 7])
    (names : List String := ["libc-threads", "libc-fork", "libc-files"]) : IO Unit := do
  for name in names do
    let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
    let kernel := Bap.Linux.Kernel.empty.addFile "/test" program
    let start (watch : Nat → List Nat → IO Unit) := Bap.Linux.start kernel "/test" ["/test", "arg1"] (watch := some watch)
    let resume (watch : Nat → List Nat → IO Unit) (data : ByteArray) := Bap.Linux.Machine.ofCheckpoint data (watch := some watch)
    for quantum in quanta do
      let whole ← tracedRun start resume quantum fun _ => none
      assertTrue s!"Linux {triple} {name} the whole run has a trace" (whole.pcs.length > 1000)
      -- A single stop, at places in a turn, and stops every so often: at the end of each turn, between turns and in the middle of them.
      let stops : List (String × (Nat → Option Nat)) :=
        [("first", fun index => if index == 0 then some 1 else none),
         ("mid-turn", fun index => if index == 0 then some (quantum / 2 + 1 + 3 * quantum) else none),
         ("turn-end", fun index => if index == 0 then some (5 * quantum) else none),
         ("every-turn-end", fun _ => some (whole.pcs.length / 6 / quantum * quantum + quantum)),
         ("every-odd", fun _ => some ((whole.pcs.length / 5) ||| 1))]
      for (label, cuts) in stops do
        let pieces ← tracedRun start resume quantum cuts
        let label := s!"Linux {triple} {name} quantum {quantum} stopped {label}"
        assertEqual s!"{label} ends as it would have" whole.outcome pieces.outcome
        let firstDifference := (whole.pcs.zip pieces.pcs).findIdx? fun (left, right) => left != right
        assertEqual s!"{label} runs the same instructions" (whole.pcs.length, none) (pieces.pcs.length, firstDifference)
        assertEqual s!"{label} makes the same system calls" whole.syscalls pieces.syscalls
        assertEqual s!"{label} says the same" whole.written.toList pieces.written.toList
        assertTrue s!"{label} ends in the same state" (whole.final == pieces.final)

/-- A model of a runtime: it counts the system calls, and what a guest gets depends on the count. -/
private def countingModel (getcwd threshold : Nat) (seen : IO.Ref Nat) (version : Nat := 1) (id : String := "counter") : Bap.Linux.RuntimeModel where
  id := id
  version := version
  attach := fun machine => do
    let count ← IO.mkRef 0
    let _ ← Bap.Emu.onSyscall machine.emu fun emu number _ => do
      count.modify (· + 1)
      seen.set (← count.get)
      if number == getcwd && (← count.get) ≥ threshold then Bap.Emu.syscallReturn emu (.error 13) else pure .default
    pure {
      save := do pure (Bap.Linux.Wire.putNat ByteArray.empty (← count.get))
      load := fun data => do
        let (value, at_) ← IO.ofExcept (Bap.Linux.Wire.getNat data 0)
        IO.ofExcept (Bap.Linux.Wire.expectEnd data at_)
        count.set value
    }

/-- What a runtime model holds goes with the machine, its callbacks come back under its name, and a checkpoint that can't go on as it
would have is refused and not run. -/
def testLinuxRuntimeModels (triple : String) (getcwd : Nat) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-files"
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" program
  let seen ← IO.mkRef 0
  let runOn (machine : Bap.Linux.Machine) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let console ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => console.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← console.get))
  let start (model : Bap.Linux.RuntimeModel) := Bap.Linux.start kernel "/test" ["/test", "arg1"] (models := [model])
  -- At what count it comes to `getcwd`, which is what the threshold has to be to tell a count that is kept from one that started again.
  let calls ← IO.mkRef 0
  let counter : Bap.Linux.RuntimeModel := { id := "calls", attach := fun machine => do
    let _ ← Bap.Emu.onSyscall machine.emu fun _ number _ => do
      unless (← calls.get) >= 1000000 do
        calls.modify (· + 1)
        if number == getcwd then calls.modify (· + 1000000)
      pure .default
    pure { save := pure ByteArray.empty, load := fun _ => pure () } }
  let _ ← runOn (← start counter)
  let threshold := (← calls.get) - 1000000
  let model := countingModel getcwd threshold seen
  let (wholeOutcome, wholeText) ← runOn (← start model)
  assertTrue s!"Linux {triple} a model changes what a guest sees: {wholeText}" ((wholeText.splitOn "cwd ?").length > 1)
  let whole ← seen.get
  -- Stops once it has made some of its calls and before it comes to that one.
  let first ← start model
  let _ ← first.run (fuel := 2000) fun _ => pure ()
  assertTrue s!"Linux {triple} a model stops before it matters" ((← seen.get) < threshold && (← seen.get) > 0)
  let before := String.fromUTF8! (← first.kernel.get).output
  let data ← first.checkpoint
  let (outcome, after) ← runOn (← Bap.Linux.Machine.ofCheckpoint data (models := [model]))
  assertEqual s!"Linux {triple} a model goes on from a checkpoint" (wholeOutcome, wholeText) (outcome, before ++ after)
  assertEqual s!"Linux {triple} a model's count goes on" whole (← seen.get)
  let again ← Bap.Linux.Machine.ofCheckpoint data (models := [model])
  assertTrue s!"Linux {triple} a model saves again as it was" (data == (← again.checkpoint))
  -- Going back in the same machine takes the model back too.
  let machine ← start model
  let _ ← machine.run (fuel := 2000) fun _ => pure ()
  let saved ← machine.save
  let (once, onceText) ← runOn machine
  machine.restore saved
  assertEqual s!"Linux {triple} a model goes back with the machine" (once, onceText) (← runOn machine)
  -- What can't go on as it would have.
  expectThrow s!"Linux {triple} a checkpoint without its model is refused" (Bap.Linux.Machine.ofCheckpoint data)
  expectThrow s!"Linux {triple} a checkpoint with another version of a model is refused"
    (Bap.Linux.Machine.ofCheckpoint data (models := [countingModel getcwd threshold seen (version := 2)]))
  expectThrow s!"Linux {triple} a model that a checkpoint has nothing of is refused"
    (Bap.Linux.Machine.ofCheckpoint data (models := [model, countingModel getcwd threshold seen (id := "other")]))
  expectThrow s!"Linux {triple} two models of a name are refused" (Bap.Linux.start kernel "/test" ["/test"] (models := [model, model]))
  let tampered := data.set! (data.size / 2) (data[data.size / 2]! + 1)
  expectThrow s!"Linux {triple} a damaged checkpoint is refused" (Bap.Linux.Machine.ofCheckpoint tampered (models := [model]))
  expectThrow s!"Linux {triple} a cut checkpoint is refused" (Bap.Linux.Machine.ofCheckpoint (data.extract 0 (data.size - 1)) (models := [model]))
  let target := Bap.Linux.targetDigest first.architecture program
  assertEqual s!"Linux {triple} a checkpoint says what it is of" target first.target
  let _ ← Bap.Linux.Machine.ofCheckpoint data (models := [model]) (expectedTarget := some target)
  expectThrow s!"Linux {triple} a checkpoint of another program is refused"
    (Bap.Linux.Machine.ofCheckpoint data (models := [model]) (expectedTarget := some (target + 1)))
  -- A handler has no name to come back by, but that there was one is known.
  let handler : Bap.Linux.SyscallHandler := fun _ _ _ => pure .default
  let handled ← Bap.Linux.start kernel "/test" ["/test"] (handler := some handler)
  expectThrow s!"Linux {triple} a checkpoint without its handler is refused" (do Bap.Linux.Machine.ofCheckpoint (← handled.checkpoint))
  -- The same state makes the same bytes, as many processes as it has.
  let twice (name : String) : IO ByteArray := do
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}")) "/test" ["/test"]
    let _ ← machine.run (fuel := 15000) fun _ => pure ()
    machine.checkpoint
  for name in ["libc-fork", "libc-threads"] do
    assertTrue s!"Linux {triple} {name} the same run makes the same file" ((← twice name) == (← twice name))
  -- A file that was there stays until the whole of the new one is.
  let path := s!"native/build/emu-atomic-{triple}.bin"
  first.saveFile path
  assertTrue s!"Linux {triple} saving leaves nothing behind" !(← System.FilePath.pathExists (path ++ ".partial"))
  let _ ← Bap.Linux.Machine.loadFile path (models := [model])
  -- Where it stops of its own goes with it.
  let stopping ← start model
  let entry ← Bap.Emu.pc stopping.emu
  let _ ← Bap.Emu.addBreakpoint stopping.emu (entry + 0x100000)
  let reloaded ← Bap.Linux.Machine.ofCheckpoint (← stopping.checkpoint) (models := [model])
  assertEqual s!"Linux {triple} breakpoints go on from a checkpoint" [entry + 0x100000] (← Bap.Emu.breakpoints reloaded.emu)
  IO.FS.removeFile path

/-- A system call that a model is serving: there isn't a checkpoint in the middle of its instruction. A model stops the thread, and
there is one when the run returns, which goes on to what the run would have done. -/
def testLinuxServedCheckpoint (triple : String) (getcwd : Nat) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-files")
  let inside ← IO.mkRef (none : Option (Except IO.Error ByteArray))
  let insideSave ← IO.mkRef (none : Option Bool)
  let machine ← IO.mkRef (none : Option Bap.Linux.Machine)
  let model : Bap.Linux.RuntimeModel := { id := "stopper", attach := fun attached => do
    let _ ← Bap.Emu.onSyscall attached.emu fun emu number _ => do
      if number == getcwd then
        if let some machine := ← machine.get then
          inside.set (some (← machine.checkpoint.toBaseIO))
          insideSave.set (some (match ← machine.save.toBaseIO with | .ok _ => true | .error _ => false))
        Bap.Emu.stopThread emu (← Bap.Emu.thread emu)
      pure .default
    pure { save := pure ByteArray.empty, load := fun _ => pure () } }
  let runOn (machine : Bap.Linux.Machine) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let console ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => console.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← console.get))
  let plain ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
  let (wholeOutcome, wholeText) ← runOn plain
  let first ← Bap.Linux.start kernel "/test" ["/test", "arg1"] (models := [model])
  machine.set (some first)
  let (_, before) ← runOn first
  match ← inside.get with
  | some (.error _) => pure ()
  | _ => throw <| IO.userError s!"Linux {triple} a checkpoint in the middle of a system call should be refused"
  match ← insideSave.get with
  | some false => pure ()
  | _ => throw <| IO.userError s!"Linux {triple} a save in the middle of a system call should be refused"
  machine.set none
  -- It goes on past the call, with the result that the kernel gave.
  let second ← Bap.Linux.Machine.ofCheckpoint (← first.checkpoint) (models := [{ model with attach := fun _ => pure { save := pure ByteArray.empty, load := fun _ => pure () } }])
  Bap.Emu.resumeThread second.emu (← Bap.Emu.thread second.emu)
  let (outcome, after) ← runOn second
  assertEqual s!"Linux {triple} a call that stopped goes on as it would have" (wholeOutcome, wholeText) (outcome, before ++ after)

/-- What is atomic on a machine is atomic in a parallel round, against each other and against plain stores: each thread adds 1 many
times to one counter, and nothing is lost. -/
def testParallelAtomics : IO Unit := do
  let trialWide (label : String) (make : IO Bap.Emu.Emu) (register : Nat → Bap.Var) (width threads count : Nat) (endian : Endian) : IO Unit := do
    let emu ← make
    Bap.Emu.map emu ⟨0x10000, ByteArray.mk (Array.replicate 16 0), ⟨true, true, false⟩⟩
    let word (value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)
    let setup (write : Bap.Var → Bap.Value → IO Unit) : IO Unit := do
      write (register 0) (word 0x10000)
      write (register 1) (word count)
      write (register 2) (word 1)
    setup (Bap.Emu.setReg emu)
    for _ in [1:threads] do
      let id ← Bap.Emu.spawnThread emu 0 0
      setup (Bap.Emu.setThreadReg emu id)
    let counted : IO Nat := do
      let bytes ← Bap.Emu.read emu 0x10000 4
      pure ((List.range 4).foldl (init := 0) fun value index =>
        value + bytes[index]!.toNat * 256 ^ (if endian == .big then 3 - index else index))
    -- Until each has counted to its end, and a while past that, to show that nothing more comes of it.
    let mut rounds := 0
    while rounds < 20000 && (← counted) < threads * count do
      let _ ← Bap.Emu.runPreemptiveParallel emu 500
      rounds := rounds + 1
    for _ in [0:20] do
      let _ ← Bap.Emu.runPreemptiveParallel emu 500
    let value ← counted
    assertEqual s!"{label} loses nothing" (threads * count) value
  let trial (label : String) (make : IO Bap.Emu.Emu) (register : Nat → Bap.Var) (threads count : Nat) : IO Unit :=
    trialWide label make register 64 threads count .little
  let riscv (source : String) : IO Bap.Emu.Emu := do Bap.Emu.riscv64 (← LLVM.assemble "riscv64" source) 0 0
  -- a0 is where, a2 how many, a3 by how much.
  let riscvRegister (index : Nat) : Bap.Var := ⟨s!"X{[10, 12, 13][index]!}", .imm 64, 0, false⟩
  trial "Parallel lr and sc" (riscv "lr.w t1, (a0)\naddi t1, t1, 1\nsc.w t2, t1, (a0)\nbnez t2, -12\naddi a2, a2, -1\nbnez a2, -20\nj 0")
    riscvRegister 4 1000
  trial "Parallel amoadd" (riscv "amoadd.w zero, a3, (a0)\naddi a2, a2, -1\nbnez a2, -8\nj 0") riscvRegister 4 1000
  -- A lock that is taken by a swap and let go by a plain store, around what isn't atomic: a store that a swap went over would never end.
  trial "Parallel lock of a swap and a store"
    (riscv "addi t4, a0, 8\namoswap.w t3, a3, (t4)\nbnez t3, -4\nlw t1, (a0)\naddi t1, t1, 1\nsw t1, (a0)\nsw zero, (t4)\naddi a2, a2, -1\nbnez a2, -28\nj 0")
    riscvRegister 4 300
  let aarch64 (source : String) : IO Bap.Emu.Emu := do Bap.Emu.aarch64 (← LLVM.assemble "aarch64" source) 0 0
  let armRegister (index : Nat) : Bap.Var := ⟨s!"X{[0, 3, 4][index]!}", .imm 64, 0, false⟩
  trial "Parallel ldxr and stxr"
    (aarch64 "ldxr w1, [x0]\nadd w1, w1, #1\nstxr w2, w1, [x0]\ncbnz w2, #-12\nsub x3, x3, #1\ncbnz x3, #-20\nb #0") armRegister 4 1000
  trial "Parallel ldadd" (aarch64 "ldadd w4, wzr, [x0]\nsub x3, x3, #1\ncbnz x3, #-8\nb #0") armRegister 4 1000
  -- The others that have a monitor or instructions that are atomic.
  let mips (source : String) : IO Bap.Emu.Emu := do Bap.Emu.mips32 (← LLVM.assemble "mips" source) 0 0
  let mipsRegister (index : Nat) : Bap.Var := ⟨s!"R{[4, 5, 6][index]!}", .imm 32, 0, false⟩
  trialWide "Parallel ll and sc" (mips "ll $8, 0($4)\naddiu $8, $8, 1\nsc $8, 0($4)\nbeqz $8, -16\nnop\naddiu $5, $5, -1\nbnez $5, -28\nnop\nb -4\nnop")
    mipsRegister 32 4 1000 .big
  let powerpc (source : String) : IO Bap.Emu.Emu := do Bap.Emu.powerpc (← LLVM.assemble "powerpc64le" source) 0 0 {}
  let powerRegister (index : Nat) : Bap.Var := ⟨s!"R{[3, 4, 5][index]!}", .imm 64, 0, false⟩
  let powerpc (source : String) : IO Bap.Emu.Emu := do
    let emu ← powerpc source
    Bap.Emu.setReg emu ⟨"SO", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 0))
    pure emu
  trial "Parallel lwarx and stwcx" (powerpc "lwarx 6, 0, 3\naddi 6, 6, 1\nstwcx. 6, 0, 3\nbne 0, -12\naddi 4, 4, -1\ncmpdi 4, 0\nbne 0, -24\nb 0")
    powerRegister 4 1000
  let arm (source : String) : IO Bap.Emu.Emu := do Bap.Emu.arm32 (← LLVM.assemble "armv7" source) 0 0
  let armRegister32 (index : Nat) : Bap.Var := ⟨s!"R{[0, 1, 2][index]!}", .imm 32, 0, false⟩
  trialWide "Parallel ldrex and strex" (arm "ldrex r3, [r0]\nadd r3, r3, #1\nstrex r4, r3, [r0]\ncmp r4, #0\nbne #-24\nsub r1, r1, #1\ncmp r1, #0\nbne #-36\nb #-8")
    armRegister32 32 4 1000 .little
  -- `lock add dword ptr [rdi], 1; dec rsi; jnz back; jmp self`
  let x86Register (index : Nat) : Bap.Var := ⟨["RDI", "RSI", "RDX"][index]!, .imm 64, 0, false⟩
  trial "Parallel lock add" (Bap.Emu.x86_64 (ByteArray.mk #[0xF0, 0x83, 0x07, 0x01, 0x48, 0xFF, 0xCE, 0x75, 0xF7, 0xEB, 0xFE]) 0 0) x86Register 4 1000
  -- A round is turns of its own: what a run left of a turn isn't there after one, whether it had one thread to run or more.
  let turns ← riscv "nop\nj -4"
  let _ ← Bap.Emu.spawnThread turns 0 0
  let _ ← Bap.Emu.runPreemptive turns 10 3
  assertEqual "A run that fuel ended holds what was left of its turn" 3 (← turns.turnUsed.get)
  let _ ← Bap.Emu.runPreemptiveParallel turns 10
  assertEqual "A round goes on from no turn" 0 (← turns.turnUsed.get)
  let alone ← riscv "nop\nj -4"
  let _ ← Bap.Emu.runPreemptiveParallel alone 10
  assertEqual "A round of one thread leaves no turn" 0 (← alone.turnUsed.get)

/-- An aligned load sees a whole store, as on a machine, and never a part of one: one thread writes all ones and all zeros by turns,
and another reads what it may, and stops if it is anything else. -/
def testParallelTearing : IO Unit := do
  let trial (label loadStore : String) : IO Unit := do
    -- 0: the one that writes. 20: the one that reads, which is at `torn` if it saw a part. a0 is where.
    let code ← LLVM.assemble "riscv64" (s!"li t1, -1\n{loadStore} t1, (a0)\n{loadStore} zero, (a0)\nj -8\nnop\n" ++
      s!"{(if loadStore == "sd" then "ld" else "lw")} t2, (a0)\nbeqz t2, -4\naddi t3, t2, 1\nbeqz t3, -12\nj 0")
    let torn := code.size - 4
    -- Compiled, and never compiled, which is another way to memory.
    for (way, adjust) in [("compiled", id), ("interpreted", fun config => { config with hotThreshold := 1000000000 })] do
      let emu ← Bap.Emu.riscv64 code 0 0 (adjust := adjust)
      Bap.Emu.map emu ⟨0x10000, ByteArray.mk (Array.replicate 64 0), ⟨true, true, false⟩⟩
      let where_ : Bap.Var := ⟨"X10", .imm 64, 0, false⟩
      let address : Bap.Value := .bits (BitVec.ofNat 64 0x10000)
      Bap.Emu.setReg emu where_ address
      let reader ← Bap.Emu.spawnThread emu 20 0
      Bap.Emu.setThreadReg emu reader where_ address
      for _ in [0:(if way == "compiled" then 40 else 400)] do
        let _ ← Bap.Emu.runPreemptiveParallel emu (if way == "compiled" then 20000 else 500)
      let readerAt := ((← Bap.Emu.threads emu).find? (·.id == reader)).map (·.pc)
      assertTrue s!"{label} {way} is not seen in parts" (readerAt != some torn)
  trial "Parallel store of 4 bytes" "sw"
  trial "Parallel store of 8 bytes" "sd"

/-- A fence holds a worker until all the others have stopped, as that is what orders what they did: of each target, by how little a
round gets through. A `nop` is no reason to stop. -/
def testParallelFences : IO Unit := do
  let trial (label : String) (make : IO Bap.Emu.Emu) (stops : Bool) : IO Unit := do
    let emu ← make
    let _ ← Bap.Emu.spawnThread emu 0 0
    let steps ← Bap.Emu.runPreemptiveParallel emu 2000
    if stops then assertTrue s!"{label} ends a round early: {steps}" (steps ≤ 16)
    else assertEqual s!"{label} doesn't end a round" 4000 steps
  let riscv (source : String) : IO Bap.Emu.Emu := do Bap.Emu.riscv64 (← LLVM.assemble "riscv64" source) 0 0
  let arm (source : String) : IO Bap.Emu.Emu := do Bap.Emu.aarch64 (← LLVM.assemble "aarch64" source) 0 0
  let x86 (code : List UInt8) : IO Bap.Emu.Emu := Bap.Emu.x86_64 (ByteArray.mk code.toArray) 0 0
  trial "RISC-V fence" (riscv "fence rw, rw\nj -4") true
  trial "RISC-V fence.tso" (riscv "fence.tso\nj -4") true
  trial "RISC-V nop" (riscv "nop\nj -4") false
  trial "AArch64 dmb" (arm "dmb ish\nb #-4") true
  trial "AArch64 dsb" (arm "dsb sy\nb #-4") true
  trial "AArch64 nop" (arm "nop\nb #-4") false
  -- A jump back to the start after each.
  trial "x86 mfence" (x86 [0x0F, 0xAE, 0xF0, 0xEB, 0xFB]) true
  trial "x86 sfence" (x86 [0x0F, 0xAE, 0xF8, 0xEB, 0xFB]) true
  trial "x86 nop" (x86 [0x90, 0xEB, 0xFD]) false
  -- Each stops where it starts, so that nothing comes after it: these hold what their disassemblers call a fence.
  trial "MIPS sync" (do Bap.Emu.mips32 (← LLVM.assemble "mips" "sync") 0 0) true
  trial "PowerPC sync" (do Bap.Emu.powerpc (← LLVM.assemble "powerpc64le" "sync") 0 0 {}) true
  trial "PowerPC lwsync" (do Bap.Emu.powerpc (← LLVM.assemble "powerpc64le" "lwsync") 0 0 {}) true
  trial "ARM dmb" (do Bap.Emu.arm32 (← LLVM.assemble "armv7" "dmb ish") 0 0) true

/-- A store across a word is a store to each, but what lies within one word is seen whole, at any alignment and of any size that the
lifter makes: a store of 4 bytes at 2 off a multiple of 8. -/
def testParallelUnaligned : IO Unit := do
  let code ← LLVM.assemble "riscv64" ("li t1, -1\nsw t1, 2(a0)\nsw zero, 2(a0)\nj -8\nnop\n" ++
    "lw t2, 2(a0)\nbeqz t2, -4\naddi t3, t2, 1\nbeqz t3, -12\nj 0")
  let torn := code.size - 4
  let emu ← Bap.Emu.riscv64 code 0 0
  Bap.Emu.map emu ⟨0x10000, ByteArray.mk (Array.replicate 64 0), ⟨true, true, false⟩⟩
  let where_ : Bap.Var := ⟨"X10", .imm 64, 0, false⟩
  let address : Bap.Value := .bits (BitVec.ofNat 64 0x10000)
  Bap.Emu.setReg emu where_ address
  let reader ← Bap.Emu.spawnThread emu 20 0
  Bap.Emu.setThreadReg emu reader where_ address
  for _ in [0:40] do
    let _ ← Bap.Emu.runPreemptiveParallel emu 20000
  let readerAt := ((← Bap.Emu.threads emu).find? (·.id == reader)).map (·.pc)
  assertTrue "Parallel store within a word off its alignment is not seen in parts" (readerAt != some torn)

/-- A step that fails is taken back in the native memory by what it wrote, which is what all of that memory being made again comes to:
the same bytes as the state at each stop, and the same as a machine with no ranges at all, whether the process has its own memory or
not. What it costs is counted by why. -/
def testRollbackMemory : IO Unit := do
  let reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let word (value : Nat) : Bap.Value := .bits (BitVec.ofNat 64 value)
  let memoryVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let setup (source : String) (fork : Bool) (adjust : Bap.Emu.Config → Bap.Emu.Config := id) : IO Bap.Emu.Emu := do
    let emu ← Bap.Emu.riscv64 (← LLVM.assemble "riscv64" source) 0 0 (adjust := adjust)
    Bap.Emu.map emu ⟨0x100000, ByteArray.mk (Array.replicate 8192 7), ⟨true, true, false⟩⟩
    let registers := [("X10", 0x100000), ("X11", 0x90000000), ("X12", 5), ("X13", 0), ("X14", 0), ("X15", 0), ("X17", 64)]
    for (name, value) in registers do Bap.Emu.setReg emu (reg name) (word value)
    if fork then
      let child ← Bap.Emu.forkThread emu 0
      for (name, value) in registers do Bap.Emu.setThreadReg emu child (reg name) (word value)
      Bap.Emu.resumeThread emu child
      Bap.Emu.cloneProcessMemory emu child
      Bap.Emu.switchThread emu child
    pure emu
  -- Whatever a native memory holds is what the state has.
  let agrees (label : String) (emu : Bap.Emu.Emu) : IO Unit := do
    if let some native := ← emu.engine.persistentMemory.get then
      let (addresses, values) ← Jit.dumpMemory native
      match ← Bap.Emu.reg emu memoryVar with
      | .memory memory =>
        let cells := (Bap.Memory.cells memory).map (fun cell => (cell.1.toNat, cell.2)) |>.mergeSort fun left right => left.1 ≤ right.1
        assertTrue s!"{label} the native memory is the state's"
          ((addresses.toList.map (·.toNat)).zip values.toList == cells)
      | _ => throw <| IO.userError s!"{label} has no memory"
  let faulting := "addi a2, a2, 1\nsw a2, 0(a0)\nsd a2, 8(a0)\nlw t1, 0(a1)\nj -16"
  let cycle (emu : Bap.Emu.Emu) (label : String) : IO Unit := do
    for _ in [0:40] do
      Bap.Emu.setPc emu 0
      match ← (Bap.Emu.run emu 40).toBaseIO with
      | .ok _ => throw <| IO.userError s!"{label} should fault"
      | .error _ => pure ()
      agrees label emu
  for fork in [false, true] do
    let label := if fork then "Rollback of a fork" else "Rollback"
    let emu ← setup faulting fork
    cycle emu label
    let stats ← Bap.Emu.rollbackStats emu
    assertTrue s!"{label} counts its faults: {repr stats}" (stats.faults ≥ 40)
    assertEqual s!"{label} doesn't count them as anything else" (0, 0) (stats.restarts, stats.others)
    assertTrue s!"{label} takes back what was written: {repr stats}" (stats.patched ≥ 30)
    assertTrue s!"{label} doesn't make the memory again: {repr stats}" (stats.rebuilt ≤ 1)
    -- One step at a time, with nothing to take back, comes to the same.
    let plain ← setup faulting fork fun config => { config with rangeLimit := 1, hotThreshold := 1000000000 }
    cycle plain s!"{label} without ranges"
    assertEqual s!"{label} comes to what it would without ranges" (← Bap.Emu.read plain 0x100000 32).toList (← Bap.Emu.read emu 0x100000 32).toList
    assertEqual s!"{label} leaves registers as it would without ranges"
      (repr (← Bap.Emu.reg plain (reg "X12"))).pretty (repr (← Bap.Emu.reg emu (reg "X12"))).pretty
    -- A range that reaches what is watched goes back and comes again as one instruction.
    let watched ← setup "addi a2, a2, 1\nsw a2, 0(a0)\naddi a2, a2, 1\nlw t1, 16(a0)\nsw a2, 8(a0)\nj -20" fork
    let seen ← IO.mkRef 0
    let _ ← Bap.Emu.run watched 400
    let _ ← Bap.Emu.onRead watched (0x100010, 0x100010) fun _ _ _ => seen.modify (· + 1)
    let _ ← Bap.Emu.run watched 400
    agrees s!"{label} of a watched read" watched
    assertTrue s!"{label} of a watched read fires" ((← seen.get) > 0)
    assertTrue s!"{label} of a watched read restarts: {repr (← Bap.Emu.rollbackStats watched)}" ((← Bap.Emu.rollbackStats watched).restarts ≥ 1)
    -- What a hook wrote in a step that then failed goes as well, with native memory there to have it: a run of the same step won't put
    -- it right, as the hook doesn't do it again.
    let writing ← setup "sw a2, 0(a0)\nsw a2, 8(a0)\nj -8\necall" fork
    let _ ← Bap.Emu.onSyscall writing fun current _ _ => do
      Bap.Emu.write current 0x100040 (ByteArray.mk #[99, 98, 97])
      throw (IO.userError "refused")
    let _ ← Bap.Emu.run writing 300
    assertTrue s!"{label} of a hook's write has native memory" (← writing.engine.persistentMemory.get).isSome
    Bap.Emu.setPc writing 12
    let before ← Bap.Emu.rollbackStats writing
    let _ ← (Bap.Emu.run writing 1).toBaseIO
    agrees s!"{label} of a hook's write" writing
    assertEqual s!"{label} of a hook's write takes it back" [7, 7, 7] (← Bap.Emu.read writing 0x100040 3).toList
    let after ← Bap.Emu.rollbackStats writing
    assertEqual s!"{label} of a hook's write isn't a fault" (before.faults, before.others + 1) (after.faults, after.others)
    assertEqual s!"{label} of a hook's write is taken back, not made again" (before.patched + 1, before.rebuilt) (after.patched, after.rebuilt)
    -- What a store of a failing run wrote is taken back too, which nothing else would do where the run isn't to come again: a run that
    -- faults, and then goes somewhere else.
    let elsewhere ← setup "sw a2, 0(a0)\nsw a2, 64(a0)\nlw t1, 0(a1)\nj -12" fork
    let _ ← (Bap.Emu.run elsewhere 2).toBaseIO
    let good : Bap.Value := word 0x100000
    Bap.Emu.setReg elsewhere (reg "X11") good
    let _ ← Bap.Emu.run elsewhere 200
    Bap.Emu.setReg elsewhere (reg "X11") (word 0x90000000)
    Bap.Emu.setReg elsewhere (reg "X12") (word 200)
    Bap.Emu.setPc elsewhere 0
    -- From the top, this range stores 200 twice and faults; a run of one step undoes the range and does its first store alone.
    let _ ← (Bap.Emu.step elsewhere)
    agrees s!"{label} of a step alone" elsewhere
    assertEqual s!"{label} of a step alone stored one" [200] [(← Bap.Emu.read elsewhere 0x100000 1)[0]!.toNat]
    Bap.Emu.setPc elsewhere 0
    let _ ← (Bap.Emu.run elsewhere 40).toBaseIO
    agrees s!"{label} of a range that faulted" elsewhere
    -- What was unmapped in a step that then failed comes back in native memory too, and the state still has it.
    let unmapping ← setup "sw a2, 0(a0)\nsw a2, 8(a0)\nj -8\necall" fork
    Bap.Emu.map unmapping ⟨0x200000, ByteArray.mk (Array.replicate 8192 3), ⟨true, true, false⟩⟩
    let _ ← Bap.Emu.onSyscall unmapping fun current _ _ => do
      Bap.Emu.unmap current 0x200000 4096
      throw (IO.userError "refused")
    let _ ← Bap.Emu.run unmapping 300
    Bap.Emu.setPc unmapping 12
    let _ ← (Bap.Emu.run unmapping 1).toBaseIO
    agrees s!"{label} of an unmap" unmapping
    assertEqual s!"{label} of an unmap brings it back" 3 (← Bap.Emu.read unmapping 0x200000 1)[0]!.toNat
    Bap.Emu.unmap unmapping 0x200000 4096
    agrees s!"{label} of an unmap that stays" unmapping
    assertEqual s!"{label} of an unmap leaves the rest" 3 (← Bap.Emu.read unmapping 0x201000 1)[0]!.toNat
    -- What a state is given is what native memory has after, from the pages that it has.
    let given ← setup "sw a2, 0(a0)\nsw a2, 8(a0)\nj -8" fork
    let _ ← Bap.Emu.run given 300
    match ← Bap.Emu.reg given memoryVar with
    | .memory memory =>
      Bap.Emu.setReg given memoryVar (.memory (Bap.Memory.writeRegion memory 0x100080 (ByteArray.mk #[42, 43])))
    | _ => throw <| IO.userError "no memory"
    agrees s!"{label} of a memory given" given
    assertEqual s!"{label} of a memory given reads it" [42, 43] (← Bap.Emu.read given 0x100080 2).toList
    let _ ← Bap.Emu.run given 100
    agrees s!"{label} of a memory given goes on" given
    -- A step that replaced the memory has nothing to take back, and it is made again.
    let replacing ← setup "sw a2, 0(a0)\nsw a2, 8(a0)\nj -8\necall" fork
    let _ ← Bap.Emu.onSyscall replacing fun current _ _ => do
      Bap.Emu.setReg current memoryVar (← Bap.Emu.reg current memoryVar)
      throw (IO.userError "refused")
    let _ ← Bap.Emu.run replacing 300
    assertTrue s!"{label} of a replaced memory has native memory" (← replacing.engine.persistentMemory.get).isSome
    Bap.Emu.setPc replacing 12
    let beforeReplacing ← Bap.Emu.rollbackStats replacing
    let _ ← (Bap.Emu.run replacing 1).toBaseIO
    agrees s!"{label} of a replaced memory" replacing
    let afterReplacing ← Bap.Emu.rollbackStats replacing
    assertEqual s!"{label} of a replaced memory patches nothing" beforeReplacing.patched afterReplacing.patched
    if fork then
      assertEqual s!"{label} of a replaced memory is made again" (beforeReplacing.rebuilt + 1) afterReplacing.rebuilt
  -- What a worker writes in a round is no step's, and a step after it knows only its own.
  let rounds ← setup "addi a2, a2, 1\nsw a2, 0(a0)\nj -8" false
  let _ ← Bap.Emu.spawnThread rounds 0 0
  let _ ← Bap.Emu.runPreemptiveParallel rounds 100
  if let some native := ← rounds.engine.persistentMemory.get then
    assertTrue "A round leaves no step open" ((← Jit.memoryStepWrites native).isNone)

/-- A checkpoint is of a whole instruction and of everything at one moment: none is made by a hook of an access, or by a worker while
the others run. A hook of the code comes before its instruction, which is a place to make one. -/
def testCheckpointMoments : IO Unit := do
  let reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
  let tried (emu : Bap.Emu.Emu) (seen : IO.Ref (Option Bool)) : IO Unit := do
    let result ← (Bap.Emu.checkpointBytes emu).toBaseIO
    seen.set (some (match result with | .ok _ => true | .error _ => false))
  let start (source : String) : IO Bap.Emu.Emu := do
    let emu ← Bap.Emu.riscv64 (← LLVM.assemble "riscv64" source) 0 0
    Bap.Emu.map emu ⟨0x10000, ByteArray.mk (Array.replicate 64 7), ⟨true, true, false⟩⟩
    Bap.Emu.setReg emu (reg "X10") (.bits (BitVec.ofNat 64 0x10000))
    Bap.Emu.setReg emu (reg "X12") (.bits (BitVec.ofNat 64 1))
    pure emu
  let reading ← start "lw t1, 0(a0)\nj -4"
  let readSeen ← IO.mkRef none
  let _ ← Bap.Emu.onRead reading (0x10000, 0x10000) fun current _ _ => tried current readSeen
  let _ ← Bap.Emu.run reading 2
  assertEqual "A checkpoint isn't made by a hook of a load" (some false) (← readSeen.get)
  let writing ← start "sw a2, 0(a0)\nj -4"
  let writeSeen ← IO.mkRef none
  let _ ← Bap.Emu.onWrite writing (0x10000, 0x10000) fun current _ _ _ => tried current writeSeen
  let _ ← Bap.Emu.run writing 2
  assertEqual "A checkpoint isn't made by a hook of a store" (some false) (← writeSeen.get)
  -- When the hook is over, it can be made again.
  let _ ← Bap.Emu.checkpointBytes writing
  let coded ← start "nop\nj -4"
  let codeSeen ← IO.mkRef none
  let _ ← Bap.Emu.onCode coded (0, 0) fun current _ => tried current codeSeen
  let _ ← Bap.Emu.run coded 2
  assertEqual "A checkpoint can be made by a hook of the code" (some true) (← codeSeen.get)
  let round ← start "nop\nj -4"
  let _ ← Bap.Emu.spawnThread round 0 0
  let workerSeen ← IO.mkRef none
  let _ ← Bap.Emu.onCode round (0, 0) fun current _ => tried current workerSeen
  let _ ← Bap.Emu.runPreemptiveParallel round 10
  assertEqual "A checkpoint isn't made by a worker of a round" (some false) (← workerSeen.get)
  let _ ← Bap.Emu.checkpointBytes round
  -- Why a step was taken back is that step's: a hook that throws after a fault that was dealt with isn't a fault.
  let faulting ← start "lw t1, 0(a1)\nnop\necall"
  Bap.Emu.setReg faulting (reg "X11") (.bits (BitVec.ofNat 64 0x90000000))
  for name in ["X13", "X14", "X15", "X17"] do Bap.Emu.setReg faulting (reg name) (.bits (BitVec.ofNat 64 0))
  let _ ← Bap.Emu.onSyscall faulting fun _ _ _ => throw (IO.userError "refused")
  let _ ← (Bap.Emu.step faulting).toBaseIO
  assertTrue "A fault is left to be seen" (← Bap.Emu.failure faulting).isSome
  Bap.Emu.setPc faulting 8
  let _ ← (Bap.Emu.step faulting).toBaseIO
  let stats ← Bap.Emu.rollbackStats faulting
  assertEqual "A hook that throws after a fault isn't one" (1, 1) (stats.faults, stats.others)
  -- A file that can't be put in its place leaves nothing behind.
  match ← (Bap.Emu.writeAtomically "native/build" (ByteArray.mk #[1])).toBaseIO with
  | .ok _ => throw <| IO.userError "A directory isn't a place for a checkpoint"
  | .error _ => pure ()
  assertTrue "A save that fails leaves nothing" !(← System.FilePath.pathExists "native/build.partial")
  -- How a directory is written isn't what it holds, and what it holds is.
  let root : System.FilePath := "native/build/digest-test"
  IO.FS.createDirAll (root / "under")
  IO.FS.writeFile (root / "under" / "file") "one"
  let digest ← Bap.Linux.directoryDigest root
  assertEqual "A directory has one digest, however it is written" digest (← Bap.Linux.directoryDigest "native/build/digest-test/")
  assertEqual "A directory has one digest, with two ends" digest (← Bap.Linux.directoryDigest "native/build/digest-test//")
  IO.FS.writeFile (root / "under" / "file") "two"
  assertTrue "A directory that changed has another digest" (digest != (← Bap.Linux.directoryDigest root))
  IO.FS.removeDirAll root

/-- Handlers, masks, waiting, threads, children, faults and what a context says, as `testsuite/src/libc-signals.c` has them, whose
output is what qemu has it say on every target. -/
def testLinuxSignals (triple : String) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-signals")
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  let expected := String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/libc-signals.out")
  let actual := String.fromUTF8! (← written.get)
  -- The first line that differs says more than all of them.
  let different := ((expected.splitOn "\n").zip (actual.splitOn "\n")).find? fun (left, right) => left != right
  assertEqual s!"Linux {triple} signals say what they should" none different
  assertEqual s!"Linux {triple} signals end as they should" (Bap.Tasks.ScheduleOutcome.finished 0, expected.length) (outcome, actual.length)

/-- A run with all of that stopped and saved goes on as it would have: what is pending, the frames of handlers and what a process does
with a signal are in a checkpoint, in every piece. -/
def testLinuxSignalCheckpoints (triple : String) (step : Nat) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-signals")
  let written ← IO.mkRef ByteArray.empty
  let rec go : Nat → Bap.Linux.Machine → IO Bap.Tasks.ScheduleOutcome
    | 0, _ => throw <| IO.userError "more pieces than a run should have"
    | fuel + 1, machine => do
      let outcome ← machine.run (fuel := step) fun data => written.modify (· ++ data)
      if outcome == .outOfFuel then
        let data ← machine.checkpoint
        let next ← Bap.Linux.Machine.ofCheckpoint data
        assertTrue s!"Linux {triple} signals save again as they were" (data == (← next.checkpoint))
        go fuel next
      else pure outcome
  let outcome ← go 400 (← Bap.Linux.start kernel "/test" ["/test"])
  assertEqual s!"Linux {triple} signals end as they should, from pieces" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} signals say what they should, from pieces"
    (String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/libc-signals.out")) (String.fromUTF8! (← written.get))

/-- `brk`, `madvise`, `mremap` and shared mappings of files and of memory, also between processes: what `testsuite/src/libc-memory.c`
says on Linux itself, on x86-64. qemu says the same as far as it goes, but for `madvise` of what isn't mapped, which it doesn't check: on
64 bits it faults at a second mapping by `mremap`, the last line, and on 32 bits at growing in place, about half way. -/
def testLinuxMemory (triple : String) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-memory")
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let outcome ← machine.run fun data => written.modify (· ++ data)
  let expected := String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/libc-memory.out")
  let actual := String.fromUTF8! (← written.get)
  let different := ((expected.splitOn "\n").zip (actual.splitOn "\n")).find? fun (left, right) => left != right
  assertEqual s!"Linux {triple} memory says what Linux does" none different
  assertEqual s!"Linux {triple} memory ends as it should" (Bap.Tasks.ScheduleOutcome.finished 0, expected.length) (outcome, actual.length)

/-- The same, stopped and saved all along the way: what is mapped of a file is in a checkpoint, and what was written to a shared mapping
and hasn't reached the file yet still does. -/
def testLinuxMemoryCheckpoints (triple : String) (step : Nat) : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-memory")
  let written ← IO.mkRef ByteArray.empty
  let rec go : Nat → Bap.Linux.Machine → IO Bap.Tasks.ScheduleOutcome
    | 0, _ => throw <| IO.userError "more pieces than a run should have"
    | fuel + 1, machine => do
      let outcome ← machine.run (fuel := step) fun data => written.modify (· ++ data)
      if outcome == .outOfFuel then
        let data ← machine.checkpoint
        let next ← Bap.Linux.Machine.ofCheckpoint data
        assertTrue s!"Linux {triple} memory saves again as it was" (data == (← next.checkpoint))
        go fuel next
      else pure outcome
  let outcome ← go 400 (← Bap.Linux.start kernel "/test" ["/test"])
  assertEqual s!"Linux {triple} memory ends as it should, from pieces" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} memory says what Linux does, from pieces"
    (String.fromUTF8! (← IO.FS.readBinFile "testsuite/data/libc-memory.out")) (String.fromUTF8! (← written.get))

/-- Where the bytes of a record came from, in a run with a check, flattened control flow, vectors, a thread and a child: the status byte goes back to
what `/proc` said by way of the branch that chose it, and the bytes beside it to what they came from, with nothing widened to all of memory. -/
def testLinuxTaint (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-taint"
  let file := ByteArray.mk ((Array.range 16).map fun index => (0x40 + index).toUInt8)
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" program).addFile "/data" file
  let written ← IO.mkRef ByteArray.empty
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let tracker ← machine.track
  let main ← Bap.Emu.thread machine.emu
  let outcome ← machine.run fun data => written.modify (· ++ data)
  let text := String.fromUTF8! (← written.get)
  assertEqual s!"Linux {triple} taint goes as it would have" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  let lines := text.splitOn "\n"
  assertEqual s!"Linux {triple} taint says the status" "1" (lines.getD 1 "")
  let untracked ← IO.mkRef ByteArray.empty
  let plain ← Bap.Linux.start kernel "/test" ["/test"]
  let _ ← plain.run fun data => untracked.modify (· ++ data)
  assertEqual s!"Linux {triple} a program that is followed says the same" (String.fromUTF8! (← untracked.get)) text
  let first := (lines.getD 0 "").drop 1 |>.toString
  let record := first.foldl (fun value digit => value * 16 + (if digit.isDigit then digit.toNat - 48 else digit.toNat - 87)) 0
  let space ← Bap.Emu.spaceOf machine.emu main
  let explain (index : Nat) := tracker.explainMemory (record + index) (some space)
  let labels (explanation : Bap.Analysis.DynamicTaint.Tracker.Explanation) : List String :=
    explanation.sources.filterMap fun (node, _, _) => match node.kind with
      | .source label _ => some label
      | _ => none
  let status ← explain 4
  assertTrue s!"Linux {triple} the status comes from /proc" ((labels status).any (· == "read /proc/self/status"))
  assertTrue s!"Linux {triple} the status goes by a branch" (status.path.any fun step => step.node.kind matches .branch _)
  assertTrue s!"Linux {triple} the status is a constant that a branch chose" (status.path.any fun step =>
    step.node.kind matches .constant && step.node.valueAt step.byte == some 0x31)
  assertTrue s!"Linux {triple} the status has no file in it" (!(labels status).any (·.startsWith "pread"))
  let at_ (explanation : Bap.Analysis.DynamicTaint.Tracker.Explanation) : List (String × Option Nat × Bool) :=
    explanation.sources.filterMap fun (node, byte, edge) => match node.kind with
      | .source label offset => some (label, offset.map (· + byte), edge == .data)
      | _ => none
  assertEqual s!"Linux {triple} a byte of a file is that byte" [("pread /data", some 7, true)] (at_ (← explain 0))
  assertEqual s!"Linux {triple} the next byte is the next byte" [("pread /data", some 8, true)] (at_ (← explain 1))
  let other ← explain 5
  assertEqual s!"Linux {triple} a constant beside them comes from nothing" [] (at_ other)
  assertTrue s!"Linux {triple} a constant beside them has its instruction" (other.origin matches .clean _)
  let fromThread ← explain 6
  assertEqual s!"Linux {triple} what a thread copied is its byte" [("pread /data", some 3, true)] (at_ fromThread)
  assertTrue s!"Linux {triple} the way goes through the thread" (fromThread.path.any fun step => step.node.thread != main)
  let kept ← explain 7
  assertEqual s!"Linux {triple} what a child did stays in the child" [] (at_ kept)
  let nodes ← tracker.nodes.get
  let inChild := nodes.toList.find? fun node => node.space != space && node.place == .memory (record + 7)
  match inChild with
  | none => throw <| IO.userError s!"Linux {triple}: the store of the child has no node"
  | some node =>
    let there ← tracker.explainMemory (record + 7) (some node.space)
    assertEqual s!"Linux {triple} the child has what it did" [("pread /data", some 9, true)] (at_ there)
  assertEqual s!"Linux {triple} taint follows all that this does" [] (← tracker.gapsOf)

private def historyKernel (triple : String) (code : Char) : IO Bap.Linux.Kernel := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-history"
  let bytes := "AB".toUTF8 ++ String.toUTF8 (String.singleton code) ++ "DEFGHIJKLMNOP".toUTF8
  pure ((Bap.Linux.Kernel.empty.addFile "/test" program).addFile "/data" bytes)

private def hexOfLine (line : String) : Nat :=
  (line.drop 1).toString.foldl (fun value digit => value * 16 + (if digit.isDigit then digit.toNat - 48 else digit.toNat - 87)) 0

private def sourcesAt (explanation : Bap.Analysis.DynamicTaint.Tracker.Explanation) : List (String × Option Nat) :=
  explanation.sources.filterMap fun (node, byte, _) => match node.kind with
    | .source label offset => some (label, offset.map (· + byte))
    | _ => none

/-- What a run did and what went where, with a dispatcher that comes to a deferred routine by a byte of a file: how it first got there, who called whom in which
thread, a byte through a pipe from a child and through a file, why it went there, and where it would have gone otherwise. -/
def testLinuxHistory (triple : String) : IO Unit := do
  let run (code : Char) : IO (Bap.Linux.Machine × Bap.Analysis.Journal.Journal × Bap.Analysis.DynamicTaint.Tracker × String × Nat) := do
    let written ← IO.mkRef ByteArray.empty
    let machine ← Bap.Linux.start (← historyKernel triple code) "/test" ["/test"]
    let journal ← machine.journal
    let tracker ← machine.track
    let main ← Bap.Emu.thread machine.emu
    let outcome ← machine.run fun data => written.modify (· ++ data)
    assertEqual s!"Linux {triple} history goes as it should" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    pure (machine, journal, tracker, String.fromUTF8! (← written.get), main)
  let (machine, journal, tracker, text, main) ← run 'C'
  let lines := text.splitOn "\n"
  assertEqual s!"Linux {triple} a pipe, a file and what ends are as on Linux" ["AB00n11", "ae", ""] (lines.drop 3)
  let deferred := hexOfLine (lines.getD 0 "") / 2 * 2
  let leaf := hexOfLine (lines.getD 1 "") / 2 * 2
  let record := hexOfLine (lines.getD 2 "")
  let some entry ← journal.firstEntry deferred
    | throw <| IO.userError s!"Linux {triple}: the deferred routine never ran"
  assertTrue s!"Linux {triple} the deferred routine was called" entry.call.isSome
  assertEqual s!"Linux {triple} it is on top of the stack it was called with" (some deferred) (entry.stack.head?.map (·.callee))
  assertTrue s!"Linux {triple} what called it is under it" (entry.stack.length ≥ 3)
  assertTrue s!"Linux {triple} what ran before it is there" (!entry.before.isEmpty)
  -- A direct call on 64-bit PowerPC goes past what sets up the TOC, which is two instructions.
  let calls := (← journal.callsOf leaf) ++ (← journal.callsOf (leaf + 8))
  assertTrue s!"Linux {triple} a call is by the thread that made it" ((calls.any (·.1 == main)) && (calls.any (·.1 != main)))
  let stack ← journal.callStack (some main)
  assertTrue s!"Linux {triple} what came back isn't on the stack" (!stack.any fun frame => frame.callee == deferred || frame.callee == leaf)
  let events ← journal.events.get
  assertTrue s!"Linux {triple} a return says where from and to" (events.any fun event => match event with
    | .ret _ thread _ _ frames => thread == main && frames == 1
    | _ => false)
  let space ← Bap.Emu.spaceOf machine.emu main
  let piped ← tracker.explainMemory record (some space)
  assertEqual s!"Linux {triple} a byte from a child has where its parent got it" [("pread data", some 0)] (sourcesAt piped)
  assertTrue s!"Linux {triple} and went by the pipe" (piped.path.any fun step => match step.node.kind with
    | .carried label => label.startsWith "write pipe"
    | _ => false)
  assertTrue s!"Linux {triple} from the child" (piped.path.any fun step => step.node.thread != main)
  let filed ← tracker.explainMemory (record + 1) (some space)
  assertEqual s!"Linux {triple} a byte from a file has where it was before" [("pread data", some 1)] (sourcesAt filed)
  assertTrue s!"Linux {triple} and went by the file" (filed.path.any fun step => step.node.kind == .carried "write out")
  let shared ← tracker.explainMemory (record + 2) (some space)
  assertEqual s!"Linux {triple} a byte from a child by shared memory has where it got it" [("pread data", some 3)] (sourcesAt shared)
  let some why ← Bap.Linux.whyEntered journal tracker deferred
    | throw <| IO.userError s!"Linux {triple}: no reason for the deferred routine"
  assertTrue s!"Linux {triple} a branch led to the deferred routine" why.branch.isSome
  assertTrue s!"Linux {triple} and that came from the byte that decides it"
    ((why.explanation.map sourcesAt).getD [] |>.contains ("pread data", some 2))
  let (other, otherJournal, _, otherText, _) ← run 'D'
  assertEqual s!"Linux {triple} the other run has no deferred routine" ["AB00n10", "ae", ""] (((otherText.splitOn "\n").drop 3))
  assertTrue s!"Linux {triple} and the other run never came to it" (← otherJournal.firstEntry deferred).isNone
  let difference ← Bap.Linux.compareRuns machine other journal otherJournal
  assertTrue s!"Linux {triple} all of the runs were compared" difference.run.complete
  assertEqual s!"Linux {triple} the first file that differs is what was given" (some "/data") difference.file
  match difference.run.branch, difference.run.service with
  | some branch, some service =>
    assertTrue s!"Linux {triple} two runs part at a branch" (branch.branch.isSome && branch.left != branch.right)
    assertTrue s!"Linux {triple} after they were given something else" (service.seq ≤ branch.seq)
    assertTrue s!"Linux {triple} which was what was read" (match service.left with
      | some (.service _ _ _ _ label _ _ _) => label == "pread data"
      | _ => false)
  | _, _ => throw <| IO.userError s!"Linux {triple}: two runs don't differ"
  let again ← journal.toRecord
  let itself := Bap.Analysis.Journal.Journal.compare again again
  assertEqual s!"Linux {triple} a run doesn't differ from itself" (true, true) (itself.branch.isNone, itself.service.isNone)

/-- All of that from pieces, saved and started again each time, is what it is in one go. -/
def testLinuxHistoryCheckpoints (triple : String) (step : Nat) : IO Unit := do
  let kernel ← historyKernel triple 'C'
  let trackers : IO.Ref (Option Bap.Analysis.DynamicTaint.Tracker) ← IO.mkRef none
  let journals : IO.Ref (Option Bap.Analysis.Journal.Journal) ← IO.mkRef none
  let models := [Bap.Linux.taintModel trackers, Bap.Linux.journalModel journals]
  let written ← IO.mkRef ByteArray.empty
  let rec go : Nat → Bap.Linux.Machine → IO (Bap.Linux.Machine × Bap.Tasks.ScheduleOutcome)
    | 0, _ => throw <| IO.userError "more pieces than a run should have"
    | fuel + 1, machine => do
      let outcome ← machine.run (fuel := step) fun data => written.modify (· ++ data)
      if outcome == .outOfFuel then
        let data ← machine.checkpoint
        let next ← Bap.Linux.Machine.ofCheckpoint data (models := models)
        assertTrue s!"Linux {triple} history saves again as it was" (data == (← next.checkpoint))
        go fuel next
      else pure (machine, outcome)
  let first ← Bap.Linux.start kernel "/test" ["/test"] (models := models)
  let main ← Bap.Emu.thread first.emu
  let (machine, outcome) ← go 2000 first
  assertEqual s!"Linux {triple} history ends as it should, from pieces" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  let whole ← Bap.Linux.start kernel "/test" ["/test"]
  let wholeJournal ← whole.journal
  let wholeTracker ← whole.track
  let wholeWritten ← IO.mkRef ByteArray.empty
  let _ ← whole.run fun data => wholeWritten.modify (· ++ data)
  assertEqual s!"Linux {triple} history says the same, from pieces" (String.fromUTF8! (← wholeWritten.get)) (String.fromUTF8! (← written.get))
  let some journal ← journals.get | throw <| IO.userError "no journal"
  let some tracker ← trackers.get | throw <| IO.userError "no tracker"
  let left ← journal.toRecord
  let right ← wholeJournal.toRecord
  let parts := Bap.Analysis.Journal.Journal.compare left right
  assertEqual s!"Linux {triple} pieces run the same instructions" none (parts.branch.map (·.index))
  assertEqual s!"Linux {triple} pieces are given the same" none (parts.service.map (·.index))
  assertEqual s!"Linux {triple} pieces keep all of what ran" right.history.size left.history.size
  assertEqual s!"Linux {triple} pieces keep the calls and returns" right.events.size left.events.size
  let lines := (String.fromUTF8! (← written.get)).splitOn "\n"
  let record := hexOfLine (lines.getD 2 "")
  let space ← Bap.Emu.spaceOf machine.emu main
  assertEqual s!"Linux {triple} a byte goes back the same way, from pieces"
    (← wholeTracker.explainMemory record (some space)).text (← tracker.explainMemory record (some space)).text

/-- All that a machine is, in an order that doesn't depend on the way it got there: a file has registers in the order that they were last written, which isn't the same for compiled code. -/
private def stateOf (machine : Bap.Linux.Machine) : IO (List (Nat × ByteArray × Bool × Bool × Bool) × List (Nat × Nat × Bool × List (String × Nat)) × ByteArray) := do
  -- It brings what regions hold up to date.
  let _ ← machine.checkpoint
  let regions := (← machine.emu.regions.get).map fun region =>
    (region.address, region.data, region.protection.readable, region.protection.writable, region.protection.executable)
  let registers (env : Bap.Bil.Env) : List (String × Nat) :=
    let named := env.filterMap fun (var, value) => match value with
      | .bits bits => if var.name.startsWith "_primus_" || var.name.startsWith "intrinsic:" then none else some (var.name, bits.toNat)
      | _ => none
    (named.toArray.qsort fun left right => left.1 < right.1).toList
  let threads := (← machine.emu.threadsRef.get).map fun context => (context.id, context.pc, context.stopped, registers context.state.env)
  let sorted := (threads.toArray.qsort fun left right => left.1 < right.1).toList
  let byAddress := (regions.toArray.qsort fun left right => left.1 < right.1).toList
  pure (byAddress, sorted, Bap.Linux.Image.encode ByteArray.empty (← machine.kernel.get).image)

/-- The same whichever way it runs: a program says the same and ends with the same memory, registers and kernel in the interpreter, and when it changes from one to the other as it goes, and the
interpreter compiles nothing. -/
def testLinuxExecutionModes (triple : String) (name : String) : IO Unit := do
  let start : IO Bap.Linux.Machine := do
    let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}")
    Bap.Linux.start kernel "/test" ["/test", "arg1"]
  let finish (machine : Bap.Linux.Machine) (step : Nat) (between : Nat → IO Unit) : IO (Bap.Tasks.ScheduleOutcome × String × (List (Nat × ByteArray × Bool × Bool × Bool) × List (Nat × Nat × Bool × List (String × Nat)) × ByteArray)) := do
    let written ← IO.mkRef ByteArray.empty
    let rec go : Nat → Nat → IO Bap.Tasks.ScheduleOutcome
      | 0, _ => pure .outOfFuel
      | fuel + 1, round => do
        between round
        let outcome ← machine.run (fuel := step) fun data => written.modify (· ++ data)
        if outcome == .outOfFuel then go fuel (round + 1) else pure outcome
    let outcome ← go 100000 0
    pure (outcome, String.fromUTF8! (← written.get), ← stateOf machine)
  let jit ← start
  assertEqual s!"Linux {triple} {name} starts with the JIT" Bap.Emu.ExecutionMode.jit (← jit.executionMode)
  let (jitOutcome, jitText, jitState) ← finish jit 1000000000 fun _ => pure ()
  let interpreted ← start
  interpreted.setExecutionMode .interpret
  assertEqual s!"Linux {triple} {name} says how it runs" Bap.Emu.ExecutionMode.interpret (← interpreted.executionMode)
  let (outcome, text, state) ← finish interpreted 1000000000 fun _ => pure ()
  assertEqual s!"Linux {triple} {name} ends the same in the interpreter" jitOutcome outcome
  assertEqual s!"Linux {triple} {name} says the same in the interpreter" jitText text
  assertTrue s!"Linux {triple} {name} is in the same state after the interpreter" (jitState == state)
  let stats ← Bap.Primus.Lifted.stats interpreted.emu.engine
  assertEqual s!"Linux {triple} {name} compiles nothing in the interpreter" (0, 0) (stats.nativeRuns, stats.nativeCompilations)
  let changing ← start
  let (outcome, text, state) ← finish changing 701 fun round =>
    changing.setExecutionMode (if round % 2 == 0 then .interpret else .jit)
  assertEqual s!"Linux {triple} {name} ends the same when it changes" jitOutcome outcome
  assertEqual s!"Linux {triple} {name} says the same when it changes" jitText text
  assertTrue s!"Linux {triple} {name} is in the same state when it changes" (jitState == state)

/-- A step back is what the machine was there: the same as one that ran that far and no further, whatever ran in between, such as threads, a child, shared memory and files, and from there it goes on
as it would have. -/
def testStepBack (triple name : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let bytes := "ABCDEFGHIJKLMNOP".toUTF8
  let start : IO Bap.Linux.Machine := do
    Bap.Linux.start ((Bap.Linux.Kernel.empty.addFile "/test" program).addFile "/data" bytes) "/test" ["/test", "arg1"]
  let at_ (count : Nat) : IO _ := do
    let machine ← start
    let _ ← machine.run (fuel := count) fun _ => pure ()
    stateOf machine
  let whole ← start
  let wholeOutcome ← whole.run fun _ => pure ()
  let wholeState ← stateOf whole
  let machine ← start
  machine.keepHistory (every := 997) (limit := 100000)
  let mut position := 0
  for piece in [3001, 1, 7919, 1000000000] do
    let _ ← machine.run (fuel := piece) fun _ => pure ()
    position ← machine.position
  let last := position
  assertTrue s!"Linux {triple} {name} ran enough to step back through" (last > 12000)
  for target in [last - 1, last - 500, 11000, 3002, 3001, 1234, 1, 0] do
    machine.stepBack (position - target)
    position ← machine.position
    assertEqual s!"Linux {triple} {name} is where it stepped back to" target position
    assertTrue s!"Linux {triple} {name} stepped back to {target} is what ran to {target} is" ((← stateOf machine) == (← at_ target))
  let outcome ← machine.run fun _ => pure ()
  assertEqual s!"Linux {triple} {name} goes on from a step back as it would have" wholeOutcome outcome
  assertTrue s!"Linux {triple} {name} ends the same after stepping back" ((← stateOf machine) == wholeState)
  -- And it steps back again over what it ran again.
  machine.stepBack 3
  assertTrue s!"Linux {triple} {name} steps back again" ((← stateOf machine) == (← at_ ((← machine.position))))

private def assertThrows (name : String) (action : IO Unit) : IO Unit := do
  let failed ← try action; pure false catch _ => pure true
  assertTrue name failed

/-- A machine that is put back to what was saved steps back from there, and not from where it was before. -/
def testStepBackAfterRestore : IO Unit := do
  let program ← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-memory"
  let start : IO Bap.Linux.Machine := Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let at_ (count : Nat) : IO _ := do
    let machine ← start
    let _ ← machine.run (fuel := count) fun _ => pure ()
    stateOf machine
  let machine ← start
  machine.keepHistory (every := 997)
  let _ ← machine.run (fuel := 20000) fun _ => pure ()
  let failure ← machine.save
  let _ ← machine.run (fuel := 15000) fun _ => pure ()
  machine.restore failure
  assertEqual "a machine put back is where what it was put back to was" 20000 (← machine.position)
  machine.stepBack 5000
  assertTrue "a step back from what was put back is where that run was" ((← stateOf machine) == (← at_ 15000))

private def cffKernel (triple : String) (key : Char) : IO Bap.Linux.Kernel := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-cff"
  let data := "AB".toUTF8 ++ String.toUTF8 (String.singleton key) ++ "DEFGHIJKLMNOP".toUTF8
  pure ((Bap.Linux.Kernel.empty.addFile "/test" program).addFile "/data" data)

/-- Where the program says its dispatcher, state, record, verdict and sum are. -/
private def cffAddresses (triple : String) : IO (Nat × Nat × Nat × Nat × Nat) := do
  let machine ← Bap.Linux.start (← cffKernel triple 'C') "/test" ["/test"]
  let written ← IO.mkRef ByteArray.empty
  let _ ← machine.run fun data => written.modify (· ++ data)
  let lines := (String.fromUTF8! (← written.get)).splitOn "\n"
  let at_ (index : Nat) := hexOfLine (lines.getD index "")
  pure (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4)

/-- A flattened machine as it ran: its rounds, what each handler was, what they ask of the kernel, the rounds that come round again, which
thread and process each instruction was of, and what decided the round that a byte of a file chose. -/
def testCff (triple : String) : IO Unit := do
  let (dispatcher, state, _, _, _) ← cffAddresses triple
  let profile : Bap.Analysis.Cff.Profile := { dispatcher, state := .memory state 4, names := [(3, "asks"), (6, "ends")] }
  let run (key : Char) : IO (Bap.Analysis.Cff.Dispatcher × Nat × Bap.Analysis.Journal.Journal.Record) := do
    let machine ← Bap.Linux.start (← cffKernel triple key) "/test" ["/test"]
    let main ← Bap.Emu.thread machine.emu
    let journal ← machine.journal
    let tracker ← machine.track
    let recorder ← Bap.Analysis.Cff.Recorder.attach machine.emu profile
    let outcome ← machine.run fun _ => pure ()
    assertEqual s!"Cff {triple} the program ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    let record ← journal.toRecord
    let recovered ← Bap.Analysis.Cff.recoverIn machine.emu profile (← recorder.visits.get) (some record)
    pure (← Bap.Analysis.Cff.withPredicates recovered tracker journal, main, record)
  let (taken, main, record) ← run 'C'
  assertTrue s!"Cff {triple} all the rounds are known" taken.complete
  let states := taken.transitions.map (·.state)
  assertEqual s!"Cff {triple} the rounds start as they do" [1, 2, 3, 5] (states.take 4)
  assertEqual s!"Cff {triple} the last round ends it" (some 6) states.getLast?
  assertTrue s!"Cff {triple} rounds come round again" (taken.cycles.any fun cycle => cycle.states == [1, 2, 3, 5] && cycle.repeats ≥ 2)
  assertTrue s!"Cff {triple} a byte of the file chose 3" (taken.graph.any fun (from_, to, _) => from_ == 2 && to == 3)
  assertTrue s!"Cff {triple} and not 4" (!taken.graph.any fun (from_, to, _) => from_ == 2 && to == 4)
  let entries := taken.handlers.filterMap fun handler => if handler.state ≤ 5 then handler.entries.head? else none
  assertEqual s!"Cff {triple} each handler has where it starts" 4 entries.length
  assertEqual s!"Cff {triple} and they are different places" entries.length entries.eraseDups.length
  assertTrue s!"Cff {triple} no handler starts in the dispatcher" (!entries.any taken.dispatch.contains)
  let handlerOf (state : Nat) := taken.handlers.find? (·.state == state)
  assertTrue s!"Cff {triple} the handler that asks the kernel does" ((handlerOf 3).any fun handler => !handler.services.isEmpty)
  assertTrue s!"Cff {triple} the one that doesn't, doesn't" ((handlerOf 1).any (·.services.isEmpty))
  assertEqual s!"Cff {triple} a handler has its name" (some "asks") ((handlerOf 3).bind (·.name))
  assertTrue s!"Cff {triple} a handler has where its rounds end" ((handlerOf 1).any fun handler => !handler.exits.isEmpty)
  assertTrue s!"Cff {triple} the rounds are of the thread that runs the machine" (taken.transitions.all (·.thread == main))
  let others := record.history.filter (·.thread != main)
  assertTrue s!"Cff {triple} another thread ran" (others.size > 0)
  let group := (record.history.find? (·.thread == main)).map (·.group)
  assertTrue s!"Cff {triple} and it is of the same process" (others.all fun entry => some entry.group == group)
  let chooser := taken.transitions.find? fun transition => transition.state == 2
  let sources := (chooser.bind (·.predicate)).map (·.sources) |>.getD []
  assertTrue s!"Cff {triple} what decided a round is the byte of the file: {sources}" (sources.contains ("pread /data", some 2))
  -- What assigned each next state, which is the store to it, and of the round of 5, which chooses 6 or 1 without a branch on AArch64.
  assertTrue s!"Cff {triple} each round that went on knows what assigned its next state"
    (taken.transitions.all fun transition => transition.next.isNone || transition.assignment.isSome)
  if triple == "aarch64" then
    let chose := taken.transitions.filter fun transition => transition.state == 5 && transition.next.isSome
    assertTrue s!"Cff {triple} a state chosen by a condition is known to be: {repr (chose.head?.bind (·.assignment))}"
      (!chose.isEmpty && chose.all fun transition => transition.assignment.any fun assignment =>
        assignment.conditional && !assignment.condition.isEmpty)
  let (other, _, _) ← run 'D'
  assertTrue s!"Cff {triple} another byte chooses 4" (other.graph.any fun (from_, to, _) => from_ == 2 && to == 4)

/-- A verdict, and why: what it is, from the byte of the file that decided it; what of it no one wrote, which says that it was there when
the machine was put back from a checkpoint; and a round that went the wrong way, sliced back from where the dispatcher read its state. -/
def testVerdict (triple : String) : IO Unit := do
  let (dispatcher, state, record, verdictPoint, _) ← cffAddresses triple
  let profile : Bap.Analysis.Cff.Profile := { dispatcher, state := .memory state 4 }
  let trackers : IO.Ref (Option Bap.Analysis.DynamicTaint.Tracker) ← IO.mkRef none
  let journals : IO.Ref (Option Bap.Analysis.Journal.Journal) ← IO.mkRef none
  let models := [Bap.Linux.taintModel trackers, Bap.Linux.journalModel journals]
  let machine ← Bap.Linux.start (← cffKernel triple 'C') "/test" ["/test"] (models := models)
  let some tracker ← trackers.get | throw <| IO.userError "no tracker"
  let criteria : Bap.Analysis.Verdict.Criteria := { pc := verdictPoint, criteria := [.memory record 1, .memory (record + 3) 1] }
  let verdict ← Bap.Analysis.Verdict.captureVerdict machine criteria
  assertEqual s!"Verdict {triple} it is at the verdict" verdictPoint (← machine.emu.pc.get)
  let decided := verdict.values.headD (.memory 0 0, ByteArray.empty)
  assertTrue s!"Verdict {triple} the verdict is one" (decided.2.toList == ['P'.toNat.toUInt8] || decided.2.toList == ['F'.toNat.toUInt8])
  let report ← Bap.Analysis.Verdict.explain tracker machine verdict
  assertTrue s!"Verdict {triple} it comes from the byte that was added: {report.sources.map fun (l, o, _) => (l, o)}"
    (report.sources.any fun (label, offset, _) => label == "pread /data" && offset == some 5)
  -- What no one wrote, after going on from the checkpoint.
  let restored ← Bap.Linux.Machine.ofCheckpoint verdict.data (models := models)
  let some again ← trackers.get | throw <| IO.userError "no tracker after the checkpoint"
  let some journal ← journals.get | throw <| IO.userError "no journal after the checkpoint"
  let report ← Bap.Analysis.Verdict.explain again restored verdict
  let untouched := report.unresolved.filterMap fun unresolved => match unresolved.reason with
    | .untouched restoredFrom => if unresolved.criterion == 1 then some restoredFrom else none
    | _ => none
  assertTrue s!"Verdict {triple} what no one wrote says it was there when it was put back"
    (untouched.any fun restoredFrom => restoredFrom.any (·.2.startsWith "checkpoint"))
  assertTrue s!"Verdict {triple} the journal says what it went on from"
    ((← journal.loadedFrom.get).any (·.startsWith "checkpoint"))
  assertTrue s!"Verdict {triple} and where it came from is as it was" (report.sources.any fun (label, offset, _) => label == "pread /data" && offset == some 5)
  -- A round, sliced back from where its next state was read.
  let fresh ← Bap.Linux.start (← cffKernel triple 'C') "/test" ["/test"] (models := models)
  let some freshTracker ← trackers.get | throw <| IO.userError "no tracker"
  let transition : Bap.Analysis.Cff.Transition := { thread := ← Bap.Emu.thread fresh.emu, group := 0, index := 1, state := 2, next := some 3 }
  let atNext ← Bap.Analysis.Verdict.captureVerdict fresh (Bap.Analysis.Verdict.ofTransition profile transition)
  assertEqual s!"Verdict {triple} the next state is what was read" [3, 0, 0, 0]
    ((atNext.values.headD (.memory 0 0, ByteArray.empty)).2.toList.map (·.toNat) |> fun bytes => if bytes.head? == some 0 then bytes.reverse else bytes)
  let slice ← Bap.Analysis.Verdict.explain freshTracker fresh atNext
  assertTrue s!"Verdict {triple} a round comes from the byte that chose it"
    (slice.sources.any fun (label, offset, _) => label == "pread /data" && offset == some 2)

/-- What a handler does, as a contract, without changing the machine, and a replacement checked against it. -/
def testContract (triple : String) : IO Unit := do
  let (dispatcher, state, _, _, sum) ← cffAddresses triple
  let profile : Bap.Analysis.Cff.Profile := { dispatcher, state := .memory state 4 }
  let machine ← Bap.Linux.start (← cffKernel triple 'C') "/test" ["/test"]
  let _ ← Bap.Analysis.Verdict.captureVerdict machine { pc := dispatcher, criteria := [] }
  let recorder ← Bap.Analysis.Contract.Recorder.attach machine
  let before ← stateOf machine
  let first ← Bap.Analysis.Contract.capture recorder profile
  assertTrue s!"Contract {triple} capturing leaves the machine as it was" ((← stateOf machine) == before)
  assertEqual s!"Contract {triple} the first round is of state 1 and leaves 2" (1, some 2) (first.state, first.next)
  assertTrue s!"Contract {triple} it changes the sum and the state: {first.writes.map (·.1)}"
    (first.writes.any (fun (address, _) => sum ≤ address && address < sum + 8) &&
      first.writes.any (fun (address, _) => state ≤ address && address < state + 4) &&
      first.writes.all (fun (address, _) => (sum ≤ address && address < sum + 8) || (state ≤ address && address < state + 4)))
  assertTrue s!"Contract {triple} it asks nothing" first.services.isEmpty
  assertTrue s!"Contract {triple} it ran something" (first.instructions > 0)
  let big := machine.architecture.big
  let word (value size : Nat) : ByteArray :=
    let bytes := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
    ByteArray.mk (if big then bytes.reverse else bytes).toArray
  let width := machine.architecture.bits / 8
  let replacement (add : Nat) (machine : Bap.Linux.Machine) : IO Unit := do
    let current ← machine.read sum width
    let ordered := if big then current.toList else current.toList.reverse
    let value := ordered.foldl (fun value byte => value * 256 + byte.toNat) 0
    machine.write sum (word (value + add) width)
    machine.write state (word 2 4)
  let right ← Bap.Analysis.Contract.verify recorder profile (replacement 3)
  assertEqual s!"Contract {triple} a replacement that does the same is the same" [] right.differences
  let wrong ← Bap.Analysis.Contract.verify recorder profile (replacement 4)
  assertTrue s!"Contract {triple} one that doesn't is told apart: {wrong.differences}" (!wrong.differences.isEmpty)
  assertTrue s!"Contract {triple} verifying leaves the machine as it was" ((← stateOf machine) == before)
  -- The round that asks the kernel, two visits later.
  Bap.Emu.resumeThread machine.emu (← Bap.Emu.thread machine.emu)
  let _ ← Bap.Analysis.Verdict.captureVerdict machine { pc := dispatcher, criteria := [], hit := 2 }
  let asking ← Bap.Analysis.Contract.capture recorder profile
  assertEqual s!"Contract {triple} the third round is of state 3" 3 asking.state
  assertTrue s!"Contract {triple} and it asks the kernel" (!asking.services.isEmpty)

/-- What a machine has loaded, by what the files were and whether their initializers ran, and a checkpoint that hasn't what is expected. -/
def testManifest : IO Unit := do
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/aarch64-linux-musl-{name}"
  let dep ← binary "libdep"
  let other ← binary "libother"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files")).addFile "/lib/libdep.so" dep |>.addFile "/lib/libother.so" other
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let _ ← machine.loadLibrary "libdep.so"
  let _ ← machine.loadLibrary "libother.so" (runInitializers := false)
  let manifest ← machine.manifest
  let entry (path : String) := (manifest.find? (·.2.path == path)).map (·.2)
  let digest (data : ByteArray) := Bap.Linux.targetDigest machine.architecture data
  assertEqual "a library is known by what its file was" (some (digest dep)) ((entry "/lib/libdep.so").map (·.digest))
  assertEqual "one whose initializers ran says so" (some true) ((entry "/lib/libdep.so").map (·.initialized))
  assertEqual "one whose initializers didn't says so" (some false) ((entry "/lib/libother.so").map (·.initialized))
  -- A symbol that the library doesn't export is found in its file, and one that it does is where `findSymbol` says.
  let some depLibrary := entry "/lib/libdep.so" | throw <| IO.userError "no libdep"
  let some otherLibrary := entry "/lib/libother.so" | throw <| IO.userError "no libother"
  assertEqual "a symbol that isn't exported is found" (some (depLibrary.base + 0x1040c)) (← machine.findStaticSymbol "dep_stop")
  assertEqual "and isn't by what exports have" none (← machine.findSymbol "dep_stop")
  assertEqual "an exported one is where it is exported" (← machine.findSymbol "dep_add") (← machine.findStaticSymbol "dep_add")
  assertEqual "it is found in the library asked for" (some (depLibrary.base + 0x1040c)) (← machine.findStaticSymbol "dep_stop" (some depLibrary))
  assertEqual "and not in another" none (← machine.findStaticSymbol "dep_stop" (some otherLibrary))
  assertEqual "a symbol that is nowhere isn't found" none (← machine.findStaticSymbol "no_such_symbol")
  let data ← machine.checkpoint
  let again ← Bap.Linux.Machine.ofCheckpoint data (expectedLibraries := [digest dep, digest other])
  assertEqual "a checkpoint has what was loaded" manifest.length (← again.manifest).length
  let refused ← try let _ ← Bap.Linux.Machine.ofCheckpoint data (expectedLibraries := [digest dep + 1]); pure false catch _ => pure true
  assertTrue "a checkpoint without what is expected is refused" refused

/-- What the host does between runs is undone by stepping back before it and kept after it; a breakpoint stays and stops it again where it did; and what it doesn't have it says. -/
def testStepBackHost : IO Unit := do
  let program ← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-memory"
  let start : IO Bap.Linux.Machine := do
    Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let machine ← start
  assertThrows "a machine that keeps nothing can't step back" (machine.stepBack 1)
  machine.keepHistory (every := 1000)
  let _ ← machine.run (fuel := 5000) fun _ => pure ()
  let before ← stateOf machine
  let block ← machine.malloc 16
  machine.write block "edited".toUTF8
  let _ ← machine.run (fuel := 2000) fun _ => pure ()
  machine.stepBack 1000
  assertEqual "what the host wrote is there after it wrote it" "edited".toUTF8.toList (← machine.read block 6).toList
  machine.stepBack 1000
  assertEqual "it is where the host wrote it" 5000 (← machine.position)
  assertEqual "what the host wrote stays at the place where it wrote it" "edited".toUTF8.toList (← machine.read block 6).toList
  machine.stepBack 1
  let undone ← start
  let _ ← undone.run (fuel := 4999) fun _ => pure ()
  assertTrue "a step back before what the host did is as if it hadn't" ((← stateOf machine) == (← stateOf undone))
  assertThrows "it can't step back further than it ran" (machine.stepBack 5000)
  -- A breakpoint where it went stops it there again, and isn't where it stops when it runs again what it ran.
  let _ ← machine.run (fuel := 3000) fun _ => pure ()
  let pc ← machine.emu.pc.get
  let place ← machine.position
  machine.stepBack 2500
  let _ ← Bap.Emu.addBreakpoint machine.emu pc
  machine.stepBack 100
  assertEqual "a breakpoint doesn't stop what runs again" (place - 2600) (← machine.position)
  let outcome ← machine.run fun _ => pure ()
  assertTrue s!"a breakpoint stops it where it went: {repr outcome}" (outcome matches .stopped _)
  assertTrue "where the breakpoint is" ((← machine.position) ≤ place)
  let _ := before

/-- A record of a flattened machine of `rounds` rounds, of five states that come round in order, each round running the dispatcher, three
instructions that all do and five of its own, and the third state asking the kernel once. -/
def cffSynthetic (rounds : Nat) : Array Bap.Analysis.Cff.Visit × Bap.Analysis.Journal.Journal.Record := Id.run do
  let mut visits : Array Bap.Analysis.Cff.Visit := #[]
  let mut history : Array Bap.Analysis.Journal.Executed := #[]
  let mut events : Array Bap.Analysis.Journal.Event := #[]
  let mut seq := 0
  for round in List.range rounds do
    let state := round % 5 + 1
    visits := visits.push { thread := 1, group := 1, state }
    let pcs := [0x1000, 0x1004, 0x1008, 0x100c] ++ (List.range 5).map fun offset => 0x2000 + state * 0x100 + offset * 4
    for pc in pcs do
      history := history.push { seq, thread := 1, group := 1, index := seq, pc }
      if state == 3 && pc == 0x2300 then
        events := events.push (.service seq 1 events.size pc "getpid" [] (some 1) 0)
      seq := seq + 1
  pure (visits, { history, droppedHistory := 0, events, droppedEvents := 0 })

/-- What the host holds of its memory now, in bytes. -/
private def residentBytes : IO Nat := do
  let fields := (← IO.FS.readFile "/proc/self/statm").splitOn " "
  pure ((fields.getD 1 "0").toNat?.getD 0 * 4096)

/-- A mapping much bigger than what a program uses takes memory of the host for what it uses: when it is mapped, cut up, kept by `save`
and put back. And the program finds what it wrote and zeros elsewhere. -/
def testSparseMapping (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-sparse"
  -- Where it stops to be looked at, by its symbol, as running it to find out would leave what it held to the next run.
  let image ← IO.ofExcept (Bap.Image.Elf.decode program)
  let some symbol := image.symbols.find? (·.name == "pause_point") | throw <| IO.userError "no pause_point"
  let pausePoint := symbol.addr
  let before ← residentBytes
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let written ← IO.mkRef ByteArray.empty
  let breakpoint ← Bap.Emu.addBreakpoint machine.emu pausePoint
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertTrue s!"Sparse {triple} it comes to where it is looked at: {repr outcome}" (outcome matches .stopped _)
  let mapped ← residentBytes
  assertTrue s!"Sparse {triple} a big mapping takes little of the host: {(mapped - before) / 1048576} MB" (mapped < before + 128 * 1048576)
  let saved ← machine.save
  let kept ← residentBytes
  assertTrue s!"Sparse {triple} keeping it takes little of the host: {(kept - mapped) / 1048576} MB" (kept < mapped + 128 * 1048576)
  machine.restore saved
  let restored ← residentBytes
  assertTrue s!"Sparse {triple} putting it back takes little of the host: {(restored - kept) / 1048576} MB" (restored < kept + 128 * 1048576)
  -- A checkpoint has what isn't zeros of it, and a machine of the checkpoint takes as little of the host and goes on as the program would.
  let data ← machine.checkpoint
  assertTrue s!"Sparse {triple} a checkpoint of it is small: {data.size / 1048576} MB" (data.size < 16 * 1048576)
  let loading ← residentBytes
  let copy ← Bap.Linux.Machine.ofCheckpoint data
  let loaded ← residentBytes
  assertTrue s!"Sparse {triple} a machine of the checkpoint takes little of the host: {(loaded - loading) / 1048576} MB"
    (loaded < loading + 128 * 1048576)
  Bap.Emu.removeBreakpoint copy.emu pausePoint
  Bap.Emu.resumeThread copy.emu (← Bap.Emu.thread copy.emu)
  let copied ← IO.mkRef ByteArray.empty
  let outcome ← copy.run fun data => copied.modify (· ++ data)
  assertEqual s!"Sparse {triple} the machine of the checkpoint ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  let lines := (String.fromUTF8! (← copied.get)).splitOn "\n"
  assertTrue s!"Sparse {triple} the machine of the checkpoint finds what was written and zeros elsewhere: {lines}"
    (lines.contains "y" && !lines.contains "n")
  Bap.Emu.removeHook machine.emu breakpoint
  Bap.Emu.resumeThread machine.emu (← Bap.Emu.thread machine.emu)
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Sparse {triple} it ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Sparse {triple} it finds what it wrote and zeros elsewhere" (some "y")
    (((String.fromUTF8! (← written.get)).splitOn "\n")[1]?)

/-- What takes time in proportion to what it does and not to what it has done before: when the work is four times as much it takes about four times as long, and sixteen if it goes through all that
went before. Each is run alone, as what a test measures isn't to be what the others are doing. -/
def scaling : IO Unit := do
  let program ← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-scale"
  let time (mode : String) (arguments : List String) (prepare : Bap.Linux.Machine → IO Unit := fun _ => pure ()) : IO Nat := do
    let kernel := Bap.Linux.Kernel.empty.addFile "/test" program
    let machine ← Bap.Linux.start kernel "/test" (["/test", mode] ++ arguments)
    prepare machine
    let started ← IO.monoMsNow
    let outcome ← machine.run (fuel := 2000000000) fun _ => pure ()
    assertEqual s!"scaling {mode} ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    pure ((← IO.monoMsNow) - started)
  let grows (name mode : String) (small : Nat) (prepare : Bap.Linux.Machine → IO Unit := fun _ => pure ()) : IO Unit := do
    let first ← time mode [toString small] prepare
    let second ← time mode [toString (small * 4)] prepare
    assertTrue s!"{name} takes about 4 times as long for 4 times as much, not 16: {first} ms and {second} ms" (second ≤ 9 * max first 50)
  -- Mappings much bigger than what is used, measured by what the host holds, which is why they are here, run alone.
  for triple in ["aarch64", "x86_64", "mips"] do testSparseMapping triple
  grows "mappings" "m" 1000
  grows "growing the break" "b" 1000
  grows "making files" "f" 1000
  grows "reading a directory" "l" 2000
  grows "calls under a journal" "d" 5000 fun machine => do let _ ← machine.journal
  grows "calls under taint" "d" 5000 fun machine => do let _ ← machine.track
  grows "mappings under taint" "m" 300 fun machine => do let _ ← machine.track
  let holds (name mode : String) (small : Nat) : IO Unit := do
    let first ← time mode ["2000", toString small]
    let second ← time mode ["2000", toString (small * 16)]
    assertTrue s!"{name} takes no longer for what is already there: {first} ms and {second} ms" (second ≤ 3 * max first 100 + 400)
  holds "writing to a file" "g" 1000000
  holds "reading a pipe" "q" 1000000
  -- What analyses a record does: it goes through the rounds, instructions and events of it a few times.
  let profile : Bap.Analysis.Cff.Profile := { dispatcher := 0x1000, state := .memory 0 4 }
  let recovering (rounds : Nat) : IO Nat := do
    let (visits, record) := cffSynthetic rounds
    let started ← IO.monoMsNow
    let dispatcher := Bap.Analysis.Cff.recover profile visits (some record)
    assertEqual s!"recovering {rounds} rounds has them all" rounds dispatcher.transitions.length
    pure ((← IO.monoMsNow) - started)
  let first ← recovering 8000
  let second ← recovering 32000
  assertTrue s!"recovering a flattened machine takes about 4 times as long for 4 times as much: {first} ms and {second} ms" (second ≤ 9 * max first 50)
  let grouping (count : Nat) : IO Nat := do
    let addresses := (List.range count).map (· * 3 % count)
    let started ← IO.monoMsNow
    let runs := Bap.Analysis.Contract.changes (fun _ => some 0) (fun address => some (address % 7).toUInt8) addresses
    assertTrue s!"grouping {count} addresses finds what changed" (!runs.isEmpty)
    pure ((← IO.monoMsNow) - started)
  let first ← grouping 64000
  let second ← grouping 256000
  assertTrue s!"grouping what a contract changed takes about 4 times as long for 4 times as much: {first} ms and {second} ms" (second ≤ 9 * max first 50)
  -- Comparing runs goes through what ran once, however many threads ran it.
  let comparing (threads : Nat) : IO Nat := do
    let history := (Array.range 400000).map fun seq =>
      ({ seq, thread := seq % threads, group := 1, index := seq / threads, pc := seq % 97 } : Bap.Analysis.Journal.Executed)
    let record : Bap.Analysis.Journal.Journal.Record := { history, droppedHistory := 0, events := #[], droppedEvents := 0 }
    let started ← IO.monoMsNow
    let difference := Bap.Analysis.Journal.Journal.compare record record
    assertTrue s!"comparing a run of {threads} threads with itself finds nothing" difference.branch.isNone
    pure ((← IO.monoMsNow) - started)
  let few ← comparing 50
  let many ← comparing 800
  assertTrue s!"comparing runs takes no longer for more threads: {few} ms and {many} ms" (many ≤ 3 * max few 50)

/-- What is done in place is what it was instead of, and a mapping goes where it always went, wherever it starts looking. -/
def testScalingEquivalents : IO Unit := do
  let random ← IO.mkRef (0x2545F4914F6CDD1D : UInt64)
  let next (bound : Nat) : IO Nat := do
    let value ← random.get
    let value := value ^^^ (value <<< 13)
    let value := value ^^^ (value >>> 7)
    let value := value ^^^ (value <<< 17)
    random.set value
    pure (value.toNat % bound)
  let mut data := ByteArray.empty
  for _ in List.range 2000 do
    let offset ← next 300
    let size ← next 40
    let bytes := ByteArray.mk ((Array.range size).map fun index => (index + offset).toUInt8)
    let expected := Bap.Linux.Kernel.writeAt data offset bytes
    data := Bap.Linux.Kernel.writeInto data offset bytes
    assertEqual s!"a write in place at {offset} of {size} is a write" expected.toList data.toList
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-scale")) "/test" ["/test", "x", "0"]
  let emu := machine.emu
  let mut held : List Nat := []
  for _ in List.range 400 do
    let size := ((← next 6) + 1) * 4096
    let regions ← emu.regions.get
    let width ← Bap.Emu.wordWidth emu
    let base := if width == 32 then 0x70000000 else 0x7f0000000000
    let taken := ((regions.map fun region => (region.address, region.data.size)).toArray.qsort fun left right => left.1 > right.1).toList
    let expected := Bap.Tasks.gapBelow size base (taken.filter (·.1 < base))
    assertEqual "a mapping goes where it did" expected (← Bap.Emu.freeAddress emu size)
    if (← next 3) == 0 && !held.isEmpty then
      let which := (← next held.length)
      let address := held.getD which 0
      Bap.Emu.unmap emu address 4096
      held := held.eraseIdx which
    else
      let address ← Bap.Emu.placeMapping emu 0 false (Bap.zeroBytes size) 3
      assertEqual "it is put there" expected address
      held := address :: held
    let tree ← Bap.Emu.regionTree emu
    assertEqual "what is indexed is what is mapped" (((← emu.regions.get).filter (·.data.size != 0)).map (·.address) |>.toArray.qsort (· < ·)).toList tree.keys

/-- Native code of each architecture calls JNI by its own convention, and what it gets is what the model says: results of each width,
arguments past the registers, strings, objects and the VM, and a method's arguments of each kind in each form of each kind of call,
as a variadic function, a `va_list` and an array of `jvalue` have them. `floats` is whether this serves floating-point results there. -/
def testJniNative (triple : String) (floats : Bool := true) : IO Unit := do
  let label := s!"JNI {triple}"
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-jni-native"
  let image ← IO.ofExcept (Bap.Image.Elf.decode program)
  let some run := image.symbols.find? (·.name == "run") | throw <| IO.userError s!"{label} has no run"
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let place (bytes : ByteArray) : IO Nat := do
    let address ← machine.malloc (bytes.size + 1)
    machine.write address (bytes.push 0)
    pure address
  let arg := Bap.Emu.Jni.arg
  let method (name signature : String) (answer : Bap.Emu.Jni.Call → Bap.Emu.Jni.Answer) : Bap.Emu.Jni.MethodDecl :=
    { name, signature, answer := fun call => pure (answer call) }
  -- A bit of each argument that is what native code gave, of `-7, 0x123456789abcdef0, 2.5, 1.25f, self, (jbyte)-3, (jshort)-300,
  -- (jchar)0xBEEF`, after the method's ID, which `CallNonvirtual` has after the class.
  let self ← IO.mkRef 0
  let mixed (name : String) : Bap.Emu.Jni.MethodDecl := {
    name, signature := "(IJDFLjava/lang/Object;BSC)I"
    answer := fun call => do
      let first := if call.index ≥ 64 && call.index ≤ 93 then 4 else 3
      let expected := [2 ^ 32 - 7, 0x123456789abcdef0, 0x4004000000000000, 0x3FA00000, ← self.get, 2 ^ 32 - 3, 2 ^ 32 - 300, 0xBEEF]
      pure (.value (expected.zipIdx.foldl (fun bits (value, index) =>
        if arg call (first + index) == value then bits ||| 2 ^ index else bits) 0)) }
  let thing : Bap.Emu.Jni.ClassDecl := {
    name := "example/Thing"
    methods := [
      method "twice" "(I)I" fun call => .value (arg call 3 % 2 ^ 32 * 2),
      method "wide" "()J" fun _ => .value 0x123456789abcdef0,
      method "half" "()D" fun _ => .value 0x4004000000000000,
      method "quarter" "()F" fun _ => .value 0x3FA00000,
      mixed "mix"]
    staticMethods := [method "sum" "(IIIII)I" fun call => .value (((List.range 5).map fun index => arg call (3 + index)).foldl (· + ·) 0),
      mixed "mixStatic"] }
  let model ← Bap.Emu.Jni.create (Bap.Emu.Jni.readCString machine.emu) (fun text => place text.toUTF8) place
    (fun _ _ => pure (.value 0)) (classes := [thing]) (big := machine.architecture.big)
  let layout ← Bap.Emu.Jni.attachAt model machine.emu
  let selfHandle ← Bap.Emu.Jni.intern model 0x9001
  self.set selfHandle
  -- The address of a function of Thumb says so in its lowest bit, which the symbol has apart.
  let found ← machine.call (run.addr + if run.thumb then 1 else 0) [layout.env, selfHandle]
  let all := 0x3FFFF
  let expected := if floats then all else all - 8 - 16
  assertEqual s!"{label} native code finds what the model says, by its convention" expected found

/-- `java/io/File` of a JNI model, from the files of a machine: paths, what is in a directory as a `File[]`, a child of a directory, what
isn't there, a file's length, and the path of a file after a checkpoint of the model. -/
def testJniFiles : IO Unit := do
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-files"))
    |>.addFile "/data/app/one.txt" "hello".toUTF8
    |>.addFile "/data/app/two.txt" "hi".toUTF8
    |>.addDirectories "/data/app/sub"
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let texts : List (Nat × String) := [(0x100, "java/io/File"), (0x110, "<init>"), (0x120, "(Ljava/lang/String;)V"),
    (0x130, "(Ljava/io/File;Ljava/lang/String;)V"), (0x140, "/data/app"), (0x150, "missing"), (0x160, "isDirectory"), (0x170, "()Z"),
    (0x180, "listFiles"), (0x190, "()[Ljava/io/File;"), (0x1a0, "getPath"), (0x1b0, "()Ljava/lang/String;"), (0x1c0, "exists"),
    (0x1d0, "length"), (0x1e0, "()J"), (0x1f0, "/data/app/one.txt")]
  let make : IO Bap.Emu.Jni.Model := Bap.Emu.Jni.create (fun address => pure ((texts.lookup address).getD ""))
    (fun _ => pure 0x52040000) (fun _ => pure 0x52050000) (fun _ _ => pure (.value 0)) (files := some machine.jniFiles)
  let model ← make
  let call (index : Nat) (args : List Nat) : IO Nat := Bap.Emu.Jni.dispatch model ⟨index, (0 :: args).toArray⟩
  let file ← call 6 [0x100]
  let method (name signature : Nat) : IO Nat := call 33 [file, name, signature]
  let ofPath ← method 0x110 0x120
  let ofParent ← method 0x110 0x130
  let directory ← call 28 [file, ofPath, ← call 167 [0x140]]
  let pathOf (handle : Nat) : IO (Option String) := do
    Bap.Emu.Jni.stringContents model (← call 34 [handle, ← method 0x1a0 0x1b0])
  assertEqual "JNI a File has its path" (some "/data/app") (← pathOf directory)
  assertEqual "JNI a directory is one" 1 (← call 37 [directory, ← method 0x160 0x170])
  let listed ← call 34 [directory, ← method 0x180 0x190]
  let count ← call 171 [listed]
  assertEqual "JNI what is in it, as a File[]" 3 count
  let children ← (List.range count).mapM fun index => do pathOf (← call 173 [listed, index])
  assertEqual "JNI each with its whole path"
    [some "/data/app/one.txt", some "/data/app/sub", some "/data/app/two.txt"] children
  assertEqual "JNI and each a File" 1 (← call 24 [← call 31 [← call 173 [listed, 0]], file])
  let missing ← call 28 [file, ofParent, directory, ← call 167 [0x150]]
  assertEqual "JNI a child of a directory has its whole path" (some "/data/app/missing") (← pathOf missing)
  assertEqual "JNI what isn't there isn't" 0 (← call 37 [missing, ← method 0x1c0 0x170])
  let one ← call 28 [file, ofPath, ← call 167 [0x1f0]]
  assertEqual "JNI a file has its length" 5 (← call 52 [one, ← method 0x1d0 0x1e0])
  -- Into a checkpoint of the model and out, with the path of each.
  let saved ← (Bap.Emu.Jni.state model).save
  let again ← make
  (Bap.Emu.Jni.state again).load saved
  let getPath ← Bap.Emu.Jni.dispatch again ⟨33, #[0, file, 0x1a0, 0x1b0]⟩
  assertEqual "JNI a File has its path after a checkpoint" (some "/data/app")
    (← Bap.Emu.Jni.stringContents again (← Bap.Emu.Jni.dispatch again ⟨34, #[0, directory, getPath]⟩))

/-- What JNI gives a guest is a source, in the register it comes back in and in memory, and so is what someone says is one. -/
def testTaintSources : IO Unit := do
  let kernel := Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile "testsuite/bin/aarch64-linux-musl-libc-taint")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let tracker ← machine.track
  let model ← Bap.Emu.Jni.create (fun _ => pure "example/Class") (fun _ => pure 0x52040000) (fun _ => pure 0x52050000)
    (fun _ _ => pure (.value 0))
  let setRegister (name : String) (value : Nat) : IO Unit :=
    Bap.Emu.setReg machine.emu ⟨name, .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 value))
  setRegister "X8" 6
  setRegister "X1" 0x100
  Bap.Emu.Jni.serve model machine.emu
  let labelOf (explanation : Bap.Analysis.DynamicTaint.Tracker.Explanation) : List String :=
    explanation.sources.filterMap fun (node, _, _) => match node.kind with
      | .source label _ => some label
      | _ => none
  assertEqual "JNI gives a source in its register" ["jni:6 result"] (labelOf (← tracker.explainRegister "X0"))
  let sp ← Bap.Emu.reg machine.emu ⟨"SP", .imm 64, 0, false⟩
  let place := match Bap.Value.asBits sp with
    | .ok bits => bits.2.toNat
    | .error _ => 0
  setRegister "X8" 219
  setRegister "X1" place
  Bap.Emu.Jni.serve model machine.emu
  assertEqual "JNI gives a source in memory" ["jni:219"] (labelOf (← tracker.explainMemory place))
  tracker.markMemory place 2 "mine" (some 100)
  let marked ← tracker.explainMemory (place + 1)
  assertEqual "What is marked is a source, by the byte" [some 101] (marked.sources.map fun (node, byte, _) => match node.kind with
    | .source _ offset => offset.map (· + byte)
    | _ => none)
  assertEqual "A byte beside what is marked isn't" ["jni:219"] (labelOf (← tracker.explainMemory (place + 2)))

/-- The allocator alone, on a long run of what it can be asked: blocks are aligned, within what is mapped and apart from each other, and
when all have gone back so has all that was mapped, in mappings that may touch. -/
def testGuestHeap : IO Unit := do
  let random ← IO.mkRef (0x9E3779B97F4A7C15 : UInt64)
  let next : IO Nat := do
    let value ← random.get
    let value := value ^^^ (value <<< 13)
    let value := value ^^^ (value >>> 7)
    let value := value ^^^ (value <<< 17)
    random.set value
    pure value.toNat
  let mut heap : Bap.Linux.GuestHeap := {}
  let mut live : List (Nat × Nat) := []
  -- Where the next mapping goes: right after the last, or apart from it.
  let mut cursor := 0x10000
  let mut mapped := 0
  let mut unmapped := 0
  for round in [0:6000] do
    if (← next) % 5 < 3 then
      let kind := (← next) % 8
      let drawn ← next
      let size := match kind with
        | 0 => 0
        | 1 => drawn % 200000
        | _ => drawn % 3000
      let mut prepared := heap
      if (prepared.alloc size).isNone then
        let mapping := Bap.Linux.GuestHeap.mappingFor size
        prepared := prepared.addChunk cursor mapping
        cursor := cursor + mapping + (if (← next) % 2 == 0 then 0 else 4096)
        mapped := mapped + 1
      match prepared.alloc size with
      | none => throw <| IO.userError s!"Guest heap has no room for {size} after mapping it"
      | some (address, updated) =>
        heap := updated
        let wanted := max size 1
        if address % 16 != 0 then throw <| IO.userError s!"Guest heap gave {address}, which isn't aligned"
        unless heap.chunks.any (fun chunk => chunk.1 ≤ address && address + wanted ≤ chunk.1 + chunk.2) do
          throw <| IO.userError s!"Guest heap gave {address}, which isn't in what it has mapped"
        if live.any (fun block => address < block.1 + block.2 && block.1 < address + wanted) then
          throw <| IO.userError s!"Guest heap gave {address} of {wanted} in round {round}, which is in use"
        live := (address, wanted) :: live
    else if !live.isEmpty && (← next) % 3 == 0 then
      -- Another size where it is, if it can have that: to nothing that is another's.
      let index := (← next) % live.length
      let block := live[index]!
      let size := (← next) % 4000
      let wanted := max size 1
      if let some updated := heap.resize block.1 size then
        heap := updated
        if !heap.chunks.any (fun chunk => chunk.1 ≤ block.1 && block.1 + wanted ≤ chunk.1 + chunk.2) then
          throw <| IO.userError s!"Guest heap resized {block.1} out of what it has mapped"
        if (live.eraseIdx index).any (fun other => block.1 < other.1 + other.2 && other.1 < block.1 + wanted) then
          throw <| IO.userError s!"Guest heap resized {block.1} over another, in round {round}"
        live := live.set index (block.1, wanted)
    else if !live.isEmpty then
      let index := (← next) % live.length
      let block := live[index]!
      match heap.release block.1 with
      | none => throw <| IO.userError s!"Guest heap refused its own {block.1}"
      | some (updated, empty) =>
        heap := updated
        if let some (first, size) := empty then
          unmapped := unmapped + 1
          if live.any (fun other => other != block && other.1 < first + size && first < other.1 + other.2) then
            throw <| IO.userError s!"Guest heap gave back what has a block in it, in round {round}"
        live := live.eraseIdx index
        if (heap.release block.1).isSome then throw <| IO.userError s!"Guest heap took {block.1} twice"
    -- What is free is in order, and touches only where a mapping starts.
    for pair in heap.free.zip (heap.free.drop 1) do
      unless pair.1.1 + pair.1.2 < pair.2.1 || (pair.1.1 + pair.1.2 == pair.2.1 && heap.chunks.any (·.1 == pair.2.1)) do
        throw <| IO.userError s!"Guest heap has free ranges that touch or are out of order, in round {round}"
  for block in live do
    match heap.release block.1 with
    | some (updated, _) => heap := updated
    | none => throw <| IO.userError s!"Guest heap refused its own {block.1}"
  assertEqual "Guest heap with everything back has nothing" (([] : List (Nat × Nat)), ([] : List (Nat × Nat)), ([] : List (Nat × Nat)))
    (heap.chunks, heap.free, heap.used)
  assertTrue s!"Guest heap mapped and unmapped: {mapped} {unmapped}" (mapped > 10 && unmapped > 10)

/-- Reading and writing the memory of a guest, and allocating in it, from outside it, on a real program. -/
def testMachineMemory (triple : String) : IO Unit := do
  let file (name : String) : IO Bap.Linux.Kernel := do
    pure (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"))
  let label := s!"Machine {triple}"
  let silent (_ : ByteArray) : IO Unit := pure ()
  let collected (machine : Bap.Linux.Machine) : IO (Bap.Tasks.ScheduleOutcome × String) := do
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => written.modify (· ++ data)
    pure (outcome, String.fromUTF8! (← written.get))
  let kernel ← file "libc-files"
  let expected ← collected (← Bap.Linux.start kernel "/test" ["/test", "arg1"])
  let machine ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
  let _ ← machine.run (fuel := 5000) silent
  -- What is allocated can be written and read, and blocks are apart.
  let first ← machine.malloc 100
  let second ← machine.malloc 100
  assertEqual s!"{label} a block is aligned" 0 (first % 16)
  assertTrue s!"{label} blocks are apart" (first + 100 ≤ second || second + 100 ≤ first)
  let data := ByteArray.mk ((List.range 100).map fun index => (index + 1).toUInt8).toArray
  machine.write first data
  machine.write second (ByteArray.mk (Array.replicate 100 0xAB))
  assertEqual s!"{label} what is written is read" data.toList (← machine.read first 100).toList
  assertEqual s!"{label} a block is left alone by another" 0xAB (← machine.read second 1)[0]!.toNat
  -- Past what a chunk has, and more than one could.
  let large ← machine.malloc (3 * 1024 * 1024)
  machine.write (large + 3 * 1024 * 1024 - 8) (ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8])
  assertEqual s!"{label} a large block goes to its end" 8 (← machine.read (large + 3 * 1024 * 1024 - 1) 1)[0]!.toNat
  -- It goes back, and what was all free is unmapped.
  machine.free large
  expectThrow s!"{label} reading what was unmapped" (machine.read large 1)
  expectThrow s!"{label} a second free" (machine.free large)
  expectThrow s!"{label} a free in the middle of a block" (machine.free (first + 16))
  expectThrow s!"{label} a free of what it didn't give" (machine.free 0x1000)
  machine.free 0
  -- What can't be reached, or written, with nothing written then.
  expectThrow s!"{label} reading nowhere" (machine.read 8 4)
  expectThrow s!"{label} writing nowhere" (machine.write 8 (ByteArray.mk #[1]))
  expectThrow s!"{label} another process that isn't there" (machine.read first 1 (pid := some 99999))
  expectThrow s!"{label} an absurd block" (machine.malloc (2 ^ 40))
  let entry ← Bap.Emu.pc machine.emu
  expectThrow s!"{label} writing to code" (machine.write entry (ByteArray.mk #[0]))
  -- calloc: all zeros, also of what has been used, and nothing that is too much.
  let used ← machine.malloc 256
  machine.write used (ByteArray.mk (Array.replicate 256 0xCC))
  machine.free used
  let cleared ← machine.calloc 8 32
  assertEqual s!"{label} calloc clears what was used" (List.replicate 256 (0 : UInt8)) (← machine.read cleared 256).toList
  assertEqual s!"{label} calloc is aligned" 0 (cleared % 16)
  expectThrow s!"{label} calloc that overflows a word" (machine.calloc (2 ^ 40) (2 ^ 40))
  let none_ ← machine.calloc 0 8
  machine.free none_
  machine.free cleared
  -- realloc: what it has stays, smaller or larger, where it is if it can be.
  let pattern (size : Nat) : ByteArray := ByteArray.mk ((List.range size).map fun index => (index % 251 + 1).toUInt8).toArray
  let growing ← machine.malloc 64
  machine.write growing (pattern 64)
  let fence ← machine.malloc 16
  machine.free fence
  let grown ← machine.realloc growing 128
  assertEqual s!"{label} realloc stays if what is after it is free" growing grown
  assertEqual s!"{label} realloc in place keeps what it had" (pattern 64).toList (← machine.read grown 64).toList
  let shrunk ← machine.realloc grown 32
  assertEqual s!"{label} realloc to less stays" growing shrunk
  assertEqual s!"{label} realloc to less keeps what fits" (pattern 32).toList (← machine.read shrunk 32).toList
  -- With something right after it, it has to go elsewhere, and what it left is free.
  let neighbour ← machine.malloc 16
  machine.write neighbour (ByteArray.mk (Array.replicate 16 0x77))
  let blocked ← machine.malloc 32
  machine.write blocked (pattern 32)
  let barrier ← machine.malloc 16
  machine.write barrier (ByteArray.mk (Array.replicate 16 0x55))
  let movedBlock ← machine.realloc blocked 4096
  assertTrue s!"{label} realloc moves when it has to" (movedBlock != blocked)
  assertEqual s!"{label} realloc that moves keeps what it had" (pattern 32).toList (← machine.read movedBlock 32).toList
  assertEqual s!"{label} realloc leaves others alone" [0x55, 0x77] [(← machine.read barrier 1)[0]!.toNat, (← machine.read neighbour 1)[0]!.toNat]
  expectThrow s!"{label} what realloc moved from isn't a block" (machine.free blocked)
  -- More than any mapping has, across chunks, to its end.
  let huge ← machine.realloc movedBlock (1024 * 1024)
  assertEqual s!"{label} a large realloc keeps what it had" (pattern 32).toList (← machine.read huge 32).toList
  machine.write (huge + 1024 * 1024 - 1) (ByteArray.mk #[9])
  -- The edges.
  let fromNothing ← machine.realloc 0 48
  machine.write fromNothing (pattern 48)
  let toNothing ← machine.realloc fromNothing 0
  assertEqual s!"{label} realloc to nothing still has a block" fromNothing toNothing
  machine.free toNothing
  expectThrow s!"{label} realloc of what has gone back" (machine.realloc toNothing 16)
  expectThrow s!"{label} realloc of what it didn't give" (machine.realloc 0x1000 16)
  expectThrow s!"{label} realloc of too much" (machine.realloc huge (2 ^ 40))
  assertEqual s!"{label} a realloc that failed leaves it" (pattern 32).toList (← machine.read huge 32).toList
  -- A block that can't be read any more can't be moved, and stays a block, with nothing else left over.
  let guarded ← machine.malloc (128 * 1024)
  machine.write guarded (pattern 16)
  Bap.Emu.protect machine.emu guarded (128 * 1024 - (128 * 1024 % 4096)) ⟨false, false, false⟩
  expectThrow s!"{label} a move that can't read fails" (machine.realloc guarded (1024 * 1024))
  Bap.Emu.protect machine.emu guarded (128 * 1024 - (128 * 1024 % 4096)) ⟨true, true, false⟩
  assertEqual s!"{label} and the block is as it was" (pattern 16).toList (← machine.read guarded 16).toList
  machine.free guarded
  machine.free huge
  machine.free neighbour
  machine.free barrier
  machine.free shrunk
  -- Across mappings that touch it is written, and past them none of it is.
  Bap.Emu.map machine.emu ⟨0x50000000, ByteArray.mk (Array.replicate 4096 3), ⟨true, true, false⟩⟩
  expectThrow s!"{label} a write that runs off what is there" (machine.write 0x50000FFE (ByteArray.mk #[1, 2, 3, 4]))
  assertEqual s!"{label} nothing was written of that" [3, 3] (← machine.read 0x50000FFE 2).toList
  Bap.Emu.map machine.emu ⟨0x50001000, ByteArray.mk (Array.replicate 4096 3), ⟨true, true, false⟩⟩
  machine.write 0x50000FFE (ByteArray.mk #[1, 2, 3, 4])
  assertEqual s!"{label} a write goes across what touches" [1, 2, 3, 4] (← machine.read 0x50000FFE 4).toList
  -- Native memory and the state agree, and the program doesn't notice any of this.
  let saved ← machine.save
  let third ← machine.malloc 40
  machine.write third (ByteArray.mk #[9])
  machine.restore saved
  expectThrow s!"{label} a block that was gone back past" (machine.free third)
  assertEqual s!"{label} going back keeps what was there" 0xAB (← machine.read second 1)[0]!.toNat
  let data2 ← machine.checkpoint
  let resumed ← Bap.Linux.Machine.ofCheckpoint data2
  assertTrue s!"{label} saves again as it was" (data2 == (← resumed.checkpoint))
  assertEqual s!"{label} what was written is in a checkpoint" data.toList (← resumed.read first 100).toList
  let fourth ← resumed.malloc 100
  assertTrue s!"{label} a checkpoint knows what is given out"
    ((first + 100 ≤ fourth || fourth + 100 ≤ first) && (second + 100 ≤ fourth || fourth + 100 ≤ second))
  resumed.free first
  expectThrow s!"{label} a free after a checkpoint, twice" (resumed.free first)
  let (outcome, text) ← collected resumed
  assertEqual s!"{label} a program doesn't notice" expected.1 outcome
  assertTrue s!"{label} a program says what it would have" (expected.2.endsWith text)
  -- A program can't be told from one that nobody looked at: to the instruction, across its processes and threads.
  for name in ["libc-threads", "libc-fork"] do
    let kernel ← file name
    let run (looking : Bool) : IO (Bap.Tasks.ScheduleOutcome × List Nat × ByteArray) := do
      let machine ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
      Bap.Emu.traceStartCapacity machine.emu 100000000
      let written ← IO.mkRef ByteArray.empty
      let rec go : Nat → IO Bap.Tasks.ScheduleOutcome
        | 0 => throw <| IO.userError "more pieces than a run should have"
        | fuel + 1 => do
          let outcome ← machine.run (quantum := 13) (fuel := 811) fun data => written.modify (· ++ data)
          if outcome != .outOfFuel then return outcome
          if looking then
            let table ← machine.emu.taskTable.get
            let regions ← Bap.Emu.regions machine.emu
            for task in table.tasks do
              if task.status.isNone && task.tid == task.group then
                match regions.head? with
                | some (address, _, _) => let _ ← (machine.read address 1 (pid := some task.group)).toBaseIO
                | none => pure ()
          go fuel
      let outcome ← go 2000
      pure (outcome, ← Bap.Emu.traceStop machine.emu, ← written.get)
    let (plainOutcome, plainTrace, plainText) ← run false
    let (lookOutcome, lookTrace, lookText) ← run true
    assertEqual s!"{label} {name} ends the same looked at" plainOutcome lookOutcome
    assertEqual s!"{label} {name} says the same looked at" plainText.toList lookText.toList
    let different := (plainTrace.zip lookTrace).findIdx? fun (left, right) => left != right
    assertEqual s!"{label} {name} runs the same looked at" (plainTrace.length, none) (lookTrace.length, different)
  -- Each process its own: a child has a copy of what was allocated, which goes its own way, and its memory can be reached from outside.
  let forking ← Bap.Linux.start (← file "libc-fork") "/test" ["/test", "arg1"]
  let before ← forking.malloc 64
  forking.write before (ByteArray.mk #[5])
  let parent := (← Bap.Emu.currentTask forking.emu).group
  let rec untilChild : Nat → IO (Option Nat)
    | 0 => pure none
    | fuel + 1 => do
      let _ ← forking.run (quantum := 50) (fuel := 500) silent
      match (← forking.emu.taskTable.get).tasks.find? (fun task => task.group != parent && task.status.isNone) with
      | some child => pure (some child.group)
      | none => untilChild fuel
  match ← untilChild 400 with
  | none => throw <| IO.userError s!"{label} a child should have come"
  | some child =>
    assertEqual s!"{label} a child has what was written" 5 (← forking.read before 1 (pid := some child))[0]!.toNat
    forking.write before (ByteArray.mk #[6]) (pid := some child)
    assertEqual s!"{label} a child's own memory is written" 6 (← forking.read before 1 (pid := some child))[0]!.toNat
    assertEqual s!"{label} a parent's isn't" 5 (← forking.read before 1 (pid := some parent))[0]!.toNat
    -- Through another process.
    let inOther ← forking.calloc 4 4 (pid := some child)
    assertEqual s!"{label} calloc in a child" [0, 0, 0, 0] (← forking.read inOther 4 (pid := some child)).toList
    let bigger ← forking.realloc inOther 4096 (pid := some child)
    forking.free bigger (pid := some child)
    expectThrow s!"{label} what is a child's isn't a parent's" (forking.free bigger (pid := some parent))
    forking.free before (pid := some child)
    expectThrow s!"{label} a child's free, twice" (forking.free before (pid := some child))
    let inChild ← forking.malloc 16 (pid := some child)
    assertEqual s!"{label} a child's block is aligned" 0 (inChild % 16)
    forking.free before (pid := some parent)
    let (ending, _) ← collected forking
    assertTrue s!"{label} a run goes on after all that" (ending != .outOfFuel)
  -- From a hook, another process can't be reached, and the one that runs can.
  let holder ← IO.mkRef (none : Option Bap.Linux.Machine)
  let results ← IO.mkRef ([] : List Bool)
  let hooked ← Bap.Linux.start (← file "libc-fork") "/test" ["/test", "arg1"] (handler := some fun current _ _ => do
    if (← results.get).isEmpty then
      if let some machine := ← holder.get then
        let own := (← Bap.Emu.currentTask current).group
        -- Once there is another process, which is what it takes to have to go somewhere.
        if let some other := (← current.taskTable.get).tasks.find? (fun task => task.group != own && task.status.isNone) then
          let mine ← (machine.malloc 8).toBaseIO
          let theirs ← (machine.read 0 0 (pid := some other.group)).toBaseIO
          results.set [(match mine with | .ok _ => true | .error _ => false), (match theirs with | .ok _ => true | .error _ => false)]
    pure .default)
  holder.set (some hooked)
  let _ ← hooked.run silent
  assertEqual s!"{label} from a hook, this process and not another" [true, false] (← results.get)

/-- `execve`: what was allocated has gone with its memory. -/
def testMachineHeapExec (triple : String) : IO Unit := do
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-exec")).addFile "/script" "#!/test child\n".toUTF8
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let block ← machine.malloc 32
  let first := (← Bap.Emu.currentTask machine.emu).space
  -- It runs others in children, and a child has a copy of what its parent had until it runs another.
  let has (space : Nat) : IO Bool := do
    pure (((← machine.heaps.get).get? space).any fun heap => heap.used.any (·.1 == block))
  let mut copied : List Nat := []
  let mut executed := false
  for _ in [0:4000] do
    let outcome ← machine.run (quantum := 50) (fuel := 100) fun _ => pure ()
    let spaces := (← machine.heaps.get).toList.map (·.1)
    for space in spaces do
      if space != first && !copied.contains space then copied := space :: copied
    for space in copied do
      if !(← has space) then executed := true
    if outcome != .outOfFuel then break
  assertTrue s!"Machine {triple} a child has a copy" (!copied.isEmpty)
  assertTrue s!"Machine {triple} the first still has what it was given" (← has first)
  assertTrue s!"Machine {triple} what was allocated goes on execve" executed

/-- Functions that the host serves for what a library imports, for what it exports and for what a slot of its tables has, by each
convention; and what a checkpoint says of what was loaded, without making a machine of it. -/
def testHostFunctions (triple : String) : IO Unit := do
  let label := s!"Host functions {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files"))
    |>.addFile "/lib/libmain.so" (← binary "libmain")
    |>.addFile "/lib/libdep.so" (← binary "libdep")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let seen ← IO.mkRef ([] : List (List Nat))
  let tripled : Bap.Linux.HostFunction := fun _ arguments => do
    seen.modify (· ++ [arguments.take 2])
    pure (arguments.headD 0 * 3)
  let stubs ← machine.importStubs [("host_given", tripled)]
  let dep ← machine.loadLibrary "libdep.so"
  let library ← machine.loadLibrary "libmain.so" (resolve := stubs)
  let signed32 (value : Nat) : Nat := value % 2 ^ 32
  let call (name : String) (arguments : List Nat := []) : IO Nat := do
    match ← machine.findSymbol name (some library) with
    | some address => pure (signed32 (← machine.call address arguments))
    | none => throw <| IO.userError s!"{label} has no {name}"
  assertEqual s!"{label} what is imported is served by the host" 15 (← call "from_host" [5])
  assertEqual s!"{label} with the arguments of the call" [5] ((← seen.get).map (·.headD 0))
  assertEqual s!"{label} a stub of a name is where it was" (stubs "host_given")
    (some (← machine.hostFunction "host_given" tripled))
  -- A slot that relocating filled, for what another library has.
  assertEqual s!"{label} what another has, before" 108 (← call "dep_call" [1, 2])
  let product ← machine.hostFunction "product" fun _ arguments => pure (arguments.headD 0 * arguments.getD 1 0)
  let slots ← machine.redirectImport library "dep_add" product
  assertTrue s!"{label} its slots of a name ({slots})" (slots ≥ 1)
  assertEqual s!"{label} go where they are sent" 12 (← call "dep_call" [3, 4])
  -- What a library exports, by its name.
  let _ ← machine.hookSymbol "either_one" (library := some dep) fun _ _ => pure 7
  assertEqual s!"{label} what is exported is served by the host" 7 (← call "which_one")
  -- What a checkpoint says of it, before anything is made of it.
  let saved ← machine.checkpoint
  let info ← Bap.Linux.Machine.checkpointInfo saved
  assertEqual s!"{label} a checkpoint says what was loaded, where and of which file"
    [("/lib/libdep.so", dep.base, dep.digest), ("/lib/libmain.so", library.base, library.digest)]
    (info.libraries.map fun (_, loaded) => (loaded.path, loaded.base, loaded.digest))
  assertEqual s!"{label} and of what" machine.architecture.name info.architecture.name
  assertTrue s!"{label} and the models that it has" (info.models.any (·.1 == "bap.libraries"))
  expectThrow s!"{label} a checkpoint without a library that was expected"
    (Bap.Linux.Machine.ofCheckpoint saved (expectedLibraries := [dep.digest + 1]))
  -- Going on from it, a stub is where it was, and served again.
  let resumed ← Bap.Linux.Machine.ofCheckpoint saved (expectedLibraries := [dep.digest, library.digest])
  assertEqual s!"{label} a stub is where it was after a checkpoint" (stubs "host_given")
    (some (← resumed.hostFunction "host_given" tripled))
  let some fromHost := ← resumed.findSymbol "from_host" | throw <| IO.userError s!"{label} has no from_host"
  assertEqual s!"{label} and is served again" 21 (signed32 (← resumed.call fromHost [7]))

/-- Names of one function, each served as it is imported; initializers run after what they import is served, what is needed first, and
once, also after a checkpoint; and what a checkpoint says of what it has. -/
def testAliasDispatch (triple : String) : IO Unit := do
  let label := s!"Aliases {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files"))
    |>.addFile "/lib/libalias.so" (← binary "libalias")
    |>.addFile "/lib/libuser.so" (← binary "libuser")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let notes ← IO.mkRef ([] : List Nat)
  let note : Bap.Linux.HostFunction := fun _ arguments => do
    notes.modify (· ++ [arguments.headD 0 % 2 ^ 32])
    pure 0
  let stubs ← machine.importStubs [("host_note", note)]
  let user ← machine.loadLibrary "libuser.so" (resolve := stubs) (runInitializers := false)
  assertEqual s!"{label} nothing is initialized yet" [] (← notes.get)
  machine.runInitializers user
  assertEqual s!"{label} what is needed is initialized first, with its imports served" [1, 2] (← notes.get)
  machine.runInitializers
  assertEqual s!"{label} and once" [1, 2] (← notes.get)
  let signed32 (value : Nat) : Nat := value % 2 ^ 32
  let call (name : String) (arguments : List Nat) : IO Nat := do
    match ← machine.findSymbol name with
    | some address => pure (signed32 (← machine.call address arguments))
    | none => throw <| IO.userError s!"{label} has no {name}"
  assertEqual s!"{label} both names are one function" (1005, 1005) (← call "call_one" [5], ← call "call_two" [5])
  let some one := ← machine.findSymbol "alias_one" | throw <| IO.userError s!"{label} has no alias_one"
  let some two := ← machine.findSymbol "alias_two" | throw <| IO.userError s!"{label} has no alias_two"
  assertEqual s!"{label} at one address" one two
  let served (plus : Nat) : Bap.Linux.HostFunction := fun _ arguments => pure (arguments.headD 0 % 2 ^ 32 + plus)
  let slots ← machine.serveImport user "alias_one" (served 1)
  let _ ← machine.serveImport user "alias_two" (served 2)
  assertTrue s!"{label} a name has its slots ({slots})" (slots ≥ 1)
  assertEqual s!"{label} each name has what was given for it" (6, 7) (← call "call_one" [5], ← call "call_two" [5])
  assertEqual s!"{label} and the function is as it was" 1005 (← call "impl_value" [5])
  let _ ← machine.serveImport user "alias_two" (served 20)
  assertEqual s!"{label} a handler given again is the one" (6, 25) (← call "call_one" [5], ← call "call_two" [5])
  -- What a checkpoint says, and going on from it.
  let saved ← machine.checkpoint
  let info ← Bap.Linux.Machine.checkpointInfo saved
  assertEqual s!"{label} a checkpoint says what was initialized" [("/lib/libalias.so", true), ("/lib/libuser.so", true)]
    ((info.libraries.map fun (_, library) => (library.path, library.initialized)).toArray.qsort (fun left right => left.1 < right.1)).toList
  assertTrue s!"{label} and the files" (info.files.any fun (path, size, _) => path == "/lib/libuser.so" && size > 0)
  assertTrue s!"{label} and the tasks" (!info.tasks.isEmpty)
  assertTrue s!"{label} and what is mapped, of which some is not zeros ({info.resident} of {info.mapped})"
    (0 < info.resident && info.resident ≤ info.mapped)
  assertEqual s!"{label} and nothing keeps it from going on" ([] : List String) (← Bap.Linux.Machine.checkCheckpoint saved)
  let resumed ← Bap.Linux.Machine.ofCheckpoint saved
  let again ← IO.mkRef ([] : List Nat)
  let _ ← resumed.importStubs [("host_note", fun _ arguments => do again.modify (· ++ [arguments.headD 0]); pure 0)]
  resumed.runInitializers
  assertEqual s!"{label} what was initialized isn't again after a checkpoint" [] (← again.get)
  let some resumedUser := (← resumed.loadedLibraries).find? (·.path == "/lib/libuser.so")
    | throw <| IO.userError s!"{label} a checkpoint without libuser"
  let _ ← resumed.serveImport resumedUser "alias_one" (served 1)
  let _ ← resumed.serveImport resumedUser "alias_two" (served 2)
  let some callOne := ← resumed.findSymbol "call_one" | throw <| IO.userError s!"{label} has no call_one"
  assertEqual s!"{label} and is served again" 6 (signed32 (← resumed.call callOne [5]))

/-- A library linked against the base environment, with no libc in the guest: memory and strings, threads that count under a lock and
give back what they did, a condition, `once`, keys and `errno`; and what the environment has, had from it before a libc that is loaded
and has the same names, by what is loaded with it and by what is linked against it after. -/
def testBaseEnvironment (triple : String) : IO Unit := do
  let label := s!"Base {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files"))
    |>.addFile "/lib/libbaseuse.so" (← binary "libbaseuse")
    |>.addFile "/lib/libfakec.so" (← binary "libfakec")
    |>.addFile "/lib/libplain.so" (← binary "libplain")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let base ← machine.baseEnvironment
  let _ ← machine.loadLibrary "libfakec.so"
  let _ ← machine.loadLibrary "libplain.so"
  let _ ← machine.loadWithBase base "libbaseuse.so"
  let call (name : String) (arguments : List Nat := []) : IO Nat := do
    match ← machine.findSymbol name with
    | some address => pure ((← machine.call address arguments (threaded := true)) % 2 ^ 32)
    | none => throw <| IO.userError s!"{label} has no {name}"
  assertEqual s!"{label} a library has what it needs of a libc from it" 0xff (← call "run")
  let text ← machine.malloc 16
  machine.write text "abcdef\x00".toUTF8
  assertEqual s!"{label} before a libc that is loaded with the same names" 6 (← call "length_of" [text])
  assertEqual s!"{label} which what isn't linked against it has" 999 (← call "plain_length" [text])
  let slots ← machine.linkBase base
  assertTrue s!"{label} until it is linked against it ({slots})" (slots ≥ 1)
  assertEqual s!"{label} and then it has it" 6 (← call "plain_length" [text])
  -- What threads had goes once they are over: joined, by `run`, or detached.
  assertEqual s!"{label} a detached thread runs" 1 (← call "spawn_detached")
  let left ← base.state.get
  assertTrue s!"{label} and nothing is left of the threads ({left.stacks.size}, {left.blocks.size}, {left.joinWords.size})"
    (left.stacks.isEmpty && left.blocks.isEmpty && left.joinWords.isEmpty && left.detached.isEmpty && left.results.isEmpty)
  -- The mask of signals: what is blocked waits, and comes as the call that unblocks it returns.
  let callBase (name : String) (arguments : List Nat) (bits : Nat := 32) : IO Nat := do
    let some address := base.resolve name | throw <| IO.userError s!"{label} has no {name} of the base"
    pure ((← machine.call address arguments) % 2 ^ bits)
  let some onSignal := ← machine.findSymbol "on_signal" | throw <| IO.userError s!"{label} has no on_signal"
  let tid ← Bap.Emu.thread machine.emu
  let group := (← Bap.Emu.currentTask machine.emu).group
  machine.signals.table.modify fun table => { table with actions := table.actions.insert (group, 10) { handler := onSignal } }
  let set ← machine.malloc 16
  let old ← machine.malloc 16
  machine.write set (ByteArray.mk #[0, 2, 0, 0, 0, 0, 0, 0])
  assertEqual s!"{label} pthread_sigmask blocks" 0 (← callBase "pthread_sigmask" [0, set, 0])
  machine.signals.send machine.emu (some tid) group ⟨10, 0, .sent group 0 0⟩
  assertEqual s!"{label} and what it blocks waits" 0 (← call "caught_signal")
  assertEqual s!"{label} pthread_sigmask unblocks" 0 (← callBase "pthread_sigmask" [1, set, old])
  assertEqual s!"{label} and says what was blocked" (ByteArray.mk #[0, 2, 0, 0, 0, 0, 0, 0]).toList (← machine.read old 8).toList
  assertEqual s!"{label} and what was pending comes as it returns" 10 (← call "caught_signal")
  assertEqual s!"{label} pthread_sigmask gives back what is wrong" 22 (← callBase "pthread_sigmask" [7, set, 0])
  assertEqual s!"{label} and sigprocmask -1" (2 ^ 32 - 1) (← callBase "sigprocmask" [7, set, 0])
  assertEqual s!"{label} with errno" [22, 0, 0, 0] (← machine.read (← callBase "__errno_location" [] 64) 4).toList
  -- It is in a checkpoint, and a machine that goes on from one has it as it was, at the same places.
  let key ← machine.malloc 8
  assertEqual s!"{label} a key" 0 (← callBase "pthread_key_create" [key, 0])
  let keyValue := (← machine.read key 4).toList.foldr (fun byte value => value * 256 + byte.toNat) 0
  assertEqual s!"{label} with a value" 0 (← callBase "pthread_setspecific" [keyValue, 1234])
  let errnoAt ← callBase "__errno_location" [] 64
  let data ← machine.checkpoint
  let refused ← (Bap.Linux.Machine.ofCheckpoint data *> pure false).catchExceptions fun _ => pure true
  assertTrue s!"{label} a checkpoint of it needs it to go on" refused
  let cell ← IO.mkRef none
  let again ← Bap.Linux.Machine.ofCheckpoint data (models := [Bap.Linux.baseModel cell])
  let some restored := ← cell.get | throw <| IO.userError s!"{label} has no base environment after a checkpoint"
  assertEqual s!"{label} at the same places" base.symbols restored.symbols
  let callAgain (name : String) (arguments : List Nat) (bits : Nat := 32) : IO Nat := do
    let some address := restored.resolve name | throw <| IO.userError s!"{label} has no {name} of the base"
    pure ((← again.call address arguments) % 2 ^ bits)
  assertEqual s!"{label} with the values of its keys" 1234 (← callAgain "pthread_getspecific" [keyValue])
  assertEqual s!"{label} and the errno of each thread" errnoAt (← callAgain "__errno_location" [] 64)
  let some run := ← again.findSymbol "run" | throw <| IO.userError s!"{label} has no run after a checkpoint"
  -- Its counter goes on from what the first run left, in both: `once` ran, and doesn't again.
  assertEqual s!"{label} and what was linked against it runs as it would have" (← call "run")
    ((← again.call run (threaded := true)) % 2 ^ 32)

/-- What a wait says of the process that it found, for a host that gives the guest ids of its own: the machine's own until it is told,
and what the host says once it is, both of a wait that is answered at once and of one that waited. A checkpoint doesn't have it: a
machine that goes on from one is told again. -/
def testWaitResultMapping (triple : String) : IO Unit := do
  let label := s!"Wait pids {triple}"
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-waitpids"
  let outputOf (machine : Bap.Linux.Machine) : IO String := do
    let written ← IO.mkRef ByteArray.empty
    let outcome ← machine.run fun data => written.modify (· ++ data)
    assertEqual s!"{label} it ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
    pure (String.fromUTF8! (← written.get))
  let start : IO Bap.Linux.Machine := Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  assertEqual s!"{label} are the machine's own until it is told" "0 0\n" (← outputOf (← start))
  let machine ← start
  let data ← machine.checkpoint
  machine.setWaitResultMapping (· + 1000)
  assertEqual s!"{label} are what the host says, at once and after waiting" "1000 1000\n" (← outputOf machine)
  assertEqual s!"{label} aren't in a checkpoint" "0 0\n" (← outputOf (← Bap.Linux.Machine.ofCheckpoint data))
  let again ← Bap.Linux.Machine.ofCheckpoint data
  again.setWaitResultMapping (· + 1000)
  assertEqual s!"{label} and are what the host says once it is told again" "1000 1000\n" (← outputOf again)

/-- What seccomp keeps comes out of a checkpoint as it went in, of the threads that there are, and a filter that isn't one is refused
before it is run. -/
def testSeccompState : IO Unit := do
  let program : Array Bap.Linux.Seccomp.Insn := #[⟨0x20, 0, 0, 0⟩, ⟨0x15, 0, 1, 39⟩, ⟨0x06, 0, 0, 0x00050001⟩, ⟨0x06, 0, 0, 0x7fff0000⟩]
  let state : Bap.Linux.Seccomp.State := {
    programs := #[program, program], filters := Std.HashMap.ofList [(5, [1, 0]), (6, [0]), (9, [1])]
    strict := Std.HashSet.ofList [7], noNewPrivs := Std.HashSet.ofList [5, 9], traced := Std.HashSet.ofList [6] }
  let live (tid : Nat) : Bool := tid != 9
  let some again := (Bap.Linux.Seccomp.decode (Bap.Linux.Seccomp.encode state live)).toOption
    | throw <| IO.userError "seccomp: a checkpoint of it isn't read back"
  let sorted (list : List Nat) : List Nat := list.mergeSort (· ≤ ·)
  assertEqual "seccomp: its filters, of the threads that there are" [(5, [1, 0]), (6, [0])]
    (again.filters.toList.mergeSort (fun a b => a.1 ≤ b.1))
  assertEqual "seccomp: and its programs" [program.toList, program.toList] (again.programs.toList.map (·.toList))
  assertEqual "seccomp: and its modes" ([7], [5], [6]) (sorted again.strict.toList, sorted again.noNewPrivs.toList, sorted again.traced.toList)
  let word (offset : Nat) : Nat := if offset == 0 then 39 else 0
  assertEqual "seccomp: a filter runs" 0x00050001 (Bap.Linux.Seccomp.run program word)
  assertEqual "seccomp: the first result of the actions" 0x80000000
    (Bap.Linux.Seccomp.combine [0x7fff0000, 0x00050001, 0x80000000, 0x00030000])
  assertTrue "seccomp: a load past seccomp_data isn't a filter" (!Bap.Linux.Seccomp.valid #[⟨0x20, 0, 0, 64⟩, ⟨0x06, 0, 0, 0⟩])

/-- Files and directories put in a kernel, before a run and as a machine runs, through links and over what is there. -/
def testKernelFiles : IO Unit := do
  let label := "Kernel files"
  let found (kernel : Bap.Linux.Kernel) (path : String) : Option Bap.Linux.Content :=
    match kernel.resolve "/" path with
    | .ok (_, some number) => (kernel.inodes.get? number).map (·.content)
    | _ => none
  let isFile (kernel : Bap.Linux.Kernel) (path : String) (data : String) : Bool :=
    match found kernel path with
    | some (.file bytes) => bytes == data.toUTF8
    | _ => false
  let isDirectory (kernel : Bap.Linux.Kernel) (path : String) : Bool :=
    match found kernel path with
    | some .directory => true
    | _ => false
  let error (result : Bap.Linux.Result Bap.Linux.Kernel) : Nat := match result with | .ok _ => 0 | .error errno => errno
  let some kernel := (Bap.Linux.Kernel.empty.putDirectory "/data/app" 0o700).toOption
    | throw <| IO.userError s!"{label}: no directory"
  assertTrue s!"{label} a directory with those before it" (isDirectory kernel "/data" && isDirectory kernel "/data/app")
  assertEqual s!"{label} of its mode" (some 0o40700) ((kernel.paths.get? "/data/app").bind (kernel.inodes.get? ·) |>.map (·.mode))
  let kernel := kernel.addSymlink "/app" "/data/app"
  let some kernel := (kernel.putFile "/app/lib/one.so" "one".toUTF8).toOption | throw <| IO.userError s!"{label}: no file"
  assertTrue s!"{label} a file through a link, where the link goes" (isFile kernel "/data/app/lib/one.so" "one")
  assertTrue s!"{label} and not beside it" (!kernel.paths.contains "/app/lib/one.so")
  let some kernel := (kernel.putFile "/app/lib/one.so" "two".toUTF8).toOption | throw <| IO.userError s!"{label}: not replaced"
  assertTrue s!"{label} a file over one" (isFile kernel "/data/app/lib/one.so" "two")
  assertEqual s!"{label} a directory is there again" 0 (error (kernel.putDirectory "/app/lib"))
  assertEqual s!"{label} not a file over a directory" Bap.Linux.Errno.eisdir (error (kernel.putFile "/app/lib" ByteArray.empty))
  assertEqual s!"{label} not a directory over a file" Bap.Linux.Errno.eexist (error (kernel.putDirectory "/app/lib/one.so"))
  assertEqual s!"{label} not under a file" Bap.Linux.Errno.enotdir (error (kernel.putFile "/app/lib/one.so/x" ByteArray.empty))
  -- What a file has of itself stays as its bytes are put again, and it was written then.
  let some number := kernel.paths.get? "/data/app/lib/one.so" | throw <| IO.userError s!"{label}: no inode"
  let owned := { kernel with inodes := kernel.inodes.modify number fun inode =>
    { inode with details := { inode.details with uid := 7, attributes := [("user.kept", "yes".toUTF8)] } } }
  let owned := { owned with clock := owned.clock + 5 }
  let some again := (owned.putFile "/app/lib/one.so" "three".toUTF8).toOption | throw <| IO.userError s!"{label}: not put again"
  let details := (again.inodes.get? number).map (·.details)
  assertEqual s!"{label} keeps its owner and attributes as its bytes are put again" (some (7, ["user.kept"]))
    (details.map fun details => (details.uid, details.attributes.map (·.1)))
  assertEqual s!"{label} and was written then" (some owned.clock) (details.map (·.modified))
  -- On a machine that runs: what a library is loaded from is there as it is put there.
  let triple := "x86_64"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files")) "/test" ["/test"]
  machine.addDirectory "/vendor/lib"
  machine.addFile "/vendor/lib/libfakec.so" (← binary "libfakec")
  let _ ← machine.loadLibrary "/vendor/lib/libfakec.so"
  assertTrue s!"{label} a library put in as the machine runs is loaded" (← machine.findSymbol "strlen").isSome
  let refused ← (machine.addFile "/vendor/lib" ByteArray.empty *> pure false).catchExceptions fun _ => pure true
  assertTrue s!"{label} and a machine says what it can't put" refused

/-- A byte of a node past 4096, as a read of a file makes, is its own: its tag is no other node's, and says its node and byte. -/
def testTaintTags : IO Unit := do
  let tag := Bap.Analysis.DynamicTaint.nodeTag 0 5000
  assertTrue "Taint tags of a node of more than 4096 bytes are no other's" (tag != Bap.Analysis.DynamicTaint.nodeTag 1 904)
  assertEqual "and say their node and byte" (0, 5000) (Bap.Analysis.DynamicTaint.Tag.node tag, Bap.Analysis.DynamicTaint.Tag.byte tag)

/-- A function of a target of 32 bits that `Emu.call` calls has its arguments and gives its result, in registers of that width, or on
the stack of i386. -/
def testCall32 : IO Unit := do
  for (triple, binary, source, adds) in [("riscv32", "riscv32", "addi a0, a0, 1\njalr x0, 0(ra)", 1),
      ("armv7", "arm", "add r0, r0, r1\nbx lr", 2), ("i686", "i686", "movl 4(%esp), %eax\naddl 8(%esp), %eax\nret", 2)] do
    let program ← IO.FS.readBinFile s!"testsuite/bin/{binary}-linux-musl-libc-signals"
    let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
    let code ← LLVM.assemble triple source
    Bap.Emu.map machine.emu ⟨0x7000000, code, ⟨true, true, true⟩⟩
    let result ← Bap.Emu.call machine.emu 0x7000000 0x7001000 (if adds == 1 then [41] else [40, 2])
    assertBits s!"Emu call of {binary} gives what its function does" (BitVec.ofNat 32 42) (.ok result)

/-- What a program opens and closes many times is let go of, and what it keeps open stays. -/
def testChurn (triple : String) : IO Unit := do
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-churn"
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  let written ← IO.mkRef ByteArray.empty
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} churn ends with what it kept" (Bap.Tasks.ScheduleOutcome.finished 0, "kept\n")
    (outcome, String.fromUTF8! (← written.get))
  let kernel ← machine.kernel.get
  assertTrue s!"Linux {triple} of 6000 open files and 3000 pipes, few are left ({kernel.openFiles.size}, {kernel.inodes.size})"
    (kernel.openFiles.size < 600 && kernel.inodes.size < 600)

/-- MIPS has its own numbers of errors above 34, which a call gives a program of it. -/
def testMipsErrno : IO Unit := do
  let mips : Bap.Linux.Architecture := .mips 32 true false
  for (generic, own) in [(42, 35), (43, 36), (61, 61), (74, 77), (110, 145), (38, 89), (95, 122), (11, 11), (22, 22)] do
    assertEqual s!"MIPS has error {generic} as {own}" own (mips.errno generic)
  assertEqual "and others have it as it is" 42 (Bap.Linux.Architecture.x86_64.errno 42)

/-- A directory of the host that a machine sees: what a program finds in it comes from the host, and what it changes stays in the
machine. -/
def testHostMount (triple : String) : IO Unit := do
  let label := s!"Linux {triple} a directory of the host"
  -- Of the test suite, with a link in it and one to outside of it, whose target isn't there; nothing writes it.
  let host := (← IO.FS.realPath "testsuite/host").toString
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-host"
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  machine.mountHost host "/host"
  let written ← IO.mkRef ByteArray.empty
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"{label} is read and ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"{label} has what the host has, as the program changes it"
    ("names a.txt link sub\na alpha\nb beta\nlink /host/a.txt\nthrough the link alpha\nwritten changed\nunlink 0\nunlinked -2\n" ++
      "sub\nmissing -2\nnames after a.txt link new sub\n")
    (String.fromUTF8! (← written.get))
  assertEqual s!"{label} isn't written" "alpha" (← IO.FS.readFile s!"{host}/a.txt")
  assertTrue s!"{label} has what the program took away" (← System.FilePath.pathExists s!"{host}/sub/b.txt")
  assertTrue s!"{label} and not what it made" !(← System.FilePath.pathExists s!"{host}/new")

/-- A program that runs a script of a directory of the host that the machine sees, which names a program there to run it through a
link: none of them is in the machine until `execve` looks for it. -/
def testHostExec (triple : String) : IO Unit := do
  -- Of the test suite: the program in `bin`, a link `alias` to it beside it, and a script that names the program through the link.
  let host := (← IO.FS.realPath s!"testsuite/hostexec/{triple}").toString
  let program ← IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-libc-hostexec"
  let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/test" program) "/test" ["/test"]
  machine.mountHost host "/host"
  let written ← IO.mkRef ByteArray.empty
  let outcome ← machine.run fun data => written.modify (· ++ data)
  assertEqual s!"Linux {triple} a script of the host runs a program of the host" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
  assertEqual s!"Linux {triple} with what it was given" "child /host/script x\n" (String.fromUTF8! (← written.get))

/-- Shared libraries from outside a program, as `dlopen` has them, on a machine with no libc or linker to do it. -/
def testLinuxLibraries (triple : String) (ifunc : Bool := false) : IO Unit := do
  let label := s!"Library {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files"))
    |>.addFile "/lib/libmain.so" (← binary "libmain")
    |>.addFile "/lib/libdep.so" (← binary "libdep")
    |>.addFile "/lib/libother.so" (← binary "libother")
    |>.addFile "/lib/libtls.so" (← binary "libtls")
    |>.addFile "/nothing" "not a library".toUTF8
  let start : IO Bap.Linux.Machine := Bap.Linux.start kernel "/test" ["/test", "arg1"]
  let machine ← start
  -- What the host gives it: here, what is in another library, to have something that can run on every target.
  let dep ← machine.loadLibrary "libdep.so"
  let some either := ← machine.findSymbol "either_one"
    | throw <| IO.userError s!"{label} has no either_one"
  let given : String → Option Nat := fun name => if name == "host_given" then some either else none
  let library ← machine.loadLibrary "libmain.so" (resolve := given)
  let call (name : String) (arguments : List Nat := []) : IO Nat := do
    match ← machine.findSymbol name (some library) with
    | some address => machine.call address arguments
    | none => throw <| IO.userError s!"{label} has no {name}"
  let signed32 (value : Nat) : Nat := value % 2 ^ 32
  assertEqual s!"{label} its initializers ran" 1007 (signed32 (← call "own_data"))
  assertEqual s!"{label} a table of its own functions" (42, 21)
    (signed32 (← call "table_call" [0, 21]), signed32 (← call "table_call" [1, 7]))
  assertEqual s!"{label} what isn't in the file is zero" 1 (signed32 (← call "bss_is_zero"))
  assertEqual s!"{label} a pointer into its own, with what is added" 1 (signed32 (← call "bss_offset_right"))
  assertEqual s!"{label} that can be written" 9 (signed32 (← call "set_bss" [100, 9]))
  assertEqual s!"{label} a string through a table" 116 ((← call "text_char" [2, 0]) % 256)
  assertEqual s!"{label} data of another, as a word and as code has it" (105, 105)
    (signed32 (← call "dep_data_through_pointer"), signed32 (← call "dep_data_directly"))
  assertEqual s!"{label} a function of another, by its table and a pointer" (108, 108)
    (signed32 (← call "dep_call" [1, 2]), signed32 (← call "dep_call_through_pointer" [1, 2]))
  assertEqual s!"{label} a string of another" 100 ((← call "dep_text" [0]) % 256)
  assertEqual s!"{label} what the host gives" 1 (signed32 (← call "from_host" [5]))
  assertEqual s!"{label} what is weak and nowhere is 0" 1 (signed32 (← call "weak_is_absent"))
  assertEqual s!"{label} the first that has it is what it gets" 1 (signed32 (← call "which_one"))
  assertEqual s!"{label} all its arguments" 4321 (signed32 (← call "many" [1, 2, 3, 4]))
  -- In the order that they are to be: what it needs, then its own, the one with a priority first.
  let wordOf (bytes : ByteArray) : Nat :=
    let list := if machine.architecture.big then bytes.toList else bytes.toList.reverse
    list.foldl (fun value byte => value * 256 + byte.toNat) 0
  let notes : IO (List Nat) := do
    let some orders := ← machine.findSymbol "dep_orders" | throw <| IO.userError "no dep_orders"
    let some order := ← machine.findSymbol "dep_order" | throw <| IO.userError "no dep_order"
    let count := wordOf (← machine.read orders 4)
    (List.range count).mapM fun index => do pure (wordOf (← machine.read (order + index * 4) 4))
  assertEqual s!"{label} what runs first runs first" [1, 3, 2] (← notes)
  -- What only relocating writes is read-only, and code is.
  let some relocated := ← machine.findSymbol "to_own_data" (some library)
    | throw <| IO.userError "no to_own_data"
  expectThrow s!"{label} what is read-only after relocating" (machine.write relocated (ByteArray.mk #[0]))
  let some code := ← machine.findSymbol "own_data" (some library)
    | throw <| IO.userError "no own_data"
  expectThrow s!"{label} code isn't written" (machine.write (code - code % 2) (ByteArray.mk #[0]))
  let some data := ← machine.findSymbol "main_data" (some library)
    | throw <| IO.userError "no main_data"
  machine.write data (ByteArray.mk #[0, 0, 0, 0])
  assertEqual s!"{label} data is written" 0 (signed32 (← call "own_data"))
  machine.write data (if machine.architecture.big then ByteArray.mk #[0, 0, 3, 0xEF] else ByteArray.mk #[0xEF, 3, 0, 0])
  -- A call changes nothing of who is running.
  let registers : IO String := do
    let memoryVar := machine.emu.config.memory
    pure (repr ((← machine.emu.state.get).env.filter fun binding => binding.1 != memoryVar)).pretty
  let before ← registers
  let pcBefore ← Bap.Emu.pc machine.emu
  let _ ← call "many" [1, 2, 3, 4]
  assertTrue s!"{label} a call leaves its registers" (before == (← registers))
  assertEqual s!"{label} a call leaves its place" pcBefore (← Bap.Emu.pc machine.emu)
  expectThrow s!"{label} a call of nowhere" (machine.call 16 [])
  assertTrue s!"{label} and it leaves them then too" (before == (← registers))
  -- A second load holds on to it; going needs both to let go.
  let again ← machine.loadLibrary "/lib/libmain.so" (resolve := given)
  assertEqual s!"{label} a second load is the same" library.base again.base
  machine.unloadLibrary library
  assertEqual s!"{label} it stays while something holds it" 1007 (signed32 (← call "own_data"))
  -- Into a checkpoint, and on from it.
  let saved ← machine.checkpoint
  let resumed ← Bap.Linux.Machine.ofCheckpoint saved
  assertTrue s!"{label} saves again as it was" (saved == (← resumed.checkpoint))
  let some resumedCall := ← resumed.findSymbol "dep_call"
    | throw <| IO.userError s!"{label} a checkpoint has no dep_call"
  assertEqual s!"{label} goes on from a checkpoint" 108 (signed32 (← resumed.call resumedCall [1, 2]))
  assertEqual s!"{label} a checkpoint knows what is loaded" ["/lib/libdep.so", "/lib/libmain.so"]
    ((← resumed.loadedLibraries).map (·.path))
  let (originalOutcome, originalText) ← (do
    let plain ← Bap.Linux.start kernel "/test" ["/test", "arg1"]
    let written ← IO.mkRef ByteArray.empty
    let outcome ← plain.run fun data => written.modify (· ++ data)
    pure (outcome, (← written.get).toList))
  let written ← IO.mkRef ByteArray.empty
  let outcome ← resumed.run fun data => written.modify (· ++ data)
  assertEqual s!"{label} a program doesn't notice" (originalOutcome, originalText) (outcome, (← written.get).toList)
  -- Going for good: its finalizers, and it is gone, in order; what it needed too when nothing else holds it.
  machine.unloadLibrary library
  assertEqual s!"{label} it goes with what undoes it" [1, 3, 2, 8] (← notes)
  expectThrow s!"{label} what went can't be read" (machine.read relocated 1)
  assertEqual s!"{label} what it needed stays while held" ["/lib/libdep.so"] ((← machine.loadedLibraries).map (·.path))
  expectThrow s!"{label} what isn't loaded can't go" (machine.unloadLibrary library)
  let some counter := ← machine.findSymbol "dep_counter" | throw <| IO.userError "no dep_counter"
  machine.unloadLibrary dep
  expectThrow s!"{label} all of it is gone" (machine.read counter 1)
  assertEqual s!"{label} nothing is left" ([] : List String) ((← machine.loadedLibraries).map (·.path))
  -- From nothing, all at once: what it needs comes with it, and goes with it.
  let fresh ← start
  -- The page that calls return to stays once it is there, and isn't a library's.
  let _ ← (fresh.call 16 []).toBaseIO
  let regions ← Bap.Emu.regions fresh.emu
  let other ← fresh.loadLibrary "libother.so"
  let main ← fresh.loadLibrary "libmain.so"
  assertEqual s!"{label} what is first is found first" 2 (signed32 (← fresh.call (← (do
    let some address := ← fresh.findSymbol "which_one" | throw <| IO.userError "no which_one"
    pure address)) []))
  assertEqual s!"{label} what is loaded is in that order" ["/lib/libother.so", "/lib/libmain.so", "/lib/libdep.so"]
    ((← fresh.loadedLibraries).map (·.path))
  fresh.unloadLibrary main
  assertEqual s!"{label} what it needed goes with it" ["/lib/libother.so"] ((← fresh.loadedLibraries).map (·.path))
  fresh.unloadLibrary other
  assertEqual s!"{label} all that was mapped went" regions.length (← Bap.Emu.regions fresh.emu).length
  -- What can't be done leaves nothing behind.
  let empty ← start
  let untouched ← Bap.Emu.regions empty.emu
  let check (what : String) (action : IO Bap.Linux.LoadedLibrary) : IO Unit := do
    expectThrow s!"{label} {what}" action
    assertEqual s!"{label} {what} leaves nothing" (([] : List String), untouched.length)
      ((← empty.loadedLibraries).map (·.path), (← Bap.Emu.regions empty.emu).length)
  check "what is nowhere" (empty.loadLibrary "libnothing.so")
  check "what isn't a library" (empty.loadLibrary "/nothing")
  check "what isn't one that can go anywhere" (empty.loadLibrary "/test")
  let messages ← IO.mkRef ""
  match ← (empty.loadLibrary "libmain.so").toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label} an import that isn't there should be refused"
  | .error error => messages.set (toString error)
  assertTrue s!"{label} it says what isn't there: {← messages.get}" (((← messages.get).splitOn "host_given").length > 1)
  assertEqual s!"{label} an import that isn't there leaves nothing" (([] : List String), untouched.length)
    ((← empty.loadedLibraries).map (·.path), (← Bap.Emu.regions empty.emu).length)
  -- Without what it needs, if it is told that it can do without and something gives what that would have.
  let sparse ← Bap.Linux.start ((Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files")).addFile "/lib/libmain.so" (← binary "libmain")
    |>.addFile "/lib/libother.so" (← binary "libother")) "/test" ["/test"]
  expectThrow s!"{label} what it needs isn't there" (sparse.loadLibrary "libmain.so")
  let otherFirst ← sparse.loadLibrary "libother.so"
  let some stand := ← sparse.findSymbol "host_given" (some otherFirst) | throw <| IO.userError "no host_given"
  let standIn ← sparse.malloc 16
  let sparseLibrary ← sparse.loadLibrary "libmain.so" (ignoreMissing := true) (resolve := fun name =>
    if name == "dep_counter" then some standIn else if name.startsWith "dep_" then some stand else none)
  assertEqual s!"{label} it goes on without" ["/lib/libother.so", "/lib/libmain.so"] ((← sparse.loadedLibraries).map (·.path))
  let some fromHost := ← sparse.findSymbol "from_host" (some sparseLibrary) | throw <| IO.userError "no from_host"
  assertEqual s!"{label} and what is given is what runs" 1005 (signed32 (← sparse.call fromHost [5]))
  -- From a hook, in the middle of an instruction, none of this.
  let holder ← IO.mkRef (none : Option Bap.Linux.Machine)
  let hooked ← IO.mkRef ([] : List Bool)
  let hookedMachine ← Bap.Linux.start kernel "/test" ["/test", "arg1"] (handler := some fun _ _ _ => do
    if (← hooked.get).isEmpty then
      if let some machine := ← holder.get then
        let loaded ← (machine.loadLibrary "libother.so").toBaseIO
        let called ← (machine.call 16 []).toBaseIO
        hooked.set [(match loaded with | .ok _ => true | .error _ => false), (match called with | .ok _ => true | .error _ => false)]
    pure .default)
  holder.set (some hookedMachine)
  let _ ← hookedMachine.run (fuel := 3000) fun _ => pure ()
  assertEqual s!"{label} not in the middle of an instruction" [false, false] (← hooked.get)
  if ifunc then
    let chosen := (kernel.addFile "/lib/libifunc.so" (← binary "libifunc"))
    let picking ← Bap.Linux.start chosen "/test" ["/test"]
    let loaded ← picking.loadLibrary "libifunc.so"
    let some direct := ← picking.findSymbol "chosen" (some loaded) | throw <| IO.userError "no chosen"
    assertEqual s!"{label} a symbol is what its resolver chose" 77 (signed32 (← picking.call direct []))
    let some plt := ← picking.findSymbol "through_plt" (some loaded) | throw <| IO.userError "no through_plt"
    assertEqual s!"{label} by its table" 77 (signed32 (← picking.call plt []))
    let some pointer := ← picking.findSymbol "through_pointer" (some loaded) | throw <| IO.userError "no through_pointer"
    assertEqual s!"{label} by a pointer" 77 (signed32 (← picking.call pointer []))

/-- Thread-local storage of libraries, by what code reads through the thread pointer, so that it only comes to what it should where the
offsets are right, with a block for each of two threads. -/
def testLinuxLibraryTls (triple : String) (runsByModule : Bool := true) : IO Unit := do
  let label := s!"Library TLS {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files"))
    |>.addFile "/lib/libtls.so" (← binary "libtls")
    |>.addFile "/lib/libtlsuser.so" (← binary "libtlsuser")
    |>.addFile "/lib/libtlsdyn.so" (← binary "libtlsdyn")
    |>.addFile "/lib/libtlsrt.so" (← binary "libtlsrt")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let tlsLibrary ← machine.loadLibrary "libtls.so"
  let user ← machine.loadLibrary "libtlsuser.so"
  let runtime ← machine.loadLibrary "libtlsrt.so"
  let dynamic ← machine.loadLibrary "libtlsdyn.so"
  let call (name : String) (arguments : List Nat := []) : IO Nat := do
    match ← machine.findSymbol name with
    | some address => pure ((← machine.call address arguments) % 2 ^ 32)
    | none => throw <| IO.userError s!"{label} has no {name}"
  assertEqual s!"{label} each has a module of its own" [1, 2, 3]
    ([tlsLibrary, user, dynamic].filterMap fun library => library.tls.map (·.module))
  assertEqual s!"{label} one without has none" none (runtime.tls.map (·.module))
  -- What `__tls_get_addr` looks in, for the blocks of a thread, if it goes that way on this target.
  let wordBytes := machine.architecture.bits / 8
  let some blocks := ← machine.findSymbol "rt_blocks" | throw <| IO.userError s!"{label} has no rt_blocks"
  let number (value : Nat) : ByteArray :=
    let little := (List.range wordBytes).map fun index => (value >>> (8 * index)).toUInt8
    ByteArray.mk (if machine.architecture.big then little.reverse else little).toArray
  let enter : IO Nat := do
    let threadPointer ← machine.setupThreadTls
    for library in [tlsLibrary, user, dynamic] do
      if let some tls := library.tls then
        machine.write (blocks + tls.module * wordBytes) (number (machine.threadLocalAddress tls threadPointer))
    pure threadPointer
  -- Against the ABI of each target, and not only against itself: what is read through a thread pointer here has to be where a libc would
  -- have put it. The first block starts past what is above a thread pointer, at what it aligns to; or ends at it, below.
  let (below, gap, bias) : Bool × Nat × Nat := match machine.architecture with
    | .x86_64 | .i686 => (true, 0, 0)
    | .aarch64 => (false, 16, 0)
    | .arm => (false, 8, 0)
    | .riscv64 | .riscv32 => (false, 0, 0)
    | .mips .. | .powerpc .. => (false, 0, 0x7000)
  let some firstBlock := tlsLibrary.tls | throw <| IO.userError s!"{label} has no thread-local storage"
  let alignedUp (value : Nat) : Nat := (value + 63) / 64 * 64
  assertEqual s!"{label} a block is aligned as it says" 64 firstBlock.alignment
  assertEqual s!"{label} the first block is where the ABI has it"
    (if below then alignedUp firstBlock.memorySize else alignedUp gap) firstBlock.offset
  let modulus := 2 ^ machine.architecture.bits
  let fromPointer := (machine.threadLocalAddress firstBlock 0x1000000 + modulus - 0x1000000) % modulus
  assertEqual s!"{label} and that far from a thread pointer"
    (if below then modulus - firstBlock.offset else (firstBlock.offset + modulus - bias) % modulus) fromPointer
  let first ← enter
  assertEqual s!"{label} what a block starts with" 3 (← call "get")
  assertEqual s!"{label} what a block has as zeros" 0 (← call "get_zero")
  assertEqual s!"{label} what is aligned is" 1 (← call "aligned_right")
  assertEqual s!"{label} what is written is read" 9 (← call "set" [9])
  assertEqual s!"{label} in another library" 9 (← call "other_get")
  assertEqual s!"{label} a library's own" 11 (← call "own_get")
  if runsByModule then
    assertEqual s!"{label} by a module and an offset, its own" 21 (← call "dynamic_own")
    assertEqual s!"{label} by a module and an offset, another's" 9 (← call "dynamic_other")
    assertEqual s!"{label} by a module and an offset, written" 22 (← call "dynamic_set" [22])
  else
    -- Clang and ld.lld make no call of `__tls_get_addr` that runs on 32-bit PowerPC, as its stub wants r30, that that code doesn't set.
    -- What such a call would be given can still be read: a module and an offset, of the one and of the other.
    let image ← IO.ofExcept (Image.Elf.decode (← binary "libtlsdyn"))
    let relocations ← IO.ofExcept (Image.Elf.allDynamicRelocations image)
    let names ← IO.ofExcept (Image.Elf.allDynamicSymbols image)
    let read32 (address : Nat) : IO Nat := do
      pure ((← machine.read address 4).toList.foldl (fun value byte => value * 256 + byte.toNat) 0)
    let slot (typ : Nat) (name : String) : IO Nat := do
      match relocations.find? fun relocation => relocation.typ == typ && (names[relocation.symbol]?.map (·.name)) == some name with
      | some relocation => read32 (dynamic.base + relocation.offset)
      | none => throw <| IO.userError s!"{label} has no relocation {typ} of {name}"
    assertEqual s!"{label} the module of its own" ((dynamic.tls.map (·.module)).getD 0) (← slot 68 "dynamic_per_thread")
    assertEqual s!"{label} the module of another's" ((tlsLibrary.tls.map (·.module)).getD 0) (← slot 68 "per_thread")
    assertEqual s!"{label} the offset of another's, from where those are biased" (2 ^ 32 - 0x8000) (← slot 78 "per_thread")
  -- Another thread: its own of all of that.
  let second ← enter
  assertTrue s!"{label} a block is another's" (first != second)
  assertEqual s!"{label} a new block has what it starts with" (3, 11)
    (← call "get", ← call "own_get")
  if runsByModule then
    assertEqual s!"{label} a new block by a module" 21 (← call "dynamic_own")
  assertEqual s!"{label} and doesn't have the other's" 4 (← call "set" [4])
  -- Back: what the first had is still there.
  Bap.Emu.setReg machine.emu ⟨(Bap.Emu.threadRegisters machine.emu.config.syscallAbi).2, .imm machine.architecture.bits, 0, false⟩
    (.bits (BitVec.ofNat machine.architecture.bits first))
  for library in [tlsLibrary, user, dynamic] do
    if let some tls := library.tls then
      machine.write (blocks + tls.module * wordBytes) (number (machine.threadLocalAddress tls first))
  assertEqual s!"{label} a thread keeps its own" 9 (← call "get")
  if runsByModule then
    assertEqual s!"{label} a thread keeps its own by a module" 22 (← call "dynamic_own")
  -- It goes through a checkpoint, as what is laid out has to stay.
  let resumed ← Bap.Linux.Machine.ofCheckpoint (← machine.checkpoint)
  assertEqual s!"{label} a checkpoint knows it" (some 1)
    (((← resumed.loadedLibraries).find? (·.path == "/lib/libtls.so")).bind fun library => library.tls.map (·.module))
  let some getAddress := ← resumed.findSymbol "get" | throw <| IO.userError s!"{label} has no get"
  assertEqual s!"{label} goes on from a checkpoint" 9 ((← resumed.call getAddress []) % 2 ^ 32)
  -- What is thread-local isn't where it has an address.
  assertEqual s!"{label} what is thread-local has no address" none (← machine.findSymbol "per_thread")

/-- Another architecture's library isn't one that this can load, and what `fork` and `execve` do to what is loaded. -/
def testLinuxLibraryProcesses (triple other : String) : IO Unit := do
  let label := s!"Library {triple}"
  let binary (name : String) : IO ByteArray := IO.FS.readBinFile s!"testsuite/bin/{triple}-linux-musl-{name}"
  let foreign := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-files")).addFile "/lib/libdep.so"
    (← IO.FS.readBinFile s!"testsuite/bin/{other}-linux-musl-libdep")
  expectThrow s!"{label} of another machine" ((← Bap.Linux.start foreign "/test" ["/test"]).loadLibrary "libdep.so")
  let kernel := (Bap.Linux.Kernel.empty.addFile "/test" (← binary "libc-exec")).addFile "/script" "#!/test child\n".toUTF8
    |>.addFile "/lib/libdep.so" (← binary "libdep")
  let machine ← Bap.Linux.start kernel "/test" ["/test"]
  let _ ← machine.loadLibrary "libdep.so"
  let first := (← Bap.Emu.currentTask machine.emu).space
  let mut copied : List Nat := []
  let mut executed := false
  for _ in [0:4000] do
    let outcome ← machine.run (quantum := 50) (fuel := 100) fun _ => pure ()
    for (space, libraries) in (← machine.libraries.get).toList do
      if space != first && !libraries.isEmpty && !copied.contains space then copied := space :: copied
    for space in copied do
      if ((← machine.libraries.get).get? space).isNone then executed := true
    if outcome != .outOfFuel then break
  assertTrue s!"{label} a child has what its parent had" (!copied.isEmpty)
  assertTrue s!"{label} what runs another has none of it" executed

/-- The kernel itself: a program isn't needed to say what it does. -/
private def testKernel : IO Unit := do
  let unwrap {α} (result : Bap.Linux.Result α) : IO α := match result with
    | .ok value => pure value
    | .error errno => throw <| IO.userError s!"errno {errno}"
  let start := (Bap.Linux.Kernel.empty.addFile "/etc/name" "bap".toUTF8).addSymlink "/link" "/etc/name"
  assertEqual "Kernel a path is cleaned" ["a", "c"] (Bap.Linux.Path.parts "/" "/a/./b/../c/")
  assertEqual "Kernel .. of the root is the root" ([] : List String) (Bap.Linux.Path.parts "/" "/../..")
  let (kernel, fd) ← unwrap (start.openPath 1 "/" "/link" 0 0)
  assertEqual "Kernel a descriptor is the lowest" 0 fd
  let (kernel, first) ← unwrap (kernel.read 1 fd 2)
  assertEqual "Kernel reads through a link" "ba" (String.fromUTF8! first)
  let (kernel, duplicate) ← unwrap (kernel.dup 1 fd)
  let (kernel, rest) ← unwrap (kernel.read 1 duplicate 9)
  assertEqual "Kernel a dup shares the offset" "p" (String.fromUTF8! rest)
  let forked := kernel.fork 1 2
  let (forked, position) ← unwrap (forked.seek 2 fd false 1 0)
  assertEqual "Kernel seek" 1 position
  let (_, moved) ← unwrap (forked.read 1 fd 9)
  assertEqual "Kernel a fork shares the offset" "ap" (String.fromUTF8! moved)
  let forked ← unwrap (forked.close 2 fd)
  assertTrue "Kernel a fork closes its own" (forked.read 1 fd 1 |>.toOption).isSome
  assertEqual "Kernel a closed descriptor is EBADF" (some Bap.Linux.Errno.ebadf)
    (match forked.read 2 fd 1 with | .error errno => some errno | .ok _ => none)
  let errnoOf {α} (result : Bap.Linux.Result α) : Option Nat := match result with
    | .error errno => some errno
    | .ok _ => none
  assertEqual "Kernel no such file" (some Bap.Linux.Errno.enoent) (errnoOf (start.openPath 1 "/" "/none" 0 0))
  assertEqual "Kernel a file isn't a directory on the way" (some Bap.Linux.Errno.enotdir)
    (errnoOf (start.openPath 1 "/" "/etc/name/x" 0 0))
  let looped := (start.addSymlink "/a" "/b").addSymlink "/b" "/a"
  assertEqual "Kernel links that go round are ELOOP" (some Bap.Linux.Errno.eloop) (errnoOf (looped.openPath 1 "/" "/a" 0 0))
  let (written, out) ← unwrap (start.openPath 1 "/" "/new" (0x40 ||| 2) 0o644)
  let (written, _) ← unwrap (written.writeTo 1 out "abc".toUTF8 5)
  let hole ← unwrap (written.readFrom 1 out 8 3)
  assertEqual "Kernel a write past the end leaves zeros" [0, 0, 97, 98, 99] (hole.toList.map (·.toNat))
  let renamed ← unwrap (start.rename "/" "/etc" "/conf")
  assertTrue "Kernel a directory moves with what is in it" ((renamed.statPath "/" "/conf/name").toOption).isSome
  assertTrue "Kernel it isn't where it was" ((renamed.statPath "/" "/etc/name").toOption).isNone
  assertEqual "Kernel a directory with something in it stays" (some Bap.Linux.Errno.enotempty)
    (errnoOf (start.remove "/" "/etc" true))
  assertEqual "Kernel the entries are sorted" ["etc", "link"] ((start.children "/").map (·.1))
  assertEqual "Kernel struct stat" 144 (Bap.Linux.Abi.stat { inode := 1, mode := 0, size := 0, links := 1, accessed := 0, modified := 0, changed := 0 }).size
  match Bap.Linux.Elf.parse "not an elf".toUTF8 with
  | .error _ => IO.println "ok: Kernel what isn't ELF doesn't start"
  | .ok _ => throw <| IO.userError "Kernel started what isn't ELF"

/-- Where the fields are, as qemu-user has them from the structures of Linux. -/
def testLinuxLayouts : IO Unit := do
  let word (bytes : ByteArray) (at_ : Nat) (big : Bool) : Nat :=
    let part := (List.range 4).map fun index => bytes[at_ + (if big then 3 - index else index)]!.toNat <<< (8 * index)
    part.foldl (· + ·) 0
  let value : Bap.Linux.Kernel.Stat := { inode := 7, mode := 0o100644, size := 0x12345, links := 2, accessed := 0, modified := 0, changed := 0 }
  let cases : List (String × Bap.Linux.Architecture × Bool × Nat × Nat × Nat × Nat) :=
    [("i686", .i686, false, 96, 44, 16, 20), ("arm", .arm, false, 104, 48, 16, 20),
     ("mips", .mips 32 true false, true, 104, 60, 24, 28), ("powerpc", .powerpc 32 true, true, 104, 52, 16, 20)]
  for (name, architecture, big, size, sizeAt, modeAt, linksAt) in cases do
    let bytes := architecture.stat value
    assertEqual s!"stat64 of {name} is its size" size bytes.size
    assertEqual s!"stat64 of {name} has the size of the file" 0x12345 (word bytes sizeAt big)
    assertEqual s!"stat64 of {name} has the mode" 0o100644 (word bytes modeAt big)
    assertEqual s!"stat64 of {name} has the links" 2 (word bytes linksAt big)
  let filesystems : List (String × Bool × Bool × Bool × Nat × Nat) :=
    [("i686", false, false, false, 0, 56), ("mips", false, true, true, 0, 64), ("powerpc", false, true, false, 0, 56),
     ("x86-64", true, false, false, 0, 64), ("mips64", true, true, true, 4, 76), ("powerpc64", true, true, false, 4, 68)]
  for (name, wide, big, mips, typeAt, nameAt) in filesystems do
    let bytes := Bap.Linux.Abi.statfs wide big mips
    assertEqual s!"statfs of {name} has the type" 0x01021994 (word bytes typeAt big)
    assertEqual s!"statfs of {name} has the longest name" 255 (word bytes nameAt big)
  let refreshed := Bap.Linux.Proc.refresh Bap.Linux.Kernel.empty 1 2 [1] fun _ => [1, 2]
  assertTrue "/proc has each task of a process" (refreshed.statPath "/" "/proc/1/task/2/comm" |>.toOption).isSome
  assertTrue "/proc/thread-self is the task that looks" (refreshed.statPath "/" "/proc/thread-self/status" |>.toOption).isSome
  assertTrue "/proc has no task that isn't there" (refreshed.statPath "/" "/proc/1/task/3/comm" |>.toOption).isNone
  assertEqual "sysinfo of 32 bits has the unit" 1 (word (Bap.Linux.Abi.sysinfo false false 5 1) 52 false)
  assertEqual "sysinfo of 64 bits has the unit" 1 (word (Bap.Linux.Abi.sysinfo true false 5 1) 104 false)
  assertEqual "sysinfo of 32 bits is its size" 64 (Bap.Linux.Abi.sysinfo false false 5 1).size
  assertEqual "sysinfo of 64 bits is its size" 112 (Bap.Linux.Abi.sysinfo true false 5 1).size

/-- Programs of libc under the virtual kernel, dynamic, if there is a compiler to make them. The program does all of
what it does to files in the kernel's, and says what it found. -/
def testLinuxPrograms : IO Unit := do
  if System.Platform.isWindows || !System.Platform.target.startsWith "x86_64" then
    IO.println "ok: skipped the programs of libc, as nothing here compiles them"
  else
    let expected := "args 2 arg1\ncwd /\nread hello 42\nsize 9 dir 0\nseek yz\ndup x\nlink c\nentries 3\ngone -1\ntime 1\nmalloc 1\nnope 1\n"
    let compile (extra : Array String) (binary : String) : IO Bool := do
      match ← (IO.Process.output { cmd := "gcc", args := extra ++ #["-O1", "testsuite/src/libc-files.c", "-o", binary] }).toBaseIO with
      | .ok { exitCode := 0, .. } => pure true
      | _ => pure false
    let run (kernel : Bap.Linux.Kernel) (path : String) : IO (Bap.Tasks.ScheduleOutcome × String) := do
      let written ← IO.mkRef ByteArray.empty
      let machine ← Bap.Linux.start kernel path [path, "arg1"]
      let outcome ← machine.run fun data => written.modify (· ++ data)
      pure (outcome, String.fromUTF8! (← written.get))
    let dynamicBinary := "native/build/libc-files-dynamic"
    if ← compile #[] dynamicBinary then
      let kernel ← Bap.Linux.Kernel.empty.copyProgramFromHost dynamicBinary
      let (outcome, text) ← run kernel dynamicBinary
      assertEqual "Linux a dynamic program has its status" (Bap.Tasks.ScheduleOutcome.finished (Bap.Tasks.exitedStatus 5)) outcome
      assertEqual "Linux a dynamic program finds its files" expected text
    -- Floating point, as the machine that this runs on does it: whatever it prints, the emulator prints.
    let floats := "native/build/libc-floats"
    let compiled ← (IO.Process.output
      { cmd := "gcc", args := #["-static", "-O1", "testsuite/src/libc-floats.c", "-o", floats, "-lm"] }).toBaseIO
    if let .ok { exitCode := 0, .. } := compiled then
      let native ← IO.Process.output { cmd := floats }
      let written ← IO.mkRef ByteArray.empty
      let machine ← Bap.Linux.start (Bap.Linux.Kernel.empty.addFile "/f" (← IO.FS.readBinFile floats)) "/f" ["/f"]
      let outcome ← machine.run fun data => written.modify (· ++ data)
      assertEqual "Linux a program of floating point ends" (Bap.Tasks.ScheduleOutcome.finished 0) outcome
      assertEqual "Linux floating point is what the machine does" native.stdout (String.fromUTF8! (← written.get))
    -- Nothing but what is in the kernel: without its libraries, a dynamic program doesn't start.
    if ← compile #[] dynamicBinary then
      let alone := Bap.Linux.Kernel.empty.addFile dynamicBinary (← IO.FS.readBinFile dynamicBinary)
      expectThrow "Linux what isn't in the kernel isn't there" (Bap.Linux.start alone dynamicBinary [dynamicBinary])

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
    ⟨{ env := env }, pc, [region 0x10 [1, 2]], false, [], 0, 0, none, [], none, {}⟩
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
  -- What a fetch remembers of a page doesn't outlive the permission or the mapping.
  let three ← LLVM.assemble "riscv64" "addi a0, a0, 1\naddi a0, a0, 1\naddi a0, a0, 1"
  let protecting ← Tuned.riscv64 three 0 0
  Bap.Emu.setReg protecting a0 (.bits (BitVec.ofNat 64 0))
  assertTrue "Emu fetches before it loses the permission" (← Bap.Emu.step protecting)
  Bap.Emu.protect protecting 0 12 rw
  expectThrow "Emu doesn't fetch what lost the permission" (Bap.Emu.step protecting)
  let unmapping ← Tuned.riscv64 three 0 0
  Bap.Emu.setReg unmapping a0 (.bits (BitVec.ofNat 64 0))
  assertTrue "Emu fetches before the unmapping" (← Bap.Emu.step unmapping)
  Bap.Emu.unmap unmapping 0 12
  expectThrow "Emu doesn't fetch what was unmapped" (Bap.Emu.step unmapping)
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
  let stubResult ← Bap.Emu.call emu 0x1000 0x2000 [41]
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
  testCloneThread
  testProcesses
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
  testBlrLink
  testZeroRegisterWidth
  testThumbItFlags
  testKernel
  allEmulatorTests
  tuningRef.set (some (1, 4096, 16))
  allEmulatorTests
  tuningRef.set (some (1, 128, 1))
  stepwise.set true
  allEmulatorTests

end Bap.Tests.Emu
