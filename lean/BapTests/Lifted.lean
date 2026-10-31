import BapTests.Support

namespace Bap.Tests.Lifted

open Bap
open Bap.Bil

private def reg (name : String) : Var := ⟨name, .imm 64, 0, false⟩
private def reg1 (name : String) : Var := ⟨name, .imm 1, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 64 value)
private def state (var : Var) (value : Nat) : State :=
  { env := [(var, .bits (BitVec.ofNat 64 value))] }

private def fixed (block : Primus.Lifted.Block) : Primus.Lifted.Fetch × Primus.Lifted.Lift :=
  (fun _ => pure (ByteArray.mk #[1]), fun _ _ => pure block)

private def expectThrow (name : String) (action : IO Unit) : IO Unit := do
  let threw ← try
      action
      pure false
    catch _ => pure true
  assertTrue name threw

set_option maxRecDepth 4000 in
def run : IO Unit := do
  let program ← Jit.compile [.set 0 40, .add 1 0 2, .jumpSlot 1]
  let (next, slots) ← Jit.run program #[0, 0]
  assertEqual "native JIT returns the next PC" 42 next
  assertEqual "native JIT updates state slots" 42 (slots[1]!.toNat)
  let persistent ← Jit.createMemory #[0x1000] #[0]
  let storeProgram ← Jit.compile [.set 0 0x1000, .set 1 41, .memStore 0 1 1 false, .jump 0]
  let loadProgram ← Jit.compile [.set 0 0x1000, .memLoad 1 0 1 false, .jumpSlot 1]
  let (_, _, changedAddresses, changedValues) ← Jit.runWithPersistentMemory storeProgram #[0, 0] persistent none
  assertEqual "persistent JIT reports changed addresses" #[0x1000] changedAddresses
  assertEqual "persistent JIT reports changed values" #[41] changedValues
  let (_, loaded, _, _) ← Jit.runWithPersistentMemory loadProgram #[0, 0] persistent none
  assertEqual "persistent JIT memory is reused across executions" 41 (loaded[1]!.toNat)
  let (memoryAddresses, memoryValues) ← Jit.dumpMemory persistent
  assertEqual "persistent JIT memory dump size" 1 memoryAddresses.size
  assertEqual "persistent JIT memory dump value" 41 (memoryValues[0]!.toNat)
  let selectProgram ← Jit.compile [
    .set 0 0,
    .set 1 0xfffffffffffffffe,
    .signExtend 64 2 1,
    .bin .slt 3 2 0,
    .set 4 5,
    .set 5 0xfffffffffffffffb,
    .select 6 3 5 4,
    .jumpSlot 6
  ]
  let (_, selectSlots) ← Jit.run selectProgram (Array.replicate 7 0)
  assertEqual "native signed select" 0xfffffffffffffffb (selectSlots[6]!.toNat)

  let x := reg "x"
  let y := reg "y"
  -- A jump out of a block before a write leaves the variable as it was, here without a value, like the interpreter.
  let early ← Primus.Lifted.Engine.create
  let earlyBlock : Primus.Lifted.Block := {
    address := 0x1000
    next := 0x1004
    program := [.ifElse (.var (⟨"c", .imm 1, 0, false⟩ : Var)) [.jmp (int 0x2000)] [], .move x (int 40), .jmp (int 0x3000)]
  }
  let earlyState (bit : Nat) : State := { env := [(⟨"c", .imm 1, 0, false⟩, .bits (BitVec.ofNat 1 bit))] }
  let (earlyFetch, earlyLift) := fixed earlyBlock
  let earlyTaken ← Primus.Lifted.runBlock early earlyFetch earlyLift (earlyState 1) 0x1000
  assertEqual "native jump before a write has the target" 0x2000 earlyTaken.pc
  assertTrue "native jump before a write leaves it unbound" (match Bil.lookup earlyTaken.state.env x with | .error _ => true | .ok _ => false)
  assertEqual "the block ran natively" 1 (← Primus.Lifted.stats early).nativeRuns
  let earlyFall ← Primus.Lifted.runBlock early earlyFetch earlyLift (earlyState 0) 0x1000
  assertEqual "native run past the branch has the target" 0x3000 earlyFall.pc
  assertBits "native run past the branch writes" (BitVec.ofNat 64 40) (Bil.lookup earlyFall.state.env x)
  let engine ← Primus.Lifted.Engine.create
  let block : Primus.Lifted.Block := {
    address := 0x1000
    next := 0x1004
    program := [.move x (int 40), .move y (.bin .add (.var x) (int 2)), .jmp (.var y)]
  }
  let (fetch, lift) := fixed block
  let result ← Primus.Lifted.runBlock engine fetch lift {} 0x1000
  assertEqual "lifted computed jump" 42 result.pc
  assertBits "lifted native result" (BitVec.ofNat 64 42) (lookup result.state.env y)
  let stats ← Primus.Lifted.stats engine
  assertEqual "lifted block uses native code" 1 stats.nativeRuns
  assertEqual "lifted block avoids fallback" 0 stats.interpretedRuns

  let cachedEngine ← Primus.Lifted.Engine.create
  let liftCount ← IO.mkRef 0
  let cachedBlock : Primus.Lifted.Block := {
    address := 0x2000
    next := 0x2004
    program := [.move y (.bin .add (.var x) (int 2)), .jmp (.var y)]
  }
  let cachedFetch : Primus.Lifted.Fetch := fun _ => pure (ByteArray.mk #[1, 2, 3])
  let cachedLift : Primus.Lifted.Lift := fun _ _ => do
    liftCount.modify (· + 1)
    pure cachedBlock
  let first ← Primus.Lifted.runBlock cachedEngine cachedFetch cachedLift (state x 40) 0x2000
  let second ← Primus.Lifted.runBlock cachedEngine cachedFetch cachedLift (state x 10) 0x2000
  assertEqual "cached native code uses new state" (42, 12) (first.pc, second.pc)
  let cachedStats ← Primus.Lifted.stats cachedEngine
  assertEqual "instruction lifted once" 1 (← liftCount.get)
  assertEqual "cached native block compiled once" 1 cachedStats.nativeCompilations
  assertEqual "cached native block executed twice" 2 cachedStats.nativeRuns
  assertEqual "instruction cache hit" 1 cachedStats.cacheHits

  let versionEngine ← Primus.Lifted.Engine.create
  let versionBytes ← IO.mkRef (ByteArray.mk #[1])
  let versionFetch : Primus.Lifted.Fetch := fun _ => versionBytes.get
  let versionLift : Primus.Lifted.Lift := fun address code =>
    pure ⟨address, address + 4, [.move y (int code[0]!.toNat), .jmp (.var y)]⟩
  let _ ← Primus.Lifted.runBlock versionEngine versionFetch versionLift {} 0x17000
  Primus.Lifted.discardRange versionEngine 0x17000 0x17000
  let _ ← Primus.Lifted.runBlock versionEngine versionFetch versionLift {} 0x17000
  let restoredStats ← Primus.Lifted.stats versionEngine
  assertEqual "matching block version avoids recompilation" 1 restoredStats.nativeCompilations
  assertEqual "matching block version avoids relifting" 1 restoredStats.lifts
  versionBytes.set (ByteArray.mk #[2])
  let _ ← Primus.Lifted.runBlock versionEngine versionFetch versionLift {} 0x17000
  versionBytes.set (ByteArray.mk #[1])
  let _ ← Primus.Lifted.runBlock versionEngine versionFetch versionLift {} 0x17000
  let versionStats ← Primus.Lifted.stats versionEngine
  assertEqual "changed block compiles a new version" 2 versionStats.nativeCompilations
  assertEqual "restored block version avoids another compilation" 2 versionStats.nativeCompilations
  assertEqual "restored block version avoids another lift" 2 versionStats.lifts
  assertEqual "all block versions execute natively" 4 versionStats.nativeRuns

  let chainedEngine ← Primus.Lifted.Engine.create
  let z := reg "z"
  let chainedFetch : Primus.Lifted.Fetch := fun pc =>
    match pc with
    | 0x1000 => pure (ByteArray.mk #[1])
    | 0x2000 => pure (ByteArray.mk #[2])
    | _ => throw <| IO.userError s!"unexpected fetch at {pc}"
  let chainedLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x1000 => pure ⟨pc, pc + 4, [.jmp (int 0x2000)]⟩
    | 0x2000 => pure ⟨pc, pc + 4, [.move z (int 9)]⟩
    | _ => throw <| IO.userError s!"unexpected lift at {pc}"
  let chained ← Primus.Lifted.run chainedEngine chainedFetch chainedLift {} 0x1000
  assertEqual "direct jump chains into the next block" 0x2004 chained.pc
  assertBits "chained block preserves native state" (BitVec.ofNat 64 9) (lookup chained.state.env z)
  let chainedStats ← Primus.Lifted.stats chainedEngine
  assertEqual "two blocks execute natively" 2 chainedStats.nativeRuns

  let fallbackEngine ← Primus.Lifted.Engine.create
  let memoryVar : Var := ⟨"mem", .mem 64 8, 0, false⟩
  let fallbackBlock : Primus.Lifted.Block := {
    address := 0x3000
    next := 0x3004
    program := [.move y (.load
      (.store (.var memoryVar) (int 0) (.int (BitVec.ofNat 8 0x12)) .little 1)
      (int 0) .little 1)]
  }
  let (fallbackFetch, fallbackLift) := fixed fallbackBlock
  let fallbackInitial : State := { env := [
    (memoryVar, .memory (Memory.empty 64)),
    (x, .bits (BitVec.ofNat 64 0))
  ] }
  let fallback ← Primus.Lifted.runBlock fallbackEngine fallbackFetch fallbackLift fallbackInitial 0x3000
  assertBits "unsupported expression uses BIL" (BitVec.ofNat 8 0x12) (lookup fallback.state.env y)
  let fallbackStats ← Primus.Lifted.stats fallbackEngine
  assertEqual "fallback is interpreted" 1 fallbackStats.interpretedRuns
  assertEqual "fallback is not JIT compiled" 0 fallbackStats.nativeCompilations
  let fallbackEvents ← IO.mkRef []
  let fallbackObserver : Jit.MemoryObserver := fun write address size value =>
    fallbackEvents.modify fun events => (write, address, size, value) :: events
  let _ ← Primus.Lifted.runBlockObserved fallbackEngine fallbackFetch fallbackLift fallbackInitial 0x3000
    (some fallbackObserver)
  assertEqual "interpreted memory hooks observe nested operations"
    [(true, 0, 1, 0x12), (false, 0, 1, 0)] (← fallbackEvents.get).reverse

  let staleEngine ← Primus.Lifted.Engine.create
  let bytes ← IO.mkRef (ByteArray.mk #[1])
  let staleFetch : Primus.Lifted.Fetch := fun _ => bytes.get
  let staleLift : Primus.Lifted.Lift := fun pc code =>
    pure ⟨pc, pc + 1, [.move y (int code[0]!.toNat)]⟩
  let before ← Primus.Lifted.runBlock staleEngine staleFetch staleLift {} 0x4000
  bytes.set (ByteArray.mk #[2])
  let after ← Primus.Lifted.runBlock staleEngine staleFetch staleLift {} 0x4000
  assertBits "original bytes retain their lift" (BitVec.ofNat 64 1) (lookup before.state.env y)
  assertBits "changed bytes are lifted again" (BitVec.ofNat 64 2) (lookup after.state.env y)
  let staleStats ← Primus.Lifted.stats staleEngine
  assertEqual "changed bytes invalidate the cached lift" 2 staleStats.lifts

  let primusEngine ← Primus.Lifted.Engine.create
  let instructionBytes ← LLVM.assemble "x86_64" "movq $42, %rax"
  let primusFetch : Primus.Lifted.Fetch := fun _ => pure instructionBytes
  let primusLift : Primus.Lifted.Lift := fun address code => do
    let insn ← Target.LLVMLift.decodeX86 address address code
    pure ⟨insn.address, insn.next, insn.bil⟩
  let primusResult ← Primus.Lifted.runBlock primusEngine primusFetch primusLift {} 0x5000
  assertBits "Primus x86 semantics execute through JIT" (BitVec.ofNat 64 42)
    (lookup primusResult.state.env (reg "RAX"))
  let primusStats ← Primus.Lifted.stats primusEngine
  assertEqual "Primus x86 block is native" 1 primusStats.nativeRuns
  assertEqual "Primus x86 block does not fall back" 0 primusStats.interpretedRuns

  let x8 : Var := ⟨"x8", .imm 8, 0, false⟩
  let y8 : Var := ⟨"y8", .imm 8, 0, false⟩
  let z8 : Var := ⟨"z8", .imm 8, 0, false⟩
  let flag : Var := ⟨"flag", .imm 1, 0, false⟩
  let narrowEngine ← Primus.Lifted.Engine.create
  let narrowBlock : Primus.Lifted.Block := {
    address := 0x6000
    next := 0x6001
    program := [
      .move z8 (.bin .rshift (.bin .add (.var x8) (.var y8)) (.int (BitVec.ofNat 8 2))),
      .move flag (.bin .lt (.var x8) (.var y8))
    ]
  }
  let (narrowFetch, narrowLift) := fixed narrowBlock
  let narrowInitial : State := { env := [
    (x8, .bits (BitVec.ofNat 8 200)),
    (y8, .bits (BitVec.ofNat 8 100))
  ] }
  let narrow ← Primus.Lifted.runBlock narrowEngine narrowFetch narrowLift narrowInitial 0x6000
  assertBits "native narrow arithmetic wraps before shifting" (BitVec.ofNat 8 11)
    (lookup narrow.state.env z8)
  assertBits "native unsigned comparison" (BitVec.ofNat 1 0) (lookup narrow.state.env flag)
  let narrowStats ← Primus.Lifted.stats narrowEngine
  assertEqual "narrow expression tree is native" 1 narrowStats.nativeRuns

  let shiftEngine ← Primus.Lifted.Engine.create
  let shiftBlock : Primus.Lifted.Block := {
    address := 0x7000
    next := 0x7001
    program := [.move z (.bin .lshift (.var x) (.var y))]
  }
  let (shiftFetch, shiftLift) := fixed shiftBlock
  let shiftInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 1)),
    (y, .bits (BitVec.ofNat 64 64))
  ] }
  let shifted ← Primus.Lifted.runBlock shiftEngine shiftFetch shiftLift shiftInitial 0x7000
  assertBits "native oversized shift is zero" (BitVec.ofNat 64 0) (lookup shifted.state.env z)

  let armEngine ← Primus.Lifted.Engine.create
  let armBytes ← LLVM.assemble "aarch64" "add x0, x0, x1"
  let armFetch : Primus.Lifted.Fetch := fun _ => pure armBytes
  let armLift : Primus.Lifted.Lift := fun address code => do
    let insn ← Target.LLVMLift.decodeAArch64 address address code
    pure ⟨insn.address, insn.next, insn.bil⟩
  let armInitial : State := { env := [
    (reg "X0", .bits (BitVec.ofNat 64 40)),
    (reg "X1", .bits (BitVec.ofNat 64 2))
  ] }
  let armResult ← Primus.Lifted.runBlock armEngine armFetch armLift armInitial 0x8000
  assertBits "Primus AArch64 ADD executes through LLVM JIT" (BitVec.ofNat 64 42)
    (lookup armResult.state.env (reg "X0"))
  let armStats ← Primus.Lifted.stats armEngine
  assertEqual "Primus AArch64 ADD is native" 1 armStats.nativeRuns
  assertEqual "Primus AArch64 ADD does not fall back" 0 armStats.interpretedRuns

  let cmpBytes ← LLVM.assemble "aarch64" "cmp x8, x9"
  let cmpResult ← Primus.Lifted.runBlock armEngine (fun _ => pure cmpBytes) armLift
    { env := [(reg "X8", .bits (BitVec.ofNat 64 0)), (reg "X9", .bits (BitVec.ofNat 64 0))] } 0x8004
  assertBits "Primus AArch64 CMP sets ZF for equal operands" (BitVec.ofNat 1 1)
    (lookup cmpResult.state.env ⟨"ZF", .imm 1, 0, false⟩)

  let clzBytes ← LLVM.assemble "aarch64" "clz x9, x9"
  let clzResult ← Primus.Lifted.runBlock armEngine (fun _ => pure clzBytes) armLift
    { env := [(reg "X9", .bits (BitVec.ofNat 64 1))] } 0x8004
  assertBits "Primus AArch64 CLZ accepts a shared destination and source" (BitVec.ofNat 64 63)
    (lookup clzResult.state.env (reg "X9"))
  let clzDistinctBytes ← LLVM.assemble "aarch64" "clz x9, x10"
  let clzDistinct ← Primus.Lifted.runBlock armEngine (fun _ => pure clzDistinctBytes) armLift
    { env := [(reg "X10", .bits (BitVec.ofNat 64 0x8000000000000000))] } 0x8008
  assertBits "Primus AArch64 CLZ counts distinct operand bits" (BitVec.ofNat 64 0)
    (lookup clzDistinct.state.env (reg "X9"))

  let ashr8 : Var := ⟨"ashr8", .imm 8, 0, false⟩
  let not8 : Var := ⟨"not8", .imm 8, 0, false⟩
  let ite8 : Var := ⟨"ite8", .imm 8, 0, false⟩
  let signedEngine ← Primus.Lifted.Engine.create
  let signedBlock : Primus.Lifted.Block := {
    address := 0x9000
    next := 0x9001
    program := [
      .move z8 (.bin .sdiv (.var x8) (.var y8)),
      .move flag (.bin .slt (.var x8) (.var y8)),
      .move ashr8 (.bin .ashift (.var x8) (.int (BitVec.ofNat 8 1))),
      .move not8 (.un .not (.var x8)),
      .move ite8 (.ite (.bin .slt (.var x8) (.var y8)) (.int (BitVec.ofNat 8 42)) (.int (BitVec.ofNat 8 0))),
      .move z (.cast .signed 64 (.var x8))
    ]
  }
  let (signedFetch, signedLift) := fixed signedBlock
  let signedInitial : State := { env := [
    (x8, .bits (BitVec.ofNat 8 0xfe)),
    (y8, .bits (BitVec.ofNat 8 2))
  ] }
  let signed ← Primus.Lifted.runBlock signedEngine signedFetch signedLift signedInitial 0x9000
  assertBits "native signed division" (BitVec.ofNat 8 0xff) (lookup signed.state.env z8)
  assertBits "native signed comparison" (BitVec.ofNat 1 1) (lookup signed.state.env flag)
  assertBits "native arithmetic shift" (BitVec.ofNat 8 0xff) (lookup signed.state.env ashr8)
  assertBits "native bitwise not" (BitVec.ofNat 8 1) (lookup signed.state.env not8)
  assertBits "native conditional expression" (BitVec.ofNat 8 42) (lookup signed.state.env ite8)
  assertBits "native sign extension" (BitVec.ofNat 64 0xfffffffffffffffe) (lookup signed.state.env z)
  let signedStats ← Primus.Lifted.stats signedEngine
  assertEqual "signed expression tree is native" 1 signedStats.nativeRuns

  let w := reg "w"
  let s := reg "s"
  let r := reg "r"
  let divisionEngine ← Primus.Lifted.Engine.create
  let divisionBlock : Primus.Lifted.Block := {
    address := 0xa000
    next := 0xa001
    program := [
      .move z (.bin .div (.var x) (.var y)),
      .move w (.bin .rem (.var x) (.var y)),
      .move s (.bin .sdiv (.var x) (.var y)),
      .move r (.bin .srem (.var x) (.var y))
    ]
  }
  let (divisionFetch, divisionLift) := fixed divisionBlock
  let zeroInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 40)),
    (y, .bits (BitVec.ofNat 64 0))
  ] }
  let divided ← Primus.Lifted.runBlock divisionEngine divisionFetch divisionLift zeroInitial 0xa000
  assertBits "native unsigned division by zero" (BitVec.ofNat 64 0xffffffffffffffff) (lookup divided.state.env z)
  assertBits "native unsigned remainder by zero" (BitVec.ofNat 64 40) (lookup divided.state.env w)
  assertBits "native signed division by zero" (BitVec.ofNat 64 0xffffffffffffffff) (lookup divided.state.env s)
  assertBits "native signed remainder by zero" (BitVec.ofNat 64 40) (lookup divided.state.env r)
  let overflowInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 0x8000000000000000)),
    (y, .bits (BitVec.ofNat 64 0xffffffffffffffff))
  ] }
  let overflow ← Primus.Lifted.runBlock divisionEngine divisionFetch divisionLift overflowInitial 0xa000
  assertBits "native signed division overflow wraps" (BitVec.ofNat 64 0x8000000000000000)
    (lookup overflow.state.env s)
  assertBits "native signed remainder overflow is zero" (BitVec.ofNat 64 0) (lookup overflow.state.env r)
  let divisionStats ← Primus.Lifted.stats divisionEngine
  assertEqual "native division guards execute twice" 2 divisionStats.nativeRuns
  let negativeInitial : Bil.State := { env := [
    (x, .bits (BitVec.ofInt 64 (-40))),
    (y, .bits (BitVec.ofNat 64 0))
  ] }
  let negative ← Primus.Lifted.runBlock divisionEngine divisionFetch divisionLift negativeInitial 0xa000
  assertBits "native signed division of a negative by zero" (BitVec.ofNat 64 1) (lookup negative.state.env s)

  let riscvEngine ← Primus.Lifted.Engine.create
  let riscvBytes ← LLVM.assemble "riscv64" "slt a0, a1, a2"
  let riscvFetch : Primus.Lifted.Fetch := fun _ => pure riscvBytes
  let riscvLift : Primus.Lifted.Lift := fun address code => do
    let insn ← Target.LLVMLift.decodeRISCV address address code
    pure ⟨insn.address, insn.next, insn.bil⟩
  let riscvInitial : State := { env := [
    (reg "X11", .bits (BitVec.ofNat 64 0xffffffffffffffff)),
    (reg "X12", .bits (BitVec.ofNat 64 1))
  ] }
  let riscvResult ← Primus.Lifted.runBlock riscvEngine riscvFetch riscvLift riscvInitial 0xb000
  assertBits "Primus RISC-V SLT executes through LLVM JIT" (BitVec.ofNat 64 1)
    (lookup riscvResult.state.env (reg "X10"))
  let riscvStats ← Primus.Lifted.stats riscvEngine
  assertEqual "Primus RISC-V SLT is native" 1 riscvStats.nativeRuns
  assertEqual "Primus RISC-V SLT does not fall back" 0 riscvStats.interpretedRuns

  let conditionalEngine ← Primus.Lifted.Engine.create
  let conditionalBlock : Primus.Lifted.Block := {
    address := 0xc000
    next := 0xc001
    program := [
      .ifElse (.bin .lt (.var x) (.var y))
        [
          .move z (.bin .add (.var x) (.var y)),
          .ifElse (.bin .eq (.var z) (int 5)) [.move flag (.int (BitVec.ofNat 1 1))] [.move flag (.int (BitVec.ofNat 1 0))]
        ]
        [.move z (.bin .sub (.var x) (.var y)), .move flag (.int (BitVec.ofNat 1 0))],
      .move w (.bin .add (.var z) (int 1))
    ]
  }
  let (conditionalFetch, conditionalLift) := fixed conditionalBlock
  let trueInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 2)),
    (y, .bits (BitVec.ofNat 64 3))
  ] }
  let falseInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 5)),
    (y, .bits (BitVec.ofNat 64 3))
  ] }
  let taken ← Primus.Lifted.runBlock conditionalEngine conditionalFetch conditionalLift trueInitial 0xc000
  let notTaken ← Primus.Lifted.runBlock conditionalEngine conditionalFetch conditionalLift falseInitial 0xc000
  assertBits "native conditional true value" (BitVec.ofNat 64 5) (lookup taken.state.env z)
  assertBits "native conditional true continuation" (BitVec.ofNat 64 6) (lookup taken.state.env w)
  assertBits "native nested conditional" (BitVec.ofNat 1 1) (lookup taken.state.env flag)
  assertBits "native conditional false value" (BitVec.ofNat 64 2) (lookup notTaken.state.env z)
  assertBits "native conditional false continuation" (BitVec.ofNat 64 3) (lookup notTaken.state.env w)
  assertBits "native conditional false flag" (BitVec.ofNat 1 0) (lookup notTaken.state.env flag)
  let conditionalStats ← Primus.Lifted.stats conditionalEngine
  assertEqual "both conditional paths execute natively" 2 conditionalStats.nativeRuns
  assertEqual "conditional paths avoid fallback" 0 conditionalStats.interpretedRuns

  let pathEngine ← Primus.Lifted.Engine.create
  let missing := reg "missing"
  let pathBlock : Primus.Lifted.Block := {
    address := 0xd000
    next := 0xd001
    program := [.ifElse (.int (BitVec.ofNat 1 0)) [.move z (.var missing)] [.move z (int 7)]]
  }
  let (pathFetch, pathLift) := fixed pathBlock
  let pathResult ← Primus.Lifted.runBlock pathEngine pathFetch pathLift {} 0xd000
  assertEqual "unexecuted bad path uses BIL fallback" 0xd001 pathResult.pc
  assertBits "path-sensitive fallback preserves the taken write" (BitVec.ofNat 64 7)
    (lookup pathResult.state.env z)
  let pathStats ← Primus.Lifted.stats pathEngine
  assertEqual "path-sensitive fallback is interpreted" 1 pathStats.interpretedRuns
  assertEqual "path-sensitive fallback avoids native execution" 0 pathStats.nativeRuns

  let smodEngine ← Primus.Lifted.Engine.create
  let smodBlock : Primus.Lifted.Block := {
    address := 0xe000
    next := 0xe001
    program := [.move z (.bin .smod (.var x) (.var y))]
  }
  let (smodFetch, smodLift) := fixed smodBlock
  let smodCases := [
    (40, 3, 1),
    (0xfffffffffffffffb, 2, 1),
    (5, 0xfffffffffffffffe, 0xfffffffffffffffb),
    (0xfffffffffffffffb, 0xfffffffffffffffe, 0xfffffffffffffffb),
    (40, 0, 40)
  ]
  smodCases.forM fun test => do
    let initial : State := { env := [
      (x, .bits (BitVec.ofNat 64 test.1)),
      (y, .bits (BitVec.ofNat 64 test.2.1))
    ] }
    let result ← Primus.Lifted.runBlock smodEngine smodFetch smodLift initial 0xe000
    let (expected, _) ← match Bil.run smodBlock.program initial with
      | .ok result => pure result
      | .error error => throw <| IO.userError error
    match Bil.lookup expected.env z with
    | .ok (.bits expectedValue) =>
      assertBits s!"native smod {test.1} {test.2.1}" expectedValue (lookup result.state.env z)
    | _ => throw <| IO.userError "BIL smod result is missing"
  let smodStats ← Primus.Lifted.stats smodEngine
  assertEqual "all smod cases execute natively" 5 smodStats.nativeRuns

  let jumpEngine ← Primus.Lifted.Engine.create
  let jumpBlock : Primus.Lifted.Block := {
    address := 0xf000
    next := 0xf001
    program := [
      .move z (int 42),
      .ifElse (.bin .eq (.var x) (int 1))
        [.move y (int 9), .jmp (.var z)]
        [.move y (int 7)]
    ]
  }
  let (jumpFetch, jumpLift) := fixed jumpBlock
  let jumped ← Primus.Lifted.runBlock jumpEngine jumpFetch jumpLift (state x 1) 0xf000
  assertEqual "conditional body jumps natively" 42 jumped.pc
  assertBits "conditional jump preserves writes" (BitVec.ofNat 64 9) (lookup jumped.state.env y)
  let continued ← Primus.Lifted.runBlock jumpEngine jumpFetch jumpLift (state x 0) 0xf000
  assertEqual "conditional jump fallthrough" 0xf001 continued.pc
  assertBits "conditional fallthrough preserves writes" (BitVec.ofNat 64 7) (lookup continued.state.env y)
  let jumpStats ← Primus.Lifted.stats jumpEngine
  assertEqual "both conditional jump paths execute natively" 2 jumpStats.nativeRuns

  let a : Var := ⟨"a", .imm 32, 0, false⟩
  let count : Var := ⟨"count", .imm 32, 0, false⟩
  let int32 (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
  let loopEngine ← Primus.Lifted.Engine.create
  let loopBlock : Primus.Lifted.Block := {
    address := 0x10000
    next := 0x10001
    program := [
      .move a (int32 3),
      .move count (int32 0),
      .while (.bin .neq (.var a) (int32 1)) [
        .ifElse (.bin .eq (.bin .rem (.var a) (int32 2)) (int32 0))
          [.move a (.bin .div (.var a) (int32 2))]
          [.move a (.bin .add (.bin .mul (.var a) (int32 3)) (int32 1))],
        .move count (.bin .add (.var count) (int32 1))
      ]
    ]
  }
  let (loopFetch, loopLift) := fixed loopBlock
  let loopResult ← Primus.Lifted.runBlock loopEngine loopFetch loopLift {} 0x10000
  let (expectedLoop, _) ← match Bil.run loopBlock.program {} with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  match Bil.lookup expectedLoop.env a, Bil.lookup expectedLoop.env count with
  | .ok (.bits expectedA), .ok (.bits expectedCount) =>
    assertBits "native while result" expectedA (lookup loopResult.state.env a)
    assertBits "native while iteration count" expectedCount (lookup loopResult.state.env count)
  | _, _ => throw <| IO.userError "BIL while result is missing"
  let loopStats ← Primus.Lifted.stats loopEngine
  assertEqual "native while avoids fallback" 0 loopStats.interpretedRuns

  -- a finished loop goes on with the next statement
  let afterLoop := reg "afterLoop"
  let followedBlock : Primus.Lifted.Block := {
    address := 0x10100
    next := 0x10101
    program := [
      .move a (int32 0),
      .while (.bin .neq (.var a) (int32 3)) [.move a (.bin .add (.var a) (int32 1))],
      .move afterLoop (int 7)
    ]
  }
  let followedEngine ← Primus.Lifted.Engine.create
  let (followedFetch, followedLift) := fixed followedBlock
  let followed ← Primus.Lifted.runBlock followedEngine followedFetch followedLift {} 0x10100
  assertBits "a statement after a native loop runs" (BitVec.ofNat 64 7) (lookup followed.state.env afterLoop)
  assertBits "the native loop ran" (BitVec.ofNat 32 3) (lookup followed.state.env a)
  assertEqual "a native loop falls through to the next block" 0x10101 followed.pc
  assertEqual "the loop stayed native" 0 (← Primus.Lifted.stats followedEngine).interpretedRuns

  -- the else branch that jumps keeps its slots and labels: the inputs it reads, and what follows
  let elseInput := reg "elseInput"
  let elseFollow := reg "elseFollow"
  let terminatingElse : Primus.Lifted.Block := {
    address := 0x10200
    next := 0x10201
    program := [
      .ifElse (.bin .eq (.var elseInput) (int 0))
        [.move elseFollow (int 1)]
        [.move elseFollow (int 2), .jmp (.bin .add (.var elseInput) (int 0x100))],
      .move elseFollow (.bin .add (.var elseFollow) (int 10))
    ]
  }
  let elseEngine ← Primus.Lifted.Engine.create
  let (elseFetch, elseLift) := fixed terminatingElse
  let taken ← Primus.Lifted.runBlock elseEngine elseFetch elseLift (state elseInput 5) 0x10200
  assertEqual "a jump in the else branch reads its input" 0x105 taken.pc
  assertBits "the else branch writes" (BitVec.ofNat 64 2) (lookup taken.state.env elseFollow)
  let fallen ← Primus.Lifted.runBlock elseEngine elseFetch elseLift (state elseInput 0) 0x10200
  assertBits "code after a terminating else runs" (BitVec.ofNat 64 11) (lookup fallen.state.env elseFollow)
  assertEqual "the conditional stayed native" 0 (← Primus.Lifted.stats elseEngine).interpretedRuns

  -- narrow operators against the interpreter, on every sign and on a zero divisor
  let narrowLeft : Var := ⟨"narrowLeft", .imm 8, 0, false⟩
  let narrowRight : Var := ⟨"narrowRight", .imm 8, 0, false⟩
  let narrowResult : Var := ⟨"narrowResult", .imm 8, 0, false⟩
  let narrowBit : Var := ⟨"narrowBit", .imm 1, 0, false⟩
  for (leftValue, rightValue) in [(7, 3), (0xf9, 3), (7, 0xfd), (0xf9, 0xfd), (6, 3), (0xfa, 3), (6, 0xfd),
      (0xfa, 0xfd), (0x80, 0xff), (0x7f, 0xff), (5, 0), (0xfb, 0), (0, 0), (0x80, 1), (1, 9), (0x80, 9), (0x80, 8)] do
    let initial : State := { env := [(narrowLeft, .bits (BitVec.ofNat 8 leftValue)),
      (narrowRight, .bits (BitVec.ofNat 8 rightValue))] }
    for op in [BinOp.add, .sub, .mul, .div, .sdiv, .rem, .srem, .smod, .lshift, .rshift, .ashift, .and, .or, .xor] do
      let block : Primus.Lifted.Block := {
        address := 0x10300, next := 0x10301,
        program := [.move narrowResult (.bin op (.var narrowLeft) (.var narrowRight))]
      }
      let engine ← Primus.Lifted.Engine.create
      let (fetch, lift) := fixed block
      let native ← Primus.Lifted.runBlock engine fetch lift initial 0x10300
      assertEqual "a narrow operator is native" 0 (← Primus.Lifted.stats engine).interpretedRuns
      match Bil.run block.program initial with
      | .ok (expected, _) =>
        match lookup expected.env narrowResult with
        | .ok (.bits value) => assertBits s!"narrow {repr op} {leftValue} {rightValue}" value (lookup native.state.env narrowResult)
        | _ => throw <| IO.userError "narrow result is not bits"
      | .error error => throw <| IO.userError error
    for op in [BinOp.eq, .neq, .lt, .le, .gt, .ge, .slt, .sle, .sgt, .sge] do
      let block : Primus.Lifted.Block := {
        address := 0x10300, next := 0x10301,
        program := [.move narrowBit (.bin op (.var narrowLeft) (.var narrowRight))]
      }
      let engine ← Primus.Lifted.Engine.create
      let (fetch, lift) := fixed block
      let native ← Primus.Lifted.runBlock engine fetch lift initial 0x10300
      match Bil.run block.program initial with
      | .ok (expected, _) =>
        match lookup expected.env narrowBit with
        | .ok (.bits value) => assertBits s!"narrow {repr op} {leftValue} {rightValue}" value (lookup native.state.env narrowBit)
        | _ => throw <| IO.userError "narrow result is not bits"
      | .error error => throw <| IO.userError error

  -- what the interpreter must decide stays with the interpreter
  let wideMemory : Var := ⟨"mem", .mem 64 8, 0, false⟩
  let wordMemory : Var := ⟨"mem32", .mem 32 8, 0, false⟩
  let interpretedOnly : List (String × Bil.Program) := [
    ("an address of the wrong width", [.move narrowResult (.load (.var wordMemory) (int 0) .little 1)]),
    ("a store to an address of the wrong width",
      [.move wordMemory (.store (.var wordMemory) (int 0) (.int (BitVec.ofNat 8 0)) .little 1)]),
    ("a load in an alternative of ite", [.move narrowResult
      (.ite (.int (BitVec.ofNat 1 0)) (.load (.var wideMemory) (int 0) .little 1) (.int (BitVec.ofNat 8 0)))]),
    ("a memory of wider cells", [.move narrowResult (.load (.var ⟨"mem", .mem 64 16, 0, false⟩) (int 0) .little 1)]),
    ("a jump target wider than a slot", [.jmp (.int (BitVec.ofNat 128 0))])]
  for (name, program) in interpretedOnly do
    let engine ← Primus.Lifted.Engine.create
    let (fetch, lift) := fixed { address := 0x10400, next := 0x10401, program }
    let memory := Bap.Memory.empty 64
    let initial : State := { env := [(wideMemory, .memory memory), (wordMemory, .memory (Bap.Memory.empty 32))] }
    match (← (Primus.Lifted.runBlock engine fetch lift initial 0x10400).toBaseIO) with
    | _ => pure ()
    assertEqual s!"{name} is not native" 0 (← Primus.Lifted.stats engine).nativeRuns

  let memoryEngine ← Primus.Lifted.Engine.create
  let memoryBlock : Primus.Lifted.Block := {
    address := 0x11000
    next := 0x11001
    program := [
      .move memoryVar (.store (.var memoryVar) (int 0) (int 0x0123456789abcdef) .little 8),
      .move y (.load (.var memoryVar) (int 0) .little 8),
      .move z (.load (.var memoryVar) (int 0) .big 8)
    ]
  }
  let (memoryFetch, memoryLift) := fixed memoryBlock
  let memoryInitial : State := { env := [(memoryVar, .memory (Memory.empty 64))] }
  let memoryResult ← Primus.Lifted.runBlock memoryEngine memoryFetch memoryLift memoryInitial 0x11000
  assertBits "native little-endian memory" (BitVec.ofNat 64 0x0123456789abcdef)
    (lookup memoryResult.state.env y)
  assertBits "native big-endian memory" (BitVec.ofNat 64 0xefcdab8967452301)
    (lookup memoryResult.state.env z)
  let memoryStats ← Primus.Lifted.stats memoryEngine
  assertEqual "native memory avoids fallback" 0 memoryStats.interpretedRuns

  let hotEngine ← Primus.Lifted.Engine.create 3
  let hotBlock : Primus.Lifted.Block := {
    address := 0x12000
    next := 0x12004
    program := [.move x (int 40), .move y (.bin .add (.var x) (int 2)), .jmp (.var y)]
  }
  let (hotFetch, hotLift) := fixed hotBlock
  let coldFirst ← Primus.Lifted.runBlock hotEngine hotFetch hotLift {} 0x12000
  let coldSecond ← Primus.Lifted.runBlock hotEngine hotFetch hotLift {} 0x12000
  assertEqual "cold blocks preserve results" (42, 42) (coldFirst.pc, coldSecond.pc)
  let coldStats ← Primus.Lifted.stats hotEngine
  assertEqual "cold blocks execute twice in BIL" 2 coldStats.interpretedRuns
  assertEqual "cold blocks are not compiled" 0 coldStats.nativeCompilations
  assertEqual "cold blocks lift once" 1 coldStats.lifts
  let hotThird ← Primus.Lifted.runBlock hotEngine hotFetch hotLift {} 0x12000
  assertEqual "threshold block preserves result" 42 hotThird.pc
  let hotStats ← Primus.Lifted.stats hotEngine
  assertEqual "threshold block compiles once" 1 hotStats.nativeCompilations
  assertEqual "threshold block runs natively" 1 hotStats.nativeRuns
  assertEqual "threshold block retains cold runs" 2 hotStats.interpretedRuns
  let hotFourth ← Primus.Lifted.runBlock hotEngine hotFetch hotLift {} 0x12000
  assertEqual "hot cached block preserves result" 42 hotFourth.pc
  let reusedStats ← Primus.Lifted.stats hotEngine
  assertEqual "hot cached block does not recompile" 1 reusedStats.nativeCompilations
  assertEqual "hot cached block executes natively twice" 2 reusedStats.nativeRuns
  assertEqual "hot cached block hits cache three times" 3 reusedStats.cacheHits

  let syncEngine ← Primus.Lifted.Engine.create
  let syncPersistent ← Jit.createMemory #[0] #[1]
  syncEngine.persistentMemory.set (some syncPersistent)
  syncEngine.persistentVariable.set (some memoryVar)
  let syncInitial : State := { env := [
    (memoryVar, .memory (Memory.writeByte (Memory.empty 64) (BitVec.ofNat 64 0) 1))
  ] }
  let syncFallback : Primus.Lifted.Block := {
    address := 0x12500
    next := 0x12504
    program := [
      .move memoryVar (.store (.var memoryVar) (int 0) (.int (BitVec.ofNat 8 2)) .little 1),
      .move y (.letIn x (int 2) (.var x))
    ]
  }
  let (syncFallbackFetch, syncFallbackLift) := fixed syncFallback
  let syncFallbackResult ← Primus.Lifted.runBlock syncEngine syncFallbackFetch syncFallbackLift syncInitial 0x12500
  let (_, synchronizedValues) ← Jit.dumpMemory syncPersistent
  assertEqual "interpreted write updates persistent memory in place" #[2] synchronizedValues
  let byteResult : Var := ⟨"byteResult", .imm 8, 0, false⟩
  let syncRead : Primus.Lifted.Block := {
    address := 0x12504
    next := 0x12508
    program := [.move byteResult (.load (.var memoryVar) (int 0) .little 1)]
  }
  let (syncReadFetch, syncReadLift) := fixed syncRead
  let syncResult ← Primus.Lifted.runBlock syncEngine syncReadFetch syncReadLift syncFallbackResult.state 0x12504
  assertBits "native read observes synchronized interpreted write" (BitVec.ofNat 8 2)
    (lookup syncResult.state.env byteResult)
  let syncStats ← Primus.Lifted.stats syncEngine
  assertEqual "memory synchronization uses both executors" (1, 1)
    (syncStats.nativeRuns, syncStats.interpretedRuns)

  let evictEngine ← Primus.Lifted.Engine.create 1 2
  let evictFetch : Primus.Lifted.Fetch := fun _ => pure ByteArray.empty
  let evictLift : Primus.Lifted.Lift := fun address _ =>
    pure ⟨address, address + 4, [.jmp (.int (BitVec.ofNat 64 (address + 4)))]⟩
  for address in [0x13000, 0x13004, 0x13008, 0x13000] do
    let _ ← Primus.Lifted.runBlock evictEngine evictFetch evictLift {} address
  let evictStats ← Primus.Lifted.stats evictEngine
  assertEqual "evicted block version avoids relifting" 3 evictStats.lifts
  assertEqual "evicted block version avoids recompilation" 3 evictStats.nativeCompilations
  assertEqual "evicted block version is reused" 1 evictStats.versionHits
  assertEqual "bounded cache rejects stale entries" 0 evictStats.cacheHits
  let retainEngine ← Primus.Lifted.Engine.create 1 2
  for address in [0x13000, 0x13004, 0x13000, 0x13008, 0x13000] do
    let _ ← Primus.Lifted.runBlock retainEngine evictFetch evictLift {} address
  let retainStats ← Primus.Lifted.stats retainEngine
  assertEqual "bounded cache retains frequently used entries" 3 retainStats.lifts
  assertEqual "bounded cache reuses retained entries" 2 retainStats.cacheHits
  let limitedEngine ← Primus.Lifted.Engine.create 1 128 1 16 0 false 2
  for address in [0x13000, 0x13004, 0x13008] do
    let _ ← Primus.Lifted.runBlock limitedEngine evictFetch evictLift {} address
  let limitedStats ← Primus.Lifted.stats limitedEngine
  assertEqual "native limit compiles within budget" 2 limitedStats.nativeCompilations
  assertEqual "native limit leaves excess blocks interpreted" 1 limitedStats.interpretedRuns
  Primus.Lifted.clearCache limitedEngine
  let _ ← Primus.Lifted.runBlock limitedEngine evictFetch evictLift {} 0x1300c
  let clearedStats ← Primus.Lifted.stats limitedEngine
  assertEqual "clearing native programs releases budget" 3 clearedStats.nativeCompilations

  let rangeIncrement ← IO.mkRef 2
  let rangeFetch : Primus.Lifted.Fetch := fun _ => do
    let increment ← rangeIncrement.get
    pure (ByteArray.mk #[UInt8.ofNat increment])
  let rangeLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x14000 => pure ⟨pc, pc + 4, [
        .move memoryVar (.store (.var memoryVar) (int 0) (int 40) .little 8),
        .jmp (int 0x14004)
      ]⟩
    | 0x14004 => pure ⟨pc, pc + 4, [
        .move y (.load (.var memoryVar) (int 0) .little 8),
        .jmp (int 0x14008)
      ]⟩
    | 0x14008 => do
      let increment ← rangeIncrement.get
      pure ⟨pc, pc + 4, [.move z (.bin .add (.var y) (int increment)), .jmp (.var z)]⟩
    | 42 => pure ⟨42, 42, []⟩
    | _ => throw <| IO.userError s!"unexpected range lift at {pc}"
  let rangeInitial : State := { env := [(memoryVar, .memory (Memory.empty 64))] }
  let singleEngine ← Primus.Lifted.Engine.create
  let singleResult ← Primus.Lifted.run singleEngine rangeFetch rangeLift rangeInitial 0x14000 10
  assertEqual "single-block reference continuation" 42 singleResult.pc

  let rangeEngine ← Primus.Lifted.Engine.create 1 128 4
  let rangeEvents ← IO.mkRef []
  let rangeObserver : Jit.CodeObserver := fun pc => do
    rangeEvents.modify fun events => pc :: events
    pure false
  let rangeResult ← Primus.Lifted.runBlockObserved rangeEngine rangeFetch rangeLift rangeInitial 0x14000
    none (some rangeObserver)
  assertEqual "range preserves continuation" singleResult.pc rangeResult.pc
  assertBits "range matches single-block result" (BitVec.ofNat 64 42) (lookup rangeResult.state.env z)
  assertEqual "range observes each internal block" [0x14004, 0x14008] (← rangeEvents.get).reverse
  let rangeStats ← Primus.Lifted.stats rangeEngine
  assertEqual "range executes once natively" 1 rangeStats.nativeRuns
  assertEqual "range compiles its first block only once" 1 rangeStats.nativeCompilations
  assertEqual "range lifts each block once" 3 rangeStats.lifts
  assertEqual "range avoids interpreted fallback" 0 rangeStats.interpretedRuns
  let cachedRange ← Primus.Lifted.runBlockObserved rangeEngine rangeFetch rangeLift rangeInitial 0x14000
    none (some rangeObserver)
  assertEqual "cached range preserves continuation" 42 cachedRange.pc
  let cachedRangeStats ← Primus.Lifted.stats rangeEngine
  assertEqual "cached range does not relift" 3 cachedRangeStats.lifts
  assertEqual "cached range executes natively twice" 2 cachedRangeStats.nativeRuns

  let graphFetch : Primus.Lifted.Fetch := fun _ => pure (ByteArray.mk #[1])
  let graphLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x16000 => pure ⟨pc, 0x16000, [
        .ifElse (.bin .eq (.var x) (int 1)) [.jmp (int 0x16100)] [.jmp (int 0x16004)]
      ]⟩
    | 0x16004 => pure ⟨pc, 0x16008, [.move y (int 40), .jmp (int 0x16100)]⟩
    | 0x16100 => pure ⟨pc, 0x16104, [.move z (.bin .add (.var y) (int 2)), .jmp (.var z)]⟩
    | 42 => pure ⟨42, 42, []⟩
    | _ => throw <| IO.userError s!"unexpected graph lift at {pc}"
  let graphInitial : State := { env := [
    (x, .bits (BitVec.ofNat 64 0)),
    (y, .bits (BitVec.ofNat 64 0))
  ] }
  let graphReference ← Primus.Lifted.run singleEngine graphFetch graphLift graphInitial 0x16000 10
  assertEqual "graph block reference continuation" 42 graphReference.pc
  assertBits "graph block reference result" (BitVec.ofNat 64 42) (lookup graphReference.state.env z)
  let graphEngine ← Primus.Lifted.Engine.create 1 128 8 16 0 false
  let graphEvents ← IO.mkRef []
  let graphObserver : Jit.CodeObserver := fun pc => do
    graphEvents.modify fun events => pc :: events
    pure false
  let graphResult ← Primus.Lifted.runBlockObserved graphEngine graphFetch graphLift graphInitial 0x16000
    none (some graphObserver)
  assertEqual "graph preserves continuation" graphReference.pc graphResult.pc
  assertBits "graph matches block execution" (BitVec.ofNat 64 42) (lookup graphResult.state.env z)
  assertEqual "graph observes internal blocks" [0x16004, 0x16100] (← graphEvents.get).reverse
  let graphStats ← Primus.Lifted.stats graphEngine
  assertEqual "graph compiles once" 1 graphStats.nativeCompilations
  assertEqual "graph executes natively" 1 graphStats.nativeRuns
  assertEqual "graph avoids interpreted blocks" 0 graphStats.interpretedRuns
  assertEqual "graph lifts each discovered block once" 3 graphStats.lifts
  Primus.Lifted.discardRange graphEngine 0x16004 0x16007
  let invalidatedGraph ← Primus.Lifted.runBlockObserved graphEngine graphFetch graphLift graphInitial 0x16000
    none (some graphObserver)
  assertEqual "invalidated graph preserves continuation" 42 invalidatedGraph.pc
  let invalidatedGraphStats ← Primus.Lifted.stats graphEngine
  assertEqual "matching graph version avoids recompilation" 1 invalidatedGraphStats.nativeCompilations
  assertEqual "matching graph version avoids relifting" 3 invalidatedGraphStats.lifts

  let stopEngine ← Primus.Lifted.Engine.create 1 128 4
  let stopObserver : Jit.CodeObserver := fun pc => pure (pc = 0x14008)
  let stoppedRange ← Primus.Lifted.runBlockObserved stopEngine rangeFetch rangeLift rangeInitial 0x14000
    none (some stopObserver)
  assertEqual "range stops before the requested internal block" 0x14008 stoppedRange.pc
  assertEqual "range stop uses the internal continuation" 0x14008 stoppedRange.next
  assertBits "range stop preserves earlier writes" (BitVec.ofNat 64 40) (lookup stoppedRange.state.env y)
  match stoppedRange.effect with
  | .normal => pure ()
  | _ => throw <| IO.userError "range stop did not have normal effect"
  match lookup stoppedRange.state.env z with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "range stop committed a future-block output"

  rangeIncrement.set 3
  Primus.Lifted.discardRange rangeEngine 0x14008 0x14008
  let invalidated ← Primus.Lifted.runBlockObserved rangeEngine rangeFetch rangeLift rangeInitial 0x14000
    none (some rangeObserver)
  assertEqual "overlapping write invalidates the whole range" 43 invalidated.pc
  assertBits "invalidated range uses new bytes" (BitVec.ofNat 64 43) (lookup invalidated.state.env z)

  let cooldownEngine ← Primus.Lifted.Engine.create 1 128 1 16 2
  let cooldownBlock : Primus.Lifted.Block := {
    address := 0x15000
    next := 0x15004
    program := [.move y (int 42)]
  }
  let (cooldownFetch, cooldownLift) := fixed cooldownBlock
  let _ ← Primus.Lifted.runBlock cooldownEngine cooldownFetch cooldownLift {} 0x15000
  Primus.Lifted.discardRange cooldownEngine 0x15000 0x15000
  let _ ← Primus.Lifted.runBlock cooldownEngine cooldownFetch cooldownLift {} 0x15000
  let _ ← Primus.Lifted.runBlock cooldownEngine cooldownFetch cooldownLift {} 0x15000
  let _ ← Primus.Lifted.runBlock cooldownEngine cooldownFetch cooldownLift {} 0x15000
  let cooldownStats ← Primus.Lifted.stats cooldownEngine
  assertEqual "write cooldown suppresses two native runs" 2 cooldownStats.interpretedRuns
  assertEqual "native compilation resumes after write cooldown" 2 cooldownStats.nativeRuns
  assertEqual "write cooldown avoids repeated compilation" 2 cooldownStats.nativeCompilations

  -- Graph cycles: `gatherGraph` keeps every compiled range acyclic, whatever the cycle's length.
  let cycleX := reg "cycleX"
  let cycleFetch : Primus.Lifted.Fetch := fun _ => pure (ByteArray.mk #[1])
  let cycleBack (limit : Nat) (back exit : Nat) : Bil.Stmt :=
    .ifElse (.bin .neq (.var cycleX) (int limit)) [.jmp (int back)] [.jmp (int exit)]
  let cycleStep (next : Nat) : Bil.Program := [.move cycleX (.bin .add (.var cycleX) (int 1)), .jmp (int next)]
  let cycleExit : Primus.Lifted.Block := ⟨0x30000, 0x30004, []⟩
  let runCycle (name : String) (entry : Nat) (cycle : Nat → Primus.Lifted.Block) (expected : Nat) : IO Primus.Lifted.Statistics := do
    let engine ← Primus.Lifted.Engine.create 1 128 8 16 0 false
    let result ← Primus.Lifted.run engine cycleFetch (fun pc _ => pure (cycle pc)) (state cycleX 0) entry 50
    assertBits s!"{name} result" (BitVec.ofNat 64 expected) (lookup result.state.env cycleX)
    assertEqual s!"{name} leaves the cycle" 0x30004 result.pc
    let stats ← Primus.Lifted.stats engine
    assertEqual s!"{name} stays native" 0 stats.interpretedRuns
    pure stats
  let twoCycle : Nat → Primus.Lifted.Block
    | 0x20000 => ⟨0x20000, 0x20004, cycleStep 0x20004⟩
    | 0x20004 => ⟨0x20004, 0x20008, [cycleBack 5 0x20000 0x30000]⟩
    | _ => cycleExit
  let twoStats ← runCycle "two-block cycle through the seed" 0x20000 twoCycle 5
  assertEqual "two-block cycle compiles one range" (1, 3) (twoStats.nativeCompilations, twoStats.graphBlocks)
  let threeCycle : Nat → Primus.Lifted.Block
    | 0x21000 => ⟨0x21000, 0x21004, cycleStep 0x21004⟩
    | 0x21004 => ⟨0x21004, 0x21008, cycleStep 0x21008⟩
    | 0x21008 => ⟨0x21008, 0x2100c, [cycleBack 6 0x21000 0x30000]⟩
    | _ => cycleExit
  let threeStats ← runCycle "three-block cycle through the seed" 0x21000 threeCycle 6
  assertEqual "three-block cycle compiles one range" (1, 4) (threeStats.nativeCompilations, threeStats.graphBlocks)
  let innerCycle : Nat → Primus.Lifted.Block
    | 0x22000 => ⟨0x22000, 0x22004, [.jmp (int 0x22004)]⟩
    | 0x22004 => ⟨0x22004, 0x22008, cycleStep 0x22008⟩
    | 0x22008 => ⟨0x22008, 0x2200c, cycleStep 0x2200c⟩
    | 0x2200c => ⟨0x2200c, 0x22010, [cycleBack 6 0x22004 0x30000]⟩
    | _ => cycleExit
  let innerStats ← runCycle "cycle behind the seed" 0x22000 innerCycle 6
  assertEqual "a cycle behind the seed stays in its range" 1 innerStats.nativeRuns

  -- An interpreted jump reports its fall-through as its next, as a native one does, and its target as its pc.
  let jumpEngine ← Primus.Lifted.Engine.create (hotThreshold := 2)
  let jumpBlock : Primus.Lifted.Block := ⟨0x45000, 0x45004, [.jmp (int 0x46000)]⟩
  let (jumpFetch, jumpLift) := fixed jumpBlock
  let jumped ← Primus.Lifted.runBlock jumpEngine jumpFetch jumpLift {} 0x45000
  assertEqual "an interpreted jump has its target for a pc" 0x46000 jumped.pc
  assertEqual "an interpreted jump has its fall-through for next" 0x45004 jumped.next
  -- A range ends wherever a block leaves it, with what that way through it wrote.
  let pathX := reg "path_x"
  let pathY := reg "path_y"
  let pathZ := reg "path_z"
  let pathFetch : Primus.Lifted.Fetch := fun _ => pure (ByteArray.mk #[1])
  let pathLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x40000 => pure ⟨pc, 0x40004, [.ifElse (.bin .eq (.var pathX) (int 1)) [.jmp (int 0x40004)] [.jmp (int 0x40008)]]⟩
    | 0x40004 => pure ⟨pc, 0x40008, [.move pathY (int 7), .jmp (int 0x40008)]⟩
    | 0x40008 => pure ⟨pc, 0x4000c, [.move pathZ (int 9), .jmp (int 0x50000)]⟩
    | _ => pure ⟨pc, pc + 4, []⟩
  let pathEngine ← Primus.Lifted.Engine.create 1 128 8 16 0 false
  let skipped ← Primus.Lifted.run pathEngine pathFetch pathLift (state pathX 0) 0x40000 20
  assertBits "a range writes what the way through it does" (BitVec.ofNat 64 9) (lookup skipped.state.env pathZ)
  match lookup skipped.state.env pathY with
  | .error _ => pure ()
  | .ok value => throw <| IO.userError s!"a way around a write bound its variable to {repr value}"
  assertTrue "the way around ran natively" ((← Primus.Lifted.stats pathEngine).interpretedRuns == 0)
  let through ← Primus.Lifted.run pathEngine pathFetch pathLift (state pathX 1) 0x40000 20
  assertBits "the way through a write has its value" (BitVec.ofNat 64 7) (lookup through.state.env pathY)
  -- A read of what only one way wrote is an input: unbound, it fails as in the interpreter.
  let readLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x41000 => pure ⟨pc, 0x41004, [.ifElse (.bin .eq (.var pathX) (int 1)) [.jmp (int 0x41004)] [.jmp (int 0x41008)]]⟩
    | 0x41004 => pure ⟨pc, 0x41008, [.move pathY (int 7), .jmp (int 0x41008)]⟩
    | 0x41008 => pure ⟨pc, 0x4100c, [.move pathZ (.var pathY), .jmp (int 0x50000)]⟩
    | _ => pure ⟨pc, pc + 4, []⟩
  let readEngine ← Primus.Lifted.Engine.create 1 128 8 16 0 false
  expectThrow "a read of what the way there did not write fails"
    (do let _ ← Primus.Lifted.run readEngine pathFetch readLift (state pathX 0) 0x41000 20)
  let readThere ← Primus.Lifted.run readEngine pathFetch readLift (state pathX 1) 0x41000 20
  assertBits "a read on the way that wrote it has its value" (BitVec.ofNat 64 7) (lookup readThere.state.env pathZ)
  -- The fuel of `run` counts the blocks of a range: a loop that never ends runs out of it.
  let spinLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x42000 => pure ⟨pc, 0x42004, [.move pathX (.bin .add (.var pathX) (int 1)), .jmp (int 0x42004)]⟩
    | _ => pure ⟨pc, pc + 4, [.jmp (int 0x42000)]⟩
  let spinEngine ← Primus.Lifted.Engine.create 1 128 8 16 0 false
  expectThrow "a range runs out of the fuel of `run`"
    (do let _ ← Primus.Lifted.run spinEngine pathFetch spinLift (state pathX 0) 0x42000 100)
  -- An access of several bytes on a narrower memory is the interpreter's, which wraps, unless the runner rejects it.
  let mem32 : Var := ⟨"mem", .mem 32 8, 0, false⟩
  let address32 : Var := ⟨"address", .imm 32, 0, false⟩
  let value32 : Var := ⟨"value", .imm 32, 0, false⟩
  let wrapBlock : Primus.Lifted.Block := ⟨0x43000, 0x43004, [
    .move mem32 (.store (.var mem32) (.var address32) (.int 0x04030201#32) .little 4),
    .move value32 (.load (.var mem32) (.var address32) .little 4)]⟩
  let (wrapFetch, wrapLift) := fixed wrapBlock
  let wrapEngine ← Primus.Lifted.Engine.create
  let wrapInitial : State := { env := [(mem32, .memory (Memory.empty 32)), (address32, .bits 0xfffffffe#32)] }
  let wrapped ← Primus.Lifted.runBlock wrapEngine wrapFetch wrapLift wrapInitial 0x43000
  assertBits "a load that wraps reads what the store wrote" 0x04030201#32 (lookup wrapped.state.env value32)
  match Bil.lookup wrapped.state.env mem32 with
  | .ok (.memory memory) =>
    assertEqual "a store that wraps goes to the start of memory" 3 (Bap.Memory.readRegion memory 0 1)[0]!.toNat
  | _ => throw <| IO.userError "memory is missing"
  assertEqual "an access that may wrap is interpreted" 1 (← Primus.Lifted.stats wrapEngine).interpretedRuns
  let byteBlock : Primus.Lifted.Block := ⟨0x44000, 0x44004, [
    .move mem32 (.store (.var mem32) (.var address32) (.int 7#8) .little 1)]⟩
  let (byteFetch, byteLift) := fixed byteBlock
  let byteEngine ← Primus.Lifted.Engine.create
  let _ ← Primus.Lifted.runBlock byteEngine byteFetch byteLift wrapInitial 0x44000
  assertEqual "an access of one byte cannot wrap, and runs natively" 1 (← Primus.Lifted.stats byteEngine).nativeRuns

  -- A write after a statement that can leave does not count for later blocks, so that a read there is an input: unbound,
  -- it sends the run to the interpreter, and never reads as a 0.
  let leftFlag := reg1 "left"
  let leaver := reg "leaver"
  let reader := reg "reader"
  let leaveFetch : Primus.Lifted.Fetch := fun pc => pure (ByteArray.mk #[UInt8.ofNat (pc % 251)])
  let leaveLift : Primus.Lifted.Lift := fun pc _ =>
    match pc with
    | 0x45000 => pure ⟨pc, 0x45004, [.ifElse (.var leftFlag) [.jmp (int 0x46000)] [], .move leaver (int 1)]⟩
    | 0x45004 => pure ⟨pc, 0x45008, [.move reader (.var leaver)]⟩
    | _ => pure ⟨pc, pc + 4, [.jmp (int pc)]⟩
  let leaveEngine ← Primus.Lifted.Engine.create (rangeLimit := 8) (chainFallthrough := true)
  let leaveInitial : State := { env := [(leftFlag, .bits 0#1)] }
  let leaveFirst ← Primus.Lifted.runBlock leaveEngine leaveFetch leaveLift leaveInitial 0x45000
  assertEqual "a block whose later read is an unbound input is interpreted" 1 (← Primus.Lifted.stats leaveEngine).interpretedRuns
  assertEqual "and it does not chain" 0x45004 leaveFirst.pc
  assertBits "and writes what it writes" 1#64 (lookup leaveFirst.state.env leaver)
  let leaveSecond ← Primus.Lifted.runBlock leaveEngine leaveFetch leaveLift leaveFirst.state 0x45004
  assertBits "the later block reads the write, not a 0" 1#64 (lookup leaveSecond.state.env reader)
  let leaveBound ← Primus.Lifted.runBlock leaveEngine leaveFetch leaveLift
    { env := (leaver, .bits 7#64) :: leaveInitial.env } 0x45000
  assertEqual "with the input bound the range runs natively" 2 (← Primus.Lifted.stats leaveEngine).nativeRuns
  assertBits "and the later block reads the write" 1#64 (lookup leaveBound.state.env reader)

  -- A native loop gives up at its 100000th test, and the interpreter, on the same fuel, no later.
  let counter := reg "counter"
  let counted (limit : Nat) : Primus.Lifted.Block :=
    ⟨0x47000, 0x47004, [.move counter (int 0),
      .while (.bin .lt (.var counter) (int limit)) [.move counter (.bin .add (.var counter) (int 1))]]⟩
  let interprets (limit : Nat) : IO Bool := do
    match ← Bil.runObserved none (counted limit).program {} with
    | .ok _ => pure true
    | .error _ => pure false
  let countNative (limit : Nat) : IO (Except String Primus.Lifted.Result) := do
    let engine ← Primus.Lifted.Engine.create
    let (fetch, lift) := fixed (counted limit)
    let result ← (Primus.Lifted.runBlock engine fetch lift {} 0x47000).toBaseIO
    assertEqual "the loop is native" 1 (← Primus.Lifted.stats engine).nativeRuns
    pure (match result with | .ok result => .ok result | .error error => .error (toString error))
  assertTrue "the interpreter finishes a loop well within its fuel" (← interprets 99996)
  match ← countNative 99996 with
  | .ok result => assertBits "and so does native code" (BitVec.ofNat 64 99996) (lookup result.state.env counter)
  | .error error => throw <| IO.userError error
  assertTrue "the interpreter runs out of fuel first" (!(← interprets 99998))
  match ← countNative 99998 with
  | .ok result => assertBits "99999 tests are native code's last" (BitVec.ofNat 64 99998) (lookup result.state.env counter)
  | .error error => throw <| IO.userError error
  assertTrue "100000 tests are out of the interpreter's fuel" (!(← interprets 99999))
  match ← countNative 99999 with
  | .ok _ => throw <| IO.userError "100000 tests are too many in native code"
  | .error error => assertEqual "native code says so" "Primus loop fuel exhausted" error

end Bap.Tests.Lifted
