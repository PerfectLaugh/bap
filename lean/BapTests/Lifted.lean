import BapTests.Support

namespace Bap.Tests.Lifted

open Bap
open Bap.Bil

private def reg (name : String) : Var := ⟨name, .imm 64, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 64 value)
private def state (var : Var) (value : Nat) : State :=
  { env := [(var, .bits (BitVec.ofNat 64 value))] }

private def fixed (block : Primus.Lifted.Block) : Primus.Lifted.Fetch × Primus.Lifted.Lift :=
  (fun _ => pure (ByteArray.mk #[1]), fun _ _ => pure block)

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
  assertEqual "bounded cache evicts old lifts" 4 evictStats.lifts
  assertEqual "bounded cache rejects stale entries" 0 evictStats.cacheHits

end Bap.Tests.Lifted
