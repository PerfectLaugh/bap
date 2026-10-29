import BapTests.Support

namespace Bap.Tests.Primus

open Bap
open Bap.Primus

private def bytes : ByteArray := ByteArray.mk #[1, 2, 3, 4]
private def rw : Protection := ⟨true, true, true⟩
private def ro : Protection := ⟨true, false, false⟩
private def memVar : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def int (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)

private def mapped : IO Primus.Memory :=
  match Primus.Memory.map Primus.Memory.empty 0x1000 bytes rw with
  | .ok memory => pure memory
  | .error error => throw <| IO.userError s!"map failed: {repr error}"

private def modify (machine : Machine) (f : Instance → Instance) : IO Machine :=
  match machine.modifyCurrent f with
  | .ok machine => pure machine
  | .error error => throw <| IO.userError error

private def expectError (name : String) : Except String α → IO Unit
  | .error _ => IO.println s!"ok: {name}"
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly succeeded"

private def current (machine : Machine) : IO Instance :=
  match machine.currentInstance with
  | some inst => pure inst
  | none => throw <| IO.userError "current machine does not exist"

def run : IO Unit := do
  let memory ← mapped
  match memory.loadByte 0x1001 with
  | .ok value => assertEqual "Primus mapped byte" 2 value
  | .error error => throw <| IO.userError s!"load failed: {repr error}"
  match memory.load 0x1000 .little 4 with
  | .ok value => assertEqual "Primus little-endian word" 0x04030201 value.toNat
  | .error error => throw <| IO.userError s!"word load failed: {repr error}"
  let modified ← match memory.storeByte 0x1001 9 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"store failed: {repr error}"
  match modified.loadByte 0x1001 with
  | .ok value => assertEqual "Primus store/read" 9 value
  | .error error => throw <| IO.userError s!"store read failed: {repr error}"
  match Primus.Memory.restore (Primus.Memory.snapshot memory) modified |>.loadByte 0x1001 with
  | .ok value => assertEqual "Primus snapshot restore" 2 value
  | .error error => throw <| IO.userError s!"restore failed: {repr error}"
  match memory.loadByte 0x2000 with
  | .error (.unmapped 0x2000) => IO.println "ok: unmapped access rejected"
  | .error error => throw <| IO.userError s!"wrong unmapped error: {repr error}"
  | .ok _ => throw <| IO.userError "unmapped access accepted"
  match memory.storeByte 0x2000 0 with
  | .error (.unmapped 0x2000) => IO.println "ok: unmapped store rejected"
  | .error error => throw <| IO.userError s!"wrong store error: {repr error}"
  | .ok _ => throw <| IO.userError "unmapped store accepted"
  let readOnly ← match Primus.Memory.map Primus.Memory.empty 0x3000 bytes ro with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"read-only map failed: {repr error}"
  match readOnly.storeByte 0x3000 0 with
  | .error (.readonly 0x3000) => IO.println "ok: read-only store rejected"
  | .error error => throw <| IO.userError s!"wrong read-only error: {repr error}"
  | .ok _ => throw <| IO.userError "read-only store accepted"
  match readOnly.fetch 0x3000 with
  | .error (.notExecutable 0x3000) => IO.println "ok: non-executable fetch rejected"
  | .error error => throw <| IO.userError s!"wrong fetch error: {repr error}"
  | .ok _ => throw <| IO.userError "non-executable fetch accepted"
  match memory.addRegion ⟨0x1000, 0x1004, rw⟩ with
  | .error (.overlap 0x1000 0x1004) => IO.println "ok: overlapping region rejected"
  | .error error => throw <| IO.userError s!"wrong overlap error: {repr error}"
  | .ok _ => throw <| IO.userError "overlapping region accepted"
  let x := reg "x"
  let y := reg "y"
  let initial ← modify ({ : Machine }) fun inst =>
    { inst with state := { env := [(x, .bits (BitVec.ofNat 64 40)), (memVar, .memory Primus.Memory.empty.cells)] } }
  let program : Bil.Program := [
    .move y (.bin .add (.var x) (int 2)),
    .jmp (.var y)
  ]
  let system : System := { observers := [fun _ machine => .ok machine] }
  match Machine.run initial system program with
  | .error error => throw <| IO.userError error
  | .ok (final, effect) =>
    match effect with
    | .jump target => assertEqual "Primus jump target" 42 target.toNat
    | other => throw <| IO.userError s!"unexpected Primus effect {repr other}"
    assertEqual "Primus execution time" 2 final.time
    assertEqual "Primus observer delivery" 2 final.observerHits
    assertTrue "Primus jump event" (final.log.any fun event => match event with | .jump 42 => true | _ => false)
  let committed := Machine.runAtomic initial system program
  match committed.result with
  | .error error => throw <| IO.userError error
  | .ok (.jump target) => assertEqual "Primus transaction commits control flow" 42 target.toNat
  | .ok effect => throw <| IO.userError s!"unexpected transaction effect {repr effect}"
  let committedInst ← current committed.machine
  assertBits "Primus transaction commits registers" (BitVec.ofNat 64 42)
    (Bil.lookup committedInst.state.env y)
  assertEqual "Primus transaction commits time" 2 committed.machine.time
  assertEqual "Primus transaction commits events" 5 committed.machine.log.length

  let broken : Bil.Program := [
    .move y (int 42),
    .move memVar (.store (.var memVar) (int 0) (.int (BitVec.ofNat 8 0x42)) .little 1),
    .move (reg "z") (.var (reg "missing"))
  ]
  let rolled := Machine.runAtomic initial system broken
  expectError "Primus transaction propagates interpreter failure" rolled.result
  let rolledInst ← current rolled.machine
  assertEqual "Primus rollback restores time" initial.time rolled.machine.time
  assertEqual "Primus rollback restores event log" initial.log rolled.machine.log
  assertEqual "Primus rollback restores observer count" initial.observerHits rolled.machine.observerHits
  expectError "Primus rollback restores registers" (Bil.lookup rolledInst.state.env y)
  assertEqual "Primus rollback restores memory" 0
    (Bap.Memory.readByte rolledInst.memory.cells (BitVec.ofNat 64 0))

  let failingSystem : System := { observers := [fun _ _ => .error "observer failed"] }
  let observerRolled := Machine.stepAtomic initial failingSystem (.move y (int 42))
  expectError "Primus transaction propagates observer failure" observerRolled.result
  assertEqual "Primus observer failure restores event log" initial.log observerRolled.machine.log
  let observerInst ← current observerRolled.machine
  expectError "Primus observer failure restores registers" (Bil.lookup observerInst.state.env y)

  let exhausted := Machine.runAtomic initial system program 0
  expectError "Primus transaction reports fuel exhaustion" exhausted.result
  assertEqual "Primus fuel exhaustion restores time" initial.time exhausted.machine.time
  assertEqual "Primus fuel exhaustion restores log" initial.log exhausted.machine.log

  let (machines, id) := Machine.newMachine {}
  let machines ← match machines.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machines ← modify machines fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 1))] } }
  let machines ← match machines.switch 0 with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machines ← modify machines fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 2))] } }
  let machines ← match machines.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  match machines.currentInstance with
  | some inst => assertBits "machine instances are independent" (BitVec.ofNat 64 1) (Bil.lookup inst.state.env x)
  | none => throw <| IO.userError "missing machine instance"

end Bap.Tests.Primus
