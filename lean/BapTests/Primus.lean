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

private def semanticsForms (bits : Nat) (input : String) : IO Primus.Semantics.State := do
  let context : Primus.Semantics.Context := { bits }
  let forms ← match Sexp.parseMany input with
    | .ok forms => pure forms
    | .error error => throw <| IO.userError error
  match Primus.Semantics.evalForms context [("R", Primus.Semantics.register "R" bits bits)] forms with
  | .ok state => pure state
  | .error error => throw <| IO.userError error

private def assignedConstant (state : Primus.Semantics.State) : IO Nat :=
  match state.code with
  | [.move _ (.int value)] => pure value.toNat
  | _ => throw <| IO.userError s!"expected one constant move, got {repr state.code}"

private def semanticsRegressions : IO Unit := do
  assertEqual "word-width of a literal is the machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 5))"))
  assertEqual "word-width of a literal agrees with arithmetic" 64
    (← assignedConstant (← semanticsForms 64 "(set R (word-width 5))"))
  match (← semanticsForms 32 "(set R (mod 0xfffffff9 3))").code with
  | [.move _ (.bin .rem _ _)] => IO.println "ok: mod is the unsigned remainder"
  | code => throw <| IO.userError s!"mod changed: {repr code}"
  match (← semanticsForms 32 "(set R (signed-mod 0xfffffff9 3))").code with
  | [.move _ (.bin .smod _ _)] => IO.println "ok: signed-mod takes the sign of the divisor"
  | code => throw <| IO.userError s!"signed-mod changed: {repr code}"
  match (← semanticsForms 32 "(set R (signed-rem 0xfffffff9 3))").code with
  | [.move _ (.bin .srem _ _)] => IO.println "ok: signed-rem takes the sign of the dividend"
  | code => throw <| IO.userError s!"signed-rem changed: {repr code}"
  assertEqual "local binding shadows replicate" 7
    (← assignedConstant (← semanticsForms 64 "(let ((replicate 7)) (set R replicate))"))
  match (← semanticsForms 64 "(let ((replicate 7)) (set R (replicate 1:32 2)))").code with
  | [.move _ (.concat _ _)] => IO.println "ok: replicate stays callable under a local binding"
  | code => throw <| IO.userError s!"replicate call changed: {repr code}"
  let compiled ← semanticsForms 64 "(defun op () (let ((replicate 7)) (set R replicate)))"
  match (← Primus.Semantics.lift compiled.globals {} "op" []) with
  | [.move _ (.int value)] => assertEqual "compiled local shadows replicate" 7 value.toNat
  | code => throw <| IO.userError s!"compiled replicate shadow changed: {repr code}"
  assertEqual "word-width with no arguments is the machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width))"))
  assertEqual "word-width is the widest argument" 16
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 1:8 1:16 1:4))"))
  assertEqual "word-width counts a literal as a machine word" 32
    (← assignedConstant (← semanticsForms 32 "(set R (word-width 1:8 5))"))
  match (← semanticsForms 64 "(let ((x 1)) (set x 2) (set R x))").code with
  | [.move slot (.int first), .move assigned (.int second), .move _ (.var read)] =>
    assertEqual "set assigns the let variable" (1, 2) (first.toNat, second.toNat)
    assertTrue "the assignment and the read use the let variable" (slot == assigned && assigned == read)
  | code => throw <| IO.userError s!"let assignment changed: {repr code}"
  match (← semanticsForms 64 "(let ((x 1)) (if (is-zero R) (set x 2) (set x 3)) (set R x))").code with
  | [.move slot _, .ifElse _ [.move yes _] [.move no _], .move _ (.var read)] =>
    assertTrue "both branches assign the let variable" (slot == yes && yes == no && no == read)
  | code => throw <| IO.userError s!"conditional let assignment changed: {repr code}"
  match (← semanticsForms 64 "(defmacro put (v e) (set v e)) (let ((x 1)) (put x 2) (set R x))").code with
  | [.move slot _, .move assigned _, .move _ (.var read)] =>
    assertTrue "a macro assigns the let variable" (slot == assigned && assigned == read)
  | code => throw <| IO.userError s!"macro let assignment changed: {repr code}"
  let assigning ← semanticsForms 64 "(defun op () (let ((x 1)) (set x 2) (set R x)))"
  match (← Primus.Semantics.lift assigning.globals {} "op" []) with
  | [_, _, .move _ (.var _)] => IO.println "ok: a function assigning a let variable lifts"
  | code => throw <| IO.userError s!"let assignment in a function changed: {repr code}"
  match (← semanticsForms 64 "(let ((x 1)) (set R x))").code with
  | [.move _ (.int value)] => assertEqual "an unassigned let variable stays a constant" 1 value.toNat
  | code => throw <| IO.userError s!"constant let changed: {repr code}"
  for (source, value) in [("0o17", 15), ("0b101", 5), ("1_000", 1000), ("0x1_0", 16), ("0", 0)] do
    assertEqual s!"literal {source} parses" value (← assignedConstant (← semanticsForms 64 s!"(set R {source})"))
  assertEqual "negative hexadecimal literal parses" (2 ^ 64 - 16)
    (← assignedConstant (← semanticsForms 64 "(set R -0x10)"))
  for source in ["(set R 0xzz)", "(set R 12abc)", "(set R 1:2:3)", "(set R 5:abc)", "(set R 0x_1)",
      "(defun unused () 0xzz)", "(defmacro unused (x) (+ x 9z))", "(set R -1q)"] do
    match (← (semanticsForms 64 source).toBaseIO) with
    | .error _ => IO.println s!"ok: {source} is rejected"
    | .ok _ => throw <| IO.userError s!"{source} accepted"
  let documented ← semanticsForms 64 "(defun op () \"64-bit add\" (set R 1))"
  assertTrue "documentation strings are not literals" (Assoc.get "op" documented.globals).isSome
  assertEqual "an atom not starting like a number is a symbol" 0
    (← semanticsForms 64 "(defun x1y () 1)").code.length
  assertEqual "hexadecimal literal parses" 16 (← assignedConstant (← semanticsForms 64 "(set R 0x10)"))
  assertEqual "bare 0x is zero, as in Zarith" 0 (← assignedConstant (← semanticsForms 64 "(set R 0x)"))

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
  let executeOnly ← match Primus.Memory.map Primus.Memory.empty 0x4000 bytes ⟨false, false, true⟩ with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"map failed: {repr error}"
  match executeOnly.fetch 0x4001 with
  | .ok value => assertEqual "execute-only memory is fetchable" 2 value
  | .error error => throw <| IO.userError s!"execute-only fetch failed: {repr error}"
  match executeOnly.loadByte 0x4001 with
  | .error (.unmapped 0x4001) => IO.println "ok: execute-only memory is not loadable"
  | _ => throw <| IO.userError "execute-only load accepted"
  match Primus.Memory.map Primus.Memory.empty (2 ^ 64 - 4) bytes rw with
  | .ok top =>
    match top.loadByte (2 ^ 64 - 1) with
    | .ok value => assertEqual "last byte of the address space is mapped" 4 value
    | .error error => throw <| IO.userError s!"top load failed: {repr error}"
  | .error error => throw <| IO.userError s!"map at the top failed: {repr error}"
  match Primus.Memory.map Primus.Memory.empty (2 ^ 64 - 3) bytes rw with
  | .error (.outOfRange ..) => IO.println "ok: mapping across the end of the address space rejected"
  | _ => throw <| IO.userError "mapping across the end of the address space accepted"
  let aliased : Primus.Memory := ⟨Primus.Memory.empty.cells, [⟨0, 2 ^ 64 + 1, rw⟩]⟩
  match aliased.storeByte (2 ^ 64) 7 with
  | .error (.unmapped _) => IO.println "ok: store at 2^64 does not alias address 0"
  | _ => throw <| IO.userError "store at 2^64 accepted"
  semanticsRegressions
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
