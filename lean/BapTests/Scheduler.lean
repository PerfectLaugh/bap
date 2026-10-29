import BapTests.Support

namespace Bap.Tests.Scheduler

open Bap
open Bap.Primus

private def reg (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def x := reg "x"
private def y := reg "y"
private def int (value : Nat) : Bil.Exp := .int (BitVec.ofNat 64 value)
private def rw : Protection := ⟨true, true, true⟩

private def modify (machine : Machine) (f : Instance → Instance) : IO Machine :=
  match machine.modifyCurrent f with
  | .ok machine => pure machine
  | .error error => throw <| IO.userError error

def run : IO Unit := do
  assertEqual "round-robin advances" (some 1) (Scheduler.roundRobin.next [0, 1] 0 0 [])
  assertEqual "round-robin wraps" (some 0) (Scheduler.roundRobin.next [0, 1] 1 0 [])
  assertEqual "greedy chooses first" (some 0) (Scheduler.greedy.next [1, 0] 1 0 [])
  assertEqual "exploring chooses unvisited" (some 1) (Scheduler.exploring.next [0, 1] 0 0 [0])
  assertEqual "wandering is deterministic" (Scheduler.wandering.next [0, 1, 2] 0 4 [])
    (Scheduler.wandering.next [0, 1, 2] 0 4 [])
  let (machine, id) := Machine.newMachine {}
  let machine ← modify machine fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 40))] } }
  let machine ← match machine.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machine ← modify machine fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 41))] } }
  let machine ← match machine.switch 0 with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let program : Bil.Program := [.move y (.bin .add (.var x) (int 1)), .jmp (.var y)]
  match Scheduler.runAll machine {} Scheduler.roundRobin program with
  | .error error => throw <| IO.userError error
  | .ok (_, results) =>
    match results with
    | [(firstId, .jump first), (secondId, .jump second)] =>
      assertEqual "round-robin first machine" 1 firstId
      assertEqual "round-robin first result" 42 first.toNat
      assertEqual "round-robin second machine" 0 secondId
      assertEqual "round-robin second result" 41 second.toNat
    | _ => throw <| IO.userError "unexpected scheduler results"
  let bytes : ByteArray := ByteArray.mk #[1, 2, 3]
  let original ← match Primus.Memory.map Primus.Memory.empty 0x1000 bytes rw with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"map failed: {repr error}"
  let changed ← match original.storeByte 0x1001 9 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"store failed: {repr error}"
  let changed := { changed with cells := { changed.cells with
    cells := changed.cells.cells.filter fun cell => cell.1 != BitVec.ofNat 64 0x1002 } }
  let delta := Delta.diff original changed
  assertEqual "checkpoint tracks changed and deleted cells" 2 delta.cells.length
  let restored := delta.apply original
  match restored.loadByte 0x1001 with
  | .ok value => assertEqual "checkpoint changed value restored" 9 value
  | .error error => throw <| IO.userError s!"restore failed: {repr error}"
  match restored.loadByte 0x1002 with
  | .ok value => assertEqual "checkpoint deleted value restored" 0 value
  | .error error => throw <| IO.userError s!"deleted restore failed: {repr error}"
  assertEqual "checkpoint regions restored" original.regions restored.regions
  let good : Job := ⟨"good", "successful", [], {}, {}⟩
  let bad : Job := {
    name := "bad"
    program := [.move x (.unknown "intentional" .unknown)]
  }
  assertEqual "jobs pending" 2 (Job.pending [good, bad])
  let result := Job.run [good, bad] {}
  assertEqual "job success recorded" 1 result.finished.length
  assertEqual "job failure recorded" 1 result.failures.length

end Bap.Tests.Scheduler
