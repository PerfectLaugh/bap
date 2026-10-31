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
  let (machine, id) ← match Machine.clone {} with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  let machine ← modify machine fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 40))] } }
  let machine ← match machine.switch id with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let machine ← modify machine fun inst => { inst with state := { env := [(x, .bits (BitVec.ofNat 64 41))] } }
  let machine ← match machine.switch 1 with
    | .ok machine => pure machine
    | .error error => throw <| IO.userError error
  let program : Bil.Program := [.move y (.bin .add (.var x) (int 1)), .jmp (.var y)]
  match Scheduler.runAll machine {} Scheduler.roundRobin program with
  | .error error => throw <| IO.userError error
  | .ok (_, results) =>
    match results with
    | [(firstId, .jump first), (secondId, .jump second)] =>
      assertEqual "round-robin first machine" id firstId
      assertEqual "round-robin first result" 42 first.toNat
      assertEqual "round-robin second machine" 1 secondId
      assertEqual "round-robin second result" 41 second.toNat
    | _ => throw <| IO.userError "unexpected scheduler results"
  -- A parent that waits runs after its child, and finds its status; a task in the same space is another process.
  let (waiting, child) ← match Machine.clone {} with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  let waiting := waiting.blockInWait (some child)
  assertEqual "a task that waits isn't runnable" [child] waiting.runnable
  match Scheduler.runAll waiting {} Scheduler.roundRobin [] with
  | .error error => throw <| IO.userError error
  | .ok (after, order) =>
    assertEqual "a parent runs after the child it waits for" [child, 1] (order.map (·.1))
    assertEqual "a parent finds the status of its child" [(1, Bap.Tasks.WaitResult.exited child (Bap.Tasks.exitedStatus 0))] after.waited
    assertEqual "a reported child is gone" [1] (after.insts.map (·.id))
  let (blocked, _) ← match Machine.clone {} with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  let blocked := (blocked.blockInWait (some 99))
  assertEqual "no such child wakes with nothing" [1] ((Machine.settle blocked).waited.map (·.1))
  let (sharing, sibling) ← match Machine.clone {} (shareMemory := true) (sameGroup := true) with
    | .ok result => pure result
    | .error error => throw <| IO.userError error
  assertEqual "a thread is in its process" [(1, 1), (sibling, 1)] (sharing.tasks.tasks.map fun task => (task.tid, task.group))
  assertEqual "a thread is in its space" (sharing.tasks.spaceOf 1) (sharing.tasks.spaceOf sibling)
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  let filled ← modify sharing fun inst =>
    { inst with state := { env := [(mem, .memory (Bap.Memory.empty 64))] } }
  match Machine.step filled {} (.move mem (.store (.var mem) (int 0x10) (int 7) .little 8)) with
  | .error error => throw <| IO.userError error
  | .ok (after, _) =>
    match after.insts.find? (·.id == sibling) with
    | some thread => assertEqual "a thread sees what its process writes" 7 (Bap.Memory.readByte thread.memory.cells (BitVec.ofNat 64 0x10)).toNat
    | none => throw <| IO.userError "the thread is gone"
  let bytes : ByteArray := ByteArray.mk #[1, 2, 3]
  let original ← match Primus.Memory.map Primus.Memory.empty 0x1000 bytes rw with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"map failed: {repr error}"
  let changed ← match original.storeByte 0x1001 9 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError s!"store failed: {repr error}"
  let changed := { changed with cells := Bap.Memory.writeByte changed.cells (BitVec.ofNat 64 0x1002) 0 }
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
