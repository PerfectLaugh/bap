import Bap.Primus.Machine

namespace Bap.Primus

structure Scheduler where
  name : String
  next : List Nat → Nat → Nat → List Nat → Option Nat

namespace Scheduler

private def first (ids : List Nat) : Option Nat := ids.head?

def roundRobin : Scheduler := {
  name := "round-robin"
  next := fun ids current _ _ =>
    match ids with
    | [] => none
    | _ =>
      let index := (ids.findIdx? (· = current)).getD 0 + 1
      some (ids[index % ids.length]? |>.getD ids.head!)
}

def greedy : Scheduler := {
  name := "greedy"
  next := fun ids _ _ _ => ids.min?
}

def wandering : Scheduler := {
  name := "wandering"
  next := fun ids _ time _ =>
    if ids.isEmpty then none else some (ids[(time * 1103515245 + 12345) % ids.length]? |>.getD ids.head!)
}

def exploring : Scheduler := {
  name := "exploring"
  next := fun ids _ _ history =>
    match ids.find? fun id => id ∉ history with
    | some id => some id
    | none => ids.head?
}

private def runAllAux (machine : Machine) (system : System) (scheduler : Scheduler)
    (program : Bil.Program) : Nat → List Nat → List Nat → List (Nat × Bil.Effect) →
      Except String (Machine × List (Nat × Bil.Effect))
  | 0, _, _, _ => .error "scheduler fuel exhausted"
  | fuel + 1, pending, history, results => do
    match scheduler.next pending machine.current machine.time history with
    | none => .ok (machine, results)
    | some id =>
      let machine ← machine.switch id
      let (machine, effect) ← machine.run system program
      runAllAux machine system scheduler program fuel (pending.erase id) (history ++ [id]) (results ++ [(id, effect)])

def runAll (machine : Machine) (system : System) (scheduler : Scheduler) (program : Bil.Program)
    (fuel : Nat := 1000) : Except String (Machine × List (Nat × Bil.Effect)) :=
  runAllAux machine system scheduler program fuel (machine.insts.map Instance.id) [] []

end Scheduler
end Bap.Primus
