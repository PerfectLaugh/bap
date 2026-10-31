import Bap.Primus.Memory
import Bap.Bil.Eval

namespace Bap.Primus

inductive Event where
  | clock (time : Nat)
  | pcChange (address : Nat)
  | enterStmt
  | jump (address : Nat)
  | halt
  | exit (status : Nat)
  | pagefault (address : Nat)
  deriving DecidableEq, Repr

structure Instance where
  id : Nat
  state : Bil.State := {}
  memory : Memory := Memory.empty

structure Machine where
  insts : List Instance := [⟨0, {}, Memory.empty⟩]
  current : Nat := 0
  time : Nat := 0
  log : List Event := []
  observerHits : Nat := 0
  args : List String := []
  envp : List String := []

structure Component where
  name : String
  init : Machine → Except String Machine

structure System where
  components : List Component := []
  observers : List (Event → Machine → Except String Machine) := []

namespace Machine

def currentInstance (machine : Machine) : Option Instance :=
  machine.insts.find? fun inst => inst.id = machine.current

def modifyCurrent (machine : Machine) (f : Instance → Instance) : Except String Machine := do
  if (currentInstance machine).isSome then
    .ok { machine with insts := machine.insts.map fun inst =>
      if inst.id = machine.current then f inst else inst }
  else
    .error "current machine does not exist"

def newMachine (machine : Machine) : Machine × Nat :=
  let id := machine.insts.foldl (fun id inst => max id (inst.id + 1)) 0
  ({ machine with insts := machine.insts ++ [⟨id, {}, Memory.empty⟩] }, id)

def switch (machine : Machine) (id : Nat) : Except String Machine := do
  if machine.insts.any fun inst => inst.id = id then
    .ok { machine with current := id }
  else
    .error s!"unknown machine {id}"

def notify (event : Event) (machine : Machine) (system : System) : Except String Machine := do
  let machine := { machine with log := machine.log ++ [event] }
  system.observers.foldlM (fun machine observer => observer event machine) machine

def syncMemory (machine : Machine) : Except String Machine := do
  let mem : Bap.Var := ⟨"mem", .mem 64 8, 0, false⟩
  match currentInstance machine with
  | none => .error "current machine does not exist"
  | some inst =>
    match Bil.lookup inst.state.env mem with
    | .ok (@Bap.Value.memory addressWidth cells) =>
      if h : addressWidth = 64 then
        let cells : Bap.Memory 64 := h ▸ cells
        modifyCurrent machine fun inst => { inst with memory := { inst.memory with cells := cells } }
      else
        .ok machine
    | _ => .ok machine

def step (machine : Machine) (system : System) (stmt : Bil.Stmt) (fuel : Nat := 100000) :
    Except String (Machine × Bil.Effect) := do
  let inst ← match currentInstance machine with
    | some inst => .ok inst
    | none => .error "current machine does not exist"
  let machine ← notify .enterStmt machine system
  let machine ← notify (.clock machine.time) machine system
  let (state, effect) ← Bil.execStmt fuel inst.state stmt
  let machine ← modifyCurrent machine fun inst => { inst with state := state }
  let machine := { machine with time := machine.time + 1, observerHits := machine.observerHits + system.observers.length }
  let machine ← syncMemory machine
  match effect with
  | .normal => .ok (machine, effect)
  | .jump target => do
    let machine ← notify (.jump target.toNat) machine system
    .ok (machine, effect)
  | .special _ | .cpuExn _ => do
    let machine ← notify .halt machine system
    .ok (machine, effect)

private def runAux (machine : Machine) (system : System) : Nat → Bil.Program →
    Except String (Machine × Bil.Effect)
  | 0, _ => .error "Primus execution fuel exhausted"
  | _fuel + 1, [] => .ok (machine, .normal)
  | fuel + 1, stmt :: rest => do
    let (machine, effect) ← step machine system stmt
    match effect with
    | .normal => runAux machine system fuel rest
    | other => .ok (machine, other)

def run (machine : Machine) (system : System) (program : Bil.Program) (fuel : Nat := 100000) :
    Except String (Machine × Bil.Effect) :=
  runAux machine system fuel program

def init (system : System) (machine : Machine) : Except String Machine :=
  system.components.foldlM (fun machine component => component.init machine) machine

structure Transaction (α : Type) where
  machine : Machine
  result : Except String α

def atomically (initial : Machine) (action : Machine → Except String (Machine × α)) : Transaction α :=
  match action initial with
  | .ok (machine, value) => ⟨machine, .ok value⟩
  | .error error => ⟨initial, .error error⟩

def stepAtomic (machine : Machine) (system : System) (stmt : Bil.Stmt) (fuel : Nat := 100000) :
    Transaction Bil.Effect :=
  atomically machine fun initial => step initial system stmt fuel

def runAtomic (machine : Machine) (system : System) (program : Bil.Program) (fuel : Nat := 100000) :
    Transaction Bil.Effect :=
  atomically machine fun initial => run initial system program fuel

end Machine
end Bap.Primus
