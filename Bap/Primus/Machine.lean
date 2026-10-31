import Bap.Primus.Memory
import Bap.Bil.Eval
import Bap.Tasks

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

/-- A task of the machine, as `Bap.Tasks` has them: a thread and a process differ in what `clone` shares. -/
structure Instance where
  id : Nat
  state : Bil.State := {}
  memory : Memory := Memory.empty

structure Machine where
  insts : List Instance := [⟨1, {}, Memory.empty⟩]
  current : Nat := 1
  tasks : Tasks.TaskTable := Tasks.TaskTable.initial 1
  /-- What each task that `waitpid` blocked found, once it could go on. -/
  waited : List (Nat × Tasks.WaitResult) := []
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

/-- A new task with a copy of the state of the one that runs. `shareMemory` puts it in the same address space, and
`sameGroup`, which needs that, makes it a thread of the same process. -/
def clone (machine : Machine) (shareMemory sameGroup : Bool := false) : Except String (Machine × Nat) := do
  if sameGroup && !shareMemory then
    .error "a thread of a process shares its memory"
  let inst ← match currentInstance machine with
    | some inst => .ok inst
    | none => .error "current machine does not exist"
  let task ← match machine.tasks.find? machine.current with
    | some task => .ok task
    | none => .error "current machine has no task"
  let id := machine.insts.foldl (fun id inst => max id (inst.id + 1)) 0
  let added : Tasks.Entry := {
    tid := id
    group := if sameGroup then task.group else id
    parent := if sameGroup then task.parent else task.group
    space := if shareMemory then task.space else id }
  .ok ({ machine with insts := machine.insts ++ [{ inst with id }], tasks := machine.tasks.addTask added }, id)

/-- The first task, which takes in the children of a process that is over. -/
private def initTask (machine : Machine) : Nat :=
  match machine.tasks.tasks.head? with
  | some first => first.tid
  | none => 0

/-- The task that runs has exited with `code`, and its process if it was the last of it. -/
def exit (machine : Machine) (code : Nat) : Machine :=
  { machine with tasks := machine.tasks.exitTask machine.current (Tasks.exitedStatus code) (initTask machine) }

/-- `waitpid` in the task that runs, which doesn't block: what is reported is gone. -/
def waitpid (machine : Machine) (target : Option Nat := none) : Except String (Machine × Tasks.WaitResult) := do
  let task ← match machine.tasks.find? machine.current with
    | some task => .ok task
    | none => .error "current machine has no task"
  let found := machine.tasks.poll task.group target
  match found with
  | .exited child _ =>
    .ok ({ machine with
      tasks := machine.tasks.reap child
      insts := machine.insts.filter fun inst => (machine.tasks.reap child).find? inst.id |>.isSome }, found)
  | _ => .ok (machine, found)

/-- The task that runs doesn't run again until a child that `target` asks for is over. -/
def blockInWait (machine : Machine) (target : Option Nat := none) : Machine :=
  { machine with tasks := { machine.tasks with waiters := machine.tasks.waiters ++ [{ thread := machine.current, target }] } }

/-- The tasks that may run: those that have not exited and don't wait. -/
def runnable (machine : Machine) : List Nat :=
  (machine.insts.map Instance.id).filter fun id =>
    !machine.tasks.waiters.any (·.thread == id) &&
      match machine.tasks.find? id with
      | some task => task.status.isNone
      | none => false

/-- The waiters whose children are over can go on, and each is told what it found. -/
def settle (machine : Machine) : Machine :=
  let (tasks, woken) := machine.tasks.settle
  { machine with
    tasks
    insts := machine.insts.filter fun inst => (tasks.find? inst.id).isSome
    waited := machine.waited ++ woken.map fun entry => (entry.1.thread, entry.2) }

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
        -- What a task writes is in the state of each task of its address space.
        let space := machine.tasks.spaceOf machine.current
        .ok { machine with insts := machine.insts.map fun other =>
          if machine.tasks.spaceOf other.id != space then other
          else
            { other with
              memory := { other.memory with cells := cells }
              state := { env := Bil.bind other.state.env mem (.memory cells) } } }
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
