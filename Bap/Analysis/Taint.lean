import Bap.Bil.Eval

namespace Bap.Analysis.Taint

abbrev Labels := List Nat

/-- A byte of a memory variable. -/
structure Cell where
  memory : Bap.Var
  address : Nat
  deriving DecidableEq, Repr

/-- `memory` holds the labels of the bytes of each memory variable, and `anywhere` labels that may be at any address of
any memory: a store with an address that is not known puts them there, and so does an assignment of a memory that is not
a store into itself. -/
structure State where
  vars : List (Bap.Var × Labels) := []
  memory : List (Cell × Labels) := []
  anywhere : Labels := []
  deriving Repr

private def union (left right : Labels) : Labels := (left ++ right).eraseDups

private def putVar (var : Bap.Var) (labels : Labels) (state : State) : State :=
  let vars := state.vars.filter fun binding => binding.1 != var
  { state with vars := if labels.isEmpty then vars else (var, labels) :: vars }

private def putMemory (cell : Cell) (labels : Labels) (state : State) : State :=
  let memory := state.memory.filter fun binding => binding.1 != cell
  { state with memory := if labels.isEmpty then memory else (cell, labels) :: memory }

def labelsOfVar (state : State) (var : Bap.Var) : Labels :=
  match state.vars.find? fun binding => binding.1 = var with
  | some binding => binding.2
  | none => []

private def byteLabels (state : State) (cell : Cell) : Labels :=
  match state.memory.find? fun binding => binding.1 = cell with
  | some binding => binding.2
  | none => []

def labelsOfMemory (state : State) (cell : Cell) : Labels :=
  union (byteLabels state cell) state.anywhere

def sourceVar (state : State) (var : Bap.Var) (labels : Labels) : State :=
  putVar var (union (labelsOfVar state var) labels) state

def sourceMemory (state : State) (cell : Cell) (labels : Labels) : State :=
  putMemory cell (union (byteLabels state cell) labels) state

def clearVar (state : State) (var : Bap.Var) : State := putVar var [] state

/-- Clears what is known to be at a byte; `anywhere` still applies to every address. -/
def clearMemory (state : State) (cell : Cell) : State := putMemory cell [] state

private def constant (exp : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

/-- The bytes of a `size`-byte access of `memory` at `address`, wrapping like the address space. -/
private def bytes (memory : Bap.Var) (address : Σ width, BitVec width) (size : Nat) : List Cell :=
  (List.range size).map fun offset => ⟨memory, (address.2 + BitVec.ofNat address.1 offset).toNat⟩

/-- Whether a variable can only hold bits, by its type. -/
private def bitsOnly (var : Bap.Var) : Bool :=
  match var.typ with
  | .imm _ => true
  | _ => false

/-- The memory variable whose bytes an expression holds, with what stores on it add, which are in its labels. -/
private def memoryOf : Bil.Exp → Option Bap.Var
  | .var var => if bitsOnly var then none else some var
  | .store memory .. => memoryOf memory
  | _ => none

/-- Whether an expression can have a memory for a value. -/
private def holdsMemory : Bil.Exp → Bool
  | .var var => !bitsOnly var
  | .store .. => true
  | .ite _ yes no => holdsMemory yes || holdsMemory no
  | .letIn _ _ body => holdsMemory body
  | _ => false

/-- Whether assigning `value` to `var` gives a memory bytes that are not its own, whose labels are not worth following. -/
private def mixes (var : Bap.Var) (value : Bil.Exp) : Bool :=
  match value with
  | .var source => source != var && (!bitsOnly var || !bitsOnly source)
  | _ => !bitsOnly var || holdsMemory value

private def allLabels (state : State) : Labels :=
  (state.vars.flatMap Prod.snd ++ state.memory.flatMap Prod.snd ++ state.anywhere).eraseDups

private def memoryLabels (state : State) : Labels :=
  union ((state.memory.map Prod.fst).flatMap (byteLabels state)) state.anywhere

/-- Labels may now be at any address of any memory. -/
private def smear (state : State) : State := { state with anywhere := memoryLabels state }

/-- Labels of a value. Control dependencies and pointer taint are not data flow: an `ite` condition
and a load address add nothing. A load of what is not known to be the bytes of a memory variable has the labels of
every memory, and so has what a `let` binds a memory to, whose name may be that of another. -/
def exp (state : State) : Bil.Exp → Labels
  | .int _ => []
  | .var var => labelsOfVar state var
  | .load memory address _ size =>
    union (exp state memory) <|
      match constant address, memoryOf memory with
      | some address, some var => ((bytes var address size).flatMap (labelsOfMemory state)).eraseDups
      | _, _ => memoryLabels state
  | .store memory address value _ _ =>
    union (exp state memory) (union (exp state address) (exp state value))
  | .bin _ left right => union (exp state left) (exp state right)
  | .un _ value => exp state value
  | .cast _ _ value => exp state value
  | .letIn var value body =>
    union (exp state value) (union (exp state body) (if bitsOnly var then [] else memoryLabels state))
  | .ite _ yes no => union (exp state yes) (exp state no)
  | .extract _ _ value => exp state value
  | .concat left right => union (exp state left) (exp state right)
  | .unknown _ _ => []

/-- The effect of assigning `value` to the memory variable `dst`, innermost store first. Only a memory stored into itself
keeps track of its bytes. -/
private def store (dst : Bap.Var) (state : State) : Bil.Exp → State
  | .store memory address value _ size =>
    let labels := union (exp state address) (exp state value)
    let inner := store dst state memory
    match constant address with
    | some address => (bytes dst address size).foldl (fun state byte => putMemory byte labels state) inner
    | none => { inner with anywhere := union inner.anywhere labels }
  | .var source =>
    if source = dst then state else smear (putVar dst (labelsOfVar state source) state)
  | other => smear (putVar dst (exp state other) state)

private def joinBindings [BEq α] (left right : List (α × Labels)) : List (α × Labels) :=
  let find (key : α) (bindings : List (α × Labels)) : Labels :=
    match bindings.find? fun binding => binding.1 == key with
    | some binding => binding.2
    | none => []
  left.map (fun binding => (binding.1, union binding.2 (find binding.1 right))) ++
    right.filter fun binding => !left.any fun other => other.1 == binding.1

/-- What holds if execution came through either state. -/
def join (left right : State) : State := {
  vars := joinBindings left.vars right.vars
  memory := joinBindings left.memory right.memory
  anywhere := union left.anywhere right.anywhere
}

/-- Whether every label of `left` is also in `right`. -/
def subsumed (left right : State) : Bool :=
  left.vars.all (fun binding => (labelsOfVar left binding.1).all (labelsOfVar right binding.1).contains) &&
    left.memory.all (fun binding => (byteLabels left binding.1).all (labelsOfMemory right binding.1).contains) &&
    left.anywhere.all right.anywhere.contains

/-- Everything `statement` can assign, at any depth. -/
private def assigned : Bil.Stmt → List Bap.Var
  | .move var _ => [var]
  | .while _ body => body.flatMap assigned
  | .ifElse _ yes no => yes.flatMap assigned ++ no.flatMap assigned
  | _ => []

private def storeCount : Bil.Exp → Nat
  | .store memory _ _ _ size => size + storeCount memory
  | _ => 0

private def writeCount : Bil.Stmt → Nat
  | .move _ value => 1 + storeCount value
  | .while _ body => (body.map writeCount).sum
  | .ifElse _ yes no => (yes.map writeCount).sum + (no.map writeCount).sum
  | _ => 0

/-- Above `state` and stable under `body` however it runs: every label may be anywhere in memory
and in everything `body` assigns. -/
private def saturate (state : State) (body : List Bil.Stmt) : State :=
  let labels := allLabels state
  let all := (body.flatMap assigned).foldl (fun state var => putVar var (union (labelsOfVar state var) labels) state) state
  { all with anywhere := labels }

/-- Rounds a loop can need: each one but the last adds a label to a variable or byte. -/
private def loopFuel (state : State) (body : List Bil.Stmt) : Nat :=
  (allLabels state).length * (state.vars.length + state.memory.length + (body.map writeCount).sum + 1) + 1

mutual
  def stmt (state : State) : Bil.Stmt → State
    | .move var value =>
      match value with
      | .store .. => store var state value
      | _ =>
        let assigned := putVar var (exp state value) state
        if mixes var value then smear assigned else assigned
    | .jmp _ | .special _ | .cpuExn _ => state
    | .while _ body => loopState body (loopFuel state body) state
    | .ifElse _ yes no => join (run state yes) (run state no)
  termination_by statement => (sizeOf statement, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  /-- The least state above `state` that one more run of `body` adds nothing to. -/
  private def loopState (body : List Bil.Stmt) : Nat → State → State
    | 0, state => saturate state body
    | fuel + 1, state =>
      let next := join state (run state body)
      if subsumed next state then state else loopState body fuel next
  termination_by fuel _ => (sizeOf body, fuel + 1)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  def run (state : State) (program : Bil.Program) : State :=
    program.foldl stmt state
  termination_by (sizeOf program, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
end

def taintedVars (state : State) : List Bap.Var := state.vars.map Prod.fst
def taintedMemory (state : State) : List Cell := state.memory.map Prod.fst

end Bap.Analysis.Taint
