import Bap.Bil.Eval

namespace Bap.Analysis.Taint

abbrev Labels := List Nat

/-- `memory` holds per-byte labels, and `anywhere` labels a store may have put at any address. -/
structure State where
  vars : List (Bap.Var × Labels) := []
  memory : List (Nat × Labels) := []
  anywhere : Labels := []
  deriving Repr

private def union (left right : Labels) : Labels := (left ++ right).eraseDups

private def putVar (var : Bap.Var) (labels : Labels) (state : State) : State :=
  let vars := state.vars.filter fun binding => binding.1 != var
  { state with vars := if labels.isEmpty then vars else (var, labels) :: vars }

private def putMemory (address : Nat) (labels : Labels) (state : State) : State :=
  let memory := state.memory.filter fun binding => binding.1 != address
  { state with memory := if labels.isEmpty then memory else (address, labels) :: memory }

def labelsOfVar (state : State) (var : Bap.Var) : Labels :=
  match state.vars.find? fun binding => binding.1 = var with
  | some binding => binding.2
  | none => []

private def byteLabels (state : State) (address : Nat) : Labels :=
  match state.memory.find? fun binding => binding.1 = address with
  | some binding => binding.2
  | none => []

def labelsOfMemory (state : State) (address : Nat) : Labels :=
  union (byteLabels state address) state.anywhere

def sourceVar (state : State) (var : Bap.Var) (labels : Labels) : State :=
  putVar var (union (labelsOfVar state var) labels) state

def sourceMemory (state : State) (address : Nat) (labels : Labels) : State :=
  putMemory address (union (byteLabels state address) labels) state

def clearVar (state : State) (var : Bap.Var) : State := putVar var [] state

/-- Clears what is known to be at `address`; `anywhere` still applies to every address. -/
def clearMemory (state : State) (address : Nat) : State := putMemory address [] state

private def constant (exp : Bil.Exp) : Option (Σ width, BitVec width) :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption
  | .error _ => none

/-- The addresses of a `size`-byte access at `address`, wrapping like the address space. -/
private def bytes (address : Σ width, BitVec width) (size : Nat) : List Nat :=
  (List.range size).map fun offset => (address.2 + BitVec.ofNat address.1 offset).toNat

private def allLabels (state : State) : Labels :=
  (state.vars.flatMap Prod.snd ++ state.memory.flatMap Prod.snd ++ state.anywhere).eraseDups

private def memoryLabels (state : State) : Labels :=
  union ((state.memory.map Prod.fst).flatMap (byteLabels state)) state.anywhere

/-- Labels of a value. Control dependencies and pointer taint are not data flow: an `ite` condition
and a load address add nothing. -/
def exp (state : State) : Bil.Exp → Labels
  | .int _ => []
  | .var var => labelsOfVar state var
  | .load memory address _ size =>
    union (exp state memory) <|
      match constant address with
      | some address => ((bytes address size).flatMap (labelsOfMemory state)).eraseDups
      | none => memoryLabels state
  | .store memory address value _ _ =>
    union (exp state memory) (union (exp state address) (exp state value))
  | .bin _ left right => union (exp state left) (exp state right)
  | .un _ value => exp state value
  | .cast _ _ value => exp state value
  | .letIn _ value body => union (exp state value) (exp state body)
  | .ite _ yes no => union (exp state yes) (exp state no)
  | .extract _ _ value => exp state value
  | .concat left right => union (exp state left) (exp state right)
  | .unknown _ _ => []

/-- The effect of assigning `value` to the memory variable `dst`, innermost store first. -/
private def store (dst : Bap.Var) (state : State) : Bil.Exp → State
  | .store memory address value _ size =>
    let labels := union (exp state address) (exp state value)
    let inner := store dst state memory
    match constant address with
    | some address => (bytes address size).foldl (fun state byte => putMemory byte labels state) inner
    | none => { inner with anywhere := union inner.anywhere labels }
  | .var source =>
    if source = dst then state else putVar dst (labelsOfVar state source) state
  | other => putVar dst (exp state other) state

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
      | _ => putVar var (exp state value) state
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
def taintedMemory (state : State) : List Nat := state.memory.map Prod.fst

end Bap.Analysis.Taint
