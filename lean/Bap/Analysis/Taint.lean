import Bap.Bil.Eval

namespace Bap.Analysis.Taint

abbrev Labels := List Nat

structure State where
  vars : List (Bap.Var × Labels) := []
  memory : List (Nat × Labels) := []
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

def labelsOfMemory (state : State) (address : Nat) : Labels :=
  match state.memory.find? fun binding => binding.1 = address with
  | some binding => binding.2
  | none => []

def sourceVar (state : State) (var : Bap.Var) (labels : Labels) : State :=
  putVar var (union (labelsOfVar state var) labels) state

def sourceMemory (state : State) (address : Nat) (labels : Labels) : State :=
  putMemory address (union (labelsOfMemory state address) labels) state

def clearVar (state : State) (var : Bap.Var) : State := putVar var [] state
def clearMemory (state : State) (address : Nat) : State := putMemory address [] state

private def constant (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption.map fun value => value.2.toNat
  | .error _ => none

def exp (state : State) : Bil.Exp → Labels
  | .int _ => []
  | .var var => labelsOfVar state var
  | .load _ address _ _ => (constant address).toList.flatMap (labelsOfMemory state)
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

def stmt (state : State) : Bil.Stmt → State
  | .move _ (.store memory address value _ _) =>
    let labels := union (exp state memory) (union (exp state address) (exp state value))
    match constant address with
    | some address => putMemory address labels state
    | none => state
  | .move var value => putVar var (exp state value) state
  | .jmp _ | .special _ | .cpuExn _ => state
  | .while _ body => body.foldl stmt state
  | .ifElse _ yes no => no.foldl stmt (yes.foldl stmt state)

def run (state : State) (program : Bil.Program) : State :=
  program.foldl stmt state

def taintedVars (state : State) : List Bap.Var := state.vars.map Prod.fst
def taintedMemory (state : State) : List Nat := state.memory.map Prod.fst

end Bap.Analysis.Taint
