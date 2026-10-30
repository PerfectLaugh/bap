import Bap.Analysis.Xrefs

namespace Bap.Analysis.StateMachine

structure Case where
  value : Nat
  target : Nat
  deriving DecidableEq, Repr

structure Result where
  stateVar : Option Bap.Var := none
  cases : List Case := []
  complete : Bool := false
  deriving Repr

private def directTarget (next : Disasm.Insn) : Option Nat :=
  match next.bil.reverse.find? fun stmt => match stmt with | .jmp _ => true | _ => false with
  | some (.jmp (.int target)) => some target.toNat
  | _ => if next.flow = .normal then some next.address else next.target

private def assignments (insn : Disasm.Insn) : List (Bap.Var × Nat) :=
  insn.bil.filterMap fun stmt =>
    match stmt with
    | .move var exp =>
      match Bil.evalExp [] exp with
      | .ok value => (Bap.Value.asBits value).toOption.map fun value => (var, value.2.toNat)
      | .error _ => none
    | _ => none

private def simplerCandidates (instructions : List Disasm.Insn) : List (Bap.Var × Nat × Nat) :=
  (List.range (instructions.length - 1)).flatMap fun index =>
    match instructions[index]?, instructions[index + 1]? with
    | some current, some next =>
      match directTarget next with
      | some target => (assignments current).map fun assignment => (assignment.1, assignment.2, target)
      | none => []
    | _, _ => []

private def choose (instructions : List Disasm.Insn) : Option (Bap.Var × List Case) :=
  let triples := simplerCandidates instructions
  let variables := triples.map Prod.fst |>.eraseDups
  variables.foldl (init := none) fun best var =>
    let cases := (triples.filter fun triple => triple.1 = var).map fun triple => ⟨triple.2.1, triple.2.2⟩
    match best with
    | some current =>
      if current.2.length < cases.length then some (var, cases) else best
    | none => some (var, cases)

def analyzeWithState (instructions : List Disasm.Insn) (var : Bap.Var) : Result :=
  let cases := (simplerCandidates instructions).filterMap fun triple =>
    if triple.1 = var then some ⟨triple.2.1, triple.2.2⟩ else none
  {
    stateVar := some var
    cases
    complete := cases.length ≥ 2 && !instructions.any fun insn => insn.flow = .indirectJump
  }

def analyze (instructions : List Disasm.Insn) : Result :=
  match choose instructions with
  | none => {}
  | some (var, cases) => {
    stateVar := some var
    cases
    complete := cases.length ≥ 2 && !instructions.any fun insn => insn.flow = .indirectJump
  }

def isFlattened (result : Result) : Bool := result.complete && result.cases.length ≥ 2

def transition (result : Result) (value : Nat) : Option Nat :=
  (result.cases.find? fun current => current.value = value).map Case.target

def render (result : Result) : String :=
  let header := match result.stateVar with
    | some var => s!"state {var.name}"
    | none => "state <unknown>"
  let cases := result.cases.map fun current => s!"{current.value}: loc_{current.target}"
  String.intercalate "\n" (header :: cases)

end Bap.Analysis.StateMachine
