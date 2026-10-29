import Bap.Analysis.StateMachine

namespace Bap.Analysis.Deflatten

structure Recovery where
  disasm : Disasm.Disasm
  stateVar : Option Bap.Var := none
  cases : List StateMachine.Case := []
  complete : Bool := false

private def assigns (insn : Disasm.Insn) (var : Bap.Var) (value : Nat) : Bool :=
  insn.bil.any fun stmt =>
    match stmt with
    | .move dst (.int immediate) => dst = var && immediate.toNat = value
    | _ => false

private def assignmentAddresses (instructions : List Disasm.Insn) (var : Bap.Var) (cases : List StateMachine.Case) : List Nat :=
  instructions.filterMap fun insn =>
    if cases.any (fun current => assigns insn var current.value) then some insn.address else none

def recover (entry : Nat) (instructions : List Disasm.Insn) (external : List Nat := []) : Recovery :=
  let machine := StateMachine.analyze instructions
  match machine.stateVar with
  | none => { disasm := { entry, instructions } }
  | some var =>
    let addresses := instructions.map Disasm.Insn.address
    let missing := machine.cases.filter (fun current => !addresses.contains current.target && !external.contains current.target)
    let assignments := assignmentAddresses instructions var machine.cases
    let direct := machine.cases.flatMap fun current =>
      (assignmentAddresses instructions var [current]).map fun source => (source, current.target)
    let remaining := instructions.flatMap fun insn =>
      if assignments.contains insn.address || insn.flow = .indirectJump then []
      else insn.successors.map (insn.address, ·)
    {
      disasm := {
        entry
        instructions
        edges := (direct ++ remaining).eraseDups
      }
      stateVar := some var
      cases := machine.cases
      complete := machine.complete && missing.isEmpty
    }

end Bap.Analysis.Deflatten
