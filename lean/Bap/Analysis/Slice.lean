import Bap.Analysis.Xrefs

namespace Bap.Analysis.Slice

inductive Location where
  | reg (var : Bap.Var)
  | mem (address size : Nat)
  deriving DecidableEq, Repr

structure Result where
  sites : List Nat := []
  live : List Location := []
  complete : Bool := true
  deriving Repr

private structure Info where
  defs : List Location := []
  uses : List Location := []
  dynamic : Bool := false
  always : Bool := false

private def constant (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption.map fun value => value.2.toNat
  | .error _ => none

private def usesExp : Bil.Exp → Info
  | .int _ => {}
  | .var var => if var.typ matches .imm _ then { uses := [.reg var] } else {}
  | .load memory address _ size =>
    let dynamic := (constant address).isNone
    let uses := (constant address).toList.map (fun address => Location.mem address size)
    { uses := uses ++ (usesExp memory).uses ++ (usesExp address).uses,
      dynamic := dynamic || (usesExp memory).dynamic || (usesExp address).dynamic }
  | .store memory address value _ _ =>
    let left := usesExp memory
    let middle := usesExp address
    let right := usesExp value
    { uses := left.uses ++ middle.uses ++ right.uses, dynamic := left.dynamic || middle.dynamic || right.dynamic }
  | .bin _ left right =>
    let left := usesExp left
    let right := usesExp right
    { uses := left.uses ++ right.uses, dynamic := left.dynamic || right.dynamic }
  | .un _ value => usesExp value
  | .cast _ _ value => usesExp value
  | .letIn _ value body =>
    let value := usesExp value
    let body := usesExp body
    { uses := value.uses ++ body.uses, dynamic := value.dynamic || body.dynamic }
  | .ite condition yes no =>
    let condition := usesExp condition
    let yes := usesExp yes
    let no := usesExp no
    { uses := condition.uses ++ yes.uses ++ no.uses, dynamic := condition.dynamic || yes.dynamic || no.dynamic }
  | .extract _ _ value => usesExp value
  | .concat left right =>
    let left := usesExp left
    let right := usesExp right
    { uses := left.uses ++ right.uses, dynamic := left.dynamic || right.dynamic }
  | .unknown _ _ => { dynamic := true, always := true }

private def merge (left right : Info) : Info := {
  defs := left.defs ++ right.defs
  uses := left.uses ++ right.uses
  dynamic := left.dynamic || right.dynamic
  always := left.always || right.always
}

private def stmtInfo : Bil.Stmt → Info
  | .move _ (.store memory address value _ size) =>
    let dynamic := (constant address).isNone
    let defs := (constant address).toList.map (fun address => Location.mem address size)
    let used := merge (usesExp memory) (merge (usesExp address) (usesExp value))
    { defs, uses := used.uses, dynamic := dynamic || used.dynamic }
  | .move var value => { defs := [.reg var], uses := (usesExp value).uses, dynamic := (usesExp value).dynamic }
  | .jmp target => usesExp target
  | .special _ => { dynamic := true, always := true }
  | .cpuExn _ => { dynamic := true, always := true }
  | .while condition body =>
    let condition := usesExp condition
    let body := body.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition { body with always := true, dynamic := true }
  | .ifElse condition yes no =>
    let condition := usesExp condition
    let yes := yes.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    let no := no.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition (merge yes no)

private def addUnique (values : List Location) (value : Location) : List Location :=
  if values.contains value then values else values ++ [value]

private def removeDefinitions (live : List Location) (defs : List Location) : List Location :=
  live.filter fun location => !defs.contains location

private def relevant (live : List Location) (info : Info) : Bool :=
  info.always || info.defs.any (fun definition => live.contains definition) ||
    info.uses.any (fun use => live.contains use)

private def backwardInstruction (live : List Location) (info : Info) : List Location :=
  let live := removeDefinitions live info.defs
  info.uses.foldl addUnique live

def backward (instructions : List Disasm.Insn) (criteria : List Location) : Result :=
  let final := instructions.reverse.foldl (init := (criteria, [], true)) fun current insn =>
    let info := insn.bil.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    if relevant current.1 info then
      (backwardInstruction current.1 info, current.2.1 ++ [insn.address], current.2.2 && !info.dynamic)
    else
      current
  { sites := final.2.1.reverse, live := final.1, complete := final.2.2 }

def backwardProject (project : Project.Project) (entry : Nat) (criteria : List Location) : Result :=
  let index := Xrefs.create project
  let owner := Xrefs.functionOf index entry
  let instructions := project.disasm.map (fun disasm =>
    if owner.isSome then
      disasm.instructions.filter fun insn => Xrefs.functionOf index insn.address = owner
    else
      disasm.instructions) |>.getD []
  backward instructions criteria

end Bap.Analysis.Slice
