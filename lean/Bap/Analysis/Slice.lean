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

namespace Location

/-- Whether two locations share a register or at least one byte. -/
def overlaps : Location → Location → Bool
  | .reg left, .reg right => left == right
  | .mem left leftSize, .mem right rightSize => left < right + rightSize && right < left + leftSize
  | _, _ => false

/-- Whether a write to `outer` overwrites every byte of `inner`. -/
def covers (outer inner : Location) : Bool :=
  outer.overlaps inner && match outer, inner with
    | .mem outerAddress outerSize, .mem innerAddress innerSize =>
      outerAddress ≤ innerAddress && innerAddress + innerSize ≤ outerAddress + outerSize
    | _, _ => true

def isMemory : Location → Bool
  | .mem _ _ => true
  | .reg _ => false

end Location

/-- What an instruction does. `defs` are always overwritten, `mayDefs` possibly overwritten, and
`unknownWrite` means memory is written somewhere that could not be determined. -/
private structure Info where
  defs : List Location := []
  mayDefs : List Location := []
  uses : List Location := []
  dynamic : Bool := false
  always : Bool := false
  unknownWrite : Bool := false

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
  mayDefs := left.mayDefs ++ right.mayDefs
  uses := left.uses ++ right.uses
  dynamic := left.dynamic || right.dynamic
  always := left.always || right.always
  unknownWrite := left.unknownWrite || right.unknownWrite
}

/-- The locations `value` writes when assigned to `dst`, and whether it writes anywhere else. -/
private def memoryWrites (dst : Bap.Var) : Bil.Exp → List Location × Bool
  | .store memory address _ _ size =>
    let inner := memoryWrites dst memory
    match constant address with
    | some address => (.mem address size :: inner.1, inner.2)
    | none => (inner.1, true)
  | .var source => ([], source != dst)
  | _ => ([], true)

private def isStore : Bil.Exp → Bool
  | .store .. => true
  | _ => false

private def stmtInfo : Bil.Stmt → Info
  | .move var value =>
    if isStore value || var.typ matches .mem _ _ then
      let writes := memoryWrites var value
      let target : List Location := if var.typ matches .mem _ _ then [] else [.reg var]
      { defs := writes.1 ++ target, uses := (usesExp value).uses, dynamic := writes.2 || (usesExp value).dynamic,
        unknownWrite := writes.2 }
    else
      { defs := [.reg var], uses := (usesExp value).uses, dynamic := (usesExp value).dynamic }
  | .jmp target => usesExp target
  | .special _ => { dynamic := true, always := true }
  | .cpuExn _ => { dynamic := true, always := true }
  | .while condition body =>
    let condition := usesExp condition
    let body := body.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition { uses := body.uses, mayDefs := body.defs ++ body.mayDefs,
                      unknownWrite := body.unknownWrite, always := true, dynamic := true }
  | .ifElse condition yes no =>
    let condition := usesExp condition
    let yes := yes.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    let no := no.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    merge condition {
      defs := yes.defs.filter no.defs.contains
      mayDefs := yes.defs ++ yes.mayDefs ++ no.defs ++ no.mayDefs
      uses := yes.uses ++ no.uses
      dynamic := yes.dynamic || no.dynamic
      always := yes.always || no.always
      unknownWrite := yes.unknownWrite || no.unknownWrite
    }

private def addUnique (values : List Location) (value : Location) : List Location :=
  if values.contains value then values else values ++ [value]

private def removeDefinitions (live : List Location) (defs : List Location) : List Location :=
  live.filter fun location => !defs.any fun definition => definition.covers location

private def touches (live : List Location) (location : Location) : Bool :=
  live.any location.overlaps

private def relevant (live : List Location) (info : Info) : Bool :=
  info.always || (info.unknownWrite && live.any Location.isMemory) ||
    info.defs.any (touches live) || info.mayDefs.any (touches live) || info.uses.any (touches live)

private def backwardInstruction (live : List Location) (info : Info) : List Location :=
  let live := removeDefinitions live info.defs
  info.uses.foldl addUnique live

/-- Slices `instructions`, taken as a linear execution order. `complete` means no site's effect on
a live location was undetermined. -/
def backward (instructions : List Disasm.Insn) (criteria : List Location) : Result :=
  let final := instructions.reverse.foldl (init := (criteria, [], true)) fun current insn =>
    let info := insn.bil.foldl (fun info stmt => merge info (stmtInfo stmt)) {}
    if relevant current.1 info then
      (backwardInstruction current.1 info, current.2.1 ++ [insn.address], current.2.2 && !info.dynamic)
    else
      current
  { sites := final.2.1.reverse, live := final.1, complete := final.2.2 }

/-- Whether the listing order of `instructions` is an execution order: no branch can skip or
repeat a listed instruction. -/
private def linear (instructions : List Disasm.Insn) : Bool :=
  let addresses := instructions.map Disasm.Insn.address
  instructions.all fun insn =>
    match insn.flow with
    | .conditionalJump | .indirectJump => false
    | .jump => !insn.target.any addresses.contains
    | _ => true

def backwardProject (project : Project.Project) (entry : Nat) (criteria : List Location) : Result :=
  let index := Xrefs.create project
  let owner := (Xrefs.functionOf index entry).map Image.Symbol.addr
  let instructions := project.disasm.map (fun disasm =>
    if owner.isSome then
      disasm.instructions.filter fun insn =>
        (Xrefs.functionOf index insn.address).map Image.Symbol.addr = owner
    else
      disasm.instructions) |>.getD []
  let result := backward instructions criteria
  { result with complete := result.complete && linear instructions }

end Bap.Analysis.Slice
