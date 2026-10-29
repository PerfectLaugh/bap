import Bap.Project.Basic
import Bap.Bil.Eval

namespace Bap.Analysis.Xrefs

inductive Kind where
  | call | jump | load | store
  deriving DecidableEq, Repr

structure Xref where
  source : Nat
  target : Nat
  kind : Kind
  deriving DecidableEq, Repr

structure Index where
  xrefs : List Xref := []
  functions : List Image.Symbol := []

private def constant (exp : Bil.Exp) : Option Nat :=
  match Bil.evalExp [] exp with
  | .ok value => (Bap.Value.asBits value).toOption.map fun value => value.2.toNat
  | .error _ => none

private def memoryRefs (source : Nat) : Bil.Exp → List Xref
  | .load memory address _ _ =>
    (constant address).toList.map (⟨source, ·, .load⟩) ++ memoryRefs source memory ++ memoryRefs source address
  | .store memory address value _ _ =>
    (constant address).toList.map (⟨source, ·, .store⟩) ++
      memoryRefs source memory ++ memoryRefs source address ++ memoryRefs source value
  | .bin _ left right => memoryRefs source left ++ memoryRefs source right
  | .un _ value => memoryRefs source value
  | .cast _ _ value => memoryRefs source value
  | .letIn _ value body => memoryRefs source value ++ memoryRefs source body
  | .ite condition yes no => memoryRefs source condition ++ memoryRefs source yes ++ memoryRefs source no
  | .extract _ _ value => memoryRefs source value
  | .concat left right => memoryRefs source left ++ memoryRefs source right
  | _ => []

private def stmtRefs (insn : Disasm.Insn) : Bil.Stmt → List Xref
  | .move _ value => memoryRefs insn.address value
  | .jmp target =>
    (constant target).toList.map (⟨insn.address, ·, if insn.flow = .call then .call else .jump⟩) ++
      memoryRefs insn.address target
  | .while condition body =>
    memoryRefs insn.address condition ++ body.flatMap (stmtRefs insn)
  | .ifElse condition yes no =>
    memoryRefs insn.address condition ++ yes.flatMap (stmtRefs insn) ++ no.flatMap (stmtRefs insn)
  | _ => []

private def insnRefs (insn : Disasm.Insn) : List Xref :=
  insn.bil.flatMap (stmtRefs insn)

def create (project : Project.Project) : Index := {
  xrefs := project.disasm.map (fun disasm => disasm.instructions.flatMap insnRefs) |>.getD []
  functions := project.image.map (fun image => image.symbols.filter Image.Symbol.isFunction) |>.getD []
}

def functionAt (index : Index) (address : Nat) : Option Image.Symbol :=
  index.functions.find? fun symbol => symbol.addr = address

def functionOf (index : Index) (address : Nat) : Option Image.Symbol :=
  index.functions.foldl (init := none) fun best symbol =>
    if symbol.addr ≤ address && (match best with
      | some current => current.addr ≤ symbol.addr
      | none => true) then
      some symbol
    else
      best

def functions (index : Index) : List String := index.functions.map Image.Symbol.name

def references (index : Index) (kind : Kind) (target : Nat) : List Xref :=
  index.xrefs.filter fun xref => xref.kind = kind && xref.target = target

def callers (index : Index) (target : Nat) : List Xref := references index .call target

def callees (index : Index) (function : String) : List Xref :=
  index.xrefs.filter fun xref =>
    xref.kind = .call && (functionOf index xref.source).map Image.Symbol.name = some function

end Bap.Analysis.Xrefs
