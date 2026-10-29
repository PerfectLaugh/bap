import Bap.Plugin.Basic
import Bap.Core.Sexp

namespace Bap.Plugin

private def decodeSet (input : Sexp) : Except String (String × String) := do
  let args ← Sexp.expectTagged "set" 2 input
  match args with
  | [key, value] => .ok (← Sexp.asAtom key, ← Sexp.asAtom value)
  | _ => .error "invalid plugin set action"

private def decodeDependencies (input : Sexp) : Except String (List String) := do
  let items ← Sexp.asList input
  match items with
  | .atom "deps" :: dependencies => dependencies.mapM Sexp.asAtom
  | _ => .error "invalid plugin dependencies"

private def makePass (name : String) (dependencies : List String) (action : Sexp) : Except String Project.Pass := do
  let (key, value) ← decodeSet action
  .ok {
    name
    dependencies
    autorun := true
    run := fun project => .ok (project.set key value)
  }

private def decodePass (input : Sexp) : Except String Project.Pass := do
  let items ← Sexp.asList input
  match items with
  | [.atom "pass", .atom name, action] => makePass name [] action
  | [.atom "pass", .atom name, dependencies, action] =>
    makePass name (← decodeDependencies dependencies) action
  | _ => .error "invalid plugin pass"

private def decodePlugin (input : Sexp) : Except String Plugin := do
  let items ← Sexp.asList input
  match items with
  | .atom "plugin" :: .atom name :: passes => .ok ⟨name, ← passes.mapM decodePass⟩
  | _ => .error "invalid plugin bundle"

def load (registry : Registry) (path : String) : IO Registry := do
  let input ← IO.FS.readFile path
  match Sexp.parse input with
  | .error error => throw <| IO.userError error
  | .ok input =>
    match decodePlugin input with
    | .error error => throw <| IO.userError error
    | .ok plugin => pure (registry.register plugin)

def loadMany (registry : Registry) (paths : List String) : IO Registry :=
  paths.foldlM load registry

end Bap.Plugin
