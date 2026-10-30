import Bap.Project.Basic

namespace Bap.Project

structure Pass where
  name : String
  dependencies : List String := []
  autorun : Bool := false
  runonce : Bool := true
  run : Project → Except String Project

inductive PassError where
  | missingDependency (pass dependency : String)
  | cycle (pass : String)
  | runtime (pass message : String)
  | unknownPass (name : String)
  deriving Repr

private def runPass (pass : Pass) (project : Project) : Except PassError Project := do
  if pass.runonce && project.passed.contains pass.name then
    .ok project
  else
    match pass.run project with
    | .ok project => .ok (project.markPassed pass.name)
    | .error error => .error (.runtime pass.name error)

/-- Depth-first traversal. Fuel bounds the depth only, and each level adds a new name to
`temporary`, so more fuel than there are distinct names is never exhausted. -/
def visit (passes : List Pass) (pass : Pass) (fuel : Nat) (temporary permanent : List String) :
    Except PassError (List String × List String) := do
  match fuel with
  | 0 => .error (.runtime "scheduler" "dependency traversal fuel exhausted")
  | fuel + 1 =>
    if permanent.contains pass.name then
      .ok (temporary, permanent)
    else if temporary.contains pass.name then
      .error (.cycle pass.name)
    else
      let (temporary, permanent) ←
        pass.dependencies.foldlM (init := (pass.name :: temporary, permanent)) fun visited dependency =>
          match passes.find? fun candidate => candidate.name = dependency with
          | none => .error (.missingDependency pass.name dependency)
          | some dependencyPass => visit passes dependencyPass fuel visited.1 visited.2
      .ok (temporary, pass.name :: permanent)
termination_by structural fuel

private def sortPassesAux (passes remaining : List Pass) (ordered : List String) :
    Except PassError (List String) := do
  match remaining with
  | [] => .ok ordered
  | pass :: rest =>
    let (_, ordered) ← visit passes pass (passes.length + 1) [] ordered
    sortPassesAux passes rest ordered

private def sortPasses (passes : List Pass) : Except PassError (List Pass) := do
  let ordered ← sortPassesAux passes passes []
  .ok (ordered.filterMap fun name => passes.find? fun pass => pass.name = name).reverse

def runPasses (passes : List Pass) (project : Project) : Except PassError Project := do
  let passes ← sortPasses passes
  passes.foldlM (fun project pass => runPass pass project) project

end Bap.Project
