import Bap.Project.Pass

namespace Bap.Plugin

structure Plugin where
  name : String
  passes : List Project.Pass := []

structure Registry where
  plugins : List Plugin := []

namespace Registry

def register (plugin : Plugin) (registry : Registry) : Registry :=
  { plugins := plugin :: registry.plugins.filter fun old => old.name != plugin.name }

def passes (registry : Registry) : List Project.Pass := registry.plugins.flatMap Plugin.passes

def findPass (registry : Registry) (name : String) : Option Project.Pass :=
  registry.passes.find? fun pass => pass.name = name

end Registry

def summarize : Project.Pass := {
  name := "summarize"
  autorun := true
  run := fun project =>
    let instructions := project.disasm.map (fun disasm => disasm.instructions.length) |>.getD 0
    .ok (project.set "instructions" (toString instructions))
}

def report : Project.Pass := {
  name := "report"
  dependencies := ["summarize"]
  autorun := true
  run := fun project =>
    let blocks := project.disasm.map (fun disasm => disasm.blocks.length) |>.getD 0
    .ok (project.set "blocks" (toString blocks) |>.set "status" "analyzed")
}

def defaultRegistry : Registry := Registry.register ⟨"x86-summary", [summarize, report]⟩ {}

private def includePass (registry : Registry) (pass : Project.Pass) (fuel : Nat)
    (included : List Project.Pass) : Except Project.PassError (List Project.Pass) := do
  if included.any fun old => old.name = pass.name then
    .ok included
  else
    match fuel with
    | 0 => .error (.runtime "plugins" "dependency closure fuel exhausted")
    | fuel + 1 =>
      let included ← pass.dependencies.foldlM (init := included) fun included dependency =>
        match registry.findPass dependency with
        | none => .error (.missingDependency pass.name dependency)
        | some dependencyPass => includePass registry dependencyPass fuel included
      .ok (included ++ [pass])
  termination_by structural fuel

private def includeDependencies (registry : Registry) (passes : List Project.Pass) :
    Except Project.PassError (List Project.Pass) :=
  passes.foldlM (init := []) fun included pass =>
    includePass registry pass (registry.passes.length * 2 + 1) included

def analyze (registry : Registry) (project : Project.Project) (names : List String := []) :
    Except Project.PassError Project.Project := do
  let passes ←
    if names.isEmpty then
      .ok (registry.passes.filter fun pass => pass.autorun)
    else
      includeDependencies registry (names.filterMap registry.findPass)
  Project.runPasses passes project

end Bap.Plugin
