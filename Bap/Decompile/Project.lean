import Bap.Decompile
import Bap.Analysis.Xrefs
import Bap.ABI
import Bap.Bil.Transform

namespace Bap.Decompile

private def usedStmt : Bil.Stmt → List Bap.Var
  | .move _ value => Bil.freeVars value
  | .jmp target => Bil.freeVars target
  | .special _ | .cpuExn _ => []
  | .while condition body =>
    Bil.freeVars condition ++ body.flatMap usedStmt
  | .ifElse condition yes no =>
    Bil.freeVars condition ++ yes.flatMap usedStmt ++ no.flatMap usedStmt

private def usedInsns (instructions : List Disasm.Insn) : List Bap.Var :=
  (instructions.flatMap fun insn => insn.bil.flatMap usedStmt).eraseDups

private def functionDisasm (project : Project.Project) (symbol : Image.Symbol) : String :=
  let index := Analysis.Xrefs.create project
  let instructions := project.disasm.map (fun disasm =>
    disasm.instructions.filter fun insn => Analysis.Xrefs.owns index symbol insn.address) |>.getD []
  let code := instructions.flatMap Disasm.Insn.bil
  let used := usedInsns instructions
  let width := project.image.map (fun image => image.addrWidth) |>.getD 64
  let arch := project.image.map (fun image => image.arch) |>.getD .unknown
  match ABI.convention arch width with
  | some abi => function symbol.name (abi.functionArguments.filter used.contains) code
  | none => function symbol.name [] code

def project (project : Project.Project) : String :=
  let functions := project.image.map (fun image => image.symbols.filter Image.Symbol.isFunction) |>.getD []
  String.intercalate "\n\n" (functions.map (functionDisasm project))

end Bap.Decompile
