import Bap.Analysis.Propagate

namespace Bap.Analysis.DeadCode

structure Result where
  code : Bil.Program
  live : List Bap.Var
  deriving Repr

private def addVars (live additions : List Bap.Var) : List Bap.Var := (live ++ additions).eraseDups
private def removeVar (live : List Bap.Var) (var : Bap.Var) : List Bap.Var := live.filter (· != var)

mutual
  private def stmtLive (live : List Bap.Var) : Bil.Stmt → List Bap.Var × Option Bil.Stmt
    | .move var value =>
      if var.typ matches .mem _ _ then
        (addVars live (Bil.freeVars value), some (.move var value))
      else if live.contains var then
        (addVars (removeVar live var) (Bil.freeVars value), some (.move var value))
      else
        (live, none)
    | .jmp target => (addVars live (Bil.freeVars target), some (.jmp target))
    | .special message => (live, some (.special message))
    | .cpuExn number => (live, some (.cpuExn number))
    | .while condition body =>
      (addVars live (Bil.freeVars condition ++ (program live body).1), some (.while condition body))
    | .ifElse condition yes no =>
      (addVars live (Bil.freeVars condition ++ (program live yes).1 ++ (program live no).1),
        some (.ifElse condition yes no))

  private def program (live : List Bap.Var) (code : Bil.Program) : List Bap.Var × Bil.Program :=
    code.reverse.foldl (fun current statement =>
      let (live, statement) := stmtLive current.1 statement
      (live, statement.toList ++ current.2)) (live, [])
end

def analyze (outputs : List Bap.Var) (code : Bil.Program) : Result :=
  let (live, code) := program outputs code
  ⟨code, live⟩

def optimize (outputs : List Bap.Var) (code : Bil.Program) : Bil.Program :=
  (analyze outputs code).code

def optimizePropagated (outputs : List Bap.Var) (code : Bil.Program) : Bil.Program :=
  optimize outputs (Propagate.propagate code)

end Bap.Analysis.DeadCode
