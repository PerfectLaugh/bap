import Bap.Analysis.Propagate

namespace Bap.Analysis.DeadCode

structure Result where
  code : Bil.Program
  live : List Bap.Var
  deriving Repr

private def addVars (live additions : List Bap.Var) : List Bap.Var := (live ++ additions).eraseDups
private def removeVar (live : List Bap.Var) (var : Bap.Var) : List Bap.Var := live.filter (· != var)

/-- Every variable a statement reads, at any depth. -/
private def reads : Bil.Stmt → List Bap.Var
  | .move _ value => Bil.freeVars value
  | .jmp target => Bil.freeVars target
  | .special _ | .cpuExn _ => []
  | .while condition body => Bil.freeVars condition ++ body.flatMap reads
  | .ifElse condition yes no => Bil.freeVars condition ++ yes.flatMap reads ++ no.flatMap reads

mutual
  /-- Liveness before a statement given `live` after it. Jumps, specials and CPU exceptions end
  the program, so what is live before them is `outputs` and not what follows them. -/
  private def stmtLive (outputs live : List Bap.Var) : Bil.Stmt → List Bap.Var × Option Bil.Stmt
    | .move var value =>
      if var.typ matches .mem _ _ then
        (addVars live (Bil.freeVars value), some (.move var value))
      else if live.contains var then
        (addVars (removeVar live var) (Bil.freeVars value), some (.move var value))
      else
        (live, none)
    | .jmp target => (addVars outputs (Bil.freeVars target), some (.jmp target))
    | .special message => (outputs, some (.special message))
    | .cpuExn number => (outputs, some (.cpuExn number))
    | .while condition body =>
      let start := addVars live (Bil.freeVars condition)
      let head := loopLive outputs body
        ((body.flatMap reads ++ outputs ++ start).eraseDups.length + 1) start
      (head, some (.while condition (program outputs head body).2))
    | .ifElse condition yes no =>
      let yes := program outputs live yes
      let no := program outputs live no
      (addVars (Bil.freeVars condition) (yes.1 ++ no.1), some (.ifElse condition yes.2 no.2))
  termination_by statement => (sizeOf statement, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  /-- Liveness at a loop head: the least set above `current` closed under one run of `body`.
  Each round either stops or adds a variable; without fuel, everything the loop can read. -/
  private def loopLive (outputs : List Bap.Var) (body : List Bil.Stmt) :
      Nat → List Bap.Var → List Bap.Var
    | 0, current => addVars current (body.flatMap reads ++ outputs)
    | fuel + 1, current =>
      let before := (program outputs current body).1
      if before.all current.contains then current
      else loopLive outputs body fuel (addVars current before)
  termination_by fuel _ => (sizeOf body, fuel + 1)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  private def program (outputs live : List Bap.Var) (code : List Bil.Stmt) :
      List Bap.Var × List Bil.Stmt :=
    code.reverse.foldl (fun current statement =>
      let (live, kept) := stmtLive outputs current.1 statement
      (live, kept.toList ++ current.2)) (live, [])
  termination_by (sizeOf code, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
end

def analyze (outputs : List Bap.Var) (code : Bil.Program) : Result :=
  let (live, code) := program outputs outputs code
  ⟨code, live⟩

def optimize (outputs : List Bap.Var) (code : Bil.Program) : Bil.Program :=
  (analyze outputs code).code

def optimizePropagated (outputs : List Bap.Var) (code : Bil.Program) : Bil.Program :=
  optimize outputs (Propagate.propagate code)

end Bap.Analysis.DeadCode
