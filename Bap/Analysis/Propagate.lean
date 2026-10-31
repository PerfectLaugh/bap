import Bap.Bil.Transform

namespace Bap.Analysis.Propagate

abbrev Known := List (Bap.Var × Bil.Exp)

def simplify (known : Known) (exp : Bil.Exp) : Bil.Exp :=
  Bil.foldExp (Bil.substitute known exp)

private def sameConstant : Bil.Exp → Bil.Exp → Bool
  | @Bil.Exp.int leftWidth left, @Bil.Exp.int rightWidth right =>
    leftWidth == rightWidth && left.toNat == right.toNat
  | _, _ => false

/-- The facts of `left` that `right` agrees with: what is known on both of two paths. -/
def meet (left right : Known) : Known :=
  left.filter fun entry => (Assoc.get entry.1 right).any (sameConstant entry.2)

mutual
  def stmt (known : Known) : Bil.Stmt → Known × Bil.Stmt
    | .move var value =>
      let value := simplify known value
      let known := match value with
        | .int _ => Assoc.put var value known
        | _ => Assoc.remove var known
      (known, .move var value)
    | .jmp target => (known, .jmp (simplify known target))
    | .special message => (known, .special message)
    | .cpuExn number => (known, .cpuExn number)
    | .while condition body =>
      let invariant := loopInvariant body (known.length + 1) known
      (invariant, .while (simplify invariant condition) (program invariant body).2)
    | .ifElse condition yes no =>
      let yes := program known yes
      let no := program known no
      (meet yes.1 no.1, .ifElse (simplify known condition) yes.2 no.2)
  termination_by statement => (sizeOf statement, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  /-- The greatest subset of `known` that one run of `body` preserves. Each round either stops at
  a fixpoint or drops a fact, so `known.length + 1` rounds suffice; without fuel nothing is known. -/
  def loopInvariant (body : List Bil.Stmt) : Nat → Known → Known
    | 0, _ => []
    | fuel + 1, known =>
      let next := meet known (program known body).1
      if next.length = known.length then known else loopInvariant body fuel next
  termination_by fuel _ => (sizeOf body, fuel + 1)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))

  def program (known : Known) (code : List Bil.Stmt) : Known × List Bil.Stmt :=
    code.foldl (fun current statement =>
      let (known, statement) := stmt current.1 statement
      (known, current.2 ++ [statement])) (known, [])
  termination_by (sizeOf code, 0)
  decreasing_by
    all_goals first
      | (apply Prod.Lex.right; simp_wf <;> omega)
      | (apply Prod.Lex.left; simp_wf <;> first
          | omega
          | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega))
end

def propagate (code : Bil.Program) : Bil.Program := (program {} code).2

end Bap.Analysis.Propagate
