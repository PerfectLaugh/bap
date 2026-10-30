import Bap.IR.Transform

namespace Bap.IR

private def union (left right : List Bap.Var) : List Bap.Var := (left ++ right).eraseDups
private def subtract (left right : List Bap.Var) : List Bap.Var := left.filter fun var => var ∉ right

private def blockOut (cfg : Cfg) (ins : List (Tid × List Bap.Var)) (tid : Tid) : List Bap.Var :=
  (cfg.successors tid).foldl (init := []) fun out successor =>
    match cfg.block successor with
    | none => out
    | some block =>
      let phiVars := block.phis.map Phi.var
      let successorIn := (Assoc.get successor ins).getD []
      let out := union out (subtract successorIn phiVars)
      block.phis.foldl (init := out) fun out phi =>
        match Assoc.get tid phi.values with
        | some value => union out (Bil.freeVars value)
        | none => out

private def blockIn (blk : Blk) (out : List Bap.Var) : List Bap.Var :=
  let step := blk.defs.foldl (init := ([], [])) fun state defn =>
    let input := state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2
    (input, defn.var :: state.2)
  let input := blk.jmps.foldl (init := step.1) fun input jmp => union input jmp.freeVars
  union input (subtract out step.2)

/-- Live-out of a block: what its successors need, plus the seed if it is the seeded exit. -/
private def seedOut (initial : Option (Tid × List Bap.Var)) (tid : Tid) (out : List Bap.Var) : List Bap.Var :=
  match initial with
  | some (exit, vars) => if exit = tid then union out vars else out
  | none => out

private def livenessStep (cfg : Cfg) (initial : Option (Tid × List Bap.Var))
    (ins outs : List (Tid × List Bap.Var)) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  cfg.reachable.reverse.foldl (init := (ins, outs)) fun state tid =>
    match cfg.block tid with
    | none => state
    | some blk =>
      let out := seedOut initial tid (blockOut cfg state.1 tid)
      let input := blockIn blk out
      (Assoc.put tid input state.1, Assoc.put tid out state.2)

/-- Tables are compared as sets per key: rebuilding a set may reorder it without changing it. -/
private def sameSets (keys : List Tid) (left right : List (Tid × List Bap.Var)) : Bool :=
  keys.all fun tid => Bap.Graph.setEq ((Assoc.get tid left).getD []) ((Assoc.get tid right).getD [])

private def livenessAux (cfg : Cfg) (initial : Option (Tid × List Bap.Var)) :
    Nat → List (Tid × List Bap.Var) → List (Tid × List Bap.Var) →
      List (Tid × List Bap.Var) × List (Tid × List Bap.Var)
  | 0, ins, outs => (ins, outs)
  | fuel + 1, ins, outs =>
    let (nextIns, nextOuts) := livenessStep cfg initial ins outs
    if sameSets cfg.reachable nextIns ins && sameSets cfg.reachable nextOuts outs then
      (ins, outs)
    else
      livenessAux cfg initial fuel nextIns nextOuts

/-- Each pass that changes a table adds a variable to a row of one of the two tables. -/
private def livenessFuel (cfg : Cfg) (vars : List Bap.Var) : Nat :=
  let varCount := (cfg.blocks.flatMap (fun blk => blk.definedVars ++ blk.freeVars) ++ vars).eraseDups.length
  2 * varCount * cfg.reachable.length + 1

def Cfg.livenessFrom (cfg : Cfg) (exit : Tid) (vars : List Bap.Var) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  let outs := Assoc.put exit vars ins
  livenessAux cfg (some (exit, vars)) (livenessFuel cfg vars) ins outs

def Cfg.liveness (cfg : Cfg) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  livenessAux cfg none (livenessFuel cfg []) ins ins

@[simp] theorem liveness_empty : (Cfg.fromSub ⟨1, "empty", [], []⟩).liveness = ([], []) := by
  rfl

end Bap.IR
