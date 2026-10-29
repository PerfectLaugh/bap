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

private def livenessStep (cfg : Cfg) (initial : Option (Tid × List Bap.Var))
    (ins outs : List (Tid × List Bap.Var)) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  cfg.reachable.reverse.foldl (init := (ins, outs)) fun state tid =>
    if initial.any fun entry => entry.1 = tid then
      state
    else
      match cfg.block tid with
      | none => state
      | some blk =>
        let out := blockOut cfg state.1 tid
        let input := blockIn blk out
        (Assoc.put tid input state.1, Assoc.put tid out state.2)

private def livenessAux (cfg : Cfg) (initial : Option (Tid × List Bap.Var)) :
    Nat → List (Tid × List Bap.Var) → List (Tid × List Bap.Var) →
      List (Tid × List Bap.Var) × List (Tid × List Bap.Var)
  | 0, ins, outs => (ins, outs)
  | fuel + 1, ins, outs =>
    let (nextIns, nextOuts) := livenessStep cfg initial ins outs
    if nextIns = ins ∧ nextOuts = outs then (ins, outs) else livenessAux cfg initial fuel nextIns nextOuts

def Cfg.livenessFrom (cfg : Cfg) (exit : Tid) (vars : List Bap.Var) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  let outs := Assoc.put exit vars ins
  let varCount := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length
  livenessAux cfg (some (exit, vars)) ((varCount + 1) * (cfg.reachable.length + 1)) ins outs

def Cfg.liveness (cfg : Cfg) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  let varCount := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length
  livenessAux cfg none ((varCount + 1) * (cfg.reachable.length + 1)) ins ins

@[simp] theorem liveness_empty : (Cfg.fromSub ⟨1, "empty", [], []⟩).liveness = ([], []) := by
  rfl

end Bap.IR
