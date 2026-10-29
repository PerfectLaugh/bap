import Bap.IR.Liveness

namespace Bap.IR

structure Constant where
  width : Nat
  value : Nat
  deriving DecidableEq, Repr

abbrev ConstEnv := List (Bap.Var × Constant)
abbrev ExitEnvs := List (Tid × ConstEnv)

def Constant.ofExp : Bil.Exp → Option Constant
  | @Bil.Exp.int width value => some ⟨width, value.toNat⟩
  | _ => none

def Constant.toExp (constant : Constant) : Bil.Exp := .int (BitVec.ofNat constant.width constant.value)

private def replacements (env : ConstEnv) : List (Bap.Var × Bil.Exp) :=
  env.map fun entry => (entry.1, entry.2.toExp)

private def joinEnv (left right : ConstEnv) : ConstEnv :=
  left.filter fun entry => Assoc.get entry.1 right = some entry.2

private def propagateBlock (blk : Blk) (env : ConstEnv) : Blk × ConstEnv :=
  let phis := blk.phis.map fun phi =>
    { phi with values := phi.values.map fun input => (input.1, Bil.simplifyExp input.2) }
  let (defs, env) := blk.defs.foldl (init := ([], env)) fun state defn =>
    let rhs := Bil.simplifyExp (Bil.substitute (replacements state.2) defn.rhs)
    let env := match Constant.ofExp rhs with
      | some constant => Assoc.put defn.var constant state.2
      | none => Assoc.remove defn.var state.2
    (state.1 ++ [{ defn with rhs := rhs }], env)
  let jmps := blk.jmps.map (Jmp.mapExp fun exp => Bil.simplifyExp (Bil.substitute (replacements env) exp))
  ({ blk with phis := phis, defs := defs, jmps := jmps }, env)

private def propagateAux (cfg : Cfg) : Nat → ExitEnvs → List Tid → Cfg × ExitEnvs
  | 0, exits, _ => (cfg, exits)
  | _fuel + 1, exits, [] => (cfg, exits)
  | fuel + 1, exits, tid :: work =>
    let predecessors := cfg.predecessors tid
    let incoming := predecessors.filterMap fun pred => Assoc.get pred exits
    let env := match incoming with
      | [] => []
      | first :: rest => rest.foldl joinEnv first
    match cfg.block tid with
    | none => propagateAux cfg fuel exits work
    | some blk =>
      let (blk, env) := propagateBlock blk env
      let cfg := cfg.updateBlock tid fun _ => blk
      if Assoc.get tid exits = some env then
        propagateAux cfg fuel exits work
      else
        propagateAux cfg fuel (Assoc.put tid env exits) (work ++ cfg.successors tid)

def propagateConstants (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let varCount := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length
  let fuel := (varCount + 2) * (cfg.blocks.length + 2) * (cfg.graph.edges.length + 2)
  (propagateAux cfg fuel [] (cfg.blocks.map Blk.tid)).1

private def hasSideEffect : Bil.Exp → Bool
  | .store _ _ _ _ _ => true
  | .load memory address _ _ => hasSideEffect memory || hasSideEffect address
  | .bin _ left right | .concat left right => hasSideEffect left || hasSideEffect right
  | .un _ value | .cast _ _ value | .extract _ _ value => hasSideEffect value
  | .letIn _ value body => hasSideEffect value || hasSideEffect body
  | .ite condition yes no => hasSideEffect condition || hasSideEffect yes || hasSideEffect no
  | .int _ | .var _ | .unknown _ _ => false

private def dcePass (cfg : Cfg) : Cfg :=
  let outs := cfg.liveness.2
  { cfg with blocks := cfg.blocks.map fun blk =>
    let live := ((Assoc.get blk.tid outs).getD [] ++ blk.freeVars).eraseDups
    { blk with
      defs := blk.defs.filter fun defn => live.contains defn.var || hasSideEffect defn.rhs
      phis := blk.phis.filter fun phi => live.contains phi.var
    }
  }

private def dceAux (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let next := dcePass cfg
    let before : List (Nat × Nat) := cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)
    let after : List (Nat × Nat) := next.blocks.map fun blk => (blk.defs.length, blk.phis.length)
    if before = after then cfg else dceAux next fuel

def eliminateDeadCode (cfg : Cfg) : Cfg :=
  let count := cfg.blocks.foldl (fun count blk => count + blk.defs.length + blk.phis.length) 0
  dceAux cfg (count + 1)

def optimize (sub : Sub) : Sub :=
  let cfg := propagateConstants (Cfg.fromSub sub)
  (eliminateDeadCode cfg).intoSub sub

theorem eval_constant_toExp (constant : Constant) :
    Bil.evalExp [] constant.toExp = .ok (.bits (BitVec.ofNat constant.width constant.value)) := by
  rfl

end Bap.IR
