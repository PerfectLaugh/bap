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

/-- Rewrites a block under the constants known at its entry and returns those known at its exit.
A phi assigns its variable on entry, so an incoming constant for it no longer holds. -/
private def propagateBlock (blk : Blk) (env : ConstEnv) : Blk × ConstEnv :=
  let phiVars := blk.phis.map Phi.var
  let env : ConstEnv := env.filter fun entry => entry.1 ∉ phiVars
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

/-- Constants known on entry: nothing at the start, whose entry state is unconstrained even when it
has predecessors, otherwise the join over the predecessors analysed so far. -/
private def entryEnv (cfg : Cfg) (exits : ExitEnvs) (tid : Tid) : ConstEnv :=
  if tid = cfg.start then
    []
  else
    match (cfg.predecessors tid).filterMap fun pred => Assoc.get pred exits with
    | [] => []
    | first :: rest => rest.foldl joinEnv first

/-- Optimistic forward analysis from the start. It never edits the CFG. -/
private def propagateAux (cfg : Cfg) : Nat → ExitEnvs → List Tid → ExitEnvs
  | 0, exits, _ => exits
  | _fuel + 1, exits, [] => exits
  | fuel + 1, exits, tid :: work =>
    match cfg.block tid with
    | none => propagateAux cfg fuel exits work
    | some blk =>
      let env := (propagateBlock blk (entryEnv cfg exits tid)).2
      if Assoc.get tid exits = some env then
        propagateAux cfg fuel exits work
      else
        propagateAux cfg fuel (Assoc.put tid env exits) (work ++ cfg.successors tid)

/-- The analysis result is a fixpoint of the transfer functions on every block. -/
private def isSolved (cfg : Cfg) (exits : ExitEnvs) : Bool :=
  cfg.blocks.all fun blk =>
    Assoc.get blk.tid exits = some (propagateBlock blk (entryEnv cfg exits blk.tid)).2

/-- Rewrites each block once, from the fixpoint. If the analysis ran out of fuel only constants local
to each block are used. -/
def propagateConstants (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let varCount := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length
  let fuel := (varCount + 2) * (cfg.blocks.length + 2) * (cfg.graph.edges.length + 2)
  let exits := propagateAux cfg fuel [] [cfg.start]
  let solved := isSolved cfg exits
  { cfg with blocks := cfg.blocks.map fun blk =>
    (propagateBlock blk (if solved then entryEnv cfg exits blk.tid else [])).1
  }

private def hasSideEffect : Bil.Exp → Bool
  | .store _ _ _ _ _ => true
  | .load memory address _ _ => hasSideEffect memory || hasSideEffect address
  | .bin _ left right | .concat left right => hasSideEffect left || hasSideEffect right
  | .un _ value | .cast _ _ value | .extract _ _ value => hasSideEffect value
  | .letIn _ value body => hasSideEffect value || hasSideEffect body
  | .ite condition yes no => hasSideEffect condition || hasSideEffect yes || hasSideEffect no
  | .int _ | .var _ | .unknown _ _ => false

/-- Backward scan of a block's definitions from the variables live after them. Returns the kept
definitions and the variables live before them. -/
private def dceDefs (defs : List Def) (live : List Bap.Var) : List Def × List Bap.Var :=
  defs.foldr (init := ([], live)) fun defn state =>
    if state.2.contains defn.var || hasSideEffect defn.rhs then
      (defn :: state.1, state.2.filter (· != defn.var) ++ Bil.freeVars defn.rhs)
    else
      state

/-- One backward pass over every block, with `protectedVars` live at the end of each block. -/
private def dcePass (protectedVars : List Bap.Var) (cfg : Cfg) : Cfg :=
  let outs := cfg.liveness.2
  { cfg with blocks := cfg.blocks.map fun blk =>
    let (defs, live) := dceDefs blk.defs
      ((Assoc.get blk.tid outs).getD [] ++ blk.jmps.flatMap Jmp.freeVars ++ protectedVars)
    { blk with
      defs := defs
      phis := blk.phis.filter fun phi => live.contains phi.var
    }
  }

private def dceAux (protectedVars : List Bap.Var) (cfg : Cfg) : Nat → Cfg
  | 0 => cfg
  | fuel + 1 =>
    let next := dcePass protectedVars cfg
    let before : List (Nat × Nat) := cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)
    let after : List (Nat × Nat) := next.blocks.map fun blk => (blk.defs.length, blk.phis.length)
    if before = after then cfg else dceAux protectedVars next fuel

/-- Removes dead code. `[]` means nothing is read after the CFG: callers must pass their outputs, as exact variables. -/
def eliminateDeadCode (cfg : Cfg) (protectedVars : List Bap.Var := []) : Cfg :=
  let count := cfg.blocks.foldl (fun count blk => count + blk.defs.length + blk.phis.length) 0
  dceAux protectedVars cfg (count + 1)

/-- Folds and removes dead code. `[]` means nothing is read on return: callers must pass their outputs, as exact variables. -/
def optimize (sub : Sub) (protectedVars : List Bap.Var := []) : Sub :=
  let cfg := propagateConstants (Cfg.fromSub sub)
  (eliminateDeadCode cfg protectedVars).intoSub sub

theorem eval_constant_toExp (constant : Constant) :
    Bil.evalExp [] constant.toExp = .ok (.bits (BitVec.ofNat constant.width constant.value)) := by
  rfl

end Bap.IR
