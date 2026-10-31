import Bap.IR.Liveness
import Bap.IR.Ssa

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

/-- Rounds of the analysis: a block goes back on the list when its constants change, and they only go. -/
private def propagateFuel (cfg : Cfg) : Nat :=
  let varCount := (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length
  (varCount + 2) * (cfg.blocks.length + 2) * (cfg.graph.edges.length + 2)

private def propagateFuelFast (cfg : Cfg) : Nat :=
  let varCount := (Bap.Graph.Fast.dedup (cfg.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars)).length
  (varCount + 2) * (cfg.blocks.length + 2) * (cfg.graph.edges.length + 2)

@[csimp] private theorem propagateFuel_eq_fast : @propagateFuel = @propagateFuelFast := by
  funext cfg
  simp only [propagateFuel, propagateFuelFast, Bap.Graph.Fast.dedup_eq]

/-- Rewrites each block once, from the fixpoint. If the analysis ran out of fuel only constants local
to each block are used. -/
def propagateConstants (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let exits := propagateAux cfg (propagateFuel cfg) [] [cfg.start]
  let solved := isSolved cfg exits
  { cfg with blocks := cfg.blocks.map fun blk =>
    (propagateBlock blk (if solved then entryEnv cfg exits blk.tid else [])).1
  }

section FastPropagation

open Bap.Graph.Fast (assocTable assocTable_get groupBy groupBy_getD dedup dedup_eq predecessors_eq successors_eq predecessorTable successorTable)

/-- `joinEnv`, with what `right` knows in a table. -/
private def joinEnvFast (left right : ConstEnv) : ConstEnv :=
  let table : Std.HashMap Bap.Var Constant := right.foldr (fun entry table => table.insert entry.1 entry.2) {}
  left.filter fun entry => table.get? entry.1 = some entry.2

private theorem constTable_get (right : ConstEnv) (key : Bap.Var) :
    (right.foldr (fun entry table => table.insert entry.1 entry.2) ({} : Std.HashMap Bap.Var Constant)).get? key = Assoc.get key right := by
  induction right with
  | nil => simp [Assoc.get]
  | cons head tail ih =>
    simp only [List.foldr_cons, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at ih ⊢
    obtain ⟨k, v⟩ := head
    by_cases hk : k = key
    · subst hk
      simp [Assoc.get]
    · have h1 : (k == key) = false := by simpa using hk
      have h2 : (key == k) = false := by simpa using fun e : key = k => hk e.symm
      simp only [h1, Bool.false_eq_true, ite_false, ih]
      simp [Assoc.get, List.lookup, h2]

@[csimp] private theorem joinEnv_eq_fast : @joinEnv = @joinEnvFast := by
  funext left right
  simp only [joinEnv, joinEnvFast, constTable_get]

private structure PropTables where
  blocks : Std.HashMap Tid Blk
  preds : Std.HashMap Tid (List Tid)
  succs : Std.HashMap Tid (List Tid)

private def propTablesOf (cfg : Cfg) : PropTables where
  blocks := assocTable (cfg.blocks.map fun blk => (blk.tid, blk))
  preds := predecessorTable cfg.graph
  succs := successorTable cfg.graph

private def entryEnvT (cfg : Cfg) (tables : PropTables) (exits : Std.HashMap Tid ConstEnv) (tid : Tid) : ConstEnv :=
  if tid = cfg.start then
    []
  else
    match (dedup (tables.preds.getD tid [])).filterMap exits.get? with
    | [] => []
    | first :: rest => rest.foldl joinEnv first

private def propagateAuxT (cfg : Cfg) (tables : PropTables) :
    Nat → Std.HashMap Tid ConstEnv → List Tid → Std.HashMap Tid ConstEnv
  | 0, exits, _ => exits
  | _fuel + 1, exits, [] => exits
  | fuel + 1, exits, tid :: work =>
    match tables.blocks.get? tid with
    | none => propagateAuxT cfg tables fuel exits work
    | some blk =>
      let env := (propagateBlock blk (entryEnvT cfg tables exits tid)).2
      if exits.get? tid = some env then
        propagateAuxT cfg tables fuel exits work
      else
        propagateAuxT cfg tables fuel (exits.insert tid env) (work ++ dedup (tables.succs.getD tid []))

private def propagateConstantsFast (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let tables := propTablesOf cfg
  let exits := propagateAuxT cfg tables (propagateFuel cfg) {} [cfg.start]
  let solved := cfg.blocks.all fun blk =>
    exits.get? blk.tid = some (propagateBlock blk (entryEnvT cfg tables exits blk.tid)).2
  { cfg with blocks := cfg.blocks.map fun blk =>
    (propagateBlock blk (if solved then entryEnvT cfg tables exits blk.tid else [])).1
  }

private abbrev SameExits (list : ExitEnvs) (table : Std.HashMap Tid ConstEnv) : Prop :=
  ∀ tid, Assoc.get tid list = table.get? tid

private theorem prop_block (cfg : Cfg) (tid : Tid) : (propTablesOf cfg).blocks.get? tid = cfg.block tid := by
  simp only [propTablesOf, assocTable_get, Cfg.block]
  have key : ∀ l : List Blk, Assoc.get tid (l.map fun blk => (blk.tid, blk)) = l.find? (fun blk => decide (blk.tid = tid)) := by
    intro l
    induction l with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.find?_cons, List.map_cons, Assoc.get, List.lookup_cons]
      by_cases hb : b.tid = tid
      · subst hb
        simp
      · have h1 : (tid == b.tid) = false := by simpa using fun e : tid = b.tid => hb e.symm
        simp only [hb, decide_false, h1]
        exact ih
  exact key cfg.blocks

private theorem entryEnv_eq (cfg : Cfg) {exits : ExitEnvs} {table : Std.HashMap Tid ConstEnv} (h : SameExits exits table) (tid : Tid) :
    entryEnv cfg exits tid = entryEnvT cfg (propTablesOf cfg) table tid := by
  simp only [entryEnv, entryEnvT]
  split
  · rfl
  · have hp : dedup ((propTablesOf cfg).preds.getD tid []) = cfg.predecessors tid := predecessors_eq cfg.graph tid
    rw [hp]
    have hf : (fun pred => Assoc.get pred exits) = table.get? := funext h
    rw [hf]

private theorem SameExits.put {exits : ExitEnvs} {table : Std.HashMap Tid ConstEnv} (h : SameExits exits table) (tid : Tid)
    (env : ConstEnv) : SameExits (Assoc.put tid env exits) (table.insert tid env) := by
  intro key
  have hg : Assoc.get key (Assoc.put tid env exits) = if key = tid then some env else Assoc.get key exits := by
    by_cases hk : key = tid
    · subst hk
      simp
    · simp only [hk, ite_false, Assoc.get, Assoc.put, List.lookup_cons]
      have hb : (key == tid) = false := by simpa using hk
      simp only [hb]
      have key2 : ∀ l : ExitEnvs, List.lookup key (l.filter fun e => e.1 != tid) = List.lookup key l := by
        intro l
        induction l with
        | nil => rfl
        | cons e es ih =>
          obtain ⟨a, b⟩ := e
          by_cases ha : a = tid
          · subst ha
            simp [List.lookup_cons, hb, ih]
          · have hk' : (a != tid) = true := by simpa using ha
            simp only [List.filter_cons, hk', ↓reduceIte, List.lookup_cons, ih]
      exact key2 exits
  rw [hg, h key]
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hk : key = tid
  · subst hk
    simp
  · have hb : (tid == key) = false := by simpa using fun e : tid = key => hk e.symm
    simp [hk, hb]

private theorem propagateAux_same (cfg : Cfg) (fuel : Nat) (work : List Tid) {exits : ExitEnvs} {table : Std.HashMap Tid ConstEnv}
    (h : SameExits exits table) : SameExits (propagateAux cfg fuel exits work) (propagateAuxT cfg (propTablesOf cfg) fuel table work) := by
  induction fuel generalizing exits table work with
  | zero => exact h
  | succ fuel ih =>
    cases work with
    | nil => exact h
    | cons tid rest =>
      simp only [propagateAux, propagateAuxT, prop_block]
      cases hb : cfg.block tid with
      | none => exact ih _ h
      | some blk =>
        simp only
        rw [entryEnv_eq cfg h, h tid]
        split
        · exact ih _ h
        · have hs : dedup ((propTablesOf cfg).succs.getD tid []) = cfg.successors tid := successors_eq cfg.graph tid
          rw [hs]
          exact ih _ (h.put _ _)

@[csimp] private theorem propagateConstants_eq_fast : @propagateConstants = @propagateConstantsFast := by
  funext cfg
  have hempty : SameExits [] ({} : Std.HashMap Tid ConstEnv) := by
    intro tid
    simp [Assoc.get]
  have hsame := propagateAux_same cfg.prune (propagateFuel cfg.prune) [cfg.prune.start] hempty
  have hentry := entryEnv_eq cfg.prune hsame
  simp only [propagateConstants, propagateConstantsFast, isSolved, hentry, hsame _]

end FastPropagation

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

section FastDce

/-- `dceDefs`, with what is live in a set. -/
private def dceDefsFast (defs : List Def) (live : Std.HashSet Bap.Var) : List Def × Std.HashSet Bap.Var :=
  defs.foldr (init := ([], live)) fun defn state =>
    if state.2.contains defn.var || hasSideEffect defn.rhs then
      (defn :: state.1, (state.2.erase defn.var).insertMany (Bil.freeVars defn.rhs))
    else
      state

private theorem dceDefs_same (defs : List Def) {live : List Bap.Var} {set : Std.HashSet Bap.Var}
    (h : ∀ x, x ∈ live ↔ set.contains x = true) :
    (dceDefs defs live).1 = (dceDefsFast defs set).1 ∧
      ∀ x, x ∈ (dceDefs defs live).2 ↔ (dceDefsFast defs set).2.contains x = true := by
  induction defs with
  | nil => exact ⟨rfl, h⟩
  | cons d ds ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [dceDefs, dceDefsFast, List.foldr_cons] at h1 h2 ⊢
    generalize ds.foldr _ (([] : List Def), live) = l at h1 h2 ⊢
    generalize ds.foldr _ (([] : List Def), set) = t at h1 h2 ⊢
    have hc : l.2.contains d.var = t.2.contains d.var := by
      rw [Bool.eq_iff_iff]
      simp only [List.contains_eq_mem, decide_eq_true_eq]
      exact h2 d.var
    rw [hc]
    split
    · refine ⟨by simp [h1], fun x => ?_⟩
      simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq, Std.HashSet.contains_insertMany_list,
        Std.HashSet.contains_erase, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
        List.contains_eq_mem, decide_eq_true_eq, h2 x]
      grind
    · exact ⟨h1, h2⟩

private def dcePassFast (protectedVars : List Bap.Var) (cfg : Cfg) : Cfg :=
  let outs := Bap.Graph.Fast.assocTable cfg.liveness.2
  { cfg with blocks := cfg.blocks.map fun blk =>
    let (defs, live) := dceDefsFast blk.defs (Std.HashSet.ofList
      ((outs.get? blk.tid).getD [] ++ blk.jmps.flatMap Jmp.freeVars ++ protectedVars))
    { blk with
      defs := defs
      phis := blk.phis.filter fun phi => live.contains phi.var
    }
  }

@[csimp] private theorem dcePass_eq_fast : @dcePass = @dcePassFast := by
  funext ps cfg
  simp only [dcePass, dcePassFast, Bap.Graph.Fast.assocTable_get]
  congr 1
  apply List.map_congr_left
  intro blk _
  obtain ⟨h1, h2⟩ := dceDefs_same blk.defs (live := (Assoc.get blk.tid cfg.liveness.2).getD [] ++ blk.jmps.flatMap Jmp.freeVars ++ ps)
    (set := Std.HashSet.ofList ((Assoc.get blk.tid cfg.liveness.2).getD [] ++ blk.jmps.flatMap Jmp.freeVars ++ ps))
    (fun x => by simp [Std.HashSet.contains_ofList])
  simp only [h1]
  congr 1
  apply List.filter_congr
  intro phi _
  rw [Bool.eq_iff_iff, List.contains_eq_mem, decide_eq_true_eq]
  exact h2 phi.var

end FastDce

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

/-- The exact variables protecting `protectedVars` means in this CFG. A versioned entry is that one
variable. An unversioned entry names a program variable, which in SSA form lives in all its versions
(which of them holds its value depends on the exit taken), so it also protects every version assigned. -/
def Cfg.protectedNames (cfg : Cfg) (protectedVars : List Bap.Var) : List Bap.Var :=
  match protectedVars with
  | [] => []
  | _ =>
    protectedVars ++ (cfg.blocks.flatMap Blk.definedVars).filter fun var => protectedVars.contains var.base

/-- Folds and removes dead code. `[]` means nothing is read on return: callers must pass their
outputs, and an unversioned output also covers its SSA versions (see `Cfg.protectedNames`). -/
def optimize (sub : Sub) (protectedVars : List Bap.Var := []) : Sub :=
  let cfg := propagateConstants (Cfg.fromSub sub)
  (eliminateDeadCode cfg (cfg.protectedNames protectedVars)).intoSub sub

/-- Pruned SSA: `toSsa` without the phis nothing reads, and so without the definitions only they read.
`toSsa` places a phi wherever the iterated dominance frontier says, whether the variable is live or not:
liveness tells which of them are dead, once they are all there. `[]` means nothing is read on return. -/
def toSsaPruned (sub : Sub) (protectedVars : List Bap.Var := []) : Sub :=
  let ssa := Cfg.fromSub (toSsa sub)
  (eliminateDeadCode ssa (ssa.protectedNames protectedVars)).intoSub (toSsa sub)

theorem eval_constant_toExp (constant : Constant) :
    Bil.evalExp [] constant.toExp = .ok (.bits (BitVec.ofNat constant.width constant.value)) := by
  rfl

end Bap.IR
