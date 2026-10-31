import Bap.IR.Liveness
import Bap.IR.LiveSets
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

/-! ### Passes that only look at what the last one changed

A pass removes little after the first few, and solves liveness for all of it again. Whether a variable is live only depends on
the blocks that mention it, so only the variables a removed statement mentions need their rows solved again, and only the
blocks that assign those can lose anything more. The passes are the same as those of `dceAux`. -/

section Incremental

open Bap.IR.LiveSets Bap.Proofs.IR

local macro "blockIn" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockIn)

/-- What `dcePass` does to a block, given what is live at its end. -/
private def dceBlock (live : List Bap.Var) (blk : Blk) : Blk :=
  { blk with
    defs := (dceDefs blk.defs live).1
    phis := blk.phis.filter fun phi => (dceDefs blk.defs live).2.contains phi.var }

/-- What is live at the end of a block for `dcePass`. -/
private def liveAtEnd (protectedVars : List Bap.Var) (cfg : Cfg) (blk : Blk) : List Bap.Var :=
  liveOut cfg blk.tid ++ blk.jmps.flatMap Jmp.freeVars ++ protectedVars

private theorem dcePass_eq_map (protectedVars : List Bap.Var) (cfg : Cfg) :
    dcePass protectedVars cfg =
      { cfg with blocks := cfg.blocks.map fun blk => dceBlock (liveAtEnd protectedVars cfg blk) blk } := rfl

/-- `dceDefs` that also says what the definitions it removed mention. -/
private def dceDefsDropped (defs : List Def) (live : Std.HashSet Bap.Var) :
    List Def × Std.HashSet Bap.Var × List Bap.Var :=
  defs.foldr (init := ([], live, [])) fun defn state =>
    if state.2.1.contains defn.var || hasSideEffect defn.rhs then
      (defn :: state.1, (state.2.1.erase defn.var).insertMany (Bil.freeVars defn.rhs), state.2.2)
    else
      (state.1, state.2.1, defn.var :: Bil.freeVars defn.rhs ++ state.2.2)

private theorem dceDefs_cons (d : Def) (rest : List Def) (live : List Bap.Var) :
    dceDefs (d :: rest) live =
      if (dceDefs rest live).2.contains d.var || hasSideEffect d.rhs then
        (d :: (dceDefs rest live).1, (dceDefs rest live).2.filter (· != d.var) ++ Bil.freeVars d.rhs)
      else dceDefs rest live := rfl

private theorem dceDefsDropped_cons (d : Def) (rest : List Def) (live : Std.HashSet Bap.Var) :
    dceDefsDropped (d :: rest) live =
      if (dceDefsDropped rest live).2.1.contains d.var || hasSideEffect d.rhs then
        (d :: (dceDefsDropped rest live).1, ((dceDefsDropped rest live).2.1.erase d.var).insertMany (Bil.freeVars d.rhs),
          (dceDefsDropped rest live).2.2)
      else
        ((dceDefsDropped rest live).1, (dceDefsDropped rest live).2.1,
          d.var :: Bil.freeVars d.rhs ++ (dceDefsDropped rest live).2.2) := rfl

/-- Both agree as far as `Q` goes, if what is live at the end agrees and they assign what is in `Q`. -/
private theorem dceDefsDropped_agree (Q : Bap.Var → Prop) (defs : List Def) {live : List Bap.Var} {set : Std.HashSet Bap.Var}
    (h : ∀ x, Q x → (x ∈ live ↔ set.contains x = true)) (hd : ∀ d ∈ defs, Q d.var) :
    (dceDefs defs live).1 = (dceDefsDropped defs set).1 ∧
      ∀ x, Q x → (x ∈ (dceDefs defs live).2 ↔ (dceDefsDropped defs set).2.1.contains x = true) := by
  induction defs with
  | nil => exact ⟨rfl, h⟩
  | cons d ds ih =>
    obtain ⟨h1, h2⟩ := ih fun e he => hd e (List.mem_cons_of_mem _ he)
    rw [dceDefs_cons, dceDefsDropped_cons]
    have hc : (dceDefs ds live).2.contains d.var = (dceDefsDropped ds set).2.1.contains d.var := by
      rw [Bool.eq_iff_iff]
      simp only [List.contains_eq_mem, decide_eq_true_eq]
      exact h2 d.var (hd d List.mem_cons_self)
    rw [hc]
    split
    · refine ⟨by simp [h1], fun x hx => ?_⟩
      have := h2 x hx
      simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq, Std.HashSet.contains_insertMany_list,
        Std.HashSet.contains_erase, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
        List.contains_eq_mem, decide_eq_true_eq, this]
      grind
    · exact ⟨h1, h2⟩

/-- A second run keeps what the first kept, if what is live at the end agrees on what is kept. -/
private theorem dceDefs_stable (Q : Bap.Var → Prop) (defs : List Def) {live other : List Bap.Var}
    (h : ∀ x, Q x → (x ∈ live ↔ x ∈ other)) (hd : ∀ d ∈ (dceDefs defs live).1, Q d.var) :
    (dceDefs (dceDefs defs live).1 other).1 = (dceDefs defs live).1 ∧
      ∀ x, Q x → (x ∈ (dceDefs (dceDefs defs live).1 other).2 ↔ x ∈ (dceDefs defs live).2) := by
  induction defs with
  | nil => exact ⟨rfl, fun x hx => (h x hx).symm⟩
  | cons d ds ih =>
    rw [dceDefs_cons] at hd ⊢
    split
    · rename_i hc
      have hsub : ∀ e ∈ (dceDefs ds live).1, Q e.var := by
        intro e he
        rw [ite_eq_left hc] at hd
        exact hd e (List.mem_cons_of_mem _ he)
      have hdq : Q d.var := by
        rw [ite_eq_left hc] at hd
        exact hd d List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih hsub
      rw [dceDefs_cons, h1]
      have hc' : ((dceDefs (dceDefs ds live).1 other).2.contains d.var || hasSideEffect d.rhs) = true := by
        have hiff := h2 d.var hdq
        simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hc ⊢
        rcases hc with hc | hc
        · exact Or.inl (hiff.2 hc)
        · exact Or.inr hc
      rw [ite_eq_left hc']
      refine ⟨rfl, fun x hx => ?_⟩
      have := h2 x hx
      simp only [List.mem_append, List.mem_filter, this]
    · rename_i hc
      rw [ite_eq_right hc] at hd
      exact ih hd

/-- A block doesn't change again, if what is live at its end stays the same on what is left of it. -/
private theorem dceBlock_stable (blk : Blk) {live other : List Bap.Var}
    (h : ∀ x, x ∈ assigned (dceBlock live blk) → (x ∈ live ↔ x ∈ other)) :
    dceBlock other (dceBlock live blk) = dceBlock live blk := by
  have hd : ∀ d ∈ (dceDefs blk.defs live).1, d.var ∈ assigned (dceBlock live blk) := by
    intro d hm
    simp only [assigned, dceBlock, List.mem_append, List.mem_map]
    exact Or.inl ⟨d, hm, rfl⟩
  obtain ⟨h1, h2⟩ := dceDefs_stable (fun x => x ∈ assigned (dceBlock live blk)) blk.defs h hd
  simp only [dceBlock, h1]
  congr 1
  rw [List.filter_filter]
  apply List.filter_congr
  intro phi hphi
  by_cases hc : phi.var ∈ (dceDefs blk.defs live).2
  · have hp : phi.var ∈ assigned (dceBlock live blk) := by
      simp only [assigned, dceBlock, List.mem_append, List.mem_map, List.mem_filter]
      exact Or.inr ⟨phi, ⟨hphi, by simpa using hc⟩, rfl⟩
    simp [hc, (h2 phi.var hp).2 hc]
  · simp [hc]

/-- What a removed phi mentions. -/
private def phiMentions (phi : Phi) : List Bap.Var :=
  phi.var :: phi.values.flatMap fun input => Bil.freeVars input.2

/-- `dceBlock` from a set of what is live at the end of a block. Also says what it removes mentions. -/
private def scanWith (live : Std.HashSet Bap.Var) (blk : Blk) : Blk × List Bap.Var :=
  let result := dceDefsDropped blk.defs live
  ({ blk with
      defs := result.1
      phis := blk.phis.filter fun phi => result.2.1.contains phi.var },
    result.2.2 ++ (blk.phis.filter fun phi => !result.2.1.contains phi.var).flatMap phiMentions)

/-- `dceBlock` from which of the variables the block assigns are live at its end. -/
private def scanBlock (isLiveAtEnd : Bap.Var → Bool) (blk : Blk) : Blk × List Bap.Var :=
  scanWith (Std.HashSet.ofList ((assigned blk).filter isLiveAtEnd ++ blk.jmps.flatMap Jmp.freeVars)) blk

private theorem scanBlock_fst (isLiveAtEnd : Bap.Var → Bool) (blk : Blk) (live : List Bap.Var)
    (h : ∀ x, x ∈ assigned blk → (x ∈ live ↔ isLiveAtEnd x = true ∨ x ∈ blk.jmps.flatMap Jmp.freeVars)) :
    (scanBlock isLiveAtEnd blk).1 = dceBlock live blk := by
  let set : Std.HashSet Bap.Var := Std.HashSet.ofList ((assigned blk).filter isLiveAtEnd ++ blk.jmps.flatMap Jmp.freeVars)
  have hset : ∀ x, x ∈ assigned blk → (x ∈ live ↔ set.contains x = true) := by
    intro x hx
    simp only [set, Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq, List.mem_append, List.mem_filter]
    rw [h x hx]
    grind
  obtain ⟨h1, h2⟩ := dceDefsDropped_agree (fun x => x ∈ assigned blk) blk.defs hset (fun d hd => by
    simp only [assigned, List.mem_append, List.mem_map]
    exact Or.inl ⟨d, hd, rfl⟩)
  show (scanWith set blk).1 = _
  simp only [scanWith, dceBlock, ← h1]
  congr 1
  apply List.filter_congr
  intro phi hphi
  have hp : phi.var ∈ assigned blk := by
    simp only [assigned, List.mem_append, List.mem_map]
    exact Or.inr ⟨phi, hphi, rfl⟩
  rw [Bool.eq_iff_iff]
  simp only [List.contains_eq_mem, decide_eq_true_eq]
  exact (h2 phi.var hp).symm

private theorem dropped_agree (live : Std.HashSet Bap.Var) (x : Bap.Var) (defs : List Def)
    (hx : x ∉ (dceDefsDropped defs live).2.2) :
    (Exposed defs x ↔ Exposed (dceDefsDropped defs live).1 x) ∧
      ((∀ d ∈ defs, d.var ≠ x) ↔ ∀ d ∈ (dceDefsDropped defs live).1, d.var ≠ x) := by
  induction defs with
  | nil => exact ⟨Iff.rfl, Iff.rfl⟩
  | cons d ds ih =>
    rw [dceDefsDropped_cons] at hx ⊢
    split at hx
    · rename_i hc
      rw [ite_eq_left hc]
      obtain ⟨h1, h2⟩ := ih hx
      constructor
      · simp only [Exposed, h1]
      · simp only [List.mem_cons, forall_eq_or_imp, h2]
    · rename_i hc
      rw [ite_eq_right hc]
      simp only [List.cons_append, List.mem_cons, List.mem_append, not_or] at hx
      obtain ⟨h1, h2⟩ := ih hx.2.2
      constructor
      · simp only [Exposed]
        rw [← h1]
        constructor
        · rintro (h | ⟨_, h⟩)
          · exact (hx.2.1 h).elim
          · exact h
        · exact fun h => Or.inr ⟨hx.1, h⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        rw [← h2]
        exact ⟨fun h => h.2, fun h => ⟨fun e => hx.1 e.symm, h⟩⟩

/-- What is removed from a block that doesn't mention `x` makes no difference to `x`. -/
private theorem scanWith_agree (live : Std.HashSet Bap.Var) (blk : Blk) (x : Bap.Var) (hx : x ∉ (scanWith live blk).2) :
    Agree x blk (scanWith live blk).1 := by
  simp only [scanWith, List.mem_append, not_or] at hx
  obtain ⟨he, hk⟩ := dropped_agree live x blk.defs hx.1
  have hlost : ∀ phi ∈ blk.phis, (dceDefsDropped blk.defs live).2.1.contains phi.var = false → x ∉ phiMentions phi := by
    intro phi hphi hc hm
    exact hx.2 (List.mem_flatMap.2 ⟨phi, List.mem_filter.2 ⟨hphi, by simp [hc]⟩, hm⟩)
  have hphis : (∀ phi ∈ blk.phis, phi.var ≠ x) ↔
      ∀ phi ∈ blk.phis.filter (fun phi => (dceDefsDropped blk.defs live).2.1.contains phi.var), phi.var ≠ x := by
    simp only [List.mem_filter, and_imp]
    constructor
    · exact fun h phi hphi _ => h phi hphi
    · intro h phi hphi
      by_cases hc : (dceDefsDropped blk.defs live).2.1.contains phi.var = true
      · exact h phi hphi hc
      · intro e
        exact hlost phi hphi (by simpa using hc) (by simp [phiMentions, e])
  constructor
  · simp only [scanWith, mem_blockIn, ← he, ← hk, ← hphis, List.not_mem_nil, or_false]
  · simp only [scanWith, Killed]
    have h1 : (∃ d ∈ blk.defs, d.var = x) ↔ ∃ d ∈ (dceDefsDropped blk.defs live).1, d.var = x := by
      have := not_congr hk
      simpa using this
    have h2 : (∃ phi ∈ blk.phis, phi.var = x) ↔
        ∃ phi ∈ blk.phis.filter (fun phi => (dceDefsDropped blk.defs live).2.1.contains phi.var), phi.var = x := by
      have := not_congr hphis
      simpa [and_assoc] using this
    rw [h1, h2]
  · exact hphis
  · intro source
    simp only [scanWith, mem_phiReads, List.mem_filter]
    constructor
    · rintro ⟨phi, hphi, value, hg, hv⟩
      refine ⟨phi, ⟨hphi, ?_⟩, value, hg, hv⟩
      by_cases hc : (dceDefsDropped blk.defs live).2.1.contains phi.var = true
      · exact hc
      · refine (hlost phi hphi (by simpa using hc) ?_).elim
        exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(source, value), get_mem_env' hg, hv⟩)
    · rintro ⟨phi, ⟨hphi, _⟩, value, hg, hv⟩
      exact ⟨phi, hphi, value, hg, hv⟩

private theorem Agree.refl (x : Bap.Var) (blk : Blk) : Agree x blk blk :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun _ => Iff.rfl⟩

private theorem dceDefs_sublist (defs : List Def) (live : List Bap.Var) : (dceDefs defs live).1.Sublist defs := by
  induction defs with
  | nil => exact List.Sublist.refl _
  | cons d ds ih =>
    rw [dceDefs_cons]
    split
    · exact ih.cons_cons d
    · exact ih.cons d

private theorem assigned_dceBlock {live : List Bap.Var} {blk : Blk} {x : Bap.Var}
    (h : x ∈ assigned (dceBlock live blk)) : x ∈ assigned blk := by
  have hd := dceDefs_sublist blk.defs live
  simp only [assigned, dceBlock, List.mem_append, List.mem_map, List.mem_filter] at h ⊢
  rcases h with ⟨d, hm, e⟩ | ⟨phi, ⟨hp, _⟩, e⟩
  · exact Or.inl ⟨d, hd.subset hm, e⟩
  · exact Or.inr ⟨phi, hp, e⟩

private theorem vocabulary_dceBlock {live : List Bap.Var} {blk : Blk} {x : Bap.Var}
    (h : x ∈ vocabulary (dceBlock live blk)) : x ∈ vocabulary blk := by
  have hd := dceDefs_sublist blk.defs live
  simp only [vocabulary, dceBlock, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter] at h ⊢
  rcases h with ((⟨phi, ⟨hp, _⟩, e⟩ | ⟨phi, ⟨hp, _⟩, hv⟩) | ⟨d, hm, hv⟩) | ⟨j, hj, hv⟩
  · exact Or.inl (Or.inl (Or.inl ⟨phi, hp, e⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨phi, hp, hv⟩))
  · exact Or.inl (Or.inr ⟨d, hd.subset hm, hv⟩)
  · exact Or.inr ⟨j, hj, hv⟩

/-- What doesn't change between two passes, and what is known of the rows and of what can still change. -/
private structure Facts (protectedVars : List Bap.Var) (preds : Preds) (reach : Row)
    (successors : Std.HashMap Tid (List Tid)) (sites definers : VarTable) (cfg : Cfg) (affected : List Bap.Var)
    (dirty : Std.HashSet Tid) (live : Live) : Prop where
  pred : ∀ t p, p ∈ preds.getD t [] ↔ p ∈ cfg.reachable ∧ t ∈ cfg.successors p
  reach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable
  successors : ∀ t, Bap.Graph.Fast.dedup (successors.getD t []) = cfg.successors t
  sites : SitesOf cfg sites
  definers : DefinersOf cfg definers
  rows : ∀ x, x ∉ affected → RowOf cfg live x
  stable : ∀ blk ∈ cfg.blocks, dirty.contains blk.tid = false →
    dceBlock (liveAtEnd protectedVars cfg blk) blk = blk

private def blockTable (cfg : Cfg) : Blocks := Bap.Graph.Fast.assocTable (cfg.blocks.map fun blk => (blk.tid, blk))

private theorem blockTable_get (cfg : Cfg) (tid : Tid) : (blockTable cfg).get? tid = cfg.block tid := by
  simp only [blockTable, Bap.Graph.Fast.assocTable_get, Cfg.block]
  generalize cfg.blocks = l
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

private theorem block_exists_of_mem {cfg : Cfg} {blk : Blk} (hblk : blk ∈ cfg.blocks) : ∃ b, cfg.block blk.tid = some b := by
  cases hg : cfg.block blk.tid with
  | some b => exact ⟨b, rfl⟩
  | none =>
    simp only [Cfg.block, List.find?_eq_none] at hg
    have := hg blk hblk
    simp at this

/-- Which of the variables a block assigns are live at its end. -/
private def endQuery (protectedSet : Std.HashSet Bap.Var) (reach : Row) (blocks : Blocks)
    (successors : Std.HashMap Tid (List Tid)) (live : Live) (t : Tid) : Bap.Var → Bool :=
  let edges := if reach.contains t then edgesOf blocks successors t else []
  fun x => protectedSet.contains x || liveOver live edges x

private theorem endQuery_iff {protectedVars : List Bap.Var} {protectedSet : Std.HashSet Bap.Var}
    (hset : ∀ x, protectedSet.contains x = true ↔ x ∈ protectedVars) {cfg : Cfg} {reach : Row} {live : Live}
    {successors : Std.HashMap Tid (List Tid)} (hreach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable)
    (hsucc : ∀ t, Bap.Graph.Fast.dedup (successors.getD t []) = cfg.successors t) (hrows : ∀ x, RowOf cfg live x)
    {blk : Blk} (hblk : blk ∈ cfg.blocks) (x : Bap.Var) :
    x ∈ liveAtEnd protectedVars cfg blk ↔
      endQuery protectedSet reach (blockTable cfg) successors live blk.tid x = true ∨ x ∈ blk.jmps.flatMap Jmp.freeVars := by
  have hout : x ∈ liveOut cfg blk.tid ↔
      liveOver live (if reach.contains blk.tid then edgesOf (blockTable cfg) successors blk.tid else []) x = true := by
    by_cases hr : blk.tid ∈ cfg.reachable
    · rw [ite_eq_left ((hreach _).2 hr)]
      obtain ⟨b, hb⟩ := block_exists_of_mem hblk
      rw [mem_liveOut hr hb, liveOver_iff (blockTable_get cfg) hsucc (hrows x)]
    · have hnr : ¬ reach.contains blk.tid = true := fun h => hr ((hreach _).1 h)
      rw [ite_eq_right hnr, liveOut_unreachable hr]
      simp [liveOver]
  simp only [liveAtEnd, endQuery, List.mem_append, Bool.or_eq_true, hset, ← hout]
  grind

private theorem stable_or_scan {protectedVars : List Bap.Var} {protectedSet : Std.HashSet Bap.Var}
    (hset : ∀ x, protectedSet.contains x = true ↔ x ∈ protectedVars) {preds : Preds} {reach : Row}
    {successors : Std.HashMap Tid (List Tid)} {sites definers : VarTable} {cfg : Cfg} {affected : List Bap.Var}
    {dirty : Std.HashSet Tid} {live live' : Live} (h : Facts protectedVars preds reach successors sites definers cfg affected dirty live)
    (hrows : ∀ x, RowOf cfg live' x) {blk : Blk} (hblk : blk ∈ cfg.blocks) :
    (if dirty.contains blk.tid then
        scanBlock (endQuery protectedSet reach (blockTable cfg) successors live' blk.tid) blk
      else (blk, [])).1 = dceBlock (liveAtEnd protectedVars cfg blk) blk := by
  by_cases hd : dirty.contains blk.tid = true
  · rw [ite_eq_left hd]
    exact scanBlock_fst _ _ _ fun x _ => endQuery_iff hset h.reach h.successors hrows hblk x
  · rw [ite_eq_right hd]
    exact (h.stable blk hblk (by simpa using hd)).symm

/-- The rows of the next pass, for what the last one left alone. -/
private theorem agree_next (cfg : Cfg) (g : Blk → Blk) (x : Bap.Var) (htid : ∀ blk, (g blk).tid = blk.tid)
    (hagree : ∀ blk ∈ cfg.blocks, Agree x blk (g blk)) :
    let next : Cfg := { cfg with blocks := cfg.blocks.map g }
    (∀ t blk, cfg.block t = some blk → ∃ b, next.block t = some b ∧ Agree x blk b) ∧
      ∀ t blk, next.block t = some blk → ∃ b, cfg.block t = some b ∧ Agree x b blk := by
  intro next
  have hblock : ∀ t, next.block t = (cfg.block t).map g := by
    intro t
    simp only [next, Cfg.block, List.find?_map]
    congr 1
    congr 1
    funext b
    simp [htid]
  constructor
  · intro t blk hb
    exact ⟨g blk, by rw [hblock, hb]; rfl, hagree blk (block_some hb).1⟩
  · intro t blk hb
    rw [hblock] at hb
    cases hc : cfg.block t with
    | none => simp [hc] at hb
    | some b =>
      rw [hc] at hb
      cases hb
      exact ⟨b, rfl, hagree b (block_some hc).1⟩

theorem liveOut_iff_of_agree (cfg other : Cfg) (x : Bap.Var) (hreach : other.reachable = cfg.reachable)
    (hsucc : ∀ t, other.successors t = cfg.successors t)
    (hagree : ∀ t blk, cfg.block t = some blk → ∃ b, other.block t = some b ∧ Agree x blk b)
    (hagree' : ∀ t blk, other.block t = some blk → ∃ b, cfg.block t = some b ∧ Agree x b blk) (t : Tid) {blk : Blk}
    (hb : cfg.block t = some blk) : x ∈ liveOut cfg t ↔ x ∈ liveOut other t := by
  by_cases ht : t ∈ cfg.reachable
  · obtain ⟨b, hb', _⟩ := hagree t blk hb
    rw [mem_liveOut ht hb, mem_liveOut (hreach ▸ ht) hb', hsucc]
    have hlive := live_iff_of_agree cfg other x hreach hsucc hagree hagree'
    constructor
    · rintro ⟨s, hs, bs, hbs, hc⟩
      obtain ⟨bs', hbs', ha⟩ := hagree s bs hbs
      refine ⟨s, hs, bs', hbs', ?_⟩
      rcases hc with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨(hlive s).1 h1, ha.phi.1 h2⟩
      · exact Or.inr ((ha.reads t).1 h1)
    · rintro ⟨s, hs, bs, hbs, hc⟩
      obtain ⟨bs', hbs', ha⟩ := hagree' s bs hbs
      refine ⟨s, hs, bs', hbs', ?_⟩
      rcases hc with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨(hlive s).2 h1, ha.phi.2 h2⟩
      · exact Or.inr ((ha.reads t).2 h1)
  · rw [liveOut_unreachable ht, liveOut_unreachable (hreach ▸ ht : t ∉ other.reachable)]

/-- `dceAux`, solving again only what the last pass changed. The one call to `dceAux` is to its list code, as this is
compiled before the `csimp` theorem, for the case of the fuel of a solver running out. -/
private def dceLoop (protectedVars : List Bap.Var) (protectedSet : Std.HashSet Bap.Var) (preds : Preds) (reach : Row)
    (successors : Std.HashMap Tid (List Tid)) (sites definers : VarTable) : Nat → Cfg → List Bap.Var → Std.HashSet Tid → Live → Cfg
  | 0, cfg, _, _, _ => cfg
  | fuel + 1, cfg, affected, dirty, live =>
    let blocks := blockTable cfg
    match refresh blocks preds reach sites cfg.blocks.length live affected with
    | none => dceAux protectedVars cfg (fuel + 1)
    | some live =>
      let scanned := cfg.blocks.map fun blk =>
        if dirty.contains blk.tid then
          scanBlock (endQuery protectedSet reach blocks successors live blk.tid) blk
        else (blk, [])
      let next : Cfg := { cfg with blocks := scanned.map Prod.fst }
      let before : List (Nat × Nat) := cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)
      let after : List (Nat × Nat) := next.blocks.map fun blk => (blk.defs.length, blk.phis.length)
      if before = after then
        cfg
      else
        let affected := Bap.Graph.Fast.dedup (scanned.flatMap Prod.snd)
        dceLoop protectedVars protectedSet preds reach successors sites definers fuel next affected
          (Std.HashSet.ofList (affected.flatMap fun x => definers.getD x [])) live

/-- What the next pass needs to know, from a pass. -/
private theorem facts_next {protectedVars : List Bap.Var} {protectedSet : Std.HashSet Bap.Var}
    (hset : ∀ x, protectedSet.contains x = true ↔ x ∈ protectedVars) {preds : Preds} {reach : Row}
    {successors : Std.HashMap Tid (List Tid)} {sites definers : VarTable} {cfg : Cfg} {affected : List Bap.Var}
    {dirty : Std.HashSet Tid} {live live' : Live} (h : Facts protectedVars preds reach successors sites definers cfg affected dirty live)
    (hrows : ∀ x, RowOf cfg live' x) :
    let scanned := cfg.blocks.map fun blk =>
      if dirty.contains blk.tid then
        scanBlock (endQuery protectedSet reach (blockTable cfg) successors live' blk.tid) blk
      else (blk, [])
    let dropped := Bap.Graph.Fast.dedup (scanned.flatMap Prod.snd)
    Facts protectedVars preds reach successors sites definers (dcePass protectedVars cfg) dropped
      (Std.HashSet.ofList (dropped.flatMap fun x => definers.getD x [])) live' := by
  intro scanned dropped
  let g : Blk → Blk := fun blk => dceBlock (liveAtEnd protectedVars cfg blk) blk
  have hnext : dcePass protectedVars cfg = { cfg with blocks := cfg.blocks.map g } := dcePass_eq_map _ _
  have htid : ∀ blk, (g blk).tid = blk.tid := fun _ => rfl
  have hreach : (dcePass protectedVars cfg).reachable = cfg.reachable := rfl
  have hsucc : ∀ t, (dcePass protectedVars cfg).successors t = cfg.successors t := fun _ => rfl
  have hagree : ∀ x, x ∉ dropped → ∀ blk ∈ cfg.blocks, Agree x blk (g blk) := by
    intro x hx blk hblk
    have hnm : x ∉ (if dirty.contains blk.tid then
        scanBlock (endQuery protectedSet reach (blockTable cfg) successors live' blk.tid) blk
      else (blk, [])).2 := by
      intro hm
      apply hx
      show x ∈ Bap.Graph.Fast.dedup _
      rw [Bap.Graph.Fast.dedup_eq, List.mem_eraseDups, List.mem_flatMap]
      exact ⟨_, List.mem_map.2 ⟨blk, hblk, rfl⟩, hm⟩
    have hfst := stable_or_scan hset h hrows hblk
    by_cases hd : dirty.contains blk.tid = true
    · rw [ite_eq_left hd] at hnm hfst
      have ha := scanWith_agree _ blk x hnm
      show Agree x blk (dceBlock _ blk)
      rw [← hfst]
      exact ha
    · rw [ite_eq_right hd] at hfst
      show Agree x blk (dceBlock _ blk)
      rw [← hfst]
      exact Agree.refl x blk
  have hboth : ∀ x, x ∉ dropped →
      (∀ t blk, cfg.block t = some blk → ∃ b, (dcePass protectedVars cfg).block t = some b ∧ Agree x blk b) ∧
        ∀ t blk, (dcePass protectedVars cfg).block t = some blk → ∃ b, cfg.block t = some b ∧ Agree x b blk := by
    intro x hx
    rw [hnext]
    exact agree_next cfg g x htid (hagree x hx)
  refine ⟨h.pred, h.reach, h.successors, ?_, ?_, ?_, ?_⟩
  · intro blk hb y hy
    rw [hnext] at hb
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hb
    exact h.sites b hbm y (vocabulary_dceBlock hy)
  · intro blk hb y hy
    rw [hnext] at hb
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hb
    exact h.definers b hbm y (assigned_dceBlock hy)
  · intro x hx t
    obtain ⟨h1, h2⟩ := hboth x hx
    rw [hrows x t]
    exact live_iff_of_agree cfg _ x hreach hsucc h1 h2 t
  · intro blk hb hclean
    rw [hnext] at hb
    obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hb
    show dceBlock _ (dceBlock _ b) = dceBlock _ b
    apply dceBlock_stable
    intro y hy
    have hnd : y ∉ dropped := by
      intro hm
      have hc : (Std.HashSet.ofList (dropped.flatMap fun x => definers.getD x [])).contains b.tid = true := by
        simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq, List.mem_flatMap]
        exact ⟨y, hm, h.definers b hbm y (assigned_dceBlock hy)⟩
      have hclean' : (Std.HashSet.ofList (dropped.flatMap fun x => definers.getD x [])).contains b.tid = false := hclean
      rw [hc] at hclean'
      cases hclean'
    obtain ⟨h1, h2⟩ := hboth y hnd
    obtain ⟨c, hc⟩ := block_exists_of_mem hbm
    have hout := liveOut_iff_of_agree cfg _ y hreach hsucc h1 h2 b.tid hc
    simp only [liveAtEnd, List.mem_append]
    have hj : (g b).jmps = b.jmps := rfl
    have ht : (g b).tid = b.tid := rfl
    rw [hj, ht, hout]

private theorem dceAux_succ (protectedVars : List Bap.Var) (cfg : Cfg) (fuel : Nat) :
    dceAux protectedVars cfg (fuel + 1) =
      if (cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)) =
          ((dcePass protectedVars cfg).blocks.map fun blk => (blk.defs.length, blk.phis.length)) then cfg
      else dceAux protectedVars (dcePass protectedVars cfg) fuel := rfl

private theorem dceLoop_eq {protectedVars : List Bap.Var} {protectedSet : Std.HashSet Bap.Var}
    (hset : ∀ x, protectedSet.contains x = true ↔ x ∈ protectedVars) {preds : Preds} {reach : Row}
    {successors : Std.HashMap Tid (List Tid)} {sites definers : VarTable} (fuel : Nat) {cfg : Cfg} {affected : List Bap.Var}
    {dirty : Std.HashSet Tid} {live : Live} (h : Facts protectedVars preds reach successors sites definers cfg affected dirty live) :
    dceLoop protectedVars protectedSet preds reach successors sites definers fuel cfg affected dirty live = dceAux protectedVars cfg fuel := by
  induction fuel generalizing cfg affected dirty live with
  | zero => rfl
  | succ fuel ih =>
    rw [dceLoop, dceAux_succ]
    dsimp only
    cases hr : refresh (blockTable cfg) preds reach sites cfg.blocks.length live affected with
    | none => rfl
    | some live' =>
      dsimp only
      have htables : Tables cfg (blockTable cfg) preds := ⟨blockTable_get cfg, h.pred⟩
      have hrows : ∀ x, RowOf cfg live' x := refresh_spec htables h.reach h.sites h.rows hr
      have hfst : ∀ blk ∈ cfg.blocks, (if dirty.contains blk.tid then
            scanBlock (endQuery protectedSet reach (blockTable cfg) successors live' blk.tid) blk
          else (blk, [])).1 = dceBlock (liveAtEnd protectedVars cfg blk) blk :=
        fun blk hb => stable_or_scan hset h hrows hb
      have hnext : (cfg.blocks.map fun blk => if dirty.contains blk.tid then
            scanBlock (endQuery protectedSet reach (blockTable cfg) successors live' blk.tid) blk
          else (blk, [])).map Prod.fst = (dcePass protectedVars cfg).blocks := by
        rw [List.map_map, dcePass_eq_map]
        exact List.map_congr_left hfst
      simp only [hnext]
      split
      · rfl
      · apply ih
        exact facts_next hset h hrows

/-- `dceAux` from nothing known: all variables are to be solved, and all blocks to be looked at. -/
private def dceAuxFast (protectedVars : List Bap.Var) (cfg : Cfg) (fuel : Nat) : Cfg :=
  let successors := Bap.Graph.Fast.successorTable cfg.graph
  let affected := Bap.Graph.Fast.dedup (cfg.blocks.flatMap vocabulary)
  dceLoop protectedVars (Std.HashSet.ofList protectedVars) (predsOf cfg successors) (Std.HashSet.ofList cfg.reachable)
    successors (tableOf vocabulary cfg.blocks) (tableOf assigned cfg.blocks) fuel cfg affected (Std.HashSet.ofList (cfg.blocks.map Blk.tid)) {}

@[csimp] private theorem dceAux_eq_fast : @dceAux = @dceAuxFast := by
  funext protectedVars cfg fuel
  have hsucc : ∀ t, Bap.Graph.Fast.dedup ((Bap.Graph.Fast.successorTable cfg.graph).getD t []) = cfg.successors t :=
    Bap.Graph.Fast.successors_eq cfg.graph
  refine (dceLoop_eq (by simp [Std.HashSet.contains_ofList]) fuel ⟨mem_predsOf cfg hsucc, ?_, hsucc, mem_tableOf _ _, mem_tableOf _ _, ?_, ?_⟩).symm
  · simp [Std.HashSet.contains_ofList]
  · intro x hx t
    rw [Bap.Graph.Fast.dedup_eq, List.mem_eraseDups, List.mem_flatMap] at hx
    have hnot := not_live_of_unmentioned (cfg := cfg) (x := x) (fun blk hb hv => hx ⟨blk, hb, hv⟩) t
    simp [isLive, hnot]
  · intro blk hb hclean
    have hc : (Std.HashSet.ofList (cfg.blocks.map Blk.tid)).contains blk.tid = true := by
      simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq, List.mem_map]
      exact ⟨blk, hb, rfl⟩
    rw [hc] at hclean
    cases hclean

end Incremental

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
