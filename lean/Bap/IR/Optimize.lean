import Bap.IR.Liveness
import Bap.IR.LiveSets
import Bap.IR.DenseDce
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

/-- `Bil.substitute` of `replacements`: only what is read of the constants is made into expressions. -/
private def substConst (env : ConstEnv) : Bil.Exp → Bil.Exp
  | .int value => .int value
  | .var var =>
    match Assoc.get var env with
    | some constant => constant.toExp
    | none => .var var
  | .load memory address endian size => .load (substConst env memory) (substConst env address) endian size
  | .store memory address value endian size =>
    .store (substConst env memory) (substConst env address) (substConst env value) endian size
  | .bin op left right => .bin op (substConst env left) (substConst env right)
  | .un op value => .un op (substConst env value)
  | .cast kind width value => .cast kind width (substConst env value)
  | .letIn var value body => Bil.substitute (replacements env) (.letIn var value body)
  | .ite condition yes no => .ite (substConst env condition) (substConst env yes) (substConst env no)
  | .extract high low value => .extract high low (substConst env value)
  | .concat left right => .concat (substConst env left) (substConst env right)
  | .unknown message typ => .unknown message typ

private theorem get_replacements (env : ConstEnv) (var : Bap.Var) :
    Assoc.get var (replacements env) = (Assoc.get var env).map Constant.toExp := by
  induction env with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    simp only [replacements, List.map_cons, Assoc.get, List.lookup_cons] at ih ⊢
    cases var == k with
    | true => rfl
    | false => exact ih

private theorem substConst_eq (env : ConstEnv) (exp : Bil.Exp) : substConst env exp = Bil.substitute (replacements env) exp := by
  induction exp with
  | int value => rfl
  | var var =>
    simp only [substConst, Bil.substitute, get_replacements]
    cases Assoc.get var env <;> rfl
  | load m a e s ihm iha => simp only [substConst, Bil.substitute, ihm, iha]
  | store m a v e s ihm iha ihv => simp only [substConst, Bil.substitute, ihm, iha, ihv]
  | bin op l r ihl ihr => simp only [substConst, Bil.substitute, ihl, ihr]
  | un op v ih => simp only [substConst, Bil.substitute, ih]
  | cast k w v ih => simp only [substConst, Bil.substitute, ih]
  | ite c y n ihc ihy ihn => simp only [substConst, Bil.substitute, ihc, ihy, ihn]
  | extract hi lo v ih => simp only [substConst, Bil.substitute, ih]
  | concat l r ihl ihr => simp only [substConst, Bil.substitute, ihl, ihr]
  | unknown m t => rfl
  | letIn var value body _ _ => rfl

/-- `Assoc.remove`, with nothing to copy if it isn't there. -/
private def removeConst (var : Bap.Var) (env : ConstEnv) : ConstEnv :=
  if env.any (·.1 == var) then Assoc.remove var env else env

private theorem removeConst_eq (var : Bap.Var) (env : ConstEnv) : removeConst var env = Assoc.remove var env := by
  unfold removeConst
  split
  · rfl
  · rename_i h
    symm
    apply List.filter_eq_self.2
    intro entry he
    have : entry.1 ≠ var := fun e => h (List.any_eq_true.2 ⟨entry, he, by simp [e]⟩)
    simpa using this

/-- The constants after a definition. -/
private def constStep (env : ConstEnv) (var : Bap.Var) (rhs : Bil.Exp) : ConstEnv :=
  match Constant.ofExp rhs with
  | some constant => Assoc.put var constant env
  | none => removeConst var env

/-- What `propagateBlock` says of its constants, without rewriting the block. -/
private def propagateExit (blk : Blk) (env : ConstEnv) : ConstEnv :=
  let phiVars := blk.phis.map Phi.var
  let env : ConstEnv := if phiVars.isEmpty then env else env.filter fun entry => entry.1 ∉ phiVars
  blk.defs.foldl (init := env) fun env defn => constStep env defn.var (Bil.simplifyExp (substConst env defn.rhs))

private theorem propagateExit_eq (blk : Blk) (env : ConstEnv) : (propagateBlock blk env).2 = propagateExit blk env := by
  have hf : ∀ (e : ConstEnv), (if (blk.phis.map Phi.var).isEmpty then e else e.filter fun entry => entry.1 ∉ blk.phis.map Phi.var) =
      e.filter fun entry => entry.1 ∉ blk.phis.map Phi.var := by
    intro e
    split
    · rename_i h
      have hnil : blk.phis.map Phi.var = [] := by simpa using h
      rw [hnil]
      exact (List.filter_eq_self.2 (by simp)).symm
    · rfl
  have key : ∀ (defs acc : List Def) (e : ConstEnv), (defs.foldl (init := (acc, e)) fun state defn =>
        let rhs := Bil.simplifyExp (Bil.substitute (replacements state.2) defn.rhs)
        let env := match Constant.ofExp rhs with
          | some constant => Assoc.put defn.var constant state.2
          | none => Assoc.remove defn.var state.2
        (state.1 ++ [{ defn with rhs := rhs }], env)).2 =
      defs.foldl (init := e) fun env defn => constStep env defn.var (Bil.simplifyExp (substConst env defn.rhs)) := by
    intro defs
    induction defs with
    | nil => intro _ _; rfl
    | cons d ds ih =>
      intro acc e
      simp only [List.foldl_cons]
      rw [ih]
      congr 1
      simp only [constStep, removeConst_eq, substConst_eq]
  simp only [propagateBlock, propagateExit, hf]
  exact key _ _ _

/-- `propagateBlock`, with its definitions in order at the end instead of each added at the end. -/
private def propagateBlockFast (blk : Blk) (env : ConstEnv) : Blk × ConstEnv :=
  let phiVars := blk.phis.map Phi.var
  let env : ConstEnv := if phiVars.isEmpty then env else env.filter fun entry => entry.1 ∉ phiVars
  let phis := blk.phis.map fun phi =>
    { phi with values := phi.values.map fun input => (input.1, Bil.simplifyExp input.2) }
  let (defs, env) := blk.defs.foldl (init := ([], env)) fun state defn =>
    let rhs := Bil.simplifyExp (substConst state.2 defn.rhs)
    ({ defn with rhs := rhs } :: state.1, constStep state.2 defn.var rhs)
  let jmps := blk.jmps.map (Jmp.mapExp fun exp => Bil.simplifyExp (substConst env exp))
  ({ blk with phis := phis, defs := defs.reverse, jmps := jmps }, env)

@[csimp] private theorem propagateBlock_eq_fast : @propagateBlock = @propagateBlockFast := by
  funext blk env
  have hf : (if (blk.phis.map Phi.var).isEmpty then env else env.filter fun entry => entry.1 ∉ blk.phis.map Phi.var) =
      env.filter fun entry => entry.1 ∉ blk.phis.map Phi.var := by
    split
    · rename_i h
      have hnil : blk.phis.map Phi.var = [] := by simpa using h
      rw [hnil]
      exact (List.filter_eq_self.2 (by simp)).symm
    · rfl
  have key : ∀ (defs acc : List Def) (e : ConstEnv), (defs.foldl (init := (acc, e)) fun state defn =>
        let rhs := Bil.simplifyExp (Bil.substitute (replacements state.2) defn.rhs)
        let env := match Constant.ofExp rhs with
          | some constant => Assoc.put defn.var constant state.2
          | none => Assoc.remove defn.var state.2
        (state.1 ++ [{ defn with rhs := rhs }], env)) =
      let fast := defs.foldl (init := (acc.reverse, e)) fun state defn =>
        let rhs := Bil.simplifyExp (substConst state.2 defn.rhs)
        ({ defn with rhs := rhs } :: state.1, constStep state.2 defn.var rhs)
      (fast.1.reverse, fast.2) := by
    intro defs
    induction defs with
    | nil => intro acc e; simp
    | cons d ds ih =>
      intro acc e
      simp only [List.foldl_cons]
      rw [ih]
      simp only [constStep, removeConst_eq, substConst_eq, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  simp only [propagateBlock, propagateBlockFast, hf]
  have := key blk.defs [] (env.filter fun entry => entry.1 ∉ blk.phis.map Phi.var)
  simp only [List.reverse_nil] at this
  rw [this]
  simp only [substConst_eq]

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
      let env := propagateExit blk (entryEnvT cfg tables exits tid)
      if exits.get? tid = some env then
        propagateAuxT cfg tables fuel exits work
      else
        propagateAuxT cfg tables fuel (exits.insert tid env) (work ++ dedup (tables.succs.getD tid []))

private def propagateConstantsFast (cfg : Cfg) : Cfg :=
  let cfg := cfg.prune
  let tables := propTablesOf cfg
  let exits := propagateAuxT cfg tables (propagateFuel cfg) {} [cfg.start]
  let solved := cfg.blocks.all fun blk =>
    exits.get? blk.tid = some (propagateExit blk (entryEnvT cfg tables exits blk.tid))
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
      simp only [propagateAux, propagateAuxT, prop_block, propagateExit_eq]
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
  simp only [propagateConstants, propagateConstantsFast, isSolved, hentry, hsame _, propagateExit_eq]

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

section Dense

open Bap.IR.DenseDce

private theorem scanDefsD_cons (d : DDef) (rest : List DDef) (live : Marks) :
    scanDefsD (d :: rest) live =
      if (scanDefsD rest live).2.1.contains d.var || d.effect then
        (d :: (scanDefsD rest live).1, d.reads.foldl Marks.add ((scanDefsD rest live).2.1.remove d.var), (scanDefsD rest live).2.2)
      else
        ((scanDefsD rest live).1, (scanDefsD rest live).2.1, d.var :: d.reads ++ (scanDefsD rest live).2.2) := rfl

private abbrev Rel (ids : Ids) (m : Marks) (S : Std.HashSet Bap.Var) : Prop :=
  ∀ x, ids.contains x = true → (m.contains (idOf ids x) = true ↔ S.contains x = true)

private theorem scanDefs_sim {ids : Ids} (hids : IdsWF ids) (defs : List Def)
    (hdefs : ∀ d ∈ defs, ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true)
    {m : Marks} {S : Std.HashSet Bap.Var} (hw : m.WF ids.size) (hrel : Rel ids m S) :
    (scanDefsD (defs.map (denseDef hasSideEffect ids)) m).2.1.WF ids.size ∧
      (scanDefsD (defs.map (denseDef hasSideEffect ids)) m).1 = (dceDefsDropped defs S).1.map (denseDef hasSideEffect ids) ∧
      (scanDefsD (defs.map (denseDef hasSideEffect ids)) m).2.2 = (dceDefsDropped defs S).2.2.map (idOf ids) ∧
      Rel ids (scanDefsD (defs.map (denseDef hasSideEffect ids)) m).2.1 (dceDefsDropped defs S).2.1 := by
  induction defs with
  | nil => exact ⟨hw, rfl, rfl, hrel⟩
  | cons d ds ih =>
    obtain ⟨hdv, hdr⟩ := hdefs d List.mem_cons_self
    obtain ⟨i1, i2, i3, i4⟩ := ih fun e he => hdefs e (List.mem_cons_of_mem _ he)
    rw [List.map_cons, scanDefsD_cons, dceDefsDropped_cons]
    have hcond : ((scanDefsD (ds.map (denseDef hasSideEffect ids)) m).2.1.contains (denseDef hasSideEffect ids d).var || (denseDef hasSideEffect ids d).effect) =
        ((dceDefsDropped ds S).2.1.contains d.var || hasSideEffect d.rhs) := by
      have := i4 d.var hdv
      simp only [denseDef]
      rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.or_eq_true, this]
    rw [hcond]
    have hlt : ∀ y ∈ (denseDef hasSideEffect ids d).reads, y < ids.size := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hids.lt z (hdr z hz)
    split
    · refine ⟨(i1.remove _).foldl_add _, ?_, i3, ?_⟩
      · simp [i2]
      · intro x hx
        have hvl : (denseDef hasSideEffect ids d).var < ids.size := hids.lt _ hdv
        dsimp only
        rw [Marks.contains_foldl_add (i1.remove _) hlt, Marks.contains_remove i1 hvl, i4 x hx,
          Std.HashSet.contains_insertMany_list, Std.HashSet.contains_erase]
        have hmem : idOf ids x ∈ (denseDef hasSideEffect ids d).reads ↔ x ∈ Bil.freeVars d.rhs := by
          simp only [denseDef, List.mem_map]
          exact ⟨fun ⟨y, hy, he⟩ => hids.inj y x (hdr y hy) hx he ▸ hy, fun hy => ⟨x, hy, rfl⟩⟩
        have hne : idOf ids x ≠ (denseDef hasSideEffect ids d).var ↔ x ≠ d.var :=
          not_congr ⟨fun he => hids.inj x d.var hx hdv he, fun he => he ▸ rfl⟩
        rw [hmem, hne]
        simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, ne_eq]
        grind
    · refine ⟨i1, i2, ?_, i4⟩
      simp [i3, denseDef]

/-- What is live at the end of a block as far as the scan of its definitions goes. -/
private def endSpec (protectedVars : List Bap.Var) (cfg : Cfg) (blk : Blk) (x : Bap.Var) : Bool :=
  decide (x ∈ protectedVars) || decide (x ∈ liveOut cfg blk.tid)

private def endSet (protectedVars : List Bap.Var) (cfg : Cfg) (blk : Blk) : Std.HashSet Bap.Var :=
  Std.HashSet.ofList ((assigned blk).filter (endSpec protectedVars cfg blk) ++ blk.jmps.flatMap Jmp.freeVars)

private theorem scan_fst (protectedVars : List Bap.Var) (cfg : Cfg) (blk : Blk) :
    (scanWith (endSet protectedVars cfg blk) blk).1 = dceBlock (liveAtEnd protectedVars cfg blk) blk := by
  apply scanBlock_fst (endSpec protectedVars cfg blk)
  intro x _
  simp only [liveAtEnd, endSpec, List.mem_append, Bool.or_eq_true, decide_eq_true_eq]
  grind

private theorem named_phi {ids : Ids} {blk : Blk} (h : ∀ y ∈ vocabulary blk, ids.contains y = true) {p : Phi} (hp : p ∈ blk.phis) :
    ids.contains p.var = true := h _ (by
  simp only [vocabulary, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩)))

private theorem named_input {ids : Ids} {blk : Blk} (h : ∀ y ∈ vocabulary blk, ids.contains y = true) {p : Phi} (hp : p ∈ blk.phis)
    {input : Tid × Bil.Exp} (hi : input ∈ p.values) {y : Bap.Var} (hy : y ∈ Bil.freeVars input.2) : ids.contains y = true := h _ (by
  simp only [vocabulary, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨p, hp, input, hi, hy⟩)))

private theorem named_def {ids : Ids} {blk : Blk} (h : ∀ y ∈ vocabulary blk, ids.contains y = true) {d : Def} (hd : d ∈ blk.defs) :
    ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true :=
  ⟨h _ (by
    simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
    exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)), fun y hy => h _ (by
    simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
    exact Or.inl (Or.inr ⟨d, hd, Or.inr hy⟩))⟩

private theorem named_jmp {ids : Ids} {blk : Blk} (h : ∀ y ∈ vocabulary blk, ids.contains y = true) {y : Bap.Var}
    (hy : y ∈ blk.jmps.flatMap Jmp.freeVars) : ids.contains y = true := h _ (by
  simp only [vocabulary, List.mem_append]
  exact Or.inr hy)

/-- What `liveD` has marked. -/
private theorem liveD_rel {ids : Ids} (hids : IdsWF ids) {blk : Blk} (hn : ∀ y ∈ vocabulary blk, ids.contains y = true)
    (query : Nat → Bool) (spec : Bap.Var → Bool) (hq : ∀ x ∈ assigned blk, query (idOf ids x) = spec x) {m : Marks} (hw : m.WF ids.size) :
    (liveD query (denseBlk hasSideEffect ids blk) m).WF ids.size ∧
      Rel ids (liveD query (denseBlk hasSideEffect ids blk) m) (Std.HashSet.ofList ((assigned blk).filter spec ++ blk.jmps.flatMap Jmp.freeVars)) := by
  have hdefs : ∀ (l : List Def) (mm : Marks), mm.WF ids.size → (∀ d ∈ l, d ∈ blk.defs) →
      ((l.map (denseDef hasSideEffect ids)).foldl (fun live defn => if query defn.var then live.add defn.var else live) mm).WF ids.size ∧
      ∀ x, ids.contains x = true → ((((l.map (denseDef hasSideEffect ids)).foldl (fun live defn => if query defn.var then live.add defn.var else live) mm).contains (idOf ids x) = true) ↔
        mm.contains (idOf ids x) = true ∨ (∃ d ∈ l, d.var = x) ∧ spec x = true) := by
    intro l
    induction l with
    | nil => intro mm h _; exact ⟨h, by simp⟩
    | cons d ds ih =>
      intro mm h hsub
      simp only [List.map_cons, List.foldl_cons]
      have hdn := (named_def hn (hsub d List.mem_cons_self)).1
      have hqd : query (denseDef hasSideEffect ids d).var = spec d.var :=
        hq d.var (by simp only [assigned, List.mem_append, List.mem_map]; exact Or.inl ⟨d, hsub d List.mem_cons_self, rfl⟩)
      rw [hqd]
      split
      · rename_i hs
        obtain ⟨a1, a2⟩ := ih (mm.add _) (h.add _) fun e he => hsub e (List.mem_cons_of_mem _ he)
        refine ⟨a1, fun x hx => ?_⟩
        have hvl : (denseDef hasSideEffect ids d).var < ids.size := hids.lt _ hdn
        rw [a2 x hx, Marks.contains_add h hvl]
        have heq : idOf ids x = (denseDef hasSideEffect ids d).var ↔ x = d.var :=
          ⟨fun he => hids.inj x d.var hx hdn he, fun he => he ▸ rfl⟩
        rw [heq]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro ((he | he) | ⟨he, hsx⟩)
          · exact Or.inr ⟨Or.inl he.symm, he ▸ hs⟩
          · exact Or.inl he
          · exact Or.inr ⟨Or.inr he, hsx⟩
        · rintro (he | ⟨he | he, hsx⟩)
          · exact Or.inl (Or.inr he)
          · exact Or.inl (Or.inl he.symm)
          · exact Or.inr ⟨he, hsx⟩
      · rename_i hs
        obtain ⟨a1, a2⟩ := ih mm h fun e he => hsub e (List.mem_cons_of_mem _ he)
        refine ⟨a1, fun x hx => ?_⟩
        rw [a2 x hx]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (he | ⟨he, hsx⟩)
          · exact Or.inl he
          · exact Or.inr ⟨Or.inr he, hsx⟩
        · rintro (he | ⟨he | he, hsx⟩)
          · exact Or.inl he
          · exact (hs (he ▸ hsx)).elim
          · exact Or.inr ⟨he, hsx⟩
  have hphis : ∀ (l : List Phi) (mm : Marks), mm.WF ids.size → (∀ p ∈ l, p ∈ blk.phis) →
      ((l.map (densePhi ids)).foldl (fun live phi => if query phi.var then live.add phi.var else live) mm).WF ids.size ∧
      ∀ x, ids.contains x = true → ((((l.map (densePhi ids)).foldl (fun live phi => if query phi.var then live.add phi.var else live) mm).contains (idOf ids x) = true) ↔
        mm.contains (idOf ids x) = true ∨ (∃ p ∈ l, p.var = x) ∧ spec x = true) := by
    intro l
    induction l with
    | nil => intro mm h _; exact ⟨h, by simp⟩
    | cons d ds ih =>
      intro mm h hsub
      simp only [List.map_cons, List.foldl_cons]
      have hdn := named_phi hn (hsub d List.mem_cons_self)
      have hqd : query (densePhi ids d).var = spec d.var :=
        hq d.var (by simp only [assigned, List.mem_append, List.mem_map]; exact Or.inr ⟨d, hsub d List.mem_cons_self, rfl⟩)
      rw [hqd]
      split
      · rename_i hs
        obtain ⟨a1, a2⟩ := ih (mm.add _) (h.add _) fun e he => hsub e (List.mem_cons_of_mem _ he)
        refine ⟨a1, fun x hx => ?_⟩
        have hvl : (densePhi ids d).var < ids.size := hids.lt _ hdn
        rw [a2 x hx, Marks.contains_add h hvl]
        have heq : idOf ids x = (densePhi ids d).var ↔ x = d.var :=
          ⟨fun he => hids.inj x d.var hx hdn he, fun he => he ▸ rfl⟩
        rw [heq]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro ((he | he) | ⟨he, hsx⟩)
          · exact Or.inr ⟨Or.inl he.symm, he ▸ hs⟩
          · exact Or.inl he
          · exact Or.inr ⟨Or.inr he, hsx⟩
        · rintro (he | ⟨he | he, hsx⟩)
          · exact Or.inl (Or.inr he)
          · exact Or.inl (Or.inl he.symm)
          · exact Or.inr ⟨he, hsx⟩
      · rename_i hs
        obtain ⟨a1, a2⟩ := ih mm h fun e he => hsub e (List.mem_cons_of_mem _ he)
        refine ⟨a1, fun x hx => ?_⟩
        rw [a2 x hx]
        simp only [List.mem_cons, exists_eq_or_imp]
        constructor
        · rintro (he | ⟨he, hsx⟩)
          · exact Or.inl he
          · exact Or.inr ⟨Or.inr he, hsx⟩
        · rintro (he | ⟨he | he, hsx⟩)
          · exact Or.inl he
          · exact (hs (he ▸ hsx)).elim
          · exact Or.inr ⟨he, hsx⟩
  obtain ⟨d1, d2⟩ := hdefs blk.defs m.clear hw.clear fun _ h => h
  obtain ⟨p1, p2⟩ := hphis blk.phis _ d1 fun _ h => h
  have hjlt : ∀ y ∈ (blk.jmps.flatMap Jmp.freeVars).map (idOf ids), y < ids.size := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hids.lt z (named_jmp hn hz)
  simp only [liveD, denseBlk]
  refine ⟨p1.foldl_add _, fun x hx => ?_⟩
  rw [Marks.contains_foldl_add p1 hjlt, p2 x hx, d2 x hx, Marks.contains_clear hw]
  have hj : idOf ids x ∈ (blk.jmps.flatMap Jmp.freeVars).map (idOf ids) ↔ x ∈ blk.jmps.flatMap Jmp.freeVars := by
    simp only [List.mem_map]
    exact ⟨fun ⟨y, hy, he⟩ => hids.inj y x (named_jmp hn hy) hx he ▸ hy, fun hy => ⟨x, hy, rfl⟩⟩
  rw [hj]
  simp only [Std.HashSet.contains_ofList, List.contains_eq_mem, decide_eq_true_eq, List.mem_append, List.mem_filter, assigned, List.mem_map]
  simp only [Bool.false_eq_true, false_or]
  clear d1 d2 p1 p2 hdefs hphis hjlt hj hq
  generalize (∃ a, a ∈ blk.defs ∧ a.var = x) = A
  generalize (∃ a, a ∈ blk.phis ∧ a.var = x) = B
  generalize (x ∈ blk.jmps.flatMap Jmp.freeVars) = C
  generalize (spec x = true) = D
  clear hn hx hw hids
  grind

private theorem phiReadsD_lt {ids : Ids} (hids : IdsWF ids) {blk : Blk} (hn : ∀ y ∈ vocabulary blk, ids.contains y = true) (source : Tid) :
    ∀ y ∈ phiReadsD source (denseBlk hasSideEffect ids blk), y < ids.size := by
  intro y hy
  simp only [phiReadsD, denseBlk, List.mem_flatMap, List.mem_map] at hy
  obtain ⟨_, ⟨p, hp, rfl⟩, hm⟩ := hy
  simp only [densePhi] at hm
  have hlook : ∀ (values : List (Tid × Bil.Exp)), (∀ input ∈ values, input ∈ p.values) →
      y ∈ (Assoc.get source (values.map fun input => (input.1, (Bil.freeVars input.2).map (idOf ids)))).getD [] → y < ids.size := by
    intro values
    induction values with
    | nil => simp [Assoc.get]
    | cons head tail ih =>
      intro hsub
      simp only [List.map_cons, Assoc.get, List.lookup_cons]
      cases source == head.1 with
      | true =>
        intro hmem
        simp only [Option.getD_some, List.mem_map] at hmem
        obtain ⟨z, hz, rfl⟩ := hmem
        exact hids.lt z (named_input hn hp (hsub head List.mem_cons_self) hz)
      | false =>
        exact ih fun e he => hsub e (List.mem_cons_of_mem _ he)
  exact hlook p.values (fun _ h => h) hm

private theorem readsD_spec {ids : Ids} {blocks : Array DBlk} (tid : Tid) (succs : List Nat)
    (hlt : ∀ s ∈ succs, ∀ y ∈ phiReadsD tid (blkAt blocks s), y < ids.size) {reads : Marks} (hw : reads.WF ids.size) (y : Nat) :
    (readsD blocks tid succs reads).WF ids.size ∧
      ((readsD blocks tid succs reads).contains y = true ↔ ∃ s ∈ succs, y ∈ phiReadsD tid (blkAt blocks s)) := by
  have key : ∀ (l : List Nat) (m : Marks), m.WF ids.size → (∀ s ∈ l, ∀ y ∈ phiReadsD tid (blkAt blocks s), y < ids.size) →
      (l.foldl (fun reads s => (phiReadsD tid (blkAt blocks s)).foldl Marks.add reads) m).WF ids.size ∧
      ((l.foldl (fun reads s => (phiReadsD tid (blkAt blocks s)).foldl Marks.add reads) m).contains y = true ↔
        m.contains y = true ∨ ∃ s ∈ l, y ∈ phiReadsD tid (blkAt blocks s)) := by
    intro l
    induction l with
    | nil => intro m h _; simp [h]
    | cons a as ih =>
      intro m h hl
      simp only [List.foldl_cons]
      obtain ⟨a1, a2⟩ := ih _ (h.foldl_add (phiReadsD tid (blkAt blocks a))) fun s hs => hl s (List.mem_cons_of_mem _ hs)
      refine ⟨a1, ?_⟩
      rw [a2, Marks.contains_foldl_add h (hl a List.mem_cons_self)]
      simp only [List.mem_cons, exists_eq_or_imp]
      grind
  obtain ⟨h1, h2⟩ := key succs reads.clear hw.clear hlt
  refine ⟨h1, ?_⟩
  simp only [readsD]
  rw [h2, Marks.contains_clear hw]
  simp

/-- A scan of a block, whatever the marks were. -/
private theorem scanD_spec {ids : Ids} {blocks : Array DBlk} {cfg : Cfg} {g : Graphs} {ps : List Bap.Var} {n : Nat} {rows : Array DenseDce.Row}
    (hm : Mirror hasSideEffect ids blocks cfg) (hg : GraphsOK g ids cfg ps n)
    (hrows : ∀ x, ids.contains x = true → RowsOK ids cfg rows x) {i : Nat} {blk : Blk} (hi : At cfg i blk) {reads live : Marks}
    (hr : reads.WF ids.size) (hl : live.WF ids.size) :
    let result := scanD g blocks rows i (denseBlk hasSideEffect ids blk) reads live
    result.1 = denseBlk hasSideEffect ids (scanWith (endSet ps cfg blk) blk).1 ∧
      result.2.1 = (scanWith (endSet ps cfg blk) blk).2.map (idOf ids) ∧ result.2.2.1.WF ids.size ∧ result.2.2.2.WF ids.size := by
  have hids := hm.wf
  have hnamed : ∀ {j b}, At cfg j b → ∀ y ∈ vocabulary b, ids.contains y = true := fun hj => hm.named _ hj.mem
  have hn := hnamed hi
  have hat : ∀ {j}, j < n → ∃ b, At cfg j b := by
    intro j hj
    have hl : j < cfg.blocks.length := hg.count ▸ hj
    exact ⟨cfg.blocks[j], by simp only [At]; simp [hl]⟩
  have htid : g.tids.getD i 0 = blk.tid := hg.tids i blk hi
  generalize hsuccs : (if g.reach.getD i false then g.succs.getD i [] else []) = succs
  have hsin : ∀ s ∈ succs, s < n := by
    intro s hs
    rw [← hsuccs] at hs
    split at hs
    · exact hg.succs_in i s hs
    · simp at hs
  have hrlt : ∀ s ∈ succs, ∀ y ∈ phiReadsD (g.tids.getD i 0) (blkAt blocks s), y < ids.size := by
    intro s hs y hy
    obtain ⟨c, hc⟩ := hat (hsin s hs)
    rw [hm.blkAt hc] at hy
    exact phiReadsD_lt hids (hnamed hc) _ y hy
  have hreads := fun y => readsD_spec (blocks := blocks) (g.tids.getD i 0) succs hrlt hr y
  have hrw : (readsD blocks (g.tids.getD i 0) succs reads).WF ids.size := (hreads 0).1
  have hq : ∀ x ∈ assigned blk, queryD g blocks rows succs (readsD blocks (g.tids.getD i 0) succs reads) (idOf ids x) = endSpec ps cfg blk x := by
    intro x hxa
    have hx : ids.contains x = true := hn x (by
      simp only [assigned, List.mem_append, List.mem_map] at hxa
      rcases hxa with ⟨d, hd, rfl⟩ | ⟨p, hp, rfl⟩
      · exact hn _ (by
          simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
          exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)) |> fun _ => by
            simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
            exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)
      · simp only [vocabulary, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩)))
    have hedge : ∀ s c, At cfg s c → s ∈ succs → (idOf ids x ∈ phiReadsD (g.tids.getD i 0) (blkAt blocks s) ↔ x ∈ phiReads blk.tid c) := by
      intro s c hc _
      rw [hm.blkAt hc, htid, phiReadsD_dense hids (hnamed hc) _ hx]
    rw [Bool.eq_iff_iff]
    simp only [queryD, endSpec, Bool.or_eq_true, decide_eq_true_eq, hg.protect x hx, (hreads _).2, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    have hphiOf : ∀ s c, At cfg s c → (hasPhiD (blkAt blocks s) (idOf ids x) = false ↔ ∀ phi ∈ c.phis, phi.var ≠ x) := by
      intro s c hc
      rw [hm.blkAt hc, hasPhiD_dense hids (hnamed hc) hx, hasPhi_false_iff]
    by_cases hreach : blk.tid ∈ cfg.reachable
    · have hrb : g.reach.getD i false = true := (hg.reach i blk hi).2 hreach
      have hsi : succs = g.succs.getD i [] := by
        rw [← hsuccs, ite_eq_left hrb]
      rw [mem_liveOut hreach (hg.block i blk hi)]
      have main : ((∃ s ∈ succs, idOf ids x ∈ phiReadsD (g.tids.getD i 0) (blkAt blocks s)) ∨
          ∃ s ∈ succs, (rows.getD (idOf ids x) (.short [])).contains s = true ∧ hasPhiD (blkAt blocks s) (idOf ids x) = false) ↔
          ∃ τ ∈ cfg.successors blk.tid, EdgeNeed cfg (fun s => x ∈ liveIn cfg s) x blk.tid τ := by
        constructor
        · rintro (⟨s, hs, hread⟩ | ⟨s, hs, hrow, hp⟩)
          · obtain ⟨c, hc⟩ := hat (hsin s hs)
            exact ⟨c.tid, (hg.succs i blk s c hi hc).1 (hsi ▸ hs), c, hg.block s c hc, Or.inr ((hedge s c hc hs).1 hread)⟩
          · obtain ⟨c, hc⟩ := hat (hsin s hs)
            exact ⟨c.tid, (hg.succs i blk s c hi hc).1 (hsi ▸ hs), c, hg.block s c hc, Or.inl ⟨(hrows x hx s c hc).1 hrow, (hphiOf s c hc).1 hp⟩⟩
        · rintro ⟨τ, hτ, c, hbs, hneed⟩
          obtain ⟨s, hc, hct⟩ := hg.index τ c hbs
          subst hct
          have hs : s ∈ succs := hsi ▸ (hg.succs i blk s c hi hc).2 hτ
          rcases hneed with ⟨hl', hp⟩ | hread
          · exact Or.inr ⟨s, hs, (hrows x hx s c hc).2 hl', (hphiOf s c hc).2 hp⟩
          · exact Or.inl ⟨s, hs, (hedge s c hc hs).2 hread⟩
      rw [or_assoc, main]
    · have hrb : ¬ g.reach.getD i false = true := fun h => hreach ((hg.reach i blk hi).1 h)
      have hsi : succs = [] := by
        rw [← hsuccs, ite_eq_right hrb]
      rw [liveOut_unreachable hreach, hsi]
      simp
  obtain ⟨l1, l2⟩ := liveD_rel hids hn _ (endSpec ps cfg blk) hq hl
  have hrel : Rel ids (liveD (queryD g blocks rows succs (readsD blocks (g.tids.getD i 0) succs reads)) (denseBlk hasSideEffect ids blk) live) (endSet ps cfg blk) := l2
  obtain ⟨s1, s2, s3, s4⟩ := scanDefs_sim hids blk.defs (fun d hd => named_def hn hd) l1 hrel
  simp only [scanD, endLive, hsuccs]
  simp only [denseBlk] at s1 s2 s3 s4 l1 ⊢
  generalize liveD _ _ live = lm at s1 s2 s3 s4
  simp only [denseBlk] at *
  generalize scanDefsD (blk.defs.map (denseDef hasSideEffect ids)) lm = res at s1 s2 s3 s4 ⊢
  have hp : ∀ phi ∈ blk.phis, res.2.1.contains (densePhi ids phi).var = (dceDefsDropped blk.defs (endSet ps cfg blk)).2.1.contains phi.var := by
    intro phi hphi
    rw [Bool.eq_iff_iff]
    exact s4 phi.var (named_phi hn hphi)
  have hfilter : ((blk.phis.map (densePhi ids)).filter fun phi => res.2.1.contains phi.var) =
      (blk.phis.filter fun phi => (dceDefsDropped blk.defs (endSet ps cfg blk)).2.1.contains phi.var).map (densePhi ids) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro phi hphi
    exact hp phi hphi
  have hlost : ((blk.phis.map (densePhi ids)).filter fun phi => !res.2.1.contains phi.var) =
      (blk.phis.filter fun phi => !(dceDefsDropped blk.defs (endSet ps cfg blk)).2.1.contains phi.var).map (densePhi ids) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro phi hphi
    simp only [Function.comp, hp phi hphi]
  have hmention : ∀ phi : Phi, phiMentionsD (densePhi ids phi) = (phiMentions phi).map (idOf ids) := by
    intro phi
    simp only [phiMentionsD, densePhi, phiMentions, List.map_cons, List.map_flatMap, List.flatMap_map]
  refine ⟨?_, ?_, (hreads 0).1, s1⟩
  · simp only [scanWith, s2, hfilter]
  · simp only [scanWith, s3, hlost, List.map_append, List.flatMap_map, List.map_flatMap, hmention]

private abbrev sizes (blk : Blk) : Nat × Nat := (blk.defs.length, blk.phis.length)

private theorem dropped_length (defs : List Def) (S : Std.HashSet Bap.Var) :
    (dceDefsDropped defs S).1.length ≤ defs.length ∧ ((dceDefsDropped defs S).2.2 = [] ↔ (dceDefsDropped defs S).1.length = defs.length) := by
  induction defs with
  | nil => simp [dceDefsDropped]
  | cons d ds ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [dceDefsDropped_cons]
    split
    · simp only [List.length_cons]
      exact ⟨by omega, by rw [h2]; omega⟩
    · simp only [List.length_cons, List.cons_append, reduceCtorEq, false_iff]
      exact ⟨by omega, by omega⟩

private theorem phis_length (phis : List Phi) (keep : Phi → Bool) :
    (phis.filter fun phi => !keep phi).flatMap phiMentions = [] ↔ (phis.filter keep).length = phis.length := by
  induction phis with
  | nil => simp
  | cons p ps ih =>
    have hle := List.length_filter_le keep ps
    simp only [List.filter_cons]
    by_cases hk : keep p = true
    · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff]
      exact ih
    · simp only [hk, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.flatMap_cons]
      simp only [phiMentions, List.cons_append, reduceCtorEq, false_iff]
      omega

private theorem scan_sizes (S : Std.HashSet Bap.Var) (blk : Blk) :
    (scanWith S blk).2 = [] ↔ sizes (scanWith S blk).1 = sizes blk := by
  simp only [scanWith, List.append_eq_nil_iff, sizes, Prod.mk.injEq]
  rw [(dropped_length blk.defs S).2, phis_length]

/-- The blocks of `scanAll`, and what they have removed. -/
private theorem scanAll_spec {ids : Ids} {blocks : Array DBlk} {cfg : Cfg} {g : Graphs} {ps : List Bap.Var} {n : Nat} {rows : Array DenseDce.Row}
    (hm : Mirror hasSideEffect ids blocks cfg) (hg : GraphsOK g ids cfg ps n)
    (hrows : ∀ x, ids.contains x = true → RowsOK ids cfg rows x) (dirty : List Nat) (hdirty : ∀ i ∈ dirty, i < n) (hsize : blocks.size = n) (j y k : Nat)
    (reads live : Marks) (hr : reads.WF ids.size) (hl : live.WF ids.size) :
    let result := scanAll g blocks rows dirty reads live
    result.1.size = n ∧ result.2.2.1.WF ids.size ∧ result.2.2.2.WF ids.size ∧
      (result.1[j]? = if j ∈ dirty then
          (cfg.blocks[j]?).map fun b => denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1
        else blocks[j]?) ∧
      ((y, k) ∈ result.2.1 ↔ k ∈ dirty ∧ ∃ b, At cfg k b ∧ y ∈ (scanWith (endSet ps cfg b) b).2.map (idOf ids)) := by
  have hat : ∀ {i}, i < n → ∃ b, At cfg i b := by
    intro i hi
    have hl : i < cfg.blocks.length := hg.count ▸ hi
    exact ⟨cfg.blocks[i], by simp only [At]; simp [hl]⟩
  have hscan : ∀ (dirty : List Nat), (∀ i ∈ dirty, i < n) → ∀ (ups : List (Nat × DBlk)) (acc : List (Nat × Nat)) (reads live : Marks), reads.WF ids.size → live.WF ids.size →
      let result := dirty.foldl (init := (ups, acc, reads, live)) fun state i =>
        let r := scanD g blocks rows i (blkAt blocks i) state.2.2.1 state.2.2.2
        ((i, r.1) :: state.1, r.2.1.map (fun y => (y, i)) ++ state.2.1, r.2.2.1, r.2.2.2)
      result.2.2.1.WF ids.size ∧ result.2.2.2.WF ids.size ∧
        (∀ u, u ∈ result.1 ↔ u ∈ ups ∨ u.1 ∈ dirty ∧ ∃ b, At cfg u.1 b ∧ u.2 = denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1) ∧
        ((y, k) ∈ result.2.1 ↔ (y, k) ∈ acc ∨ k ∈ dirty ∧ ∃ b, At cfg k b ∧ y ∈ (scanWith (endSet ps cfg b) b).2.map (idOf ids)) := by
    intro dirty
    induction dirty with
    | nil =>
      intro _ ups acc reads live hr hl
      simp [hr, hl]
    | cons i rest ih =>
      intro hdirty ups acc reads live hr hl
      simp only [List.foldl_cons]
      obtain ⟨b, hb⟩ := hat (hdirty i List.mem_cons_self)
      rw [hm.blkAt hb]
      obtain ⟨r1, r2, r3, r4⟩ := scanD_spec (ps := ps) hm hg hrows hb hr hl
      obtain ⟨a1, a2, a3, a4⟩ := ih (fun q hq => hdirty q (List.mem_cons_of_mem _ hq)) (_ :: ups) (_ ++ acc) _ _ r3 r4
      refine ⟨a1, a2, ?_, ?_⟩
      · intro u
        rw [a3, List.mem_cons, r1]
        have hbu : ∀ c, At cfg i c → c = b := by
          intro c hc'
          simp only [At] at hc' hb
          rw [hc'] at hb
          exact Option.some.inj hb
        simp only [List.mem_cons]
        constructor
        · rintro ((rfl | h) | ⟨h1, h2⟩)
          · exact Or.inr ⟨Or.inl rfl, b, hb, rfl⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h1, h2⟩
        · rintro (h | ⟨h1 | h1, c, hc', h⟩)
          · exact Or.inl (Or.inr h)
          · have hci : c = b := hbu c (by rw [← h1]; exact hc')
            subst hci
            obtain ⟨u1, u2⟩ := u
            simp only at h1 h
            subst h1
            subst h
            exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨h1, c, hc', h⟩
      · rw [a4, List.mem_append, r2]
        have hpair : (y, k) ∈ ((scanWith (endSet ps cfg b) b).2.map (idOf ids)).map (fun y => (y, i)) ↔
            k = i ∧ y ∈ (scanWith (endSet ps cfg b) b).2.map (idOf ids) := by
          simp only [List.mem_map, Prod.mk.injEq]
          constructor
          · rintro ⟨z, ⟨w, hw, rfl⟩, rfl, rfl⟩
            exact ⟨rfl, w, hw, rfl⟩
          · rintro ⟨rfl, w, hw, rfl⟩
            exact ⟨_, ⟨w, hw, rfl⟩, rfl, rfl⟩
        rw [hpair]
        simp only [List.mem_cons]
        constructor
        · rintro ((⟨rfl, h⟩ | h) | ⟨h1, h2⟩)
          · exact Or.inr ⟨Or.inl rfl, b, hb, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h1, h2⟩
        · rintro (h | ⟨h1 | h1, c, hc', h⟩)
          · exact Or.inl (Or.inr h)
          · subst h1
            have hcb : c = b := by
              simp only [At] at hc' hb
              rw [hc'] at hb
              exact Option.some.inj hb
            exact Or.inl (Or.inl ⟨rfl, hcb ▸ h⟩)
          · exact Or.inr ⟨h1, c, hc', h⟩
  have hup : ∀ (ups : List (Nat × DBlk)) (cur : Array DBlk) (v : Option DBlk), cur.size = n → (∀ u ∈ ups, u.1 < n) →
      (∀ u ∈ ups, u.1 = j → some u.2 = v) →
      (ups.foldl (fun blocks update => blocks.setIfInBounds update.1 update.2) cur).size = n ∧
      (ups.foldl (fun blocks update => blocks.setIfInBounds update.1 update.2) cur)[j]? = if ∃ u ∈ ups, u.1 = j then v else cur[j]? := by
    intro ups
    induction ups with
    | nil => intro cur v hc _ _; simp [hc]
    | cons u us ih =>
      intro cur v hc hlt hv
      simp only [List.foldl_cons]
      obtain ⟨i1, i2⟩ := ih (cur.setIfInBounds u.1 u.2) v (by simpa using hc) (fun q hq => hlt q (List.mem_cons_of_mem _ hq)) (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      refine ⟨i1, ?_⟩
      rw [i2]
      by_cases he : u.1 = j
      · have hin : ∃ w ∈ u :: us, w.1 = j := ⟨u, List.mem_cons_self, he⟩
        rw [ite_eq_left hin]
        split
        · rfl
        · rw [Array.getElem?_setIfInBounds]
          have hlt' : u.1 < cur.size := hc ▸ hlt u List.mem_cons_self
          simp [he] at hlt' ⊢
          simp [hlt']
          exact hv u List.mem_cons_self he
      · by_cases hrest : ∃ w ∈ us, w.1 = j
        · rw [ite_eq_left hrest, ite_eq_left]
          obtain ⟨w, hw, he'⟩ := hrest
          exact ⟨w, List.mem_cons_of_mem _ hw, he'⟩
        · rw [ite_eq_right hrest, ite_eq_right, Array.getElem?_setIfInBounds]
          · simp [he]
          · rintro ⟨w, hw, he'⟩
            rcases List.mem_cons.1 hw with rfl | hw
            · exact he he'
            · exact hrest ⟨w, hw, he'⟩
  simp only [scanAll]
  obtain ⟨s1, s2, s3, s4⟩ := hscan dirty hdirty [] [] reads live hr hl
  generalize dirty.foldl (init := (([] : List (Nat × DBlk)), ([] : List (Nat × Nat)), reads, live)) (fun state i =>
        let r := scanD g blocks rows i (blkAt blocks i) state.2.2.1 state.2.2.2
        ((i, r.1) :: state.1, r.2.1.map (fun y => (y, i)) ++ state.2.1, r.2.2.1, r.2.2.2)) = res at s1 s2 s3 s4
  have hin : ∀ u ∈ res.1, u.1 ∈ dirty ∧ ∃ b, At cfg u.1 b ∧ u.2 = denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1 := by
    intro u hu
    simpa using (s3 u).1 hu
  obtain ⟨u1, u2⟩ := hup res.1 blocks ((cfg.blocks[j]?).map fun b => denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1) hsize
    (fun u hu => hdirty _ (hin u hu).1) (by
      rintro ⟨i, d⟩ hu rfl
      obtain ⟨_, b, hb, he⟩ := hin _ hu
      simp only at hb he
      have hbi : cfg.blocks[i]? = some b := hb
      simp [hbi, he])
  refine ⟨u1, s1, s2, ?_, ?_⟩
  · rw [u2]
    by_cases hjd : j ∈ dirty
    · obtain ⟨b, hb⟩ := hat (hdirty j hjd)
      rw [ite_eq_left hjd, ite_eq_left]
      exact ⟨(j, denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1), (s3 _).2 (Or.inr ⟨hjd, b, hb, rfl⟩), rfl⟩
    · rw [ite_eq_right hjd, ite_eq_right]
      rintro ⟨u, hu, he⟩
      exact hjd (he ▸ (hin u hu).1)
  · simpa using s4

private theorem scan_mentions {S : Std.HashSet Bap.Var} {blk : Blk} {x : Bap.Var} (h : x ∈ (scanWith S blk).2) : x ∈ vocabulary blk := by
  have hdefs : ∀ (l : List Def) (T : Std.HashSet Bap.Var), x ∈ (dceDefsDropped l T).2.2 → ∃ d ∈ l, x = d.var ∨ x ∈ Bil.freeVars d.rhs := by
    intro l T
    induction l with
    | nil => simp [dceDefsDropped]
    | cons d ds ih =>
      rw [dceDefsDropped_cons]
      split
      · intro hm
        obtain ⟨e, he, hc⟩ := ih hm
        exact ⟨e, List.mem_cons_of_mem _ he, hc⟩
      · simp only [List.cons_append, List.mem_cons, List.mem_append]
        rintro (he | he | he)
        · exact ⟨d, Or.inl rfl, Or.inl he⟩
        · exact ⟨d, Or.inl rfl, Or.inr he⟩
        · obtain ⟨e, hee, hc⟩ := ih he
          exact ⟨e, Or.inr hee, hc⟩
  simp only [scanWith, List.mem_append, List.mem_flatMap, List.mem_filter, phiMentions, List.mem_cons] at h
  simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons]
  rcases h with h | ⟨p, ⟨hp, _⟩, h⟩
  · obtain ⟨d, hd, hc⟩ := hdefs _ _ h
    exact Or.inl (Or.inr ⟨d, hd, hc⟩)
  · rcases h with rfl | ⟨input, hi, hy⟩
    · exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, input, hi, hy⟩))

private theorem graphs_next {g : Graphs} {ids : Ids} {cfg : Cfg} {ps : List Bap.Var} {n : Nat} (hg : GraphsOK g ids cfg ps n) (step : Blk → Blk)
    (htid : ∀ b, (step b).tid = b.tid) (hv : ∀ b y, y ∈ vocabulary (step b) → y ∈ vocabulary b) (ha : ∀ b y, y ∈ assigned (step b) → y ∈ assigned b) :
    GraphsOK g ids { cfg with blocks := cfg.blocks.map step } ps n := by
  have hat : ∀ {i b}, At { cfg with blocks := cfg.blocks.map step } i b → ∃ c, At cfg i c ∧ b = step c := by
    intro i b h
    simp only [At, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨c, hc, rfl⟩
  have hunique : ∀ i j a b, At { cfg with blocks := cfg.blocks.map step } i a → At { cfg with blocks := cfg.blocks.map step } j b → a.tid = b.tid → i = j := by
    intro i j a b ha' hb' he
    obtain ⟨c, hc, rfl⟩ := hat ha'
    obtain ⟨d, hd, rfl⟩ := hat hb'
    rw [htid, htid] at he
    exact hg.unique i j c d hc hd he
  refine ⟨?_, ?_, ?_, hunique, by simpa using hg.count, hg.preds_in, ?_, hg.succs_in, ?_, ?_, ?_, hg.sites_in, ?_, hg.definers_in, hg.protect⟩
  · intro i b h
    obtain ⟨c, hc, rfl⟩ := hat h
    rw [htid]
    exact hg.tids i c hc
  · intro i b h
    exact block_of_unique (fun p q a b h1 h2 he => hunique p q a b h1 h2 he) h.mem
  · intro t b h
    have hsome : b.tid = t := by
      simpa using List.find?_some h
    obtain ⟨i, hi⟩ := exists_at (List.mem_of_find?_eq_some h)
    exact ⟨i, hi, hsome⟩
  · intro i b p c hb hc
    obtain ⟨b', hb', rfl⟩ := hat hb
    obtain ⟨c', hc', rfl⟩ := hat hc
    rw [htid, htid]
    exact hg.preds i b' p c' hb' hc'
  · intro i b p c hb hc
    obtain ⟨b', hb', rfl⟩ := hat hb
    obtain ⟨c', hc', rfl⟩ := hat hc
    rw [htid, htid]
    exact hg.succs i b' p c' hb' hc'
  · intro i b hb
    obtain ⟨b', hb', rfl⟩ := hat hb
    rw [htid]
    exact hg.reach i b' hb'
  · intro i b hb y hy
    obtain ⟨b', hb', rfl⟩ := hat hb
    exact hg.sites i b' hb' y (hv _ _ hy)
  · intro i b hb y hy
    obtain ⟨b', hb', rfl⟩ := hat hb
    exact hg.definers i b' hb' y (ha _ _ hy)

/-! ### What a pass takes from where a variable is live -/

private theorem mem_dceDefs_live (defs : List Def) (live : List Bap.Var) (x : Bap.Var) :
    x ∈ (dceDefs defs live).2 ↔ Exposed (dceDefs defs live).1 x ∨ (x ∈ live ∧ ∀ d ∈ (dceDefs defs live).1, d.var ≠ x) := by
  induction defs with
  | nil => simp [dceDefs, Exposed]
  | cons d ds ih =>
    rw [dceDefs_cons]
    split
    · simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq, Exposed, List.mem_cons, forall_eq_or_imp, ih]
      grind
    · exact ih

private theorem exposed_dceDefs (defs : List Def) (live : List Bap.Var) (x : Bap.Var)
    (h : Exposed (dceDefs defs live).1 x) : Exposed defs x := by
  induction defs with
  | nil => exact h
  | cons d ds ih =>
    rw [dceDefs_cons] at h
    split at h
    · rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, ih h2⟩
    · rename_i hc
      refine Or.inr ⟨fun he => hc ?_, ih h⟩
      have : x ∈ (dceDefs ds live).2 := (mem_dceDefs_live ds live x).2 (Or.inl h)
      simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
      exact Or.inl (he ▸ this)

private theorem noDef_dceDefs (defs : List Def) (live : List Bap.Var) (x : Bap.Var) (hx : x ∈ live)
    (h : ∀ d ∈ (dceDefs defs live).1, d.var ≠ x) : ∀ d ∈ defs, d.var ≠ x := by
  induction defs with
  | nil => simp
  | cons d ds ih =>
    rw [dceDefs_cons] at h
    split at h
    · simp only [List.mem_cons, forall_eq_or_imp] at h ⊢
      exact ⟨h.1, ih h.2⟩
    · rename_i hc
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨fun he => hc ?_, ih h⟩
      have : x ∈ (dceDefs ds live).2 := (mem_dceDefs_live ds live x).2 (Or.inr ⟨hx, h⟩)
      simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
      exact Or.inl (he ▸ this)

/-- What is left of a block reads nothing first that the block didn't. -/
private theorem dceBlock_gen {live : List Bap.Var} {blk : Blk} {x : Bap.Var} (hj : ∀ y ∈ blk.jmps.flatMap Jmp.freeVars, y ∈ live)
    (h : x ∈ blockIn (dceBlock live blk) []) : x ∈ blockIn blk [] := by
  simp only [mem_blockIn, dceBlock, List.mem_filter, List.not_mem_nil, or_false, and_imp] at h ⊢
  obtain ⟨hphi, hcase⟩ := h
  have hlive : x ∈ (dceDefs blk.defs live).2 := by
    rw [mem_dceDefs_live]
    rcases hcase with h | ⟨⟨j, hjm, hv⟩, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hj x (List.mem_flatMap.2 ⟨j, hjm, hv⟩), h⟩
  refine ⟨fun phi hp he => hphi phi hp (by simpa [he] using hlive) he, ?_⟩
  rcases hcase with h | ⟨hjr, h⟩
  · exact Or.inl (exposed_dceDefs _ _ _ h)
  · obtain ⟨j, hjm, hv⟩ := hjr
    exact Or.inr ⟨⟨j, hjm, hv⟩, noDef_dceDefs _ _ _ (hj x (List.mem_flatMap.2 ⟨j, hjm, hv⟩)) h⟩

/-- A block only stops assigning what isn't live at its end. -/
private theorem dceBlock_unkilled {live : List Bap.Var} {blk : Blk} {x : Bap.Var} (hk : Killed blk x) (hn : ¬ Killed (dceBlock live blk) x) (hx : x ∈ live) : False := by
  have hdefs : ∀ d ∈ (dceDefs blk.defs live).1, d.var ≠ x := fun d hd he => hn (Or.inr ⟨d, hd, he⟩)
  have hall := noDef_dceDefs _ _ _ hx hdefs
  rcases hk with ⟨phi, hp, he⟩ | ⟨d, hd, he⟩
  · have hlive : x ∈ (dceDefs blk.defs live).2 := (mem_dceDefs_live _ _ _).2 (Or.inr ⟨hx, hdefs⟩)
    exact hn (Or.inl ⟨phi, List.mem_filter.2 ⟨hp, by simpa [he] using hlive⟩, he⟩)
  · exact hall d hd he

private theorem dceBlock_shrinks (live : List Bap.Var) (blk : Blk) (x : Bap.Var) : Shrinks x blk (dceBlock live blk) := by
  refine ⟨?_, fun h phi hp => h phi (List.mem_filter.1 hp).1⟩
  rintro (⟨phi, hp, he⟩ | ⟨d, hd, he⟩)
  · exact Or.inl ⟨phi, (List.mem_filter.1 hp).1, he⟩
  · exact Or.inr ⟨d, (dceDefs_sublist blk.defs live).subset hd, he⟩

private theorem dceBlock_reads {live : List Bap.Var} {blk : Blk} {x : Bap.Var} {source : Tid} (h : x ∈ phiReads source (dceBlock live blk)) : x ∈ phiReads source blk := by
  rw [mem_phiReads] at h ⊢
  obtain ⟨phi, hp, rest⟩ := h
  exact ⟨phi, (List.mem_filter.1 hp).1, rest⟩

private theorem block_next (cfg : Cfg) (g : Blk → Blk) (htid : ∀ blk, (g blk).tid = blk.tid) (t : Tid) :
    ({ cfg with blocks := cfg.blocks.map g } : Cfg).block t = (cfg.block t).map g := by
  simp only [Cfg.block, List.find?_map]
  congr 1
  congr 1
  funext b
  simp [htid]

private theorem no_phi_of_live {cfg : Cfg} {t : Tid} {blk : Blk} {x : Bap.Var} (hb : cfg.block t = some blk) (h : x ∈ liveIn cfg t) :
    ∀ phi ∈ blk.phis, phi.var ≠ x := by
  have := (liveness_equations cfg (reachable_of_live h) hb x).1.1 h
  exact ((mem_blockIn _ _ _).1 this).1

private theorem liveOut_sub_end (ps : List Bap.Var) (cfg : Cfg) (blk : Blk) {x : Bap.Var} (h : x ∈ liveOut cfg blk.tid) : x ∈ liveAtEnd ps cfg blk := by
  simp only [liveAtEnd, List.mem_append]
  exact Or.inl (Or.inl h)

private theorem jmps_sub_end (ps : List Bap.Var) (cfg : Cfg) (blk : Blk) : ∀ y ∈ blk.jmps.flatMap Jmp.freeVars, y ∈ liveAtEnd ps cfg blk := by
  intro y hy
  simp only [liveAtEnd, List.mem_append]
  exact Or.inl (Or.inr hy)

/-- A pass only takes from where a variable is live. -/
private theorem dcePass_live_sub (ps : List Bap.Var) (cfg : Cfg) (x : Bap.Var) {t : Tid}
    (h : x ∈ liveIn ({ cfg with blocks := cfg.blocks.map fun b => dceBlock (liveAtEnd ps cfg b) b } : Cfg) t) : x ∈ liveIn cfg t := by
  have htid : ∀ b : Blk, (dceBlock (liveAtEnd ps cfg b) b).tid = b.tid := fun _ => rfl
  have hblock := block_next cfg (fun b => dceBlock (liveAtEnd ps cfg b) b) htid
  refine live_least _ x (fun t => x ∈ liveIn cfg t) ?_ ?_ h
  · intro τ hτ blk hb hg
    rw [hblock] at hb
    cases hc : cfg.block τ with
    | none => simp [hc] at hb
    | some c =>
      rw [hc] at hb
      cases hb
      exact live_of_gen hτ hc (dceBlock_gen (jmps_sub_end ps cfg c) hg)
  · intro τ hτ blk hb hk σ hσ he
    rw [hblock] at hb
    cases hc : cfg.block τ with
    | none => simp [hc] at hb
    | some c =>
      rw [hc] at hb
      cases hb
      obtain ⟨bs, hbs, hcase⟩ := he
      rw [hblock] at hbs
      cases hcs : cfg.block σ with
      | none => simp [hcs] at hbs
      | some d =>
        rw [hcs] at hbs
        cases hbs
        have hedge : EdgeNeed cfg (fun s => x ∈ liveIn cfg s) x τ σ := by
          refine ⟨d, hcs, ?_⟩
          rcases hcase with ⟨h1, _⟩ | h1
          · exact Or.inl ⟨h1, no_phi_of_live hcs h1⟩
          · exact Or.inr (dceBlock_reads h1)
        by_cases hkc : Killed c x
        · have hout : x ∈ liveOut cfg τ := (mem_liveOut (cfg := cfg) hτ hc x).2 ⟨σ, hσ, hedge⟩
          have htc : c.tid = τ := (block_some hc).2
          exact (dceBlock_unkilled hkc hk (liveOut_sub_end ps cfg c (htc ▸ hout))).elim
        · exact live_of_edge hτ hc hkc hσ hedge

/-- A block keeps all it has if it keeps as many. -/
private theorem step_of_sizes (live : List Bap.Var) (blk : Blk) (h : sizes (dceBlock live blk) = sizes blk) : dceBlock live blk = blk := by
  simp only [sizes, dceBlock, Prod.mk.injEq] at h
  have h1 := (dceDefs_sublist blk.defs live).eq_of_length h.1
  have h2 := (List.filter_sublist (p := fun phi => (dceDefs blk.defs live).2.contains phi.var) (l := blk.phis)).eq_of_length h.2
  cases blk
  simp_all [dceBlock]

/-- What a state of `loopD` is. -/
private structure DenseInv (ps : List Bap.Var) (base : Cfg) (g : Graphs) (ids : Ids) (n M : Nat) (cfg : Cfg) (blocks : Array DBlk)
    (rows : Array DenseDce.Row) (dirty : List Nat) (groups : Array (List Nat)) (seen seen2 reads live : Marks) : Prop where
  mirror : Mirror hasSideEffect ids blocks cfg
  graphs : GraphsOK g ids cfg ps n
  start : cfg.start = base.start
  graph : cfg.graph = base.graph
  size : rows.size = ids.size
  nM : n ≤ M
  seen : seen.WF M
  seen2 : seen2.WF M
  reads : reads.WF ids.size
  live : live.WF ids.size
  rows : ∀ x, ids.contains x = true → RowsOK ids cfg rows x
  dirty_in : ∀ i ∈ dirty, i < n
  stable : ∀ i b, At cfg i b → i ∉ dirty → dceBlock (liveAtEnd ps cfg b) b = b
  groupsSize : groups.size = ids.size
  groups : ∀ y, groups.getD y [] = []

private theorem loopD_eq {ps : List Bap.Var} {base : Cfg} {g : Graphs} {ids : Ids} {n M : Nat} (fallback : Cfg → Nat → Cfg)
    (hf : ∀ c f, fallback c f = dceAux ps c f) (fuel : Nat) {cfg : Cfg} {blocks : Array DBlk} {rows : Array DenseDce.Row} {dirty : List Nat}
    {groups : Array (List Nat)} {seen seen2 reads live : Marks} (h : DenseInv ps base g ids n M cfg blocks rows dirty groups seen seen2 reads live) :
    loopD g (fun blocks fuel => fallback { base with blocks := blocks.toList.map DBlk.toBlk } fuel)
      (fun blocks => { base with blocks := blocks.toList.map DBlk.toBlk }) fuel blocks rows dirty groups seen seen2 reads live = dceAux ps cfg fuel := by
  have hofB : ∀ {c : Cfg} {bs : Array DBlk}, Mirror hasSideEffect ids bs c → c.start = base.start → c.graph = base.graph →
      ({ base with blocks := bs.toList.map DBlk.toBlk } : Cfg) = c := by
    intro c bs hm h1 h2
    rw [hm.ofBlocks]
    cases c
    cases base
    simp_all
  induction fuel generalizing cfg blocks rows dirty groups seen seen2 reads live with
  | zero =>
    simp only [loopD]
    rw [hofB h.mirror h.start h.graph]
    rfl
  | succ fuel ih =>
    have hids := h.mirror.wf
    rw [loopD]
    have hblocks : blocks.size = n := by
      have := congrArg List.length h.mirror.blocks
      simp only [Array.length_toList, List.length_map] at this
      rw [this, h.graphs.count]
    let step : Blk → Blk := fun b => dceBlock (liveAtEnd ps cfg b) b
    have hnext : dcePass ps cfg = { cfg with blocks := cfg.blocks.map step } := dcePass_eq_map _ _
    have hspec := scanAll_spec (ps := ps) h.mirror h.graphs h.rows dirty h.dirty_in hblocks
    generalize hres : scanAll g blocks rows dirty reads live = res
    have hsp : ∀ j y k, res.1.size = n ∧ res.2.2.1.WF ids.size ∧ res.2.2.2.WF ids.size ∧
        (res.1[j]? = if j ∈ dirty then (cfg.blocks[j]?).map fun b => denseBlk hasSideEffect ids (scanWith (endSet ps cfg b) b).1 else blocks[j]?) ∧
        ((y, k) ∈ res.2.1 ↔ k ∈ dirty ∧ ∃ b, At cfg k b ∧ y ∈ (scanWith (endSet ps cfg b) b).2.map (idOf ids)) := by
      intro j y k
      rw [← hres]
      exact hspec j y k reads live h.reads h.live
    have hdropped : ∀ y k, (y, k) ∈ res.2.1 ↔ k ∈ dirty ∧ ∃ b, At cfg k b ∧ y ∈ (scanWith (endSet ps cfg b) b).2.map (idOf ids) :=
      fun y k => (hsp 0 y k).2.2.2.2
    have hnamed : ∀ {j b}, At cfg j b → ∀ y ∈ vocabulary b, ids.contains y = true := fun hj => h.mirror.named _ hj.mem
    have hsame : ∀ {i a b}, At cfg i a → At cfg i b → a = b := by
      intro i a b ha hb
      simp only [At] at ha hb
      rw [ha] at hb
      exact Option.some.inj hb
    have hsizesAll : ∀ i b, At cfg i b → i ∈ dirty → ((scanWith (endSet ps cfg b) b).2 = [] ↔ sizes (step b) = sizes b) := by
      intro i b _ _
      rw [scan_sizes, scan_fst]
    have hasg : ∀ b y, y ∈ assigned (step b) → y ∈ assigned b := fun b y hy => assigned_dceBlock hy
    have hvoc : ∀ b y, y ∈ vocabulary (step b) → y ∈ vocabulary b := fun b y hy => vocabulary_dceBlock hy
    have htid : ∀ b, (step b).tid = b.tid := fun _ => rfl
    have hgn := graphs_next h.graphs step htid hvoc hasg
    have hmn : Mirror hasSideEffect ids res.1 { cfg with blocks := cfg.blocks.map step } := by
      refine ⟨?_, ?_, hids⟩
      · apply List.ext_getElem?
        intro j
        have hj := (hsp j 0 0).2.2.2.1
        simp only [Array.getElem?_toList, hj, List.getElem?_map]
        by_cases hd : j ∈ dirty
        · simp only [hd, ↓reduceIte]
          cases hb : cfg.blocks[j]? with
          | none => rfl
          | some b =>
            simp only [Option.map_some, scan_fst]
            rfl
        · simp only [hd, ↓reduceIte]
          have hl : blocks[j]? = (cfg.blocks.map (denseBlk hasSideEffect ids))[j]? := by
            rw [← h.mirror.blocks, Array.getElem?_toList]
          rw [hl, List.getElem?_map]
          cases hb : cfg.blocks[j]? with
          | none => rfl
          | some b =>
            simp only [Option.map_some, Option.some.injEq]
            have := h.stable j b hb hd
            show denseBlk hasSideEffect ids b = denseBlk hasSideEffect ids (dceBlock _ b)
            rw [this]
      · intro b hb y hy
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
        exact h.mirror.named c hc y (hvoc c y hy)
    rw [dceAux_succ]
    cases hdl : res.2.1 with
    | nil =>
      simp only
      have hpos : (cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)) = ((dcePass ps cfg).blocks.map fun blk => (blk.defs.length, blk.phis.length)) := by
        rw [hnext]
        simp only [List.map_map]
        apply List.map_congr_left
        intro b hb
        obtain ⟨i, hi⟩ := exists_at hb
        by_cases hd : i ∈ dirty
        · have hempty : (scanWith (endSet ps cfg b) b).2 = [] := by
            cases he : (scanWith (endSet ps cfg b) b).2 with
            | nil => rfl
            | cons z zs =>
              have hin := (hdropped (idOf ids z) i).2 ⟨hd, b, hi, List.mem_map.2 ⟨z, by simp [he], rfl⟩⟩
              rw [hdl] at hin
              cases hin
          exact ((hsizesAll i b hi hd).1 hempty).symm
        · show sizes b = sizes (dceBlock _ b)
          rw [h.stable i b hi hd]
      have hsameStep : ∀ b ∈ cfg.blocks, step b = b := by
        intro b hb
        have hsz : sizes (step b) = sizes b := by
          obtain ⟨i, hi⟩ := exists_at hb
          by_cases hd : i ∈ dirty
          · have hempty : (scanWith (endSet ps cfg b) b).2 = [] := by
              cases he : (scanWith (endSet ps cfg b) b).2 with
              | nil => rfl
              | cons z zs =>
                have hin := (hdropped (idOf ids z) i).2 ⟨hd, b, hi, List.mem_map.2 ⟨z, by simp [he], rfl⟩⟩
                rw [hdl] at hin
                cases hin
            exact (hsizesAll i b hi hd).1 hempty
          · show sizes (dceBlock _ b) = sizes b
            rw [h.stable i b hi hd]
        exact step_of_sizes _ _ hsz
      have hfixed : ({ cfg with blocks := cfg.blocks.map step } : Cfg) = cfg := by
        have : cfg.blocks.map step = cfg.blocks := by
          conv => rhs; rw [← List.map_id cfg.blocks]
          exact List.map_congr_left hsameStep
        cases cfg
        simp_all
      rw [ite_eq_left hpos, hofB hmn h.start h.graph, hfixed]
    | cons first others =>
      simp only
      have hne : ¬ (cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)) = ((dcePass ps cfg).blocks.map fun blk => (blk.defs.length, blk.phis.length)) := by
        intro heq
        obtain ⟨hd, b, hi, hm⟩ := (hdropped first.1 first.2).1 (by simp [hdl])
        have hne' : (scanWith (endSet ps cfg b) b).2 ≠ [] := by
          intro he
          simp [he] at hm
        apply hne'
        apply (hsizesAll first.2 b hi hd).2
        rw [hnext] at heq
        have hg1 := congrArg (fun l => l[first.2]?) heq
        simp only [List.getElem?_map, List.map_map] at hg1
        have hbi : cfg.blocks[first.2]? = some b := hi
        simp only [hbi, Option.map_some, Option.some.injEq, Function.comp] at hg1
        exact hg1.symm
      rw [ite_eq_right hne]
      rw [← hdl]
      have hfall : fallback { base with blocks := res.1.toList.map DBlk.toBlk } fuel = dceAux ps (dcePass ps cfg) fuel := by
        rw [hf, hofB hmn h.start h.graph, hnext]
      -- The variables, and where they were mentioned.
      have hpairsLt : ∀ p ∈ res.2.1, p.1 < groups.size ∧ ∃ x, ids.contains x = true ∧ idOf ids x = p.1 := by
        rintro ⟨y, k⟩ hp
        obtain ⟨_, b, hb, hm⟩ := (hdropped y k).1 hp
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
        have hxn := hnamed hb x (scan_mentions hx)
        exact ⟨h.groupsSize ▸ hids.lt x hxn, x, hxn, rfl⟩
      obtain ⟨gs1, gs2⟩ := addGroups_spec res.2.1 groups fun p hp => (hpairsLt p hp).1
      let orig : Nat → List Nat := fun y => (addGroups res.2.1 groups).getD y []
      have horig : ∀ y s, s ∈ orig y ↔ (y, s) ∈ res.2.1 := by
        intro y s
        have := gs2 y s
        rw [h.groups] at this
        simpa [orig] using this
      have hagreeClean : ∀ x i b, ids.contains x = true → At cfg i b → i ∉ orig (idOf ids x) → Agree x b (step b) := by
        intro x i b hx hb hn
        by_cases hd : i ∈ dirty
        · have hnm : x ∉ (scanWith (endSet ps cfg b) b).2 := fun hm =>
            hn ((horig _ _).2 ((hdropped _ _).2 ⟨hd, b, hb, List.mem_map.2 ⟨x, hm, rfl⟩⟩))
          have := scanWith_agree (endSet ps cfg b) b x hnm
          rwa [scan_fst] at this
        · show Agree x b (dceBlock _ b)
          rw [h.stable i b hb hd]
          exact Agree.refl x b
      have hatN : ∀ {i b}, At cfg i b → At { cfg with blocks := cfg.blocks.map step } i (step b) := by
        intro i b hb
        simp only [At, List.getElem?_map] at hb ⊢
        simp [hb]
      have hatN' : ∀ {i c}, At { cfg with blocks := cfg.blocks.map step } i c → ∃ b, At cfg i b ∧ c = step b := by
        intro i c hc
        simp only [At, List.getElem?_map, Option.map_eq_some_iff] at hc
        obtain ⟨b, hb, rfl⟩ := hc
        exact ⟨b, hb, rfl⟩
      have hrm : ∀ x, ids.contains x = true → Removal cfg { cfg with blocks := cfg.blocks.map step } x (orig (idOf ids x)) := by
        intro x hx
        refine ⟨rfl, fun _ => rfl, ?_, fun t hl => dcePass_live_sub ps cfg x hl⟩
        intro t before hb
        obtain ⟨hmem, htb⟩ := block_some hb
        obtain ⟨i, hi⟩ := exists_at hmem
        exact ⟨i, step before, hatN hi, htb, dceBlock_shrinks _ _ _, fun hn => hagreeClean x i before hx hi hn⟩
      have horigIn : ∀ y, ∀ s ∈ orig y, s < n := by
        intro y s hs
        obtain ⟨_, _, hb, _⟩ := (hdropped y s).1 ((horig y s).1 hs)
        have hl : s < cfg.blocks.length := (List.getElem?_eq_some_iff.1 hb).1
        exact h.graphs.count ▸ hl
      have hleft : ∀ y, (addGroups res.2.1 groups).getD y [] ≠ [] → ∃ p ∈ res.2.1, p.1 = y := by
        intro y hy
        cases hc : (addGroups res.2.1 groups).getD y [] with
        | nil => exact (hy hc).elim
        | cons s ss =>
          have hs : s ∈ orig y := by
            show s ∈ (addGroups res.2.1 groups).getD y []
            rw [hc]
            exact List.mem_cons_self
          exact ⟨(y, s), (horig y s).1 hs, rfl⟩
      have hstate : ∀ x, ids.contains x = true → (VarDone g res.1 ids cfg { cfg with blocks := cfg.blocks.map step } rows [] x (orig (idOf ids x)) ∧
            (addGroups res.2.1 groups).getD (idOf ids x) [] = []) ∨
          ((addGroups res.2.1 groups).getD (idOf ids x) [] = orig (idOf ids x) ∧ orig (idOf ids x) ≠ [] ∧
            (∀ i b, At { cfg with blocks := cfg.blocks.map step } i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn cfg b.tid))) := by
        intro x hx
        have hrowOld : ∀ i b, At { cfg with blocks := cfg.blocks.map step } i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn cfg b.tid) := by
          intro i b hb
          obtain ⟨c, hc, rfl⟩ := hatN' hb
          rw [htid]
          exact h.rows x hx i c hc
        by_cases hc : orig (idOf ids x) = []
        · refine Or.inl ⟨?_, hc⟩
          have hclean : ∀ blk ∈ cfg.blocks, Agree x blk (step blk) := by
            intro blk hb
            obtain ⟨i, hi⟩ := exists_at hb
            exact hagreeClean x i blk hx hi (by rw [hc]; exact List.not_mem_nil)
          obtain ⟨a1, a2⟩ := agree_next cfg step x htid hclean
          have hl := live_iff_of_agree cfg { cfg with blocks := cfg.blocks.map step } x rfl (fun _ => rfl) a1 a2
          refine ⟨fun i b hb => ?_, ?_⟩
          · rw [hrowOld i b hb, hl]
          · rintro t b hb (hm | ⟨h1, h2⟩) p _ _
            · rw [hc] at hm
              cases hm
            · exact (h2 ((hl _).1 h1)).elim
        · exact Or.inr ⟨rfl, hc, hrowOld⟩
      have hgs : (addGroups res.2.1 groups).size = ids.size := gs1.trans h.groupsSize
      cases hu : updateAll g res.1 res.2.1 rows (addGroups res.2.1 groups) [] seen seen2 with
      | none =>
        simp only
        exact hfall
      | some result =>
        obtain ⟨rows2, groups2, next, s1, s2⟩ := result
        obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := updateAll_spec orig hmn hgn h.nM hrm horigIn res.2.1 rows _ [] seen seen2 h.size hgs h.seen h.seen2
          (fun p hp => (hpairsLt p hp).2) hstate hleft hu
        simp only
        rw [hnext]
        have hmemDirty : ∀ {i}, i ∈ (nodup s1 next).1 ↔ i ∈ next := fun {i} => mem_nodup u1 _ i
        apply ih
        refine ⟨hmn, hgn, h.start, h.graph, u3, h.nM, nodup_wf u1 _, u2, (hsp 0 0 0).2.1, (hsp 0 0 0).2.2.1, ?_, ?_, ?_, u4, u5⟩
        · intro x hx i b hb
          exact (u6 x hx).row i b hb
        · intro i hi
          rcases u7 i (hmemDirty.1 hi) with hc | hc
          · cases hc
          · exact hc
        · intro i b hb hclean
          obtain ⟨c, hc, rfl⟩ := hatN' hb
          apply dceBlock_stable
          intro y hy
          have hyc : y ∈ assigned c := hasg c y hy
          have hyn : ids.contains y = true := hnamed hc y (by
            simp only [assigned, List.mem_append, List.mem_map] at hyc
            simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons]
            rcases hyc with ⟨d, hd, rfl⟩ | ⟨p, hp, rfl⟩
            · exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)
            · exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩)))
          have hkilled : killedD (Bap.IR.DenseDce.blkAt res.1 i) (idOf ids y) = true := by
            have hki : Killed (step c) y := by
              simp only [assigned, List.mem_append, List.mem_map] at hy
              rcases hy with ⟨d, hd, he⟩ | ⟨p, hp, he⟩
              · exact Or.inr ⟨d, hd, he⟩
              · exact Or.inl ⟨p, hp, he⟩
            rw [hmn.blkAt (hatN hc), killedD_dense hids (fun z hz => hnamed hc z (hvoc c z hz)) hyn, killed_iff]
            exact hki
          have hctid := h.graphs.block i c hc
          have hnotDirty : i ∉ next := fun hm => hclean (hmemDirty.2 hm)
          have hblockN := block_next cfg step htid
          have hstepB : ({ cfg with blocks := cfg.blocks.map step } : Cfg).block c.tid = some (step c) := by rw [hblockN, hctid]; rfl
          have hout : y ∈ liveOut cfg c.tid ↔ y ∈ liveOut { cfg with blocks := cfg.blocks.map step } c.tid := by
            by_cases hre : c.tid ∈ cfg.reachable
            · have hre' : c.tid ∈ ({ cfg with blocks := cfg.blocks.map step } : Cfg).reachable := hre
              rw [mem_liveOut hre hctid, mem_liveOut hre' hstepB]
              constructor
              · rintro ⟨σ, hσ, bs, hbs, hcase⟩
                obtain ⟨is, his, hst⟩ := h.graphs.index σ bs hbs
                subst hst
                refine ⟨bs.tid, hσ, step bs, by rw [hblockN, hbs]; rfl, ?_⟩
                have hip : i ∈ g.preds.getD is [] := (hgn.preds is (step bs) i (step c) (hatN his) (hatN hc)).2 ⟨hre', hσ⟩
                rcases hcase with ⟨h1, h2⟩ | h1
                · refine Or.inl ⟨?_, (dceBlock_shrinks _ _ _).phi h2⟩
                  refine Classical.byContradiction fun hlost => hnotDirty ?_
                  exact (u6 y hyn).dirty is (step bs) (hatN his) (Or.inr ⟨h1, hlost⟩) i hip hkilled
                · by_cases hs : is ∈ orig (idOf ids y)
                  · exact (hnotDirty ((u6 y hyn).dirty is (step bs) (hatN his) (Or.inl hs) i hip hkilled)).elim
                  · exact Or.inr (((hagreeClean y is bs hyn his hs).reads c.tid).1 h1)
              · rintro ⟨σ, hσ, bs, hbs, hcase⟩
                rw [hblockN] at hbs
                cases hcs : cfg.block σ with
                | none => simp [hcs] at hbs
                | some d =>
                  rw [hcs] at hbs
                  cases hbs
                  refine ⟨σ, hσ, d, hcs, ?_⟩
                  rcases hcase with ⟨h1, _⟩ | h1
                  · have hl := dcePass_live_sub ps cfg y h1
                    exact Or.inl ⟨hl, no_phi_of_live hcs hl⟩
                  · exact Or.inr (dceBlock_reads h1)
            · rw [liveOut_unreachable hre, liveOut_unreachable (show c.tid ∉ ({ cfg with blocks := cfg.blocks.map step } : Cfg).reachable from hre)]
          simp only [liveAtEnd, List.mem_append]
          have hj : (step c).jmps = c.jmps := rfl
          have ht : (step c).tid = c.tid := rfl
          rw [hj, ht, hout]

end Dense

/-- `dceAux` from nothing known: all variables are to be solved, and all blocks to be looked at. -/
private def dceAuxFast (protectedVars : List Bap.Var) (cfg : Cfg) (fuel : Nat) : Cfg :=
  let successors := Bap.Graph.Fast.successorTable cfg.graph
  let affected := Bap.Graph.Fast.dedup (cfg.blocks.flatMap vocabulary)
  dceLoop protectedVars (Std.HashSet.ofList protectedVars) (predsOf cfg successors) (Std.HashSet.ofList cfg.reachable)
    successors (tableOf vocabulary cfg.blocks) (tableOf assigned cfg.blocks) fuel cfg affected (Std.HashSet.ofList (cfg.blocks.map Blk.tid)) {}

private theorem dceAux_eq_fast : @dceAux = @dceAuxFast := by
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

/-- `dceAux` with its variables as numbers. What has blocks with the same tid goes by `dceAuxFast`, as does what runs out of fuel. -/
private def dceAuxDense (protectedVars : List Bap.Var) (cfg : Cfg) (fuel : Nat) : Cfg :=
  Bap.IR.DenseDce.run hasSideEffect protectedVars cfg fuel (dceAuxFast protectedVars)

@[csimp] private theorem dceAux_eq_dense : @dceAux = @dceAuxDense := by
  funext ps cfg fuel
  have hf : ∀ c f, dceAuxFast ps c f = dceAux ps c f := fun c f => by rw [dceAux_eq_fast]
  simp only [dceAuxDense, Bap.IR.DenseDce.run]
  by_cases hc : Bap.IR.DenseDce.indexChecks (DenseDce.indexOf 0 cfg.blocks {}) 0 cfg.blocks = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨p1, p2⟩ : DenseDce.IdsWF (DenseDce.internAll {} ps) ∧ ∀ y < (DenseDce.internAll {} ps).size,
        ∃ x, (DenseDce.internAll {} ps).contains x = true ∧ DenseDce.idOf (DenseDce.internAll {} ps) x = y :=
      ⟨DenseDce.internAll_wf DenseDce.idsWF_empty ps, DenseDce.internAll_onto DenseDce.idsWF_empty (by simp) ps⟩
    obtain ⟨h1, h2, h3, h4⟩ := DenseDce.internBlocks_spec cfg.blocks _ p1 p2
    have hps : ∀ x ∈ ps, (cfg.blocks.foldl DenseDce.internBlock (DenseDce.internAll {} ps)).contains x = true := fun x hx =>
      h3 x ((DenseDce.contains_internAll _ _ _).2 (Or.inr hx))
    generalize cfg.blocks.foldl DenseDce.internBlock (DenseDce.internAll {} ps) = ids at h1 h2 h3 h4 hps
    symm
    have hg := DenseDce.graphsOf_ok h1 h4 hps hc
    have hm : DenseDce.Mirror hasSideEffect ids (cfg.blocks.map (DenseDce.denseBlk hasSideEffect ids)).toArray cfg := ⟨by simp, h4, h1⟩
    have hsizeR : ids.size = (Array.replicate ids.size (DenseDce.Row.short [])).size := by simp
    cases hr : DenseDce.refreshD (DenseDce.graphsOf ids ps cfg (DenseDce.indexOf 0 cfg.blocks {})) (cfg.blocks.map (DenseDce.denseBlk hasSideEffect ids)).toArray
        (Array.replicate ids.size (.short [])) (List.range ids.size) (DenseDce.Marks.empty ids.size) (DenseDce.Marks.empty (max ids.size cfg.blocks.length)) with
    | none =>
      simp only
      exact hf cfg fuel
    | some result =>
      obtain ⟨rows, _, seen⟩ := result
      obtain ⟨q1, _, q3, q4⟩ := DenseDce.refreshD_spec hm hg (Nat.le_max_right _ _) hsizeR (by simpa using DenseDce.Marks.wf_empty _) (DenseDce.Marks.wf_empty _)
        (fun x hx hn => (hn (List.mem_range.2 (h1.lt x hx))).elim) (fun y hy => h2 y (List.mem_range.1 hy)) hr
      simp only
      refine loopD_eq (ids := ids) (base := cfg) (n := cfg.blocks.length) (M := max ids.size cfg.blocks.length) (dceAuxFast ps) hf fuel ?_
      refine ⟨hm, hg, rfl, rfl, by simpa using q1, Nat.le_max_right _ _, q3, DenseDce.Marks.wf_empty _, DenseDce.Marks.wf_empty _, DenseDce.Marks.wf_empty _, q4, ?_, ?_, by simp, ?_⟩
      · intro i hi
        exact List.mem_range.1 hi
      · intro i b hb hn
        have hbi : cfg.blocks[i]? = some b := hb
        exact (hn (List.mem_range.2 (List.getElem?_eq_some_iff.1 hbi).1)).elim
      · intro y
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
        split <;> rfl
  · simp only [hc, Bool.not_false, ↓reduceIte, hf]

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
