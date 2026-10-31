import Bap.IR.Transform

namespace Bap.IR

private def insertPhisForVar (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Bap.Var) :
    Nat → List Tid → List Tid → Cfg
  | 0, _, _ => cfg
  | _fuel + 1, [], _ => cfg
  | fuel + 1, tid :: work, inserted =>
    let joins := (Assoc.get tid frontier).getD []
    let (cfg, inserted, work) := joins.foldl (init := (cfg, inserted, work)) fun state join =>
      let (cfg, inserted, work) := state
      if join ∈ inserted then
        (cfg, inserted, work)
      else
        let predecessors := cfg.predecessors join
        let phi : Phi := ⟨join, var, predecessors.map fun pred => (pred, .var var)⟩
        -- A phi the input already has for this variable is its definition here: keep it alone.
        let insert (blk : Blk) : Blk :=
          if blk.phis.any (·.var == var) then blk else { blk with phis := blk.phis ++ [phi] }
        (cfg.updateBlock join insert, join :: inserted, join :: work)
    insertPhisForVar cfg frontier var fuel work inserted

private def insertAllPhis (cfg : Cfg) (frontier : List (Tid × List Tid)) : List Bap.Var → Cfg
  | [] => cfg
  | var :: rest =>
    let definitions := cfg.blocks.filterMap fun blk => if blk.defines var then some blk.tid else none
    let fuel := cfg.blocks.length * 2 + 1
    let cfg := insertPhisForVar cfg frontier var fuel definitions []
    insertAllPhis cfg frontier rest

/-! ### Placing phis with tables

Every phi `insertAllPhis` places looks for the predecessors and goes over all the blocks, and every variable goes over all the blocks
for what defines it. All of that is fixed before it starts, for variables that are all different, so the places of the phis
can be found first, in tables, and the blocks changed once. -/

section FastPhis

open Bap.Graph.Fast (dedup dedup_eq assocTable assocTable_get)

/-- What placing a phi does to a block. -/
private def placePhi (phi : Phi) (blk : Blk) : Blk :=
  if blk.phis.any (·.var == phi.var) then blk else { blk with phis := blk.phis ++ [phi] }

private def phiAt (graph : Bap.Graph.Graph Tid) (var : Bap.Var) (join : Tid) : Phi :=
  ⟨join, var, (Bap.Graph.predecessors graph join).map fun pred => (pred, .var var)⟩

/-- The blocks after one phi for each of `joins`. -/
private def placeAll (cfg : Cfg) (var : Bap.Var) (joins : List Tid) : Cfg :=
  joins.foldl (fun cfg join => cfg.updateBlock join (placePhi (phiAt cfg.graph var join))) cfg

private theorem placeAll_graph (cfg : Cfg) (var : Bap.Var) (joins : List Tid) : (placeAll cfg var joins).graph = cfg.graph := by
  induction joins generalizing cfg with
  | nil => rfl
  | cons j js ih => exact ih _

private theorem placeAll_snoc (cfg : Cfg) (var : Bap.Var) (joins : List Tid) (join : Tid) :
    placeAll cfg var (joins ++ [join]) =
      (placeAll cfg var joins).updateBlock join (placePhi (phiAt cfg.graph var join)) := by
  simp only [placeAll, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have := placeAll_graph cfg var joins
  simp only [placeAll] at this
  rw [this]

/-- The joins `insertPhisForVar` places phis at, last first. -/
private def joinsAux (frontier : Std.HashMap Tid (List Tid)) : Nat → List Tid → Std.HashSet Tid → List Tid → List Tid
  | 0, _, _, out => out
  | _ + 1, [], _, out => out
  | fuel + 1, tid :: work, inserted, out =>
    let next := (frontier.getD tid []).foldl (init := (inserted, work, out)) fun state join =>
      if state.1.contains join then state
      else (state.1.insert join, join :: state.2.1, join :: state.2.2)
    joinsAux frontier fuel next.2.1 next.1 next.2.2

private theorem joins_step (cfg0 : Cfg) (var : Bap.Var) (joins : List Tid) (cfg : Cfg) (inserted : List Tid) (work out : List Tid)
    (set : Std.HashSet Tid) (hcfg : cfg = placeAll cfg0 var out.reverse) (hset : ∀ t, t ∈ inserted ↔ set.contains t = true)
    (spec : Cfg × List Tid × List Tid)
    (hspec : joins.foldl (init := (cfg, inserted, work)) (fun state join =>
      let (cfg, inserted, work) := state
      if join ∈ inserted then
        (cfg, inserted, work)
      else
        let predecessors := cfg.predecessors join
        let phi : Phi := ⟨join, var, predecessors.map fun pred => (pred, .var var)⟩
        let insert (blk : Blk) : Blk :=
          if blk.phis.any (·.var == var) then blk else { blk with phis := blk.phis ++ [phi] }
        (cfg.updateBlock join insert, join :: inserted, join :: work)) = spec) :
    let fast := joins.foldl (init := (set, work, out)) fun state join =>
      if state.1.contains join then state
      else (state.1.insert join, join :: state.2.1, join :: state.2.2)
    spec.1 = placeAll cfg0 var fast.2.2.reverse ∧ spec.2.2 = fast.2.1 ∧ ∀ t, t ∈ spec.2.1 ↔ fast.1.contains t = true := by
  subst hspec
  induction joins generalizing cfg inserted work out set with
  | nil => exact ⟨hcfg, rfl, hset⟩
  | cons j js ih =>
    simp only [List.foldl_cons]
    by_cases hj : j ∈ inserted
    · have hc : set.contains j = true := (hset j).1 hj
      simp only [hj, ↓reduceIte, hc]
      exact ih _ _ _ _ _ hcfg hset
    · have hc : ¬ set.contains j = true := fun h => hj ((hset j).2 h)
      simp only [hj, ↓reduceIte, hc]
      refine ih _ _ _ _ _ ?_ ?_
      · rw [List.reverse_cons, placeAll_snoc, hcfg]
        have hg : (placeAll cfg0 var out.reverse).graph = cfg0.graph := placeAll_graph _ _ _
        have hpred : (placeAll cfg0 var out.reverse).predecessors j = Bap.Graph.predecessors cfg0.graph j := by
          simp only [Cfg.predecessors, hg]
        rw [hpred]
        rfl
      · intro t
        simp only [List.mem_cons, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hset t]
        grind

private theorem insertPhisForVar_eq (cfg0 : Cfg) (var : Bap.Var) (frontier : List (Tid × List Tid))
    (table : Std.HashMap Tid (List Tid)) (htable : ∀ t, (Assoc.get t frontier).getD [] = table.getD t [])
    (fuel : Nat) (work inserted out : List Tid) (cfg : Cfg) (set : Std.HashSet Tid)
    (hcfg : cfg = placeAll cfg0 var out.reverse) (hset : ∀ t, t ∈ inserted ↔ set.contains t = true) :
    insertPhisForVar cfg frontier var fuel work inserted = placeAll cfg0 var (joinsAux table fuel work set out).reverse := by
  induction fuel generalizing work inserted out cfg set with
  | zero => simpa [insertPhisForVar, joinsAux] using hcfg
  | succ fuel ih =>
    cases work with
    | nil => simpa [insertPhisForVar, joinsAux] using hcfg
    | cons tid work =>
      rw [insertPhisForVar, joinsAux, htable tid]
      split
      rename_i spec c i w hs
      obtain ⟨h1, h2, h3⟩ := joins_step cfg0 var (table.getD tid []) cfg inserted work out set hcfg hset _ hs
      dsimp only at h1 h2 h3
      rw [← h2]
      exact ih _ _ _ _ _ h1 h3

/-- The phis placed so far, last first, by block. -/
private def applyPending (pending : Std.HashMap Tid (List Phi)) (cfg : Cfg) : Cfg :=
  { cfg with blocks := cfg.blocks.map fun blk => (pending.getD blk.tid []).foldr placePhi blk }

private theorem placePhi_tid (phi : Phi) (blk : Blk) : (placePhi phi blk).tid = blk.tid := by
  unfold placePhi
  split <;> rfl

private theorem foldr_placePhi_tid (phis : List Phi) (blk : Blk) : (phis.foldr placePhi blk).tid = blk.tid := by
  induction phis with
  | nil => rfl
  | cons p ps ih => rw [List.foldr_cons, placePhi_tid, ih]

private def addPhi (pending : Std.HashMap Tid (List Phi)) (phi : Phi) : Std.HashMap Tid (List Phi) :=
  pending.insert phi.tid (phi :: pending.getD phi.tid [])

private theorem applyPending_add (pending : Std.HashMap Tid (List Phi)) (cfg : Cfg) (phi : Phi) :
    applyPending (addPhi pending phi) cfg = (applyPending pending cfg).updateBlock phi.tid (placePhi phi) := by
  simp only [applyPending, addPhi, Cfg.updateBlock, List.map_map]
  congr 1
  apply List.map_congr_left
  intro blk _
  simp only [Function.comp, foldr_placePhi_tid, Std.HashMap.getD_insert]
  by_cases h : blk.tid = phi.tid
  · simp [h]
  · have hq : (phi.tid == blk.tid) = false := by simpa using fun e : phi.tid = blk.tid => h e.symm
    simp [h, hq]

private theorem applyPending_joins (pending : Std.HashMap Tid (List Phi)) (cfg : Cfg) (var : Bap.Var) (joins : List Tid) :
    applyPending (joins.foldl (fun pending join => addPhi pending (phiAt cfg.graph var join)) pending) cfg =
      placeAll (applyPending pending cfg) var joins := by
  induction joins generalizing pending with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons, placeAll]
    rw [ih]
    simp only [placeAll]
    rw [applyPending_add]
    rfl

private theorem defines_iff (blk : Blk) (var : Bap.Var) :
    blk.defines var = true ↔ (∃ phi ∈ blk.phis, phi.var = var) ∨ ∃ defn ∈ blk.defs, defn.var = var := by
  simp [Blk.defines, Blk.definedVars, List.mem_eraseDups]

private theorem defines_placePhi (phi : Phi) (blk : Blk) (var : Bap.Var) (h : phi.var ≠ var) :
    (placePhi phi blk).defines var = blk.defines var := by
  rw [Bool.eq_iff_iff, defines_iff, defines_iff]
  unfold placePhi
  split
  · rfl
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (⟨p, hp | rfl, e⟩ | hd)
      · exact Or.inl ⟨p, hp, e⟩
      · exact (h e).elim
      · exact Or.inr hd
    · rintro (⟨p, hp, e⟩ | hd)
      · exact Or.inl ⟨p, Or.inl hp, e⟩
      · exact Or.inr hd

private theorem defines_foldr (phis : List Phi) (blk : Blk) (var : Bap.Var) (h : ∀ phi ∈ phis, phi.var ≠ var) :
    (phis.foldr placePhi blk).defines var = blk.defines var := by
  induction phis with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldr_cons, defines_placePhi _ _ _ (h p List.mem_cons_self),
      ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The blocks that define each variable, last first. -/
private def definersOf (blocks : List Blk) : Std.HashMap Bap.Var (List Tid) :=
  blocks.foldl (init := {}) fun table blk =>
    blk.definedVars.foldl (fun table var => table.insert var (blk.tid :: table.getD var [])) table

private theorem definers_block (tid : Tid) (vars : List Bap.Var) (hnd : vars.Nodup) (table : Std.HashMap Bap.Var (List Tid)) (var : Bap.Var) :
    (vars.foldl (fun table var => table.insert var (tid :: table.getD var [])) table).getD var [] =
      if var ∈ vars then tid :: table.getD var [] else table.getD var [] := by
  induction vars generalizing table with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.nodup_cons.1 hnd
    rw [List.foldl_cons, ih has]
    by_cases hva : var = a
    · subst hva
      simp [ha]
    · have hq : (a == var) = false := by simpa using fun e : a = var => hva e.symm
      simp [Std.HashMap.getD_insert, hq, hva]

private theorem definersOf_get (blocks : List Blk) (var : Bap.Var) :
    ((definersOf blocks).getD var []).reverse = blocks.filterMap fun blk => if blk.defines var then some blk.tid else none := by
  have key : ∀ (l : List Blk) (table : Std.HashMap Bap.Var (List Tid)),
      ((l.foldl (fun table blk => blk.definedVars.foldl (fun table var => table.insert var (blk.tid :: table.getD var [])) table) table).getD var []).reverse =
        (table.getD var []).reverse ++ l.filterMap fun blk => if blk.defines var then some blk.tid else none := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro table
      have hnd : b.definedVars.Nodup := Bap.Proofs.Graph.nodup_eraseDups _
      have hmem : var ∈ b.definedVars ↔ b.defines var = true := by simp [Blk.defines]
      rw [List.foldl_cons, ih, definers_block _ _ hnd, List.filterMap_cons]
      by_cases hd : b.defines var = true
      · simp [hd, hmem]
      · simp [hd, hmem]
  simpa [definersOf] using key blocks {}

private theorem insertAllPhis_eq (cfg : Cfg) (frontier : List (Tid × List Tid)) (vars : List Bap.Var) (hnd : vars.Nodup)
    (pending : Std.HashMap Tid (List Phi)) (hp : ∀ t, ∀ phi ∈ pending.getD t [], phi.var ∉ vars) :
    insertAllPhis (applyPending pending cfg) frontier vars =
      applyPending (vars.foldl (init := pending) fun pending var =>
        let joins := (joinsAux (assocTable frontier) (cfg.blocks.length * 2 + 1) ((definersOf cfg.blocks).getD var []).reverse {} []).reverse
        joins.foldl (fun pending join => addPhi pending (phiAt cfg.graph var join)) pending) cfg := by
  induction vars generalizing pending with
  | nil => rfl
  | cons var rest ih =>
    obtain ⟨hv, hr⟩ := List.nodup_cons.1 hnd
    simp only [List.foldl_cons]
    rw [insertAllPhis]
    have hdefs : ((applyPending pending cfg).blocks.filterMap fun blk => if blk.defines var then some blk.tid else none) =
        ((definersOf cfg.blocks).getD var []).reverse := by
      rw [definersOf_get]
      simp only [applyPending]
      generalize cfg.blocks = l
      induction l with
      | nil => rfl
      | cons b bs ih =>
        simp only [List.map_cons, List.filterMap_cons, foldr_placePhi_tid, ih]
        rw [defines_foldr _ _ _ fun phi hphi e => hp _ phi hphi (e ▸ List.mem_cons_self)]
    have hlen : (applyPending pending cfg).blocks.length = cfg.blocks.length := by simp [applyPending]
    have htable : ∀ t, (Assoc.get t frontier).getD [] = (assocTable frontier).getD t [] := by
      intro t
      rw [Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?, assocTable_get]
    simp only [hdefs, hlen]
    have hq := insertPhisForVar_eq (applyPending pending cfg) var frontier (assocTable frontier) htable
      (cfg.blocks.length * 2 + 1) ((definersOf cfg.blocks).getD var []).reverse [] [] (applyPending pending cfg) {} rfl (by simp)
    rw [hq, ← applyPending_joins]
    apply ih hr
    intro t phi hphi
    have hgo : ∀ (joins : List Tid) (table : Std.HashMap Tid (List Phi)),
        (∀ phi ∈ table.getD t [], phi.var ∉ rest) →
        ∀ phi ∈ (joins.foldl (fun pending join => addPhi pending (phiAt cfg.graph var join)) table).getD t [], phi.var ∉ rest := by
      intro joins
      induction joins with
      | nil => exact fun _ h => h
      | cons j js ih =>
        intro table htable
        apply ih
        intro phi hphi
        simp only [addPhi, Std.HashMap.getD_insert] at hphi
        split at hphi
        · rename_i he
          have he' : (phiAt cfg.graph var j).tid = t := by simpa using he
          rw [he'] at hphi
          rcases List.mem_cons.1 hphi with rfl | hphi
          · exact hv
          · exact htable phi hphi
        · exact htable phi hphi
    exact hgo _ _ (fun phi hphi hm => hp t phi hphi (List.mem_cons_of_mem _ hm)) phi hphi

/-- `insertAllPhis` from tables, for different variables. -/
private def insertAllPhisFast (cfg : Cfg) (frontier : List (Tid × List Tid)) (vars : List Bap.Var) : Cfg :=
  let frontierTable := assocTable frontier
  let definers := definersOf cfg.blocks
  let predecessors := Bap.Graph.Fast.predecessorTable cfg.graph
  let fuel := cfg.blocks.length * 2 + 1
  applyPending (vars.foldl (init := {}) fun pending var =>
    let joins := (joinsAux frontierTable fuel (definers.getD var []).reverse {} []).reverse
    joins.foldl (fun pending join =>
      addPhi pending ⟨join, var, (dedup (predecessors.getD join [])).map fun pred => (pred, .var var)⟩) pending) cfg

private theorem insertAllPhis_eq_fast (cfg : Cfg) (frontier : List (Tid × List Tid)) (vars : List Bap.Var) (hnd : vars.Nodup) :
    insertAllPhis cfg frontier vars = insertAllPhisFast cfg frontier vars := by
  have hstart : applyPending {} cfg = cfg := by
    have hm : ∀ l : List Blk, (l.map fun blk => (({} : Std.HashMap Tid (List Phi)).getD blk.tid []).foldr placePhi blk) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons b bs _ => simp
    simp only [applyPending, hm]
  have h := insertAllPhis_eq cfg frontier vars hnd {} (by simp)
  rw [hstart] at h
  rw [h]
  simp only [insertAllPhisFast, phiAt]
  have hpred : ∀ join, dedup ((Bap.Graph.Fast.predecessorTable cfg.graph).getD join []) = Bap.Graph.predecessors cfg.graph join :=
    Bap.Graph.Fast.predecessors_eq cfg.graph
  simp only [hpred]

end FastPhis

/-- Stacks are per exact variable, the name in force first: `x.1` and `x.2` of a versioned input are different variables with
their own reaching definitions. Counters are per base, so issued names never collide across them. -/
structure RenameState where
  stacks : List (Bap.Var × List Bap.Var) := []
  counters : List (Bap.Var × Nat) := []
  deriving Repr

private def newName (var : Bap.Var) (state : RenameState) : Bap.Var × RenameState :=
  let counter := (Assoc.get var.base state.counters).getD 1
  let renamed := var.version counter
  let stack := (Assoc.get var state.stacks).getD []
  (renamed, {
    stacks := Assoc.put var (renamed :: stack) state.stacks
    counters := Assoc.put var.base (counter + 1) state.counters
  })

/-- The name a read of `var` sees: the variable itself until something in scope assigns it. -/
private def topName (var : Bap.Var) (state : RenameState) : Bap.Var :=
  match Assoc.get var state.stacks with
  | some stack => stack.head?.getD var
  | none => var

private def replacements (state : RenameState) : List (Bap.Var × Bil.Exp) :=
  state.stacks.filterMap fun entry => entry.2.head?.map fun var => (entry.1, .var var)

private def renameExp (state : RenameState) (exp : Bil.Exp) : Bil.Exp :=
  Bil.substitute (replacements state) exp

private def renamePhis : List Phi → RenameState → List Phi × RenameState
  | [], state => ([], state)
  | phi :: rest, state =>
    let (var, state) := newName phi.var state
    let (rest, state) := renamePhis rest state
    ({ phi with var := var } :: rest, state)

private def renameDefs : List Def → RenameState → List Def × RenameState
  | [], state => ([], state)
  | defn :: rest, state =>
    let rhs := renameExp state defn.rhs
    let (var, state) := newName defn.var state
    let (rest, state) := renameDefs rest state
    ({ defn with var := var, rhs := rhs } :: rest, state)

private def updatePhiInputs (source successor : Tid) (state : RenameState) (cfg : Cfg) : Cfg :=
  cfg.updateBlock successor fun blk =>
    { blk with phis := blk.phis.map fun phi =>
      { phi with values := phi.values.map fun input =>
        if input.1 = source then (source, renameExp state input.2) else input
      }
    }

private def popVar (var : Bap.Var) (state : RenameState) : RenameState :=
  { state with stacks := state.stacks.map fun entry =>
    if entry.1 = var then (entry.1, entry.2.tail) else entry
  }

/-- Undoes one push per listed name, so repeated names are popped repeatedly. -/
private def popVars (vars : List Bap.Var) (state : RenameState) : RenameState :=
  vars.foldl (fun state var => popVar var state) state

private def renameBlock (idom : List (Tid × Tid)) : Nat → Tid → Cfg → RenameState → Cfg × RenameState
  | 0, _, cfg, state => (cfg, state)
  | fuel + 1, tid, cfg, state =>
    match cfg.block tid with
    | none => (cfg, state)
    | some block =>
      let pushed := block.phis.map (·.var) ++ block.defs.map (·.var)
      let (phis, state) := renamePhis block.phis state
      let (defs, state) := renameDefs block.defs state
      let jmps := block.jmps.map (Jmp.mapExp (renameExp state))
      let cfg := cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps }
      let cfg := (cfg.successors tid).foldl (fun cfg successor => updatePhiInputs tid successor state cfg) cfg
      let children := (idom.filter fun entry => entry.2 = tid).map Prod.fst
      let (cfg, state) := children.foldl (init := (cfg, state)) fun current child =>
        renameBlock idom fuel child current.1 current.2
      (cfg, popVars pushed state)

/-- Issued versions start above every version the input already uses, so a new name never coincides
with a variable of the input. -/
private def initialState (blocks : List Blk) : RenameState :=
  { counters := (blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).foldl (init := []) fun counters var =>
      if var.index = 0 then counters
      else Assoc.put var.base (max ((Assoc.get var.base counters).getD 1) (var.index + 1)) counters }

/-- `toSsa` names each version of a variable, so the list of variables to place phis for can be long. -/
def toSsa (sub : Sub) : Sub :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let state := initialState cfg.blocks
  let cfg := insertAllPhis cfg frontier (cfg.blocks.flatMap Blk.definedVars).eraseDups
  let (cfg, _) := renameBlock idom (cfg.blocks.length + 1) cfg.start cfg state
  { sub with blks := sub.blks.filterMap fun blk => cfg.block blk.tid }

private def toSsaFast (sub : Sub) : Sub :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let state := initialState cfg.blocks
  let cfg := insertAllPhisFast cfg frontier (Bap.Graph.Fast.dedup (cfg.blocks.flatMap Blk.definedVars))
  let (cfg, _) := renameBlock idom (cfg.blocks.length + 1) cfg.start cfg state
  { sub with blks := sub.blks.filterMap fun blk => cfg.block blk.tid }

/-! ### Renaming with tables

`renameBlock` looks for blocks in a list, changes them by going over the list, and goes over the edges and the dominator tree for
each block, and every expression makes a list of all the names in force. The same things with tables. -/

section FastRename

open Bap.Graph.Fast (dedup groupBy groupBy_getD successorTable successors_eq assocTable assocTable_get)

private theorem assoc_get_cons {α β : Type} [DecidableEq α] (key k : α) (v : β) (rest : List (α × β)) :
    Assoc.get key ((k, v) :: rest) = if key = k then some v else Assoc.get key rest := by
  by_cases h : key = k
  · simp [Assoc.get, h]
  · have : (key == k) = false := by simpa using h
    simp [Assoc.get, List.lookup, this, h]

private theorem assoc_get_filter {α β : Type} [DecidableEq α] (key target : α) (entries : List (α × β)) :
    Assoc.get key (entries.filter fun entry => entry.1 != target) =
      if key = target then none else Assoc.get key entries := by
  induction entries with
  | nil => simp [Assoc.get]
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    by_cases ht : k = target
    · subst ht
      by_cases hk : key = k
      · simpa [hk] using ih
      · simpa [hk, assoc_get_cons] using ih
    · have hne : (k != target) = true := by simpa using ht
      simp only [List.filter_cons, hne, ↓reduceIte, assoc_get_cons, ih]
      by_cases hk : key = k
      · subst hk
        simp [ht]
      · simp [hk]

private theorem assoc_get_put {α β : Type} [DecidableEq α] (key target : α) (value : β) (entries : List (α × β)) :
    Assoc.get key (Assoc.put target value entries) = if key = target then some value else Assoc.get key entries := by
  simp only [Assoc.put, assoc_get_cons, assoc_get_filter]
  by_cases h : key = target <;> simp [h]

private theorem assoc_mem_iff {α β : Type} [DecidableEq α] {entries : List (α × β)} (hnd : (entries.map Prod.fst).Nodup) :
    ∀ (key : α) (value : β), (key, value) ∈ entries ↔ Assoc.get key entries = some value := by
  induction entries with
  | nil => simp [Assoc.get]
  | cons head tail ih =>
    obtain ⟨k, v⟩ := head
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2⟩ := hnd
    intro key value
    rw [assoc_get_cons, List.mem_cons, ih h2]
    by_cases hk : key = k
    · subst hk
      have hnone : Assoc.get key tail = none := by
        cases hg : Assoc.get key tail with
        | none => rfl
        | some w =>
          exact (h1 (List.mem_map.2 ⟨(key, w), (ih h2 key w).2 hg, rfl⟩)).elim
      simp [hnone, eq_comm]
    · simp [hk]

/-- `freshVersion` looks at the indices of the variables to avoid and not at how they are listed. -/
private theorem freshVersion_congr (var : Bap.Var) {left right : List Bap.Var} (h : ∀ x, x ∈ left ↔ x ∈ right) :
    Bil.freshVersion var left = Bil.freshVersion var right := by
  have hbound : ∀ (l : List Bap.Var) (n : Nat), n ≤ l.foldl (fun index other => max index (other.index + 1)) n ∧
      (∀ x ∈ l, x.index + 1 ≤ l.foldl (fun index other => max index (other.index + 1)) n) ∧
      (l.foldl (fun index other => max index (other.index + 1)) n = n ∨
        ∃ x ∈ l, l.foldl (fun index other => max index (other.index + 1)) n = x.index + 1) := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro n
      obtain ⟨h1, h2, h3⟩ := ih (max n (a.index + 1))
      simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
      refine ⟨by omega, ⟨by omega, h2⟩, ?_⟩
      rcases h3 with h3 | ⟨x, hx, h3⟩
      · omega
      · exact Or.inr (Or.inr ⟨x, hx, h3⟩)
  simp only [Bil.freshVersion]
  congr 1
  obtain ⟨l1, l2, l3⟩ := hbound left (var.index + 1)
  obtain ⟨r1, r2, r3⟩ := hbound right (var.index + 1)
  apply Nat.le_antisymm
  · rcases l3 with l3 | ⟨x, hx, l3⟩
    · omega
    · have := r2 x ((h x).1 hx)
      omega
  · rcases r3 with r3 | ⟨x, hx, r3⟩
    · omega
    · have := l2 x ((h x).2 hx)
      omega

/-- With its keys different, the order of a list of replacements doesn't matter. -/
private theorem substitute_congr (exp : Bil.Exp) : ∀ {left right : List (Bap.Var × Bil.Exp)},
    (left.map Prod.fst).Nodup → (right.map Prod.fst).Nodup → (∀ k, Assoc.get k left = Assoc.get k right) →
    Bil.substitute left exp = Bil.substitute right exp := by
  induction exp with
  | int value => intros; rfl
  | var var => intro _ _ _ _ h; simp only [Bil.substitute, h]
  | load m a e s ihm iha => intro _ _ h1 h2 h; simp only [Bil.substitute, ihm h1 h2 h, iha h1 h2 h]
  | store m a v e s ihm iha ihv => intro _ _ h1 h2 h; simp only [Bil.substitute, ihm h1 h2 h, iha h1 h2 h, ihv h1 h2 h]
  | bin op l r ihl ihr => intro _ _ h1 h2 h; simp only [Bil.substitute, ihl h1 h2 h, ihr h1 h2 h]
  | un op v ih => intro _ _ h1 h2 h; simp only [Bil.substitute, ih h1 h2 h]
  | cast k w v ih => intro _ _ h1 h2 h; simp only [Bil.substitute, ih h1 h2 h]
  | ite c y n ihc ihy ihn => intro _ _ h1 h2 h; simp only [Bil.substitute, ihc h1 h2 h, ihy h1 h2 h, ihn h1 h2 h]
  | extract hi lo v ih => intro _ _ h1 h2 h; simp only [Bil.substitute, ih h1 h2 h]
  | concat l r ihl ihr => intro _ _ h1 h2 h; simp only [Bil.substitute, ihl h1 h2 h, ihr h1 h2 h]
  | unknown m t => intros; rfl
  | letIn var value body ihv ihb =>
    intro left right h1 h2 h
    have hfilter : ∀ {l : List (Bap.Var × Bil.Exp)}, (l.map Prod.fst).Nodup →
        ((l.filter fun r => r.1 != var).map Prod.fst).Nodup := fun hl =>
      (List.Sublist.map _ List.filter_sublist).nodup hl
    have hi1 := hfilter h1
    have hi2 := hfilter h2
    have hget : ∀ k, Assoc.get k (left.filter fun r => r.1 != var) = Assoc.get k (right.filter fun r => r.1 != var) := by
      intro k
      rw [assoc_get_filter, assoc_get_filter, h]
    have hmem : ∀ p, p ∈ left.filter (fun r => r.1 != var) ↔ p ∈ right.filter (fun r => r.1 != var) := by
      rintro ⟨k, v⟩
      rw [assoc_mem_iff hi1, assoc_mem_iff hi2, hget]
    have hany : ∀ P : Bap.Var × Bil.Exp → Bool, (left.filter fun r => r.1 != var).any P = (right.filter fun r => r.1 != var).any P := by
      intro P
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, hmem]
    have hnotin : ∀ {l : List (Bap.Var × Bil.Exp)}, var ∉ (l.filter fun r => r.1 != var).map Prod.fst := by
      intro l hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      have := (List.mem_filter.1 hp).2
      simp [hpv] at this
    simp only [Bil.substitute, hany, ihv h1 h2 h]
    split
    · have hfresh : Bil.freshVersion var ((left.filter fun r => r.1 != var).flatMap (fun r => Bil.freeVars r.2) ++ Bil.freeVars body) =
          Bil.freshVersion var ((right.filter fun r => r.1 != var).flatMap (fun r => Bil.freeVars r.2) ++ Bil.freeVars body) := by
        apply freshVersion_congr
        intro x
        simp only [List.mem_append, List.mem_flatMap, hmem]
      rw [hfresh]
      congr 1
      apply ihb
      · rw [List.map_cons]
        exact List.nodup_cons.2 ⟨hnotin, hi1⟩
      · rw [List.map_cons]
        exact List.nodup_cons.2 ⟨hnotin, hi2⟩
      · intro k
        rw [assoc_get_cons, assoc_get_cons, hget]
    · congr 1
      exact ihb hi1 hi2 hget

private structure FastState where
  stacks : Std.HashMap Bap.Var (List Bap.Var) := {}
  counters : Std.HashMap Bap.Var Nat := {}

private structure SameState (state : RenameState) (fast : FastState) : Prop where
  stacks : ∀ k, Assoc.get k state.stacks = fast.stacks.get? k
  counters : ∀ k, Assoc.get k state.counters = fast.counters.get? k
  nodup : (state.stacks.map Prod.fst).Nodup

private def newNameF (var : Bap.Var) (fast : FastState) : Bap.Var × FastState :=
  let counter := fast.counters.getD var.base 1
  let renamed := var.version counter
  let stack := fast.stacks.getD var []
  (renamed, { stacks := fast.stacks.insert var (renamed :: stack), counters := fast.counters.insert var.base (counter + 1) })

private theorem table_get_getD {α : Type} {table : Std.HashMap Bap.Var α} (k : Bap.Var) (d : α) :
    table.getD k d = (table.get? k).getD d := by
  rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.get?_eq_getElem?]

private theorem table_get_insert {α : Type} (table : Std.HashMap Bap.Var α) (k target : Bap.Var) (value : α) :
    (table.insert target value).get? k = if k = target then some value else table.get? k := by
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases h : k = target
  · simp [h]
  · have hq : (target == k) = false := by simpa using fun e : target = k => h e.symm
    simp [h, hq]

private theorem nodup_put {α β : Type} [DecidableEq α] (key : α) (value : β) {entries : List (α × β)}
    (h : (entries.map Prod.fst).Nodup) : ((Assoc.put key value entries).map Prod.fst).Nodup := by
  simp only [Assoc.put, List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup h⟩
  intro hm
  obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
  have := (List.mem_filter.1 hp).2
  simp [hpv] at this

private theorem newNameF_same {state : RenameState} {fast : FastState} (h : SameState state fast) (var : Bap.Var) :
    (newName var state).1 = (newNameF var fast).1 ∧ SameState (newName var state).2 (newNameF var fast).2 := by
  have hc : (Assoc.get var.base state.counters).getD 1 = fast.counters.getD var.base 1 := by
    rw [h.counters, table_get_getD]
  have hs : (Assoc.get var state.stacks).getD [] = fast.stacks.getD var [] := by
    rw [h.stacks, table_get_getD]
  simp only [newName, newNameF, hc, hs]
  refine ⟨trivial, ⟨?_, ?_, nodup_put _ _ h.nodup⟩⟩
  · intro k
    rw [assoc_get_put, table_get_insert, h.stacks]
  · intro k
    rw [assoc_get_put, table_get_insert, h.counters]

/-- What `replacements` has in it, from the table. -/
private def tableReplacements (fast : FastState) : List (Bap.Var × Bil.Exp) :=
  fast.stacks.toList.filterMap fun entry => entry.2.head?.map fun var => (entry.1, .var var)

/-- `renameExp`. What is under a `let` can capture, which is rare: that goes by a list. -/
private def substF (fast : FastState) : Bil.Exp → Bil.Exp
  | .int value => .int value
  | .var var =>
    match fast.stacks.getD var [] with
    | top :: _ => .var top
    | [] => .var var
  | .load memory address endian size => .load (substF fast memory) (substF fast address) endian size
  | .store memory address value endian size =>
    .store (substF fast memory) (substF fast address) (substF fast value) endian size
  | .bin op left right => .bin op (substF fast left) (substF fast right)
  | .un op value => .un op (substF fast value)
  | .cast kind width value => .cast kind width (substF fast value)
  | .letIn var value body => Bil.substitute (tableReplacements fast) (.letIn var value body)
  | .ite condition yes no => .ite (substF fast condition) (substF fast yes) (substF fast no)
  | .extract high low value => .extract high low (substF fast value)
  | .concat left right => .concat (substF fast left) (substF fast right)
  | .unknown message typ => .unknown message typ

private theorem filterMap_keys_nodup {entries : List (Bap.Var × List Bap.Var)} (h : (entries.map Prod.fst).Nodup) :
    ((entries.filterMap fun entry => entry.2.head?.map fun var => (entry.1, (.var var : Bil.Exp))).map Prod.fst).Nodup := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.filterMap_cons]
    cases hf : head.2.head? with
    | none => simpa using ih h2
    | some v =>
      simp only [Option.map_some, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h2⟩
      intro hm
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hm
      obtain ⟨q, hq, hqv⟩ := List.mem_filterMap.1 hp
      obtain ⟨w, _, hw⟩ := Option.map_eq_some_iff.1 hqv
      subst hw
      exact h1 (List.mem_map.2 ⟨q, hq, hpv⟩)

private theorem toList_keys_nodup (m : Std.HashMap Bap.Var (List Bap.Var)) : (m.toList.map Prod.fst).Nodup :=
  List.pairwise_map.2 ((Std.HashMap.distinct_keys_toList (m := m)).imp fun h => by simpa using h)

private theorem get_filterMap_heads {entries : List (Bap.Var × List Bap.Var)} (h : (entries.map Prod.fst).Nodup) (k : Bap.Var) :
    Assoc.get k (entries.filterMap fun entry => entry.2.head?.map fun var => (entry.1, (.var var : Bil.Exp))) =
      ((Assoc.get k entries).bind List.head?).map fun var => (.var var : Bil.Exp) := by
  induction entries with
  | nil => simp [Assoc.get]
  | cons head tail ih =>
    obtain ⟨a, b⟩ := head
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.filterMap_cons]
    rw [assoc_get_cons k a]
    have hih := ih h2
    by_cases hk : k = a
    · subst hk
      have hnone : Assoc.get k tail = none := by
        cases hg : Assoc.get k tail with
        | none => rfl
        | some w => exact (h1 (List.mem_map.2 ⟨(k, w), (assoc_mem_iff h2 k w).2 hg, rfl⟩)).elim
      rw [hnone] at hih
      cases hh : b.head? with
      | none =>
        simpa [hh] using hih
      | some v =>
        simp [assoc_get_cons, hh]
    · simp only [hk, ↓reduceIte]
      cases hh : b.head? with
      | none => simpa [hh] using hih
      | some v =>
        simp only [Option.map_some]
        rw [assoc_get_cons k a]
        simpa [hk] using hih

private theorem get_tableReplacements (fast : FastState) (k : Bap.Var) :
    Assoc.get k (tableReplacements fast) = ((fast.stacks.get? k).bind List.head?).map fun var => (.var var : Bil.Exp) := by
  have hnd := toList_keys_nodup fast.stacks
  rw [tableReplacements, get_filterMap_heads hnd]
  congr 2
  cases hg : fast.stacks.get? k with
  | none =>
    cases hl : Assoc.get k fast.stacks.toList with
    | none => rfl
    | some w =>
      have hm := (assoc_mem_iff hnd k w).2 hl
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hm
      rw [Std.HashMap.get?_eq_getElem?] at hg
      rw [hg] at hm
      cases hm
  | some w =>
    apply (assoc_mem_iff hnd k w).1
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
    rwa [Std.HashMap.get?_eq_getElem?] at hg

private theorem get_replacements {state : RenameState} {fast : FastState} (h : SameState state fast) (k : Bap.Var) :
    Assoc.get k (replacements state) = ((fast.stacks.get? k).bind List.head?).map fun var => (.var var : Bil.Exp) := by
  rw [replacements, get_filterMap_heads h.nodup, h.stacks]

private theorem substF_eq {state : RenameState} {fast : FastState} (h : SameState state fast) (exp : Bil.Exp) :
    substF fast exp = renameExp state exp := by
  simp only [renameExp]
  induction exp with
  | int value => rfl
  | var var =>
    simp only [substF, Bil.substitute, get_replacements h, table_get_getD]
    cases fast.stacks.get? var with
    | none => rfl
    | some l => cases l <;> rfl
  | load m a e s ihm iha => simp only [substF, Bil.substitute, ihm, iha]
  | store m a v e s ihm iha ihv => simp only [substF, Bil.substitute, ihm, iha, ihv]
  | bin op l r ihl ihr => simp only [substF, Bil.substitute, ihl, ihr]
  | un op v ih => simp only [substF, Bil.substitute, ih]
  | cast k w v ih => simp only [substF, Bil.substitute, ih]
  | ite c y n ihc ihy ihn => simp only [substF, Bil.substitute, ihc, ihy, ihn]
  | extract hi lo v ih => simp only [substF, Bil.substitute, ih]
  | concat l r ihl ihr => simp only [substF, Bil.substitute, ihl, ihr]
  | unknown m t => rfl
  | letIn var value body _ _ =>
    simp only [substF]
    apply substitute_congr
    · exact filterMap_keys_nodup (toList_keys_nodup _)
    · exact filterMap_keys_nodup h.nodup
    · intro k
      rw [get_tableReplacements, get_replacements h]

private theorem substF_fun {state : RenameState} {fast : FastState} (h : SameState state fast) :
    substF fast = renameExp state := funext (substF_eq h)

private def renamePhisF : List Phi → FastState → List Phi × FastState
  | [], fast => ([], fast)
  | phi :: rest, fast =>
    let (var, fast) := newNameF phi.var fast
    let (rest, fast) := renamePhisF rest fast
    ({ phi with var := var } :: rest, fast)

private theorem renamePhisF_same (phis : List Phi) {state : RenameState} {fast : FastState} (h : SameState state fast) :
    (renamePhis phis state).1 = (renamePhisF phis fast).1 ∧ SameState (renamePhis phis state).2 (renamePhisF phis fast).2 := by
  induction phis generalizing state fast with
  | nil => exact ⟨rfl, h⟩
  | cons phi rest ih =>
    obtain ⟨h1, h2⟩ := newNameF_same h phi.var
    obtain ⟨h3, h4⟩ := ih h2
    simp only [renamePhis, renamePhisF]
    rw [← h1]
    simp only [h3]
    exact ⟨trivial, h4⟩

private def renameDefsF : List Def → FastState → List Def × FastState
  | [], fast => ([], fast)
  | defn :: rest, fast =>
    let rhs := substF fast defn.rhs
    let (var, fast) := newNameF defn.var fast
    let (rest, fast) := renameDefsF rest fast
    ({ defn with var := var, rhs := rhs } :: rest, fast)

private theorem renameDefsF_same (defs : List Def) {state : RenameState} {fast : FastState} (h : SameState state fast) :
    (renameDefs defs state).1 = (renameDefsF defs fast).1 ∧ SameState (renameDefs defs state).2 (renameDefsF defs fast).2 := by
  induction defs generalizing state fast with
  | nil => exact ⟨rfl, h⟩
  | cons defn rest ih =>
    obtain ⟨h1, h2⟩ := newNameF_same h defn.var
    obtain ⟨h3, h4⟩ := ih h2
    simp only [renameDefs, renameDefsF, substF_eq h]
    rw [← h1]
    simp only [h3]
    exact ⟨trivial, h4⟩

private def popVarF (fast : FastState) (var : Bap.Var) : FastState :=
  match fast.stacks.get? var with
  | some stack => { fast with stacks := fast.stacks.insert var stack.tail }
  | none => fast

private theorem get_map_tail {entries : List (Bap.Var × List Bap.Var)} (var k : Bap.Var) :
    Assoc.get k (entries.map fun entry => if entry.1 = var then (entry.1, entry.2.tail) else entry) =
      if k = var then (Assoc.get k entries).map List.tail else Assoc.get k entries := by
  induction entries with
  | nil => simp [Assoc.get]
  | cons head tail ih =>
    obtain ⟨a, b⟩ := head
    simp only [List.map_cons]
    by_cases ha : a = var
    · subst ha
      simp only [↓reduceIte, assoc_get_cons, ih]
      by_cases hk : k = a <;> simp [hk]
    · simp only [ha, ↓reduceIte, assoc_get_cons, ih]
      by_cases hk : k = a
      · subst hk
        simp [ha]
      · simp [hk]

private theorem popVarF_same {state : RenameState} {fast : FastState} (h : SameState state fast) (var : Bap.Var) :
    SameState (popVar var state) (popVarF fast var) := by
  have hkeys : ((popVar var state).stacks.map Prod.fst) = state.stacks.map Prod.fst := by
    simp only [popVar, List.map_map]
    apply List.map_congr_left
    intro entry _
    simp only [Function.comp]
    split <;> rfl
  refine ⟨?_, ?_, hkeys ▸ h.nodup⟩
  · intro k
    have hl : Assoc.get k (popVar var state).stacks =
        if k = var then (Assoc.get k state.stacks).map List.tail else Assoc.get k state.stacks := get_map_tail var k
    rw [hl, h.stacks]
    unfold popVarF
    cases hg : fast.stacks.get? var with
    | none =>
      by_cases hk : k = var
      · subst hk
        simp only [↓reduceIte, hg]
        rfl
      · simp [hk]
    | some stack =>
      simp only [table_get_insert]
      by_cases hk : k = var
      · subst hk
        simp only [↓reduceIte, hg]
        rfl
      · simp [hk]
  · intro k
    have hc : (popVar var state).counters = state.counters := rfl
    rw [hc, h.counters]
    unfold popVarF
    cases fast.stacks.get? var <;> rfl

private theorem popVarsF_same (vars : List Bap.Var) {state : RenameState} {fast : FastState} (h : SameState state fast) :
    SameState (popVars vars state) (vars.foldl popVarF fast) := by
  induction vars generalizing state fast with
  | nil => exact h
  | cons v vs ih => exact ih (popVarF_same h v)

private abbrev BlockTable := Std.HashMap Tid Blk

private def SameBlocks (cfg : Cfg) (table : BlockTable) : Prop := ∀ t, cfg.block t = table.get? t

private theorem block_update (cfg : Cfg) (tid : Tid) (f : Blk → Blk) (hf : ∀ blk, (f blk).tid = blk.tid) (t : Tid) :
    (cfg.updateBlock tid f).block t = if t = tid then (cfg.block t).map f else cfg.block t := by
  simp only [Cfg.block, Cfg.updateBlock]
  generalize cfg.blocks = l
  induction l with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hb : b.tid = tid
    · simp only [hb, ↓reduceIte, hf]
      by_cases ht : tid = t
      · subst ht
        simp
      · have ht' : t ≠ tid := fun e => ht e.symm
        simpa [ht, ht'] using ih
    · simp only [hb, ↓reduceIte]
      by_cases ht : b.tid = t
      · subst ht
        by_cases he : b.tid = tid
        · exact (hb he).elim
        · simp [hb]
      · simp only [ht, decide_false]
        exact ih

private def updateF (tid : Tid) (f : Blk → Blk) (table : BlockTable) : BlockTable :=
  match table.get? tid with
  | some blk => table.insert tid (f blk)
  | none => table

private theorem updateF_same {cfg : Cfg} {table : BlockTable} (h : SameBlocks cfg table) (tid : Tid) (f : Blk → Blk)
    (hf : ∀ blk, (f blk).tid = blk.tid) : SameBlocks (cfg.updateBlock tid f) (updateF tid f table) := by
  intro t
  have hins : ∀ (v : Blk) (m : BlockTable), (m.insert tid v).get? t = if t = tid then some v else m.get? t := by
    intro v m
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    by_cases ht : t = tid
    · simp [ht]
    · have hq : (tid == t) = false := by simpa using fun e : tid = t => ht e.symm
      simp [ht, hq]
  rw [block_update _ _ _ hf, h t]
  unfold updateF
  by_cases ht : t = tid
  · subst ht
    cases hg : table.get? t with
    | none => rw [hg]; simp
    | some b =>
      simp only [↓reduceIte, hins]
      rfl
  · cases table.get? tid with
    | none => simp only [ht, ↓reduceIte]
    | some b => simp only [ht, ↓reduceIte, hins]

private def inputsF (source : Tid) (fast : FastState) (blk : Blk) : Blk :=
  { blk with phis := blk.phis.map fun phi =>
    { phi with values := phi.values.map fun input =>
      if input.1 = source then (source, substF fast input.2) else input } }

private def renameBlockF (children successors : Std.HashMap Tid (List Tid)) : Nat → Tid → BlockTable → FastState → BlockTable × FastState
  | 0, _, table, fast => (table, fast)
  | fuel + 1, tid, table, fast =>
    match table.get? tid with
    | none => (table, fast)
    | some block =>
      let pushed := block.phis.map (·.var) ++ block.defs.map (·.var)
      let (phis, fast) := renamePhisF block.phis fast
      let (defs, fast) := renameDefsF block.defs fast
      let jmps := block.jmps.map (Jmp.mapExp (substF fast))
      let table := table.insert tid { block with phis := phis, defs := defs, jmps := jmps }
      let table := (dedup (successors.getD tid [])).foldl (fun table successor => updateF successor (inputsF tid fast) table) table
      let (table, fast) := (children.getD tid []).foldl (init := (table, fast)) fun current child =>
        renameBlockF children successors fuel child current.1 current.2
      (table, pushed.foldl popVarF fast)

private theorem renameBlock_graph (idom : List (Tid × Tid)) (fuel : Nat) (tid : Tid) (cfg : Cfg) (state : RenameState) :
    (renameBlock idom fuel tid cfg state).1.graph = cfg.graph := by
  induction fuel generalizing tid cfg state with
  | zero => rfl
  | succ fuel ih =>
    simp only [renameBlock]
    split
    · rfl
    · have hfold : ∀ (l : List Tid) (c : Cfg) (s : RenameState),
          (l.foldl (init := (c, s)) fun current child => renameBlock idom fuel child current.1 current.2).1.graph = c.graph := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons a as iha =>
          intro c s
          simp only [List.foldl_cons]
          rw [iha, ih]
      have hsucc : ∀ (l : List Tid) (c : Cfg) (t : Tid) (s : RenameState),
          (l.foldl (fun cfg successor => updatePhiInputs t successor s cfg) c).graph = c.graph := by
        intro l
        induction l with
        | nil => intro _ _ _; rfl
        | cons a as iha => intro c t s; simp only [List.foldl_cons]; rw [iha]; rfl
      dsimp only
      rw [hfold, hsucc]
      rfl

private theorem renameBlockF_same (idom : List (Tid × Tid)) (children successors : Std.HashMap Tid (List Tid))
    (hchildren : ∀ t, children.getD t [] = (idom.filter fun entry => entry.2 = t).map Prod.fst)
    (graph : Bap.Graph.Graph Tid)
    (hsucc : ∀ t, dedup (successors.getD t []) = Bap.Graph.successors graph t) (fuel : Nat) (tid : Tid)
    {cfg : Cfg} {state : RenameState} {table : BlockTable} {fast : FastState}
    (hg : cfg.graph = graph) (hb : SameBlocks cfg table) (hs : SameState state fast) :
    SameBlocks (renameBlock idom fuel tid cfg state).1 (renameBlockF children successors fuel tid table fast).1 ∧
      SameState (renameBlock idom fuel tid cfg state).2 (renameBlockF children successors fuel tid table fast).2 := by
  induction fuel generalizing tid cfg state table fast with
  | zero => exact ⟨hb, hs⟩
  | succ fuel ih =>
    simp only [renameBlock, renameBlockF, hb tid]
    cases htb : table.get? tid with
    | none => exact ⟨hb, hs⟩
    | some block =>
      dsimp only
      obtain ⟨hp1, hp2⟩ := renamePhisF_same block.phis hs
      obtain ⟨hd1, hd2⟩ := renameDefsF_same block.defs hp2
      rw [← hp1, ← hd1]
      generalize hsp : renamePhis block.phis state = sp at hp2 hd1 hd2 ⊢
      generalize hfp : renamePhisF block.phis fast = fp at hp2 hd1 hd2 ⊢
      obtain ⟨phis, s1⟩ := sp
      obtain ⟨phis', f1⟩ := fp
      dsimp only at hp2 hd1 hd2 ⊢
      generalize hsd : renameDefs block.defs s1 = sd at hd1 hd2 ⊢
      generalize hfd : renameDefsF block.defs f1 = fd at hd1 hd2 ⊢
      obtain ⟨defs, s2⟩ := sd
      obtain ⟨defs', f2⟩ := fd
      dsimp only at hd2 ⊢
      rw [substF_fun hd2]
      generalize hj : block.jmps.map (Jmp.mapExp (renameExp s2)) = jmps
      have hfirst : SameBlocks (cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps })
          (table.insert tid { block with phis := phis, defs := defs, jmps := jmps }) := by
        have := updateF_same hb tid (fun block => { block with phis := phis, defs := defs, jmps := jmps }) (fun _ => rfl)
        simpa only [updateF, htb] using this
      rw [hsucc, ← hg]
      have hfoldS : ∀ (l : List Tid) (c : Cfg) (t : BlockTable), SameBlocks c t →
          SameBlocks (l.foldl (fun cfg successor => updatePhiInputs tid successor s2 cfg) c)
            (l.foldl (fun table successor => updateF successor (inputsF tid f2) table) t) := by
        intro l
        induction l with
        | nil => exact fun _ _ h => h
        | cons a as iha =>
          intro c t h
          simp only [List.foldl_cons]
          apply iha
          have := updateF_same h a (inputsF tid f2) (fun _ => rfl)
          have hfn : inputsF tid f2 = fun blk => { blk with phis := blk.phis.map fun phi =>
              { phi with values := phi.values.map fun input =>
                if input.1 = tid then (tid, renameExp s2 input.2) else input } } := by
            unfold inputsF
            rw [substF_fun hd2]
          rw [hfn] at this ⊢
          exact this
      have hc1 := hfoldS (Bap.Graph.successors cfg.graph tid) _ _ hfirst
      generalize hC : (Cfg.successors (cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps }) tid).foldl
        (fun cfg successor => updatePhiInputs tid successor s2 cfg) (cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps }) = c2
      have hsuccEq : Cfg.successors (cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps }) tid = Bap.Graph.successors cfg.graph tid := rfl
      rw [hsuccEq] at hC
      rw [hC] at hc1
      have hg2 : c2.graph = graph := by
        rw [← hC, ← hg]
        have hsg : ∀ (l : List Tid) (c : Cfg), (l.foldl (fun cfg successor => updatePhiInputs tid successor s2 cfg) c).graph = c.graph := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons a as iha => intro c; simp only [List.foldl_cons]; rw [iha]; rfl
        rw [hsg]
        rfl
      generalize (Bap.Graph.successors cfg.graph tid).foldl (fun table successor => updateF successor (inputsF tid f2) table) _ = t2 at hc1 ⊢
      have hfoldC : ∀ (l : List Tid) (c : Cfg) (s : RenameState) (t : BlockTable) (f : FastState), c.graph = graph → SameBlocks c t → SameState s f →
          SameBlocks (l.foldl (init := (c, s)) fun current child => renameBlock idom fuel child current.1 current.2).1
            (l.foldl (init := (t, f)) fun current child => renameBlockF children successors fuel child current.1 current.2).1 ∧
          SameState (l.foldl (init := (c, s)) fun current child => renameBlock idom fuel child current.1 current.2).2
            (l.foldl (init := (t, f)) fun current child => renameBlockF children successors fuel child current.1 current.2).2 := by
        intro l
        induction l with
        | nil => exact fun _ _ _ _ _ h1 h2 => ⟨h1, h2⟩
        | cons a as iha =>
          intro c s t f h0 h1 h2
          simp only [List.foldl_cons]
          obtain ⟨h3, h4⟩ := ih a h0 h1 h2
          exact iha _ _ _ _ (by rw [renameBlock_graph, h0]) h3 h4
      rw [hchildren]
      obtain ⟨hA, hB⟩ := hfoldC ((idom.filter fun entry => entry.2 = tid).map Prod.fst) c2 s2 t2 f2 hg2 hc1 hd2
      revert hA hB
      generalize (((idom.filter fun entry => entry.2 = tid).map Prod.fst).foldl (init := (c2, s2)) fun current child => renameBlock idom fuel child current.1 current.2) = A
      generalize (((idom.filter fun entry => entry.2 = tid).map Prod.fst).foldl (init := (t2, f2)) fun current child => renameBlockF children successors fuel child current.1 current.2) = B
      obtain ⟨a1, a2⟩ := A
      obtain ⟨b1, b2⟩ := B
      intro hA hB
      exact ⟨hA, popVarsF_same _ hB⟩

private def initialCounters (blocks : List Blk) : Std.HashMap Bap.Var Nat :=
  (blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).foldl (init := {}) fun counters var =>
    if var.index = 0 then counters
    else counters.insert var.base (max (counters.getD var.base 1) (var.index + 1))

private theorem initialCounters_same (blocks : List Blk) :
    SameState (initialState blocks) { counters := initialCounters blocks } := by
  have key : ∀ (l : List Bap.Var) (list : List (Bap.Var × Nat)) (table : Std.HashMap Bap.Var Nat),
      (∀ k, Assoc.get k list = table.get? k) → ∀ k,
      Assoc.get k (l.foldl (init := list) fun counters var =>
        if var.index = 0 then counters
        else Assoc.put var.base (max ((Assoc.get var.base counters).getD 1) (var.index + 1)) counters) =
      (l.foldl (init := table) fun counters var =>
        if var.index = 0 then counters
        else counters.insert var.base (max (counters.getD var.base 1) (var.index + 1))).get? k := by
    intro l
    induction l with
    | nil => exact fun _ _ h k => h k
    | cons a as ih =>
      intro list table h k
      simp only [List.foldl_cons]
      apply ih
      intro k
      split
      · exact h k
      · rw [assoc_get_put, table_get_insert, h, h, table_get_getD]
  refine ⟨fun k => ?_, fun k => ?_, by simp [initialState]⟩
  · simp [initialState]
  · exact key _ [] {} (by simp) k

/-- The block of a tid in a table, and the first one of those is the one a `Cfg` finds. -/
private def tableOfBlocks (blocks : List Blk) : BlockTable := assocTable (blocks.map fun blk => (blk.tid, blk))

private theorem tableOfBlocks_same (cfg : Cfg) : SameBlocks cfg (tableOfBlocks cfg.blocks) := by
  intro t
  simp only [tableOfBlocks, assocTable_get, Cfg.block]
  generalize cfg.blocks = l
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.find?_cons, assoc_get_cons]
    by_cases hb : b.tid = t
    · subst hb
      simp
    · have h1 : ¬ t = b.tid := fun e => hb e.symm
      simp only [hb, decide_false, h1, ↓reduceIte]
      exact ih

private def childTable (idom : List (Tid × Tid)) : Std.HashMap Tid (List Tid) := groupBy (idom.map fun entry => (entry.2, entry.1))

private theorem childTable_getD (idom : List (Tid × Tid)) (t : Tid) :
    (childTable idom).getD t [] = (idom.filter fun entry => entry.2 = t).map Prod.fst := by
  rw [childTable, groupBy_getD, List.filter_map, List.map_map]
  rfl

private def toSsaTables (sub : Sub) : Sub :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let counters := initialCounters cfg.blocks
  let cfg := insertAllPhisFast cfg frontier (Bap.Graph.Fast.dedup (cfg.blocks.flatMap Blk.definedVars))
  let result := renameBlockF (childTable idom) (successorTable cfg.graph) (cfg.blocks.length + 1) cfg.start
    (tableOfBlocks cfg.blocks) { counters := counters }
  { sub with blks := sub.blks.filterMap fun blk => result.1.get? blk.tid }

private theorem toSsaFast_eq_tables : @toSsaFast = @toSsaTables := by
  funext sub
  simp only [toSsaFast, toSsaTables]
  generalize insertAllPhisFast _ _ _ = cfg2
  obtain ⟨h1, _⟩ := renameBlockF_same (Cfg.connected sub).immediateDominators (childTable (Cfg.connected sub).immediateDominators) (successorTable cfg2.graph)
    (childTable_getD _) cfg2.graph (successors_eq cfg2.graph) (cfg2.blocks.length + 1) cfg2.start rfl (tableOfBlocks_same cfg2) (initialCounters_same (Cfg.connected sub).blocks)
  revert h1
  generalize renameBlock _ _ _ _ _ = spec
  generalize renameBlockF _ _ _ _ _ _ = fast
  intro h1
  obtain ⟨c, s⟩ := spec
  have hfun : (fun blk : Blk => c.block blk.tid) = fun blk => fast.1.get? blk.tid := funext fun blk => h1 blk.tid
  simp only [hfun]

end FastRename

@[csimp] private theorem toSsa_eq_fast : @toSsa = @toSsaTables := by
  rw [← toSsaFast_eq_tables]
  funext sub
  simp only [toSsa, toSsaFast, Bap.Graph.Fast.dedup_eq]
  rw [insertAllPhis_eq_fast _ _ _ (Bap.Proofs.Graph.nodup_eraseDups _)]

@[simp] theorem toSsa_tid (sub : Sub) : (toSsa sub).tid = sub.tid := by
  rfl

@[simp] theorem toSsa_name (sub : Sub) : (toSsa sub).name = sub.name := by
  rfl

end Bap.IR
