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

@[csimp] private theorem toSsa_eq_fast : @toSsa = @toSsaFast := by
  funext sub
  simp only [toSsa, toSsaFast, Bap.Graph.Fast.dedup_eq]
  rw [insertAllPhis_eq_fast _ _ _ (Bap.Proofs.Graph.nodup_eraseDups _)]

@[simp] theorem toSsa_tid (sub : Sub) : (toSsa sub).tid = sub.tid := by
  rfl

@[simp] theorem toSsa_name (sub : Sub) : (toSsa sub).name = sub.name := by
  rfl

end Bap.IR
