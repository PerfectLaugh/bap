import Bap.IR.Ssa
import Bap.IR.Optimize
import Bap.IR.Wire
import Bap.Proofs.Graph
import Bap.Proofs.Bil

namespace Bap.Proofs.IR

open Bap Bap.Bil Bap.IR Bap.Bil.Wire Bap.IR.Wire

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


local macro "connectMissingStarts" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Cfg) 0 ++ `Bap.IR.connectMissingStarts)
local macro "connectMissingExits" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Cfg) 0 ++ `Bap.IR.connectMissingExits)
local macro "reverseGraph" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Cfg) 0 ++ `Bap.IR.reverseGraph)

local macro "liveUnion" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.union)
local macro "liveSubtract" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.subtract)
local macro "blockOut" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockOut)
local macro "blockIn" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockIn)
local macro "livenessStep" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessStep)
local macro "seedOut" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.seedOut)
local macro "sameSets" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.sameSets)
local macro "livenessFuel" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessFuel)
local macro "livenessAux" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessAux)

local macro "entryEnv" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.entryEnv)
local macro "isSolved" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.isSolved)
local macro "dceDefs" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.dceDefs)
local macro "popVar" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.popVar)
local macro "constReplacements" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.replacements)
local macro "joinEnv" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.joinEnv)
local macro "propagateBlock" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.propagateBlock)
local macro "propagateAux" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.propagateAux)
local macro "hasSideEffect" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.hasSideEffect)
local macro "dcePass" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.dcePass)
local macro "dceAux" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.dceAux)
local macro "unfold_hasSideEffect" : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.IR.Optimize) 0 ++ `Bap.IR.hasSideEffect)):ident])
local macro "newName" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.newName)
local macro "topName" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.topName)
local macro "renamePhis" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.renamePhis)
local macro "renameDefs" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.renameDefs)
local macro "updatePhiInputs" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.updatePhiInputs)
local macro "popVars" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.popVars)
local macro "renameBlock" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.renameBlock)
local macro "insertPhisForVar" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.insertPhisForVar)
local macro "insertAllPhis" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.insertAllPhis)
local macro "renameExp" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.renameExp)
local macro "hexDigit" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Bil.Wire) 0 ++ `Bap.Bil.Wire.hexDigit)
local macro "parseHexLoop" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Bil.Wire) 0 ++ `Bap.Bil.Wire.parseHexLoop)
local macro "parseDefWithTag" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Wire) 0 ++ `Bap.IR.Wire.parseDefWithTag)
local macro "unfold_parseDefWithTag" : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.IR.Wire) 0 ++ `Bap.IR.Wire.parseDefWithTag)):ident,
    $(Lean.mkIdent (.num (`_private ++ `Bap.IR.Wire) 0 ++ `Bap.IR.Wire.printDefWithTag)):ident])
local macro "printDefWithTag" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Wire) 0 ++ `Bap.IR.Wire.printDefWithTag)

/-! ### Graph facts needed for CFG reasoning -/

section GraphFacts

variable {α : Type} [DecidableEq α]

private theorem mem_predecessors' (g : Bap.Graph.Graph α) (source target : α) :
    source ∈ Bap.Graph.predecessors g target ↔ (source, target) ∈ g.edges :=
  Bap.Proofs.Graph.mem_predecessors ..

private theorem countP_lt {β : Type} (P Q : β → Bool) (xs : List β)
    (hle : ∀ x ∈ xs, P x = true → Q x = true)
    (hex : ∃ x ∈ xs, Q x = true ∧ P x = false) : xs.countP P < xs.countP Q := by
  induction xs with
  | nil => simp at hex
  | cons y ys ih =>
    have hmono : ys.countP P ≤ ys.countP Q := by
      apply List.countP_mono_left
      exact fun x hx => hle x (List.mem_cons_of_mem _ hx)
    obtain ⟨x, hx, hq, hp⟩ := hex
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hq, hp]
      omega
    · have := ih (fun z hz => hle z (List.mem_cons_of_mem _ hz)) ⟨x, hx', hq, hp⟩
      have hy := hle y (by simp)
      cases hPy : P y <;> cases hQy : Q y <;> simp_all <;> omega

private theorem reachable_mono {g₁ g₂ : Bap.Graph.Graph α} (hn : g₁.nodes ⊆ g₂.nodes)
    (he : g₁.edges ⊆ g₂.edges) (start : α) :
    Bap.Graph.reachable g₁ start ⊆ Bap.Graph.reachable g₂ start :=
  Bap.Proofs.Graph.reachableFrom_mono_graph hn he _

private theorem start_mem_reachable {g : Bap.Graph.Graph α} {start : α} (h : start ∈ g.nodes) :
    start ∈ Bap.Graph.reachable g start :=
  Bap.Proofs.Graph.mem_reachableFrom_of_seed (by simp) h

private theorem reach_step {g : Bap.Graph.Graph α} {start a b : α} (ha : a ∈ Bap.Graph.reachable g start)
    (he : (a, b) ∈ g.edges) (hb : b ∈ g.nodes) : b ∈ Bap.Graph.reachable g start :=
  Bap.Proofs.Graph.reachableFrom_closed g _ ha he hb

private theorem mem_prune_nodes {g : Bap.Graph.Graph α} {s x : α} :
    x ∈ (Bap.Graph.prune g s).nodes ↔ x ∈ Bap.Graph.reachable g s :=
  Bap.Proofs.Graph.mem_prune_nodes x

private theorem mem_prune_edges {g : Bap.Graph.Graph α} {s a b : α} :
    (a, b) ∈ (Bap.Graph.prune g s).edges ↔
      (a, b) ∈ g.edges ∧ a ∈ Bap.Graph.reachable g s ∧ b ∈ Bap.Graph.reachable g s :=
  Bap.Proofs.Graph.mem_prune_edges a b

private theorem reachable_prune {g : Bap.Graph.Graph α} {s x : α} :
    x ∈ Bap.Graph.reachable (Bap.Graph.prune g s) s ↔ x ∈ Bap.Graph.reachable g s :=
  Bap.Proofs.Graph.reachable_prune x

private theorem graph_prune_idempotent {g : Bap.Graph.Graph α} {s : α} :
    Bap.Graph.prune (Bap.Graph.prune g s) s = Bap.Graph.prune g s :=
  Bap.Proofs.Graph.prune_idempotent

end GraphFacts

/-! ### Control-flow graph structure -/

theorem mem_blk_successors (blk : Blk) (t : Tid) :
    t ∈ blk.successors ↔ ∃ jmp ∈ blk.jmps, t ∈ jmp.successors := by
  simp [Blk.successors, List.mem_eraseDups, List.mem_flatMap]

theorem fromSub_mem_edges (sub : Sub) (a b : Tid) :
    (a, b) ∈ (Cfg.fromSub sub).graph.edges ↔ ∃ blk ∈ sub.blks, blk.tid = a ∧ b ∈ blk.successors := by
  simp only [Cfg.fromSub, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨blk, hblk, t, ht, rfl, rfl⟩
    exact ⟨blk, hblk, rfl, ht⟩
  · rintro ⟨blk, hblk, rfl, ht⟩
    exact ⟨blk, hblk, b, ht, rfl, rfl⟩

theorem fromSub_successors (sub : Sub) (a b : Tid) :
    b ∈ (Cfg.fromSub sub).successors a ↔ ∃ blk ∈ sub.blks, blk.tid = a ∧ b ∈ blk.successors := by
  rw [← fromSub_mem_edges]
  exact Bap.Graph.successors_mem ..

theorem fromSub_predecessors (sub : Sub) (a b : Tid) :
    a ∈ (Cfg.fromSub sub).predecessors b ↔ ∃ blk ∈ sub.blks, blk.tid = a ∧ b ∈ blk.successors := by
  rw [← fromSub_mem_edges]
  exact mem_predecessors' ..

/-- Every edge of a built CFG leaves from a real block. -/
theorem fromSub_edge_source {sub : Sub} {a b : Tid} (h : (a, b) ∈ (Cfg.fromSub sub).graph.edges) :
    a ∈ (Cfg.fromSub sub).graph.nodes := by
  obtain ⟨blk, hblk, rfl, _⟩ := (fromSub_mem_edges ..).1 h
  exact List.mem_map.2 ⟨blk, hblk, rfl⟩

theorem fromSub_start_reachable {sub : Sub} (h : sub.blks ≠ []) :
    (Cfg.fromSub sub).start ∈ (Cfg.fromSub sub).reachable := by
  match hb : sub.blks, h with
  | blk :: rest, _ =>
    apply start_mem_reachable
    simp [Cfg.fromSub, hb]

theorem block_some {cfg : Cfg} {t : Tid} {blk : Blk} (h : cfg.block t = some blk) :
    blk ∈ cfg.blocks ∧ blk.tid = t := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem block_exists {cfg : Cfg} {t : Tid} (h : t ∈ cfg.blocks.map Blk.tid) :
    ∃ blk, cfg.block t = some blk := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  have : (cfg.blocks.find? fun blk => decide (blk.tid = b.tid)).isSome := by
    rw [List.find?_isSome]
    exact ⟨b, hb, by simp⟩
  exact Option.isSome_iff_exists.1 this

theorem block_eq_none_iff {cfg : Cfg} {t : Tid} : cfg.block t = none ↔ t ∉ cfg.blocks.map Blk.tid := by
  constructor
  · intro h hm
    obtain ⟨b, hb⟩ := block_exists hm
    rw [h] at hb
    cases hb
  · intro h
    cases hb : cfg.block t with
    | none => rfl
    | some b =>
      exact absurd (List.mem_map.2 ⟨b, (block_some hb).1, (block_some hb).2⟩) h

/-! ### Single-block updates -/

@[simp] theorem updateBlock_start (cfg : Cfg) (t : Tid) (f : Blk → Blk) :
    (cfg.updateBlock t f).start = cfg.start := rfl

@[simp] theorem updateBlock_graph (cfg : Cfg) (t : Tid) (f : Blk → Blk) :
    (cfg.updateBlock t f).graph = cfg.graph := rfl

theorem updateBlock_id (cfg : Cfg) (t : Tid) : cfg.updateBlock t id = cfg := by
  obtain ⟨start, blocks, graph⟩ := cfg
  simp only [Cfg.updateBlock, id, ite_self, List.map_id']

theorem updateBlock_tids (cfg : Cfg) (t : Tid) (f : Blk → Blk) (hf : ∀ b, b.tid = t → (f b).tid = b.tid) :
    (cfg.updateBlock t f).blocks.map Blk.tid = cfg.blocks.map Blk.tid := by
  simp only [Cfg.updateBlock, List.map_map]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp]
  split
  · exact hf b ‹_›
  · rfl

private theorem find_update (l : List Blk) (t s : Tid) (f : Blk → Blk)
    (hf : ∀ b, b.tid = t → (f b).tid = b.tid) :
    (l.map fun blk => if blk.tid = t then f blk else blk).find? (fun blk => decide (blk.tid = s)) =
      (l.find? fun blk => decide (blk.tid = s)).map (fun blk => if blk.tid = t then f blk else blk) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb : (if b.tid = t then f b else b).tid = b.tid := by
      split
      · exact hf b ‹_›
      · rfl
    simp only [List.map_cons, List.find?_cons, hb]
    split
    · rfl
    · exact ih

/-- An update only changes the block it names, and leaves the lookup of any other tid alone. -/
theorem block_updateBlock_ne (cfg : Cfg) {t s : Tid} (f : Blk → Blk)
    (hf : ∀ b, b.tid = t → (f b).tid = b.tid) (hne : s ≠ t) :
    (cfg.updateBlock t f).block s = cfg.block s := by
  show (cfg.blocks.map _).find? _ = cfg.blocks.find? _
  rw [find_update _ _ _ _ hf]
  cases h : cfg.blocks.find? (fun blk => decide (blk.tid = s)) with
  | none => rfl
  | some b =>
    have hb : b.tid = s := by simpa using List.find?_some h
    have hbt : b.tid ≠ t := by rw [hb]; exact hne
    simp [hbt]

theorem block_updateBlock_same (cfg : Cfg) (t : Tid) (f : Blk → Blk)
    (hf : ∀ b, b.tid = t → (f b).tid = b.tid) :
    (cfg.updateBlock t f).block t = (cfg.block t).map f := by
  show (cfg.blocks.map _).find? _ = (cfg.blocks.find? _).map f
  rw [find_update _ _ _ _ hf]
  cases h : cfg.blocks.find? (fun blk => decide (blk.tid = t)) with
  | none => rfl
  | some b =>
    have hb : b.tid = t := by simpa using List.find?_some h
    simp [hb]

/-- Two updates of the same block compose. -/
theorem updateBlock_comp (cfg : Cfg) (t : Tid) (f g : Blk → Blk)
    (hf : ∀ b, b.tid = t → (f b).tid = b.tid) :
    (cfg.updateBlock t f).updateBlock t g = cfg.updateBlock t (g ∘ f) := by
  simp only [Cfg.updateBlock, List.map_map, Cfg.mk.injEq, true_and, and_true]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp]
  by_cases h : b.tid = t
  · simp [h, hf b h]
  · simp [h]

/-- Updates of different blocks commute. -/
theorem updateBlock_comm (cfg : Cfg) {s t : Tid} (hne : s ≠ t) (f g : Blk → Blk)
    (hf : ∀ b, b.tid = s → (f b).tid = b.tid) (hg : ∀ b, b.tid = t → (g b).tid = b.tid) :
    (cfg.updateBlock s f).updateBlock t g = (cfg.updateBlock t g).updateBlock s f := by
  simp only [Cfg.updateBlock, List.map_map, Cfg.mk.injEq, true_and, and_true]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp]
  by_cases hs : b.tid = s
  · have ht : b.tid ≠ t := by rw [hs]; exact hne
    simp [hs, hf b hs, hne]
  · by_cases ht : b.tid = t
    · simp [ht, hg b ht, Ne.symm hne]
    · simp [hs, ht]

/-! ### Pruning -/

@[simp] theorem prune_start (cfg : Cfg) : cfg.prune.start = cfg.start := rfl

theorem prune_mem_nodes {cfg : Cfg} {t : Tid} : t ∈ cfg.prune.graph.nodes ↔ t ∈ cfg.reachable :=
  mem_prune_nodes

theorem prune_reachable {cfg : Cfg} {t : Tid} : t ∈ cfg.prune.reachable ↔ t ∈ cfg.reachable :=
  reachable_prune

/-- Pruning keeps exactly the reachable blocks, without reordering or editing them. -/
theorem prune_block (cfg : Cfg) (t : Tid) :
    cfg.prune.block t = if t ∈ cfg.reachable then cfg.block t else none := by
  have key : ∀ l : List Blk, (l.filter fun blk => blk.tid ∈ cfg.prune.graph.nodes).find?
      (fun blk => decide (blk.tid = t)) =
      if t ∈ cfg.reachable then l.find? (fun blk => decide (blk.tid = t)) else none := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      by_cases hb : b.tid = t
      · subst hb
        by_cases hr : b.tid ∈ cfg.reachable
        · have : b.tid ∈ cfg.prune.graph.nodes := prune_mem_nodes.2 hr
          simp [List.filter_cons, this, hr]
        · have : b.tid ∉ cfg.prune.graph.nodes := fun h => hr (prune_mem_nodes.1 h)
          simp only [List.filter_cons, this, decide_false, Bool.cond_false, Bool.false_eq_true, ite_false, ih, hr]
      · rw [List.filter_cons]
        split
        · simp only [List.find?_cons, hb, decide_false, ih]
        · simp only [List.find?_cons, hb, decide_false, ih]
  exact key cfg.blocks

theorem prune_blocks_reachable {cfg : Cfg} {blk : Blk} (h : blk ∈ cfg.prune.blocks) :
    blk.tid ∈ cfg.reachable := by
  exact prune_mem_nodes.1 (of_decide_eq_true (List.mem_filter.1 h).2)

theorem prune_blocks_sublist (cfg : Cfg) : cfg.prune.blocks.Sublist cfg.blocks :=
  List.filter_sublist

/-- No edge of a pruned CFG touches a removed node. -/
theorem prune_edges_closed {cfg : Cfg} {a b : Tid} (h : (a, b) ∈ cfg.prune.graph.edges) :
    a ∈ cfg.prune.graph.nodes ∧ b ∈ cfg.prune.graph.nodes := by
  have := mem_prune_edges.1 h
  exact ⟨prune_mem_nodes.2 this.2.1, prune_mem_nodes.2 this.2.2⟩

theorem prune_idempotent (cfg : Cfg) : cfg.prune.prune = cfg.prune := by
  have hg : cfg.prune.prune.graph = cfg.prune.graph := graph_prune_idempotent
  have hb : cfg.prune.blocks.filter (fun blk => blk.tid ∈ cfg.prune.graph.nodes) = cfg.prune.blocks := by
    apply List.filter_eq_self.2
    intro blk hblk
    exact (List.mem_filter.1 hblk).2
  show Cfg.mk cfg.prune.start
    (cfg.prune.blocks.filter (fun blk => blk.tid ∈ cfg.prune.prune.graph.nodes)) cfg.prune.prune.graph = _
  rw [hg, hb]

@[simp] theorem pruneSub_tid (sub : Sub) : (pruneSub sub).tid = sub.tid := rfl
@[simp] theorem pruneSub_name (sub : Sub) : (pruneSub sub).name = sub.name := rfl
@[simp] theorem pruneSub_args (sub : Sub) : (pruneSub sub).args = sub.args := rfl

theorem pruneSub_blks_sublist (sub : Sub) : (pruneSub sub).blks.Sublist sub.blks :=
  prune_blocks_sublist (Cfg.fromSub sub)

theorem pruneSub_blks_reachable {sub : Sub} {blk : Blk} (h : blk ∈ (pruneSub sub).blks) :
    blk.tid ∈ (Cfg.fromSub sub).reachable :=
  prune_blocks_reachable h

/-! ### Connected CFGs -/

private theorem connectMissingStarts_zero (actual : List Tid) (cfg : Cfg) :
    connectMissingStarts actual cfg 0 = cfg := rfl

private theorem connectMissingStarts_succ (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    connectMissingStarts actual cfg (fuel + 1) =
      match actual.find? fun tid => tid ∉ cfg.reachable with
      | none => cfg
      | some tid => connectMissingStarts actual
          { cfg with graph := { cfg.graph with edges := (pseudoStart, tid) :: cfg.graph.edges } } fuel := rfl

private theorem connectMissingExits_succ (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    connectMissingExits actual cfg (fuel + 1) =
      match actual.find? fun tid => tid ∉ Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit with
      | none => cfg
      | some tid => connectMissingExits actual
          { cfg with graph := { cfg.graph with edges := (tid, pseudoExit) :: cfg.graph.edges } } fuel := rfl

/-- Frame shared by both connection loops: only edges are ever added. -/
private structure Grows (a b : Cfg) : Prop where
  start : b.start = a.start
  blocks : b.blocks = a.blocks
  nodes : b.graph.nodes = a.graph.nodes
  edges : a.graph.edges ⊆ b.graph.edges

private theorem Grows.refl (a : Cfg) : Grows a a :=
  ⟨rfl, rfl, rfl, List.Subset.refl _⟩

private theorem Grows.trans {a b c : Cfg} (h : Grows a b) (h' : Grows b c) : Grows a c :=
  ⟨h'.start.trans h.start, h'.blocks.trans h.blocks, h'.nodes.trans h.nodes,
    List.Subset.trans h.edges h'.edges⟩

private theorem grows_starts (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    Grows cfg (connectMissingStarts actual cfg fuel) := by
  induction fuel generalizing cfg with
  | zero => exact Grows.refl _
  | succ fuel ih =>
    rw [connectMissingStarts_succ]
    split
    · exact Grows.refl _
    · refine Grows.trans ?_ (ih _)
      exact ⟨rfl, rfl, rfl, List.subset_cons_self _ _⟩

private theorem grows_exits (actual : List Tid) (cfg : Cfg) (fuel : Nat) :
    Grows cfg (connectMissingExits actual cfg fuel) := by
  induction fuel generalizing cfg with
  | zero => exact Grows.refl _
  | succ fuel ih =>
    rw [connectMissingExits_succ]
    split
    · exact Grows.refl _
    · refine Grows.trans ?_ (ih _)
      exact ⟨rfl, rfl, rfl, List.subset_cons_self _ _⟩

/-- The loop finishes with every requested block reachable once the fuel covers the missing ones. -/
private theorem starts_all_reachable (actual : List Tid) (cfg : Cfg) (fuel : Nat)
    (hfuel : actual.countP (fun t => decide (t ∉ cfg.reachable)) < fuel)
    (hstart : cfg.start = pseudoStart) (hps : pseudoStart ∈ cfg.graph.nodes)
    (hactual : actual ⊆ cfg.graph.nodes) :
    ∀ t ∈ actual, t ∈ (connectMissingStarts actual cfg fuel).reachable := by
  induction fuel generalizing cfg with
  | zero => omega
  | succ fuel ih =>
    rw [connectMissingStarts_succ]
    split
    · rename_i hnone
      intro t ht
      have := List.find?_eq_none.1 hnone t ht
      simpa using this
    · rename_i tid hsome
      have hmem : tid ∈ actual := List.mem_of_find?_eq_some hsome
      have hnot : tid ∉ cfg.reachable := by simpa using List.find?_some hsome
      let cfg' : Cfg := { cfg with graph := { cfg.graph with edges := (pseudoStart, tid) :: cfg.graph.edges } }
      have hsub : cfg.reachable ⊆ cfg'.reachable :=
        reachable_mono (g₁ := cfg.graph) (g₂ := cfg'.graph) (List.Subset.refl _)
          (List.subset_cons_self _ _) _
      have htid : tid ∈ cfg'.reachable := by
        have hs : pseudoStart ∈ Bap.Graph.reachable cfg'.graph cfg'.start := by
          show pseudoStart ∈ Bap.Graph.reachable cfg'.graph cfg.start
          rw [hstart]
          exact start_mem_reachable hps
        exact reach_step (g := cfg'.graph) hs (by simp [cfg']) (hactual hmem)
      refine ih cfg' ?_ hstart hps hactual
      have := countP_lt (fun t => decide (t ∉ cfg'.reachable)) (fun t => decide (t ∉ cfg.reachable)) actual
        (by
          intro y _ hy
          simp only [decide_eq_true_eq] at *
          exact fun h => hy (hsub h))
        ⟨tid, hmem, by simpa using hnot, by simpa using htid⟩
      omega

private theorem exits_all_coreachable (actual : List Tid) (cfg : Cfg) (fuel : Nat)
    (hfuel : actual.countP
      (fun t => decide (t ∉ Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit)) < fuel)
    (hpe : pseudoExit ∈ cfg.graph.nodes) (hactual : actual ⊆ cfg.graph.nodes) :
    ∀ t ∈ actual, t ∈ Bap.Graph.reachable (reverseGraph (connectMissingExits actual cfg fuel).graph)
      pseudoExit := by
  induction fuel generalizing cfg with
  | zero => omega
  | succ fuel ih =>
    rw [connectMissingExits_succ]
    split
    · rename_i hnone
      intro t ht
      have := List.find?_eq_none.1 hnone t ht
      simpa using this
    · rename_i tid hsome
      have hmem : tid ∈ actual := List.mem_of_find?_eq_some hsome
      have hnot : tid ∉ Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit := by
        simpa using List.find?_some hsome
      let cfg' : Cfg := { cfg with graph := { cfg.graph with edges := (tid, pseudoExit) :: cfg.graph.edges } }
      have hrev : (reverseGraph cfg'.graph).edges =
          (pseudoExit, tid) :: (reverseGraph cfg.graph).edges := rfl
      have hsub : Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit ⊆
          Bap.Graph.reachable (reverseGraph cfg'.graph) pseudoExit :=
        reachable_mono (g₁ := reverseGraph cfg.graph) (g₂ := reverseGraph cfg'.graph)
          (List.Subset.refl _) (fun e he => by rw [hrev]; exact List.mem_cons_of_mem _ he) _
      have htid : tid ∈ Bap.Graph.reachable (reverseGraph cfg'.graph) pseudoExit := by
        refine reach_step (a := pseudoExit) (start_mem_reachable hpe) ?_ (hactual hmem)
        rw [hrev]
        simp
      refine ih cfg' ?_ hpe hactual
      have := countP_lt (fun t => decide (t ∉ Bap.Graph.reachable (reverseGraph cfg'.graph) pseudoExit))
        (fun t => decide (t ∉ Bap.Graph.reachable (reverseGraph cfg.graph) pseudoExit)) actual
        (by
          intro y _ hy
          simp only [decide_eq_true_eq] at *
          exact fun h => hy (hsub h))
        ⟨tid, hmem, by simpa using hnot, by simpa using htid⟩
      omega

private abbrev connectedBase (sub : Sub) : Cfg :=
  { start := pseudoStart
    blocks := ⟨pseudoStart, [], [], []⟩ :: (Cfg.fromSub sub).blocks ++ [⟨pseudoExit, [], [], []⟩]
    graph := {
      nodes := pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit]
      edges := (Cfg.fromSub sub).graph.edges ++
        (sub.blks.map Blk.tid |>.filter fun tid => ((Cfg.fromSub sub).predecessors tid).isEmpty).map
          (pseudoStart, ·) ++
        (sub.blks.map Blk.tid |>.filter fun tid => ((Cfg.fromSub sub).successors tid).isEmpty).map
          (·, pseudoExit)
    } }

private theorem connected_eq (sub : Sub) :
    Cfg.connected sub = connectMissingExits (sub.blks.map Blk.tid)
      (connectMissingStarts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1))
      (sub.blks.length + 1) := by
  simp only [Cfg.connected, List.length_map]

private theorem connected_grows (sub : Sub) : Grows (connectedBase sub) (Cfg.connected sub) := by
  rw [connected_eq]
  exact Grows.trans (grows_starts ..) (grows_exits ..)

theorem connected_blocks (sub : Sub) :
    (Cfg.connected sub).blocks =
      ⟨pseudoStart, [], [], []⟩ :: sub.blks ++ [⟨pseudoExit, [], [], []⟩] :=
  (connected_grows sub).blocks

theorem connected_nodes (sub : Sub) :
    (Cfg.connected sub).graph.nodes = pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit] :=
  (connected_grows sub).nodes

/-- The connected CFG contains every edge of the plain CFG. -/
theorem connected_edges_superset (sub : Sub) :
    (Cfg.fromSub sub).graph.edges ⊆ (Cfg.connected sub).graph.edges := by
  intro e he
  refine (connected_grows sub).edges ?_
  simp [he]

private theorem connected_actual_subset (sub : Sub) (cfg : Cfg)
    (h : cfg.graph.nodes = pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit]) :
    sub.blks.map Blk.tid ⊆ cfg.graph.nodes := by
  rw [h]
  intro x hx
  simp only [List.cons_append, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl hx)

/-- In the connected CFG every block is reachable from the pseudo start. -/
theorem connected_all_reachable (sub : Sub) {t : Tid} (ht : t ∈ sub.blks.map Blk.tid) :
    t ∈ (Cfg.connected sub).reachable := by
  have hs := starts_all_reachable (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)
    (by
      have := List.countP_le_length (l := sub.blks.map Blk.tid)
        (p := fun t => decide (t ∉ (connectedBase sub).reachable))
      simp only [List.length_map] at this
      omega)
    rfl (by simp) (connected_actual_subset sub _ rfl) t ht
  have hgrow := grows_exits (sub.blks.map Blk.tid)
    (connectMissingStarts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)) (sub.blks.length + 1)
  have hmono : (connectMissingStarts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)).reachable ⊆
      (Cfg.connected sub).reachable := by
    rw [connected_eq]
    show Bap.Graph.reachable _ _ ⊆ Bap.Graph.reachable _ _
    rw [hgrow.start]
    exact reachable_mono (by rw [hgrow.nodes]; exact List.Subset.refl _) hgrow.edges _
  exact hmono hs

/-- In the connected CFG the pseudo exit is reachable from every block along reversed edges. -/
theorem connected_all_coreachable (sub : Sub) {t : Tid} (ht : t ∈ sub.blks.map Blk.tid) :
    t ∈ Bap.Graph.reachable
      { (Cfg.connected sub).graph with
        edges := (Cfg.connected sub).graph.edges.map fun edge => (edge.2, edge.1) } pseudoExit := by
  have hgs := grows_starts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)
  have hbase : (connectMissingStarts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)).graph.nodes =
      pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit] := hgs.nodes
  rw [connected_eq]
  refine exits_all_coreachable _ _ _ ?_ (by rw [hbase]; simp) (connected_actual_subset sub _ hbase) t ht
  have := List.countP_le_length (l := sub.blks.map Blk.tid)
    (p := fun t => decide (t ∉ Bap.Graph.reachable
      (reverseGraph (connectMissingStarts (sub.blks.map Blk.tid) (connectedBase sub) (sub.blks.length + 1)).graph)
      pseudoExit))
  simp only [List.length_map] at this
  omega

/-! ### Expression mapping -/

theorem Label.mapExp_id (label : Label) : label.mapExp id = label := by
  cases label <;> rfl

theorem Label.mapExp_comp (f g : Exp → Exp) (label : Label) :
    (label.mapExp f).mapExp g = label.mapExp (g ∘ f) := by
  cases label <;> rfl

theorem JmpKind.mapExp_id (kind : JmpKind) : kind.mapExp id = kind := by
  have h : Label.mapExp id = id := funext Label.mapExp_id
  cases kind <;> simp [JmpKind.mapExp, Label.mapExp_id, h]

theorem JmpKind.mapExp_comp (f g : Exp → Exp) (kind : JmpKind) :
    (kind.mapExp f).mapExp g = kind.mapExp (g ∘ f) := by
  cases kind with
  | call target returnTo => cases returnTo <;> simp [JmpKind.mapExp, Label.mapExp_comp]
  | _ => simp [JmpKind.mapExp, Label.mapExp_comp]

theorem Jmp.mapExp_id (jmp : Jmp) : jmp.mapExp id = jmp := by
  obtain ⟨tid, condition, kind⟩ := jmp
  cases condition <;> simp [Jmp.mapExp, JmpKind.mapExp_id]

theorem Jmp.mapExp_comp (f g : Exp → Exp) (jmp : Jmp) :
    (jmp.mapExp f).mapExp g = jmp.mapExp (g ∘ f) := by
  obtain ⟨tid, condition, kind⟩ := jmp
  cases condition <;> simp [Jmp.mapExp, JmpKind.mapExp_comp]

theorem Blk.mapExp_id (blk : Blk) : blk.mapExp id = blk := by
  obtain ⟨tid, phis, defs, jmps⟩ := blk
  have h : Jmp.mapExp id = id := funext Jmp.mapExp_id
  simp [Blk.mapExp, h]

theorem Blk.mapExp_comp (f g : Exp → Exp) (blk : Blk) :
    (blk.mapExp f).mapExp g = blk.mapExp (g ∘ f) := by
  obtain ⟨tid, phis, defs, jmps⟩ := blk
  simp [Blk.mapExp, Jmp.mapExp_comp, Function.comp_def]

theorem Sub.mapExp_id (sub : Sub) : sub.mapExp id = sub := by
  obtain ⟨tid, name, args, blks⟩ := sub
  have h : Blk.mapExp id = id := funext Blk.mapExp_id
  simp [Sub.mapExp, h]

theorem Sub.mapExp_comp (f g : Exp → Exp) (sub : Sub) :
    (sub.mapExp f).mapExp g = sub.mapExp (g ∘ f) := by
  obtain ⟨tid, name, args, blks⟩ := sub
  simp [Sub.mapExp, Blk.mapExp_comp, Function.comp_def]

/-- Rewriting by an idempotent expression function is idempotent. -/
theorem Sub.mapExp_idempotent {f : Exp → Exp} (hf : ∀ e, f (f e) = f e) (sub : Sub) :
    (sub.mapExp f).mapExp f = sub.mapExp f := by
  rw [Sub.mapExp_comp]
  congr 1
  exact funext hf

theorem Label.directTarget_mapExp (f : Exp → Exp) (label : Label) :
    (label.mapExp f).directTarget = label.directTarget := by
  cases label <;> rfl

/-- Rewriting expressions never changes the static targets of a jump. -/
theorem Jmp.successors_mapExp (f : Exp → Exp) (jmp : Jmp) :
    (jmp.mapExp f).successors = jmp.successors := by
  obtain ⟨tid, condition, kind⟩ := jmp
  cases kind with
  | call target returnTo =>
    cases returnTo with
    | none => rfl
    | some label => cases label <;> rfl
  | goto target => cases target <;> rfl
  | ret target => cases target <;> rfl
  | interrupt => rfl

theorem Blk.successors_mapExp (f : Exp → Exp) (blk : Blk) :
    (blk.mapExp f).successors = blk.successors := by
  simp only [Blk.successors, Blk.mapExp, List.flatMap_map, Jmp.successors_mapExp]

theorem Blk.mapExp_definedVars (f : Exp → Exp) (blk : Blk) :
    (blk.mapExp f).definedVars = blk.definedVars := by
  simp [Blk.definedVars, Blk.mapExp, Function.comp_def]

/-- Rewriting expressions leaves the control-flow graph untouched. -/
theorem fromSub_mapExp_graph (f : Exp → Exp) (sub : Sub) :
    (Cfg.fromSub (sub.mapExp f)).graph = (Cfg.fromSub sub).graph := by
  simp only [Cfg.fromSub, Sub.mapExp, List.map_map, List.flatMap_map, Blk.successors_mapExp]
  rfl

theorem fromSub_mapExp_start (f : Exp → Exp) (sub : Sub) :
    (Cfg.fromSub (sub.mapExp f)).start = (Cfg.fromSub sub).start := by
  obtain ⟨tid, name, args, blks⟩ := sub
  cases blks <;> rfl

theorem simplifySub_graph (sub : Sub) :
    (Cfg.fromSub (simplifySub sub)).graph = (Cfg.fromSub sub).graph :=
  fromSub_mapExp_graph _ sub

theorem mem_definedVars (blk : Blk) (var : Var) :
    var ∈ blk.definedVars ↔ (∃ phi ∈ blk.phis, phi.var = var) ∨ ∃ defn ∈ blk.defs, defn.var = var := by
  simp [Blk.definedVars, List.mem_eraseDups]

theorem defines_iff (blk : Blk) (var : Var) : blk.defines var = true ↔ var ∈ blk.definedVars := by
  simp [Blk.defines]

/-- Variables read by a definition list before they are overwritten inside it. -/
def Exposed : List Def → Var → Prop
  | [], _ => False
  | defn :: rest, x => x ∈ Bil.freeVars defn.rhs ∨ (x ≠ defn.var ∧ Exposed rest x)

private abbrev defsStep (state : List Var × List Var) (defn : Def) : List Var × List Var :=
  (state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2, defn.var :: state.2)

private theorem defsFold_killed (defs : List Def) (input killed : List Var) (x : Var) :
    x ∈ (defs.foldl defsStep (input, killed)).2 ↔ x ∈ killed ∨ ∃ defn ∈ defs, defn.var = x := by
  induction defs generalizing input killed with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    grind

private theorem defsFold_input (defs : List Def) (input killed : List Var) (x : Var) :
    x ∈ (defs.foldl defsStep (input, killed)).1 ↔ x ∈ input ∨ (x ∉ killed ∧ Exposed defs x) := by
  induction defs generalizing input killed with
  | nil => simp [Exposed]
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, List.mem_append, List.mem_filter, decide_eq_true_eq, Exposed,
      List.mem_cons, not_or]
    grind

/-- Exact characterization of a block's free variables. -/
theorem mem_blk_freeVars (blk : Blk) (x : Var) :
    x ∈ blk.freeVars ↔ Exposed blk.defs x ∨
      (∃ phi ∈ blk.phis, ∃ input ∈ phi.values, x ∈ Bil.freeVars input.2) ∨
      ∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars := by
  have h : blk.freeVars = ((blk.defs.foldl defsStep ([], [])).1 ++
      blk.phis.flatMap (fun phi => phi.values.flatMap (Bil.freeVars ∘ Prod.snd)) ++
      blk.jmps.flatMap Jmp.freeVars).eraseDups := rfl
  rw [h]
  simp only [List.mem_eraseDups, List.mem_append, defsFold_input, List.mem_flatMap, Function.comp]
  simp [or_assoc]

/-! ### Liveness transfer functions -/

theorem get_put {κ β : Type} [DecidableEq κ] (z t : κ) (v : β) (S : List (κ × β)) :
    Assoc.get z (Assoc.put t v S) = if z = t then some v else Assoc.get z S := by
  by_cases hz : z = t
  · subst hz
    simp
  · simp only [hz, ite_false]
    have key : ∀ l : List (κ × β), List.lookup z (l.filter fun e => e.1 != t) = List.lookup z l := by
      intro l
      induction l with
      | nil => rfl
      | cons e es ih =>
        obtain ⟨a, b⟩ := e
        by_cases ha : a = t
        · subst ha
          have hb : (z == a) = false := by simpa using hz
          simp [List.filter_cons, List.lookup, hb, ih]
        · have hb : (a != t) = true := by simpa using ha
          simp [List.filter_cons, List.lookup, hb, ih]
    have hb : (z == t) = false := by simpa using hz
    simp [Assoc.get, Assoc.put, List.lookup, hb, key]

@[simp] private theorem mem_liveUnion (l r : List Var) (x : Var) :
    x ∈ liveUnion l r ↔ x ∈ l ∨ x ∈ r := by
  show x ∈ (l ++ r).eraseDups ↔ _
  simp [List.mem_eraseDups]

@[simp] private theorem mem_liveSubtract (l r : List Var) (x : Var) :
    x ∈ liveSubtract l r ↔ x ∈ l ∧ x ∉ r := by
  show x ∈ l.filter _ ↔ _
  simp

private theorem get_mem_env' {κ β : Type} [DecidableEq κ] {k : κ} {v : β} {T : List (κ × β)}
    (h : Assoc.get k T = some v) : (k, v) ∈ T := by
  induction T with
  | nil => simp [Assoc.get] at h
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      simp [Assoc.get] at h
      simp [h]
    · have hb : (k == a) = false := by simpa using hk
      have h' : Assoc.get k es = some v := by simpa [Assoc.get, List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (ih h')

/-- Variables a block contributes to the live-out set of predecessor `t`. -/
def LiveEdge (cfg : Cfg) (ins : List (Tid × List Var)) (t succ : Tid) (x : Var) : Prop :=
  ∃ blk, cfg.block succ = some blk ∧
    ((x ∈ (Assoc.get succ ins).getD [] ∧ ∀ phi ∈ blk.phis, phi.var ≠ x) ∨
      ∃ phi ∈ blk.phis, ∃ value, Assoc.get t phi.values = some value ∧ x ∈ Bil.freeVars value)

private theorem mem_phiFold (t : Tid) (phis : List Phi) (out : List Var) (x : Var) :
    x ∈ phis.foldl (fun out phi =>
        match Assoc.get t phi.values with
        | some value => liveUnion out (Bil.freeVars value)
        | none => out) out ↔
      x ∈ out ∨ ∃ phi ∈ phis, ∃ value, Assoc.get t phi.values = some value ∧ x ∈ Bil.freeVars value := by
  induction phis generalizing out with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih]
    split <;> rename_i heq
    · simp only [mem_liveUnion]
      grind
    · grind

/-- Exact characterization of `blockOut`. -/
theorem mem_blockOut (cfg : Cfg) (ins : List (Tid × List Var)) (t : Tid) (x : Var) :
    x ∈ blockOut cfg ins t ↔ ∃ succ ∈ cfg.successors t, LiveEdge cfg ins t succ x := by
  have key : ∀ (succs : List Tid) (out : List Var), x ∈ succs.foldl (fun out successor =>
      match cfg.block successor with
      | none => out
      | some block =>
        let phiVars := block.phis.map Phi.var
        let successorIn := (Assoc.get successor ins).getD []
        let out := liveUnion out (liveSubtract successorIn phiVars)
        block.phis.foldl (init := out) fun out phi =>
          match Assoc.get t phi.values with
          | some value => liveUnion out (Bil.freeVars value)
          | none => out) out ↔
      x ∈ out ∨ ∃ succ ∈ succs, LiveEdge cfg ins t succ x := by
    intro succs
    induction succs with
    | nil => simp
    | cons s ss ih =>
      intro out
      simp only [List.foldl_cons, ih]
      cases hb : cfg.block s with
      | none =>
        simp only [LiveEdge, hb]
        grind
      | some blk =>
        simp only [mem_phiFold, mem_liveUnion, mem_liveSubtract, LiveEdge, hb]
        simp only [List.mem_map, not_exists, not_and, Option.some.injEq]
        grind
  refine Iff.trans (key (cfg.successors t) []) ?_
  simp

/-- Exact gen/kill characterization of `blockIn`. -/
theorem mem_blockIn (blk : Blk) (out : List Var) (x : Var) :
    x ∈ blockIn blk out ↔ Exposed blk.defs x ∨ (∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars) ∨
      (x ∈ out ∧ ∀ defn ∈ blk.defs, defn.var ≠ x) := by
  have hjmp : ∀ (js : List Jmp) (input : List Var),
      x ∈ js.foldl (fun input jmp => liveUnion input jmp.freeVars) input ↔
        x ∈ input ∨ ∃ jmp ∈ js, x ∈ jmp.freeVars := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      intro input
      simp only [List.foldl_cons, ih, mem_liveUnion]
      grind
  have heq : blockIn blk out = liveUnion
      (blk.jmps.foldl (fun input jmp => liveUnion input jmp.freeVars) (blk.defs.foldl defsStep ([], [])).1)
      (liveSubtract out (blk.defs.foldl defsStep ([], [])).2) := rfl
  rw [heq]
  simp only [mem_liveUnion, mem_liveSubtract, hjmp, defsFold_input, defsFold_killed]
  simp only [List.not_mem_nil, not_false_eq_true, true_and, false_or]
  grind

theorem blockIn_mono (blk : Blk) {o₁ o₂ : List Var} (h : o₁ ⊆ o₂) : blockIn blk o₁ ⊆ blockIn blk o₂ := by
  intro x hx
  rw [mem_blockIn] at hx ⊢
  rcases hx with hx | hx | ⟨hx, hd⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr ⟨h hx, hd⟩)

/-- The live-in set distributes over unions of the live-out set. -/
theorem blockIn_union (blk : Blk) (o₁ o₂ : List Var) (x : Var) :
    x ∈ blockIn blk (o₁ ++ o₂) ↔ x ∈ blockIn blk o₁ ∨ x ∈ blockIn blk o₂ := by
  simp only [mem_blockIn, List.mem_append]
  grind

/-- A variable defined in a block and not read before that is not transferred from live-out. -/
theorem blockIn_kill {blk : Blk} {out : List Var} {x : Var} (hdef : ∃ defn ∈ blk.defs, defn.var = x)
    (hexp : ¬ Exposed blk.defs x) (hjmp : ∀ jmp ∈ blk.jmps, x ∉ jmp.freeVars) : x ∉ blockIn blk out := by
  rw [mem_blockIn]
  obtain ⟨defn, hd, hv⟩ := hdef
  rintro (h | ⟨j, hj, h⟩ | ⟨_, h⟩)
  · exact hexp h
  · exact hjmp j hj h
  · exact h defn hd hv

/-- Block-local liveness never exceeds the free variables of the block when nothing is live out. -/
theorem blockIn_nil_subset_freeVars (blk : Blk) : blockIn blk [] ⊆ blk.freeVars := by
  intro x hx
  rw [mem_blockIn] at hx
  rw [mem_blk_freeVars]
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inr hx)
  · simp at hx

/-! ### Liveness fixpoint -/

private abbrev getL (t : Tid) (S : List (Tid × List Var)) : List Var := (Assoc.get t S).getD []

private abbrev Seed := Option (Tid × List Var)

/-- The transfer function's live-out, including a seed at the seeded exit. -/
private abbrev liveOut (cfg : Cfg) (initial : Seed) (S : List (Tid × List Var)) (t : Tid) : List Var :=
  seedOut initial t (blockOut cfg S t)

private theorem mem_seedOut (initial : Seed) (t : Tid) (out : List Var) (x : Var) :
    x ∈ seedOut initial t out ↔ x ∈ out ∨ ∃ vars, initial = some (t, vars) ∧ x ∈ vars := by
  match initial with
  | none =>
    show x ∈ out ↔ _
    simp
  | some (e, vars) =>
    show x ∈ (if e = t then liveUnion out vars else out) ↔ _
    by_cases he : e = t
    · subst he
      simp
    · simp [he]

private def Le (S S' : List (Tid × List Var)) : Prop := ∀ t x, x ∈ getL t S → x ∈ getL t S'

private theorem Le.refl (S : List (Tid × List Var)) : Le S S := fun _ _ h => h

private theorem Le.trans {a b c : List (Tid × List Var)} (h : Le a b) (h' : Le b c) : Le a c :=
  fun t x hx => h' t x (h t x hx)

private theorem blockOut_mono (cfg : Cfg) {S S' : List (Tid × List Var)} (h : Le S S') (t : Tid) :
    blockOut cfg S t ⊆ blockOut cfg S' t := by
  intro x hx
  rw [mem_blockOut] at hx ⊢
  obtain ⟨succ, hs, blk, hb, hc⟩ := hx
  refine ⟨succ, hs, blk, hb, ?_⟩
  rcases hc with ⟨hin, hp⟩ | hc
  · exact Or.inl ⟨h _ _ hin, hp⟩
  · exact Or.inr hc

private theorem liveOut_mono (cfg : Cfg) (initial : Seed) {S S' : List (Tid × List Var)} (h : Le S S')
    (t : Tid) : liveOut cfg initial S t ⊆ liveOut cfg initial S' t := by
  intro x hx
  rw [mem_seedOut] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (blockOut_mono cfg h t hx)
  · exact Or.inr hx

private theorem transfer_mono (cfg : Cfg) (initial : Seed) {S S' : List (Tid × List Var)} (h : Le S S')
    (t : Tid) (blk : Blk) :
    blockIn blk (liveOut cfg initial S t) ⊆ blockIn blk (liveOut cfg initial S' t) :=
  blockIn_mono blk (liveOut_mono cfg initial h t)

private theorem getL_put_same (t : Tid) (v : List Var) (S : List (Tid × List Var)) :
    getL t (Assoc.put t v S) = v := by
  simp [getL]

private theorem getL_put_ne {z t : Tid} (h : z ≠ t) (v : List Var) (S : List (Tid × List Var)) :
    getL z (Assoc.put t v S) = getL z S := by
  simp [getL, get_put, h]

/-- Invariant of the solver: rows are justified by the transfer function and stay in the universe. -/
private structure LiveInv (cfg : Cfg) (initial : Seed) (U : List Var) (I O : List (Tid × List Var)) : Prop where
  post : ∀ t x, x ∈ getL t I → ∃ blk, cfg.block t = some blk ∧ x ∈ blockIn blk (liveOut cfg initial I t)
  outs : ∀ t x, x ∈ getL t O → x ∈ liveOut cfg initial I t
  univ : ∀ t x, x ∈ getL t I → x ∈ U

private structure Universe (cfg : Cfg) (initial : Seed) (U : List Var) : Prop where
  blocks : ∀ blk ∈ cfg.blocks, blk.freeVars ⊆ U
  seeds : ∀ t vars, initial = some (t, vars) → vars ⊆ U

private theorem liveOut_univ {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {I : List (Tid × List Var)} (hI : ∀ t x, x ∈ getL t I → x ∈ U) (t : Tid) :
    liveOut cfg initial I t ⊆ U := by
  intro x hx
  rcases (mem_seedOut _ _ _ _).1 hx with hx | ⟨vars, hi, hv⟩
  · obtain ⟨succ, _, blk, hb, hc⟩ := (mem_blockOut _ _ _ _).1 hx
    rcases hc with ⟨hin, _⟩ | ⟨phi, hphi, value, hget, hfv⟩
    · exact hI _ _ hin
    · refine hU.blocks blk (block_some hb).1 ((mem_blk_freeVars _ _).2 (Or.inr (Or.inl ?_)))
      exact ⟨phi, hphi, (t, value), get_mem_env' hget, hfv⟩
  · exact hU.seeds _ _ hi hv

private theorem blockIn_univ {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {blk : Blk} (hb : blk ∈ cfg.blocks) {out : List Var} (hout : out ⊆ U) : blockIn blk out ⊆ U := by
  intro x hx
  rcases (mem_blockIn _ _ _).1 hx with h | h | ⟨h, _⟩
  · exact hU.blocks blk hb ((mem_blk_freeVars _ _).2 (Or.inl h))
  · exact hU.blocks blk hb ((mem_blk_freeVars _ _).2 (Or.inr (Or.inr h)))
  · exact hout h

private abbrev stepFold (cfg : Cfg) (initial : Seed) (state : List (Tid × List Var) × List (Tid × List Var))
    (tid : Tid) : List (Tid × List Var) × List (Tid × List Var) :=
  match cfg.block tid with
  | none => state
  | some blk =>
    (Assoc.put tid (blockIn blk (liveOut cfg initial state.1 tid)) state.1,
      Assoc.put tid (liveOut cfg initial state.1 tid) state.2)

private theorem livenessStep_eq (cfg : Cfg) (initial : Seed) (ins outs : List (Tid × List Var)) :
    livenessStep cfg initial ins outs = cfg.reachable.reverse.foldl (stepFold cfg initial) (ins, outs) := rfl

private theorem step_preserves {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {I O : List (Tid × List Var)} (h : LiveInv cfg initial U I O) {t : Tid} {blk : Blk}
    (hb : cfg.block t = some blk) :
    let I' := Assoc.put t (blockIn blk (liveOut cfg initial I t)) I
    let O' := Assoc.put t (liveOut cfg initial I t) O
    Le I I' ∧ Le O O' ∧ LiveInv cfg initial U I' O' := by
  intro I' O'
  have hle : Le I I' := by
    intro z x hx
    by_cases hz : z = t
    · subst hz
      show x ∈ getL z (Assoc.put z _ I)
      rw [getL_put_same]
      obtain ⟨b', hb', hm⟩ := h.post z x hx
      rw [hb] at hb'
      cases hb'
      exact hm
    · show x ∈ getL z (Assoc.put t _ I)
      rwa [getL_put_ne hz]
  have hOle : Le O O' := by
    intro z x hx
    by_cases hz : z = t
    · subst hz
      show x ∈ getL z (Assoc.put z _ O)
      rw [getL_put_same]
      exact h.outs z x hx
    · show x ∈ getL z (Assoc.put t _ O)
      rwa [getL_put_ne hz]
  refine ⟨hle, hOle, ?_, ?_, ?_⟩
  · intro z x hx
    by_cases hz : z = t
    · subst hz
      have hx' : x ∈ blockIn blk (liveOut cfg initial I z) := by
        have : x ∈ getL z (Assoc.put z (blockIn blk (liveOut cfg initial I z)) I) := hx
        rwa [getL_put_same] at this
      exact ⟨blk, hb, transfer_mono cfg initial hle z blk hx'⟩
    · have hx' : x ∈ getL z I := by
        have : x ∈ getL z (Assoc.put t (blockIn blk (liveOut cfg initial I t)) I) := hx
        rwa [getL_put_ne hz] at this
      obtain ⟨b', hb', hm⟩ := h.post z x hx'
      exact ⟨b', hb', transfer_mono cfg initial hle z b' hm⟩
  · intro z x hx
    by_cases hz : z = t
    · subst hz
      have hx' : x ∈ liveOut cfg initial I z := by
        have : x ∈ getL z (Assoc.put z (liveOut cfg initial I z) O) := hx
        rwa [getL_put_same] at this
      exact liveOut_mono cfg initial hle z hx'
    · have hx' : x ∈ getL z O := by
        have : x ∈ getL z (Assoc.put t (liveOut cfg initial I t) O) := hx
        rwa [getL_put_ne hz] at this
      exact liveOut_mono cfg initial hle z (h.outs z x hx')
  · intro z x hx
    by_cases hz : z = t
    · subst hz
      have hx' : x ∈ blockIn blk (liveOut cfg initial I z) := by
        have : x ∈ getL z (Assoc.put z (blockIn blk (liveOut cfg initial I z)) I) := hx
        rwa [getL_put_same] at this
      exact blockIn_univ hU (block_some hb).1 (liveOut_univ hU h.univ z) hx'
    · have hx' : x ∈ getL z I := by
        have : x ∈ getL z (Assoc.put t (blockIn blk (liveOut cfg initial I t)) I) := hx
        rwa [getL_put_ne hz] at this
      exact h.univ z x hx'

/-- What one pass over a list of blocks establishes. -/
private structure FoldSpec (cfg : Cfg) (initial : Seed) (U : List Var) (l : List Tid)
    (I O I' O' : List (Tid × List Var)) : Prop where
  inv : LiveInv cfg initial U I' O'
  le : Le I I'
  leO : Le O O'
  inLower : ∀ t ∈ l, ∀ blk, cfg.block t = some blk → blockIn blk (liveOut cfg initial I t) ⊆ getL t I'
  outLower : ∀ t ∈ l, (∃ blk, cfg.block t = some blk) → liveOut cfg initial I t ⊆ getL t O'

private theorem foldSpec (cfg : Cfg) (initial : Seed) {U : List Var} (hU : Universe cfg initial U)
    (l : List Tid) (I O : List (Tid × List Var)) (h : LiveInv cfg initial U I O) :
    FoldSpec cfg initial U l I O (l.foldl (stepFold cfg initial) (I, O)).1
      (l.foldl (stepFold cfg initial) (I, O)).2 := by
  induction l generalizing I O with
  | nil => exact ⟨h, Le.refl _, Le.refl _, by simp, by simp⟩
  | cons t rest ih =>
    simp only [List.foldl_cons]
    cases hb : cfg.block t with
    | none =>
      have hstep : stepFold cfg initial (I, O) t = (I, O) := by simp only [stepFold, hb]
      rw [hstep]
      have hr := ih I O h
      refine ⟨hr.inv, hr.le, hr.leO, ?_, ?_⟩
      · intro z hz blk hblk
        rcases List.mem_cons.1 hz with rfl | hz
        · rw [hb] at hblk
          cases hblk
        · exact hr.inLower z hz blk hblk
      · intro z hz hex x hx
        rcases List.mem_cons.1 hz with rfl | hz
        · obtain ⟨_, hblk⟩ := hex
          rw [hb] at hblk
          cases hblk
        · exact hr.outLower z hz hex hx
    | some blk =>
      have hstep : stepFold cfg initial (I, O) t =
          (Assoc.put t (blockIn blk (liveOut cfg initial I t)) I,
            Assoc.put t (liveOut cfg initial I t) O) := by
        simp only [stepFold, hb]
      rw [hstep]
      obtain ⟨hle, hOle, hinv⟩ := step_preserves hU h hb
      have hr := ih _ _ hinv
      refine ⟨hr.inv, hle.trans hr.le, hOle.trans hr.leO, ?_, ?_⟩
      · intro z hz b hblk x hx
        rcases List.mem_cons.1 hz with rfl | hz
        · rw [hb] at hblk
          cases hblk
          exact hr.le _ _ (by rw [getL_put_same]; exact hx)
        · exact hr.inLower z hz b hblk (transfer_mono cfg initial hle z b hx)
      · intro z hz hex x hx
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hr.leO _ _ (by rw [getL_put_same]; exact hx)
        · exact hr.outLower z hz hex (liveOut_mono cfg initial hle z hx)

private theorem sameSets_iff (keys : List Tid) (a b : List (Tid × List Var)) :
    sameSets keys a b = true ↔ ∀ t ∈ keys, ∀ x, x ∈ getL t a ↔ x ∈ getL t b := by
  show (keys.all fun tid => Bap.Graph.setEq (getL tid a) (getL tid b)) = true ↔ _
  simp only [List.all_eq_true, Bap.Proofs.Graph.setEq_iff]

/-- Sum over the keys of the number of distinct variables in each row. -/
private def card (keys : List Tid) (S : List (Tid × List Var)) : Nat :=
  (keys.map fun t => (getL t S).eraseDups.length).sum

private theorem card_mono (keys : List Tid) {S S' : List (Tid × List Var)} (h : Le S S') :
    card keys S ≤ card keys S' := by
  induction keys with
  | nil => exact Nat.le_refl _
  | cons t ts ih =>
    simp only [card, List.map_cons, List.sum_cons] at ih ⊢
    have : (getL t S).eraseDups.length ≤ (getL t S').eraseDups.length := by
      apply (Bap.Proofs.Graph.nodup_eraseDups _).length_le_of_subset
      intro x hx
      rw [List.mem_eraseDups] at hx ⊢
      exact h t x hx
    omega

private theorem card_lt (keys : List Tid) {S S' : List (Tid × List Var)} (h : Le S S')
    (hne : sameSets keys S' S = false) : card keys S < card keys S' := by
  induction keys with
  | nil => exact absurd hne (by decide : ¬ (true = false)) 
  | cons t ts ih =>
    have hle : (getL t S).eraseDups.length ≤ (getL t S').eraseDups.length := by
      apply (Bap.Proofs.Graph.nodup_eraseDups _).length_le_of_subset
      intro x hx
      rw [List.mem_eraseDups] at hx ⊢
      exact h t x hx
    have hrest := card_mono ts h
    simp only [card, List.map_cons, List.sum_cons] at hrest ⊢
    by_cases htail : sameSets ts S' S = true
    · -- the head row must have grown
      have hhead : ∃ x, x ∈ getL t S' ∧ x ∉ getL t S := by
        refine Classical.byContradiction fun hno => ?_
        have hall : sameSets (t :: ts) S' S = true := by
          rw [sameSets_iff] at htail ⊢
          intro z hz x
          rcases List.mem_cons.1 hz with rfl | hz
          · refine ⟨fun hx => Classical.byContradiction fun hn => hno ⟨x, hx, hn⟩, h z x⟩
          · exact htail z hz x
        rw [hall] at hne
        cases hne
      obtain ⟨x, hx, hnx⟩ := hhead
      have hsub : (getL t S).eraseDups ⊆ (getL t S').eraseDups.erase x := by
        intro y hy
        have hy' : y ∈ getL t S := by simpa [List.mem_eraseDups] using hy
        have hyx : y ≠ x := by
          rintro rfl
          exact hnx hy'
        exact (List.mem_erase_of_ne hyx).2 ((List.mem_eraseDups).2 (h t y hy'))
      have hmem : x ∈ (getL t S').eraseDups := List.mem_eraseDups.2 hx
      have hlen := (Bap.Proofs.Graph.nodup_eraseDups (getL t S)).length_le_of_subset hsub
      rw [List.length_erase_of_mem hmem] at hlen
      have := List.length_pos_of_mem hmem
      omega
    · have := ih (by simpa using htail)
      simp only [card] at this
      omega

private theorem card_le (keys : List Tid) {U : List Var} {S : List (Tid × List Var)}
    (h : ∀ t x, x ∈ getL t S → x ∈ U) : card keys S ≤ U.length * keys.length := by
  induction keys with
  | nil => simp [card]
  | cons t ts ih =>
    simp only [card, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have : (getL t S).eraseDups.length ≤ U.length := by
      apply (Bap.Proofs.Graph.nodup_eraseDups _).length_le_of_subset
      intro x hx
      exact h t x (by simpa [List.mem_eraseDups] using hx)
    rw [Nat.mul_add]
    omega

private theorem livenessAux_succ (cfg : Cfg) (initial : Seed) (fuel : Nat) (ins outs : List (Tid × List Var)) :
    livenessAux cfg initial (fuel + 1) ins outs =
      if sameSets cfg.reachable (livenessStep cfg initial ins outs).1 ins &&
          sameSets cfg.reachable (livenessStep cfg initial ins outs).2 outs then (ins, outs)
      else livenessAux cfg initial fuel (livenessStep cfg initial ins outs).1
        (livenessStep cfg initial ins outs).2 := rfl

/-- The solver result: an invariant-respecting table on which one more pass changes no row. -/
private structure Converged (cfg : Cfg) (initial : Seed) (U : List Var) (r : List (Tid × List Var) × List (Tid × List Var)) : Prop where
  inv : LiveInv cfg initial U r.1 r.2
  ins : sameSets cfg.reachable (livenessStep cfg initial r.1 r.2).1 r.1 = true
  outs : sameSets cfg.reachable (livenessStep cfg initial r.1 r.2).2 r.2 = true

/-- Each pass that changes a table grows a row, and rows are bounded, so the fuel is sufficient. -/
private theorem livenessAux_converged (cfg : Cfg) (initial : Seed) {U : List Var} (hU : Universe cfg initial U)
    (fuel : Nat) (I O : List (Tid × List Var)) (h : LiveInv cfg initial U I O)
    (hOU : ∀ t x, x ∈ getL t O → x ∈ U)
    (hfuel : 2 * U.length * cfg.reachable.length < card cfg.reachable I + card cfg.reachable O + fuel) :
    Converged cfg initial U (livenessAux cfg initial fuel I O) := by
  induction fuel generalizing I O with
  | zero =>
    have h1 := card_le cfg.reachable h.univ
    have h2 := card_le cfg.reachable hOU
    rw [Nat.mul_assoc, Nat.two_mul] at hfuel
    omega
  | succ fuel ih =>
    rw [livenessAux_succ]
    split
    · rename_i hsame
      simp only [Bool.and_eq_true] at hsame
      exact ⟨h, hsame.1, hsame.2⟩
    · rename_i hne
      have hspec := foldSpec cfg initial hU cfg.reachable.reverse I O h
      rw [← livenessStep_eq] at hspec
      apply ih _ _ hspec.inv
      · intro t x hx
        exact liveOut_univ hU hspec.inv.univ t (hspec.inv.outs t x hx)
      · have hmI := card_mono cfg.reachable hspec.le
        have hmO := card_mono cfg.reachable hspec.leO
        by_cases hsI : sameSets cfg.reachable (livenessStep cfg initial I O).1 I = true
        · have hsO : sameSets cfg.reachable (livenessStep cfg initial I O).2 O = false := by
            simpa [hsI] using hne
          have := card_lt cfg.reachable hspec.leO hsO
          omega
        · have := card_lt cfg.reachable hspec.le (by simpa using hsI)
          omega

private theorem getL_empty (l : List Tid) (t : Tid) : getL t (l.map fun tid => (tid, ([] : List Var))) = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hta : t = a
    · subst hta
      simp [getL, Assoc.get]
    · have hb : (t == a) = false := by simpa using hta
      have ih' : (List.lookup t (as.map fun tid => (tid, ([] : List Var)))).getD [] = [] := ih
      simpa [getL, Assoc.get, List.lookup, hb] using ih'

private def universeOf (cfg : Cfg) (vars : List Var) : List Var :=
  (cfg.blocks.flatMap (fun blk => blk.definedVars ++ blk.freeVars) ++ vars).eraseDups

private theorem universeOf_spec (cfg : Cfg) (vars : List Var) (initial : Seed)
    (h : ∀ t vs, initial = some (t, vs) → vs ⊆ vars) : Universe cfg initial (universeOf cfg vars) := by
  constructor
  · intro blk hb x hx
    simp only [universeOf, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨blk, hb, Or.inr hx⟩
  · intro t vs hi x hx
    simp only [universeOf, List.mem_eraseDups, List.mem_append]
    exact Or.inr (h t vs hi hx)

private theorem fuel_eq (cfg : Cfg) (vars : List Var) :
    livenessFuel cfg vars = 2 * (universeOf cfg vars).length * cfg.reachable.length + 1 := rfl

private theorem liveness_converged (cfg : Cfg) : Converged cfg none (universeOf cfg []) cfg.liveness := by
  have hU := universeOf_spec cfg [] none (by simp)
  have hemp : ∀ t x, x ∈ getL t (cfg.reachable.map fun tid => (tid, ([] : List Var))) → False := by
    intro t x hx
    rw [getL_empty] at hx
    simp at hx
  refine livenessAux_converged cfg none hU _ _ _ ⟨?_, ?_, ?_⟩ ?_ ?_
  · exact fun t x hx => (hemp t x hx).elim
  · exact fun t x hx => (hemp t x hx).elim
  · exact fun t x hx => (hemp t x hx).elim
  · exact fun t x hx => (hemp t x hx).elim
  · rw [fuel_eq]
    omega

private theorem livenessFrom_converged (cfg : Cfg) (exit : Tid) (vars : List Var) :
    Converged cfg (some (exit, vars)) (universeOf cfg vars) (cfg.livenessFrom exit vars) := by
  have hU := universeOf_spec cfg vars (some (exit, vars)) (by
    intro t vs h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ List.Subset.refl _)
  have hemp : ∀ t x, x ∈ getL t (cfg.reachable.map fun tid => (tid, ([] : List Var))) → False := by
    intro t x hx
    rw [getL_empty] at hx
    simp at hx
  have hout : ∀ t x, x ∈ getL t (Assoc.put exit vars (cfg.reachable.map fun tid => (tid, ([] : List Var)))) →
      t = exit ∧ x ∈ vars := by
    intro t x hx
    by_cases ht : t = exit
    · subst ht
      rw [getL_put_same] at hx
      exact ⟨rfl, hx⟩
    · rw [getL_put_ne ht] at hx
      exact (hemp t x hx).elim
  refine livenessAux_converged cfg _ hU _ _ _ ⟨?_, ?_, ?_⟩ ?_ ?_
  · exact fun t x hx => (hemp t x hx).elim
  · intro t x hx
    obtain ⟨rfl, hv⟩ := hout t x hx
    exact (mem_seedOut _ _ _ _).2 (Or.inr ⟨vars, rfl, hv⟩)
  · exact fun t x hx => (hemp t x hx).elim
  · intro t x hx
    exact hU.seeds exit vars rfl (hout t x hx).2
  · rw [show livenessFuel cfg vars = _ from fuel_eq cfg vars]
    omega

private theorem converged_equations {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {r : List (Tid × List Var) × List (Tid × List Var)} (hc : Converged cfg initial U r)
    {t : Tid} (ht : t ∈ cfg.reachable) {blk : Blk} (hb : cfg.block t = some blk) (x : Var) :
    (x ∈ getL t r.1 ↔ x ∈ blockIn blk (liveOut cfg initial r.1 t)) ∧
      (x ∈ getL t r.2 ↔ x ∈ liveOut cfg initial r.1 t) := by
  have hspec := foldSpec cfg initial hU cfg.reachable.reverse r.1 r.2 hc.inv
  rw [← livenessStep_eq] at hspec
  have hI := (sameSets_iff _ _ _).1 hc.ins t ht x
  have hO := (sameSets_iff _ _ _).1 hc.outs t ht x
  have htr : t ∈ cfg.reachable.reverse := List.mem_reverse.2 ht
  refine ⟨⟨fun hx => ?_, fun hx => hI.1 (hspec.inLower t htr blk hb hx)⟩,
    ⟨fun hx => hc.inv.outs t x hx, fun hx => hO.1 (hspec.outLower t htr ⟨blk, hb⟩ hx)⟩⟩
  obtain ⟨b', hb', hm⟩ := hc.inv.post t x hx
  rw [hb] at hb'
  cases hb'
  exact hm

/-- Every variable reported live-in at a block is justified by the transfer function. -/
theorem liveness_justified (cfg : Cfg) (t : Tid) (x : Var) (hx : x ∈ (Assoc.get t cfg.liveness.1).getD []) :
    ∃ blk, cfg.block t = some blk ∧ x ∈ blockIn blk (blockOut cfg cfg.liveness.1 t) :=
  (liveness_converged cfg).inv.post t x hx

/-- The solver always converges within its fuel, and its tables satisfy the backward dataflow
equations at every reachable block. -/
theorem liveness_equations (cfg : Cfg) {t : Tid} (ht : t ∈ cfg.reachable) {blk : Blk}
    (hb : cfg.block t = some blk) (x : Var) :
    (x ∈ (Assoc.get t cfg.liveness.1).getD [] ↔ x ∈ blockIn blk (blockOut cfg cfg.liveness.1 t)) ∧
      (x ∈ (Assoc.get t cfg.liveness.2).getD [] ↔ x ∈ blockOut cfg cfg.liveness.1 t) :=
  converged_equations (universeOf_spec cfg [] none (by simp)) (liveness_converged cfg) ht hb x

/-- `livenessFrom` satisfies the same equations with the seed added to the exit's live-out. -/
theorem livenessFrom_equations (cfg : Cfg) (exit : Tid) (vars : List Var) {t : Tid} (ht : t ∈ cfg.reachable)
    {blk : Blk} (hb : cfg.block t = some blk) (x : Var) :
    let r := cfg.livenessFrom exit vars
    (x ∈ (Assoc.get t r.1).getD [] ↔
        Exposed blk.defs x ∨ (∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars) ∨
          ((x ∈ blockOut cfg r.1 t ∨ (t = exit ∧ x ∈ vars)) ∧ ∀ defn ∈ blk.defs, defn.var ≠ x)) ∧
      (x ∈ (Assoc.get t r.2).getD [] ↔ x ∈ blockOut cfg r.1 t ∨ (t = exit ∧ x ∈ vars)) := by
  intro r
  have hU := universeOf_spec cfg vars (some (exit, vars)) (by
    intro t vs h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ List.Subset.refl _)
  have heq := converged_equations hU (livenessFrom_converged cfg exit vars) ht hb x
  have hseed : ∀ y, y ∈ liveOut cfg (some (exit, vars)) r.1 t ↔ y ∈ blockOut cfg r.1 t ∨ (t = exit ∧ y ∈ vars) := by
    intro y
    rw [mem_seedOut]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨vs, ⟨h1, rfl⟩, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1.symm, h2⟩
    · rintro (h | ⟨rfl, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨vars, ⟨rfl, rfl⟩, h⟩
  refine ⟨?_, heq.2.trans (hseed x)⟩
  refine heq.1.trans ?_
  rw [mem_blockIn, hseed]

/-- A seeded exit variable the exit block does not overwrite is live into every predecessor block
whose successor edge it crosses, unless a phi or the predecessor itself assigns it. -/
theorem livenessFrom_reaches_predecessor (cfg : Cfg) {exit pred : Tid} {vars : List Var} {x : Var}
    (hx : x ∈ vars) (hexit : exit ∈ cfg.reachable) (hpred : pred ∈ cfg.reachable)
    (hedge : exit ∈ cfg.successors pred) {eb pb : Blk} (he : cfg.block exit = some eb)
    (hp : cfg.block pred = some pb) (hkill : ∀ defn ∈ eb.defs, defn.var ≠ x)
    (hphi : ∀ phi ∈ eb.phis, phi.var ≠ x) (hpkill : ∀ defn ∈ pb.defs, defn.var ≠ x) :
    x ∈ (Assoc.get pred (cfg.livenessFrom exit vars).1).getD [] := by
  have hin : x ∈ (Assoc.get exit (cfg.livenessFrom exit vars).1).getD [] :=
    (livenessFrom_equations cfg exit vars hexit he x).1.2 (Or.inr (Or.inr ⟨Or.inr ⟨rfl, hx⟩, hkill⟩))
  refine (livenessFrom_equations cfg exit vars hpred hp x).1.2 (Or.inr (Or.inr ⟨Or.inl ?_, hpkill⟩))
  exact (mem_blockOut _ _ _ _).2 ⟨exit, hedge, eb, he, Or.inl ⟨hin, hphi⟩⟩

private theorem fold_below (cfg : Cfg) (initial : Seed) (X : List (Tid × List Var)) (l : List Tid)
    (hX : ∀ t ∈ l, ∀ blk, cfg.block t = some blk → blockIn blk (liveOut cfg initial X t) ⊆ getL t X)
    (I O : List (Tid × List Var)) (hle : Le I X) : Le (l.foldl (stepFold cfg initial) (I, O)).1 X := by
  induction l generalizing I O with
  | nil => exact hle
  | cons t rest ih =>
    simp only [List.foldl_cons]
    have hrest := fun z (hz : z ∈ rest) => hX z (List.mem_cons_of_mem _ hz)
    cases hb : cfg.block t with
    | none =>
      have hstep : stepFold cfg initial (I, O) t = (I, O) := by simp only [stepFold, hb]
      rw [hstep]
      exact ih hrest I O hle
    | some blk =>
      have hstep : stepFold cfg initial (I, O) t =
          (Assoc.put t (blockIn blk (liveOut cfg initial I t)) I,
            Assoc.put t (liveOut cfg initial I t) O) := by
        simp only [stepFold, hb]
      rw [hstep]
      refine ih hrest _ _ ?_
      intro z x hx
      by_cases hz : z = t
      · subst hz
        rw [getL_put_same] at hx
        exact hX z (by simp) blk hb (transfer_mono cfg initial hle z blk hx)
      · rw [getL_put_ne hz] at hx
        exact hle z x hx

private theorem aux_below (cfg : Cfg) (initial : Seed) (X : List (Tid × List Var))
    (hX : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk →
      blockIn blk (liveOut cfg initial X t) ⊆ getL t X)
    (fuel : Nat) (I O : List (Tid × List Var)) (hle : Le I X) :
    Le (livenessAux cfg initial fuel I O).1 X := by
  induction fuel generalizing I O with
  | zero => exact hle
  | succ fuel ih =>
    rw [livenessAux_succ]
    split
    · exact hle
    · apply ih
      rw [livenessStep_eq]
      exact fold_below cfg initial X _ (fun t ht => hX t (List.mem_reverse.1 ht)) I O hle

/-- The solver computes the least solution: it stays below every table closed under the transfer. -/
theorem liveness_least (cfg : Cfg) (X : List (Tid × List Var))
    (hX : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk →
      blockIn blk (blockOut cfg X t) ⊆ (Assoc.get t X).getD [])
    (t : Tid) (x : Var) (hx : x ∈ (Assoc.get t cfg.liveness.1).getD []) :
    x ∈ (Assoc.get t X).getD [] :=
  aux_below cfg none X hX _ _ _ (by intro z y hy; rw [getL_empty] at hy; simp at hy) t x hx

/-! ### Constant environment -/

theorem Constant.ofExp_toExp (c : Constant) :
    Constant.ofExp c.toExp = some ⟨c.width, c.value % 2 ^ c.width⟩ := by
  simp [Constant.ofExp, Constant.toExp]

theorem Constant.toExp_ofExp {e : Exp} {c : Constant} (h : Constant.ofExp e = some c) :
    c.toExp = e := by
  cases e with
  | int value =>
    simp only [Constant.ofExp, Option.some.injEq] at h
    subst h
    simp [Constant.toExp]
  | _ => simp [Constant.ofExp] at h

theorem mem_joinEnv (l r : ConstEnv) (e : Var × Constant) :
    e ∈ joinEnv l r ↔ e ∈ l ∧ Assoc.get e.1 r = some e.2 := by
  show e ∈ l.filter _ ↔ _
  simp

theorem joinEnv_sublist (l r : ConstEnv) : (joinEnv l r).Sublist l :=
  List.filter_sublist

private theorem get_mem_env {β : Type} {k : Var} {v : β} {T : List (Var × β)}
    (h : Assoc.get k T = some v) : (k, v) ∈ T := by
  induction T with
  | nil => simp [Assoc.get] at h
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      simp [Assoc.get] at h
      simp [h]
    · have hb : (k == a) = false := by simpa using hk
      have h' : Assoc.get k es = some v := by simpa [Assoc.get, List.lookup, hb] using h
      exact List.mem_cons_of_mem _ (ih h')

/-- A constant surviving a join is known on both incoming paths. -/
theorem get_joinEnv {l r : ConstEnv} {k : Var} {c : Constant} (h : Assoc.get k (joinEnv l r) = some c) :
    (k, c) ∈ l ∧ Assoc.get k r = some c :=
  (mem_joinEnv l r (k, c)).1 (get_mem_env h)

/-- Substituting store-free expressions neither adds nor removes side effects. -/
theorem hasSideEffect_substitute (rs : List (Var × Exp)) (hrs : ∀ e ∈ rs, hasSideEffect e.2 = false)
    (exp : Exp) : hasSideEffect (Bil.substitute rs exp) = hasSideEffect exp := by
  induction exp generalizing rs with
  | var v =>
    simp only [Bil.substitute]
    cases hg : Assoc.get v rs with
    | none => rfl
    | some e =>
      have := hrs _ (get_mem_env hg)
      simp only [Option.getD_some]
      rw [show hasSideEffect e = false from this]
      unfold_hasSideEffect
  | letIn v val body ih1 ih2 =>
    simp only [Bil.substitute]
    have hf : ∀ e ∈ rs.filter (fun r => r.1 != v), hasSideEffect e.2 = false :=
      fun e he => hrs e (List.mem_filter.1 he).1
    split
    · unfold_hasSideEffect
      rw [ih1 rs hrs, ih2]
      intro e he
      cases List.mem_cons.1 he with
      | inl h => subst h; rfl
      | inr h => exact hf e h
    · unfold_hasSideEffect
      rw [ih1 rs hrs, ih2 _ hf]
  | int v => rfl
  | unknown _ _ => rfl
  | load _ _ _ _ ih1 ih2 =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih1 rs hrs, ih2 rs hrs]
  | store _ _ _ _ _ _ _ _ =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
  | bin _ _ _ ih1 ih2 =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih1 rs hrs, ih2 rs hrs]
  | concat _ _ ih1 ih2 =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih1 rs hrs, ih2 rs hrs]
  | un _ _ ih =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih rs hrs]
  | cast _ _ _ ih =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih rs hrs]
  | extract _ _ _ ih =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih rs hrs]
  | ite _ _ _ ih1 ih2 ih3 =>
    simp only [Bil.substitute]
    unfold_hasSideEffect
    rw [ih1 rs hrs, ih2 rs hrs, ih3 rs hrs]

/-! ### Evaluation of definition lists

There is no IR evaluator in production, so this is the reference semantics for straight-line code:
definitions run in order under `Bil.evalExp`, and the values of top-level stores are recorded. -/

/-- Is this expression a memory write at its top level? -/
def isStoreExp : Exp → Bool
  | .store _ _ _ _ _ => true
  | _ => false

/-- Runs definitions in order, returning the final environment and the values stored. -/
def execDefs (env : Env) : List Def → Except String (Env × List (Var × Value))
  | [] => .ok (env, [])
  | defn :: rest =>
    match evalExp env defn.rhs with
    | .error message => .error message
    | .ok value =>
      match execDefs (Bil.bind env defn.var value) rest with
      | .error message => .error message
      | .ok result => .ok (result.1, if isStoreExp defn.rhs then (defn.var, value) :: result.2 else result.2)

private theorem execDefs_cons {env : Env} {d : Def} {ds : List Def} {r : Env × List (Var × Value)}
    (h : execDefs env (d :: ds) = .ok r) :
    ∃ v r', evalExp env d.rhs = .ok v ∧ execDefs (Bil.bind env d.var v) ds = .ok r' ∧
      r = (r'.1, if isStoreExp d.rhs then (d.var, v) :: r'.2 else r'.2) := by
  simp only [execDefs] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · rename_i r' hr
      simp only [Except.ok.injEq] at h
      exact ⟨v, r', hv, hr, h.symm⟩

private theorem execDefs_cons_ok {env : Env} {d : Def} {ds : List Def} {v : Value} {r' : Env × List (Var × Value)}
    (hv : evalExp env d.rhs = .ok v) (hr : execDefs (Bil.bind env d.var v) ds = .ok r') :
    execDefs env (d :: ds) =
      .ok (r'.1, if isStoreExp d.rhs then (d.var, v) :: r'.2 else r'.2) := by
  simp only [execDefs, hv, hr]

private theorem lookup_bind_same (env : Env) (v : Var) (value : Value) :
    Bil.lookup (Bil.bind env v value) v = .ok value := by
  simp [Bil.lookup, Bil.bind]

private theorem lookup_bind_ne (env : Env) {v x : Var} (value : Value) (h : x ≠ v) :
    Bil.lookup (Bil.bind env v value) x = Bil.lookup env x := by
  have hv : (v == x) = false := by simpa using Ne.symm h
  have key : ∀ l : Env, (l.filter fun b => b.1 != v).find? (fun b => b.1 == x) = l.find? fun b => b.1 == x := by
    intro l
    induction l with
    | nil => rfl
    | cons e es ih =>
      obtain ⟨a, val⟩ := e
      by_cases ha : a = v
      · subst ha
        simp [List.filter_cons, List.find?_cons, hv, ih]
      · have hb : (a != v) = true := by simpa using ha
        simp only [List.filter_cons, hb, ite_true, List.find?_cons, ih]
  simp only [Bil.lookup, Bil.bind, List.find?_cons, hv, key]

/-! ### Dead-code elimination -/

private theorem dceDefs_nil (live : List Var) : dceDefs [] live = ([], live) := rfl

private theorem dceDefs_cons (d : Def) (rest : List Def) (live : List Var) :
    dceDefs (d :: rest) live =
      if (dceDefs rest live).2.contains d.var || hasSideEffect d.rhs then
        (d :: (dceDefs rest live).1, (dceDefs rest live).2.filter (· != d.var) ++ Bil.freeVars d.rhs)
      else dceDefs rest live := rfl

private theorem hasSideEffect_of_isStore {e : Exp} (h : isStoreExp e = true) : hasSideEffect e = true := by
  cases e <;> first | rfl | simp [isStoreExp] at h

theorem dceDefs_sublist (defs : List Def) (live : List Var) : (dceDefs defs live).1.Sublist defs := by
  induction defs with
  | nil => exact List.Sublist.refl _
  | cons d ds ih =>
    rw [dceDefs_cons]
    split
    · exact ih.cons_cons _
    · exact ih.cons _

theorem dceDefs_keeps_effects (defs : List Def) (live : List Var) {d : Def} (hd : d ∈ defs)
    (he : hasSideEffect d.rhs = true) : d ∈ (dceDefs defs live).1 := by
  induction defs with
  | nil => simp at hd
  | cons c cs ih =>
    rw [dceDefs_cons]
    rcases List.mem_cons.1 hd with rfl | hd
    · simp [he]
    · split
      · exact List.mem_cons_of_mem _ (ih hd)
      · exact ih hd

/-- The variables live before the kept definitions are exactly those a backward liveness scan of
the kept definitions gives: read before written, or live after and never written. -/
theorem mem_dceDefs_live (defs : List Def) (live : List Var) (x : Var) :
    x ∈ (dceDefs defs live).2 ↔ Exposed (dceDefs defs live).1 x ∨
      (x ∈ live ∧ ∀ d ∈ (dceDefs defs live).1, d.var ≠ x) := by
  induction defs with
  | nil => simp [dceDefs_nil, Exposed]
  | cons d ds ih =>
    rw [dceDefs_cons]
    split
    · simp only [List.mem_append, List.mem_filter, ih, bne_iff_ne, ne_eq, Exposed, List.mem_cons,
        forall_eq_or_imp]
      grind
    · exact ih

/-- A definition is removed only if it is free of side effects and its variable is not live after
it, that is, no kept later definition reads it before a kept redefinition and it is not live out. -/
theorem dceDefs_removed_unused (d : Def) (rest : List Def) (live : List Var)
    (hremoved : (dceDefs (d :: rest) live).1 = (dceDefs rest live).1) :
    hasSideEffect d.rhs = false ∧ d.var ∉ (dceDefs rest live).2 := by
  rw [dceDefs_cons] at hremoved
  split at hremoved
  · have := congrArg List.length hremoved
    simp at this
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.contains_eq_mem,
      decide_eq_false_iff_not] at hc
    exact ⟨hc.2, hc.1⟩

/-- Agreement of two environments on a set of variables. -/
def Agree (vs : List Var) (e₁ e₂ : Env) : Prop := ∀ x ∈ vs, Bil.lookup e₁ x = Bil.lookup e₂ x

/-- Running only the kept definitions from an environment agreeing on the live-before set succeeds
whenever the original does, agrees on the live-after set, and stores the same values. -/
theorem dceDefs_simulation (defs : List Def) (live : List Var) {env env' : Env}
    (hag : Agree (dceDefs defs live).2 env env') {r : Env × List (Var × Value)}
    (h : execDefs env defs = .ok r) :
    ∃ r', execDefs env' (dceDefs defs live).1 = .ok r' ∧ Agree live r.1 r'.1 ∧ r'.2 = r.2 := by
  induction defs generalizing env env' r with
  | nil =>
    simp only [execDefs, Except.ok.injEq] at h
    subst h
    exact ⟨(env', []), rfl, hag, rfl⟩
  | cons d ds ih =>
    obtain ⟨v, r₁, hv, hr₁, rfl⟩ := execDefs_cons h
    rw [dceDefs_cons] at hag ⊢
    split at hag
    · rename_i hc
      simp only [hc, ↓reduceIte]
      have hv' : evalExp env' d.rhs = .ok v := by
        rw [← hv]
        exact (Bap.Proofs.Bil.evalExp_congr_freeVars d.rhs fun x hx =>
          hag x (List.mem_append_right _ hx)).symm
      have hag' : Agree (dceDefs ds live).2 (Bil.bind env d.var v) (Bil.bind env' d.var v) := by
        intro x hx
        by_cases hxd : x = d.var
        · subst hxd
          rw [lookup_bind_same, lookup_bind_same]
        · rw [lookup_bind_ne _ _ hxd, lookup_bind_ne _ _ hxd]
          exact hag x (List.mem_append_left _ (List.mem_filter.2 ⟨hx, by simpa using hxd⟩))
      obtain ⟨r₂, hr₂, hl, ht⟩ := ih hag' hr₁
      refine ⟨_, execDefs_cons_ok hv' hr₂, hl, ?_⟩
      simp only [ht]
    · rename_i hc
      simp only [hc, ↓reduceIte]
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.contains_eq_mem,
        decide_eq_false_iff_not] at hc
      have hag' : Agree (dceDefs ds live).2 (Bil.bind env d.var v) env' := by
        intro x hx
        have hxd : x ≠ d.var := by
          rintro rfl
          exact hc.1 hx
        rw [lookup_bind_ne _ _ hxd]
        exact hag x hx
      obtain ⟨r₂, hr₂, hl, ht⟩ := ih hag' hr₁
      refine ⟨r₂, hr₂, hl, ?_⟩
      have hns : isStoreExp d.rhs = false := by
        cases hs : isStoreExp d.rhs with
        | false => rfl
        | true =>
          have := hasSideEffect_of_isStore hs
          rw [this] at hc
          cases hc.2
      simp only [hns, Bool.false_eq_true, ite_false, ht]

private abbrev dceLive (cfg : Cfg) (blk : Blk) : List Var :=
  (Assoc.get blk.tid cfg.liveness.2).getD [] ++ blk.jmps.flatMap Jmp.freeVars

private def dceBlk (cfg : Cfg) (blk : Blk) : Blk :=
  { blk with
    defs := (dceDefs blk.defs (dceLive cfg blk)).1
    phis := blk.phis.filter fun phi => (dceDefs blk.defs (dceLive cfg blk)).2.contains phi.var }

private theorem dcePass_eq (cfg : Cfg) : dcePass cfg = { cfg with blocks := cfg.blocks.map (dceBlk cfg) } := rfl

/-- A phi is removed only if its variable is not live on block entry. -/
theorem dcePass_phi_removed_unused (cfg : Cfg) {blk : Blk} {phi : Phi} (hphi : phi ∈ blk.phis)
    (hremoved : phi ∉ (dceBlk cfg blk).phis) : phi.var ∉ (dceDefs blk.defs (dceLive cfg blk)).2 := by
  intro hlive
  apply hremoved
  exact List.mem_filter.2 ⟨hphi, by simpa using hlive⟩

private abbrev weight (blocks : List Blk) : Nat :=
  (blocks.map fun blk => blk.defs.length + blk.phis.length).sum

private theorem dceAux_succ (cfg : Cfg) (fuel : Nat) :
    dceAux cfg (fuel + 1) =
      if (cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)) =
          ((dcePass cfg).blocks.map fun blk => (blk.defs.length, blk.phis.length))
      then cfg else dceAux (dcePass cfg) fuel := rfl

private theorem weight_cons (b : Blk) (bs : List Blk) :
    weight (b :: bs) = b.defs.length + b.phis.length + weight bs := by
  simp [weight]

private theorem foldl_count (blocks : List Blk) (acc : Nat) :
    blocks.foldl (fun count blk => count + blk.defs.length + blk.phis.length) acc = acc + weight blocks := by
  induction blocks generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, weight_cons]
    omega

private theorem eliminateDeadCode_eq (cfg : Cfg) : eliminateDeadCode cfg = dceAux cfg (weight cfg.blocks + 1) := by
  show dceAux cfg (cfg.blocks.foldl _ 0 + 1) = _
  rw [foldl_count, Nat.zero_add]

private theorem dceBlk_defs_le (cfg : Cfg) (b : Blk) : (dceBlk cfg b).defs.length ≤ b.defs.length :=
  (dceDefs_sublist ..).length_le

private theorem dceBlk_phis_le (cfg : Cfg) (b : Blk) : (dceBlk cfg b).phis.length ≤ b.phis.length :=
  List.length_filter_le ..

private theorem weight_dce_le (cfg : Cfg) (l : List Blk) : weight (l.map (dceBlk cfg)) ≤ weight l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    rw [List.map_cons, weight_cons, weight_cons]
    have := dceBlk_defs_le cfg b
    have := dceBlk_phis_le cfg b
    omega

private theorem weight_dce_lt (cfg : Cfg) (l : List Blk)
    (h : (l.map fun blk => (blk.defs.length, blk.phis.length)) ≠
      ((l.map (dceBlk cfg)).map fun blk => (blk.defs.length, blk.phis.length))) :
    weight (l.map (dceBlk cfg)) < weight l := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rw [List.map_cons, weight_cons, weight_cons]
    have h1 := dceBlk_defs_le cfg b
    have h2 := dceBlk_phis_le cfg b
    have h3 := weight_dce_le cfg bs
    by_cases hb : (b.defs.length, b.phis.length) = ((dceBlk cfg b).defs.length, (dceBlk cfg b).phis.length)
    · have htail : (bs.map fun blk => (blk.defs.length, blk.phis.length)) ≠
          ((bs.map (dceBlk cfg)).map fun blk => (blk.defs.length, blk.phis.length)) := by
        intro heq
        apply h
        simp only [List.map_cons, heq, hb]
      have := ih htail
      omega
    · have : (dceBlk cfg b).defs.length < b.defs.length ∨ (dceBlk cfg b).phis.length < b.phis.length := by
        refine Classical.byContradiction fun hc => hb ?_
        simp only [Prod.mk.injEq]
        omega
      omega

private theorem dce_self_of_shape (cfg : Cfg) (l : List Blk)
    (h : (l.map fun blk => (blk.defs.length, blk.phis.length)) =
      ((l.map (dceBlk cfg)).map fun blk => (blk.defs.length, blk.phis.length))) :
    l.map (dceBlk cfg) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hd, hp⟩, ht⟩ := h
    rw [List.map_cons, ih ht]
    congr 1
    have hd' : (dceDefs b.defs (dceLive cfg b)).1 = b.defs :=
      (dceDefs_sublist ..).eq_of_length hd.symm
    have hp' := List.filter_eq_self.2 (List.length_filter_eq_length_iff.1 hp.symm)
    simp only [dceBlk, hd', hp']

/-- With fuel above the number of definitions, dead-code elimination reaches a pass fixpoint. -/
private theorem dceAux_fixpoint (cfg : Cfg) (fuel : Nat) (hfuel : weight cfg.blocks < fuel) :
    dcePass (dceAux cfg fuel) = dceAux cfg fuel := by
  induction fuel generalizing cfg with
  | zero => omega
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · rename_i heq
      rw [dcePass_eq]
      have := dce_self_of_shape cfg cfg.blocks heq
      simp only [this]
    · rename_i hne
      apply ih
      have := weight_dce_lt cfg cfg.blocks hne
      show weight (cfg.blocks.map (dceBlk cfg)) < fuel
      omega

/-- The output of dead-code elimination is stable under one more pass. -/
theorem dcePass_eliminateDeadCode (cfg : Cfg) :
    dcePass (eliminateDeadCode cfg) = eliminateDeadCode cfg := by
  rw [eliminateDeadCode_eq]
  exact dceAux_fixpoint cfg _ (Nat.lt_succ_self _)

/-- Dead-code elimination is idempotent. -/
theorem eliminateDeadCode_idempotent (cfg : Cfg) :
    eliminateDeadCode (eliminateDeadCode cfg) = eliminateDeadCode cfg := by
  conv => lhs; rw [eliminateDeadCode_eq (eliminateDeadCode cfg)]
  rw [dceAux_succ, dcePass_eliminateDeadCode]
  simp

/-- Variables read by the jumps of a block. -/
abbrev jumpVars (blk : Blk) : List Var := blk.jmps.flatMap Jmp.freeVars

/-- One-to-one block relation: same identity and jumps, statements only removed, effects kept, and
every successful run of the original is matched by the smaller block on everything the jumps read. -/
private def DceRel (x y : Blk) : Prop :=
  x.tid = y.tid ∧ x.jmps = y.jmps ∧ x.defs.Sublist y.defs ∧ x.phis.Sublist y.phis ∧
    (∀ d ∈ y.defs, hasSideEffect d.rhs = true → d ∈ x.defs) ∧
    ∀ env r, execDefs env y.defs = .ok r → ∃ r', execDefs env x.defs = .ok r' ∧
      Agree (jumpVars y) r.1 r'.1 ∧ r'.2 = r.2

private def Shrinks : List Blk → List Blk → Prop
  | [], [] => True
  | x :: xs, y :: ys => DceRel x y ∧ Shrinks xs ys
  | _, _ => False

private theorem Shrinks.refl : (l : List Blk) → Shrinks l l
  | [] => trivial
  | b :: bs => ⟨⟨rfl, rfl, List.Sublist.refl _, List.Sublist.refl _, fun _ h _ => h,
      fun env r h => ⟨r, h, fun _ _ => rfl, rfl⟩⟩, Shrinks.refl bs⟩

private theorem DceRel.trans {a b c : Blk} (h₁ : DceRel a b) (h₂ : DceRel b c) : DceRel a c := by
  obtain ⟨t₁, j₁, d₁, p₁, e₁, s₁⟩ := h₁
  obtain ⟨t₂, j₂, d₂, p₂, e₂, s₂⟩ := h₂
  refine ⟨t₁.trans t₂, j₁.trans j₂, d₁.trans d₂, p₁.trans p₂, fun d hd hs => e₁ d (e₂ d hd hs) hs, ?_⟩
  intro env r hr
  obtain ⟨r', hr', ha, ht⟩ := s₂ env r hr
  obtain ⟨r'', hr'', ha', ht'⟩ := s₁ env r' hr'
  refine ⟨r'', hr'', fun x hx => ?_, ht'.trans ht⟩
  rw [ha x hx]
  exact ha' x (by simp only [jumpVars, j₂] at hx ⊢; exact hx)

private theorem Shrinks.trans : {a b c : List Blk} → Shrinks a b → Shrinks b c → Shrinks a c
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ => ⟨h₁.trans h₂, Shrinks.trans t₁ t₂⟩

private theorem Shrinks.tids : {a b : List Blk} → Shrinks a b → a.map Blk.tid = b.map Blk.tid
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, t⟩ => by simp [h.1, Shrinks.tids t]

private theorem dceBlk_rel (cfg : Cfg) (b : Blk) : DceRel (dceBlk cfg b) b := by
  refine ⟨rfl, rfl, dceDefs_sublist .., List.filter_sublist, ?_, ?_⟩
  · intro d hd hs
    exact dceDefs_keeps_effects _ _ hd hs
  · intro env r hr
    obtain ⟨r', hr', ha, ht⟩ := dceDefs_simulation b.defs (dceLive cfg b)
      (env := env) (env' := env) (fun _ _ => rfl) hr
    exact ⟨r', hr', fun x hx => ha x (List.mem_append_right _ hx), ht⟩

private theorem shrinks_dce (cfg : Cfg) (l : List Blk) : Shrinks (l.map (dceBlk cfg)) l := by
  induction l with
  | nil => trivial
  | cons b bs ih => exact ⟨dceBlk_rel cfg b, ih⟩

private structure DceFrame (a b : Cfg) : Prop where
  start : b.start = a.start
  graph : b.graph = a.graph
  shrinks : Shrinks b.blocks a.blocks

private theorem dceAux_frame (cfg : Cfg) (fuel : Nat) : DceFrame cfg (dceAux cfg fuel) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨rfl, rfl, Shrinks.refl _⟩
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · exact ⟨rfl, rfl, Shrinks.refl _⟩
    · have h := ih (dcePass cfg)
      exact ⟨h.start, h.graph, Shrinks.trans h.shrinks (shrinks_dce cfg cfg.blocks)⟩

private theorem eliminateDeadCode_frame (cfg : Cfg) : DceFrame cfg (eliminateDeadCode cfg) := by
  rw [eliminateDeadCode_eq]
  exact dceAux_frame cfg _

@[simp] theorem eliminateDeadCode_start (cfg : Cfg) : (eliminateDeadCode cfg).start = cfg.start :=
  (eliminateDeadCode_frame cfg).start

@[simp] theorem eliminateDeadCode_graph (cfg : Cfg) : (eliminateDeadCode cfg).graph = cfg.graph :=
  (eliminateDeadCode_frame cfg).graph

theorem eliminateDeadCode_tids (cfg : Cfg) :
    (eliminateDeadCode cfg).blocks.map Blk.tid = cfg.blocks.map Blk.tid :=
  (eliminateDeadCode_frame cfg).shrinks.tids

private theorem Shrinks.pointwise {a b : List Blk} (h : Shrinks a b) {y : Blk} (hy : y ∈ b) :
    ∃ x ∈ a, DceRel x y := by
  induction b generalizing a with
  | nil => simp at hy
  | cons z zs ih =>
    match a, h with
    | x :: xs, ⟨hx, ht⟩ =>
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨x, by simp, hx⟩
      · obtain ⟨w, hw, hr⟩ := ih ht hy
        exact ⟨w, List.mem_cons_of_mem _ hw, hr⟩

/-- Every input block has an output block with the same tid and jumps, whose statements form a
sublist of the input, which holds every side-effecting definition, and which simulates the input:
any successful run succeeds on the output, agrees on what the jumps read, and stores the same. -/
theorem eliminateDeadCode_block_spec (cfg : Cfg) {y : Blk} (hy : y ∈ cfg.blocks) :
    ∃ x ∈ (eliminateDeadCode cfg).blocks, x.tid = y.tid ∧ x.jmps = y.jmps ∧
      x.defs.Sublist y.defs ∧ x.phis.Sublist y.phis ∧
      (∀ d ∈ y.defs, hasSideEffect d.rhs = true → d ∈ x.defs) ∧
      ∀ env r, execDefs env y.defs = .ok r → ∃ r', execDefs env x.defs = .ok r' ∧
        Agree (jumpVars y) r.1 r'.1 ∧ r'.2 = r.2 :=
  (eliminateDeadCode_frame cfg).shrinks.pointwise hy

/-! ### Constant propagation -/

private abbrev propStep (state : List Def × ConstEnv) (defn : Def) : List Def × ConstEnv :=
  let rhs := Bil.simplifyExp (Bil.substitute (constReplacements state.2) defn.rhs)
  let env := match Constant.ofExp rhs with
    | some constant => Assoc.put defn.var constant state.2
    | none => Assoc.remove defn.var state.2
  (state.1 ++ [{ defn with rhs := rhs }], env)

private abbrev propEntry (blk : Blk) (env : ConstEnv) : ConstEnv :=
  env.filter fun entry => entry.1 ∉ blk.phis.map Phi.var

private abbrev propFold (blk : Blk) (env : ConstEnv) : List Def × ConstEnv :=
  blk.defs.foldl propStep ([], propEntry blk env)

/-- The rewriting of a jump expression under the constants known at block exit. -/
private abbrev propJump (env : ConstEnv) (exp : Exp) : Exp :=
  Bil.simplifyExp (Bil.substitute (constReplacements env) exp)

private theorem propagateBlock_eq (blk : Blk) (env : ConstEnv) :
    propagateBlock blk env =
      ({ blk with
          phis := blk.phis.map fun phi =>
            { phi with values := phi.values.map fun input => (input.1, Bil.simplifyExp input.2) }
          defs := (propFold blk env).1
          jmps := blk.jmps.map (Jmp.mapExp (propJump (propFold blk env).2)) },
        (propFold blk env).2) := rfl

private theorem propagateBlock_tid (blk : Blk) (env : ConstEnv) : (propagateBlock blk env).1.tid = blk.tid := rfl

private theorem propagateBlock_successors (blk : Blk) (env : ConstEnv) :
    (propagateBlock blk env).1.successors = blk.successors := by
  show ((blk.jmps.map (Jmp.mapExp _)).flatMap Jmp.successors).eraseDups = _
  simp only [List.flatMap_map, Jmp.successors_mapExp]
  rfl

/-- All constants in the table hold in the environment. -/
def ConstHold (env : Env) (constants : ConstEnv) : Prop :=
  ∀ k c, (k, c) ∈ constants → Bil.lookup env k = .ok (.bits (BitVec.ofNat c.width c.value))

private theorem eval_replaced {env : Env} {c : ConstEnv} (h : ConstHold env c) {e : Exp} {v : Value}
    (he : evalExp env e = .ok v) : evalExp env (propJump c e) = .ok v := by
  apply Bap.Proofs.Bil.evalExp_simplifyExp
  rw [← he]
  apply Bap.Proofs.Bil.evalExp_substitute
  · intro x _
    cases hg : Assoc.get x (constReplacements c) with
    | none => rfl
    | some r =>
      have hm := get_mem_env' hg
      obtain ⟨⟨k, cst⟩, hk, heq⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [h _ _ hk]
      rfl

private theorem mem_of_mem_remove {β : Type} {v k : Var} {x : β} {l : List (Var × β)}
    (h : (k, x) ∈ Assoc.remove v l) : (k, x) ∈ l ∧ k ≠ v := by
  have := List.mem_filter.1 h
  exact ⟨this.1, by simpa using this.2⟩

private theorem store_not_bits (env : Env) (m a v : Exp) (e : Endian) (n w : Nat) (b : BitVec w) :
    evalExp env (.store m a v e n) ≠ .ok (.bits b) := by
  intro h
  rw [evalExp] at h
  simp only [Bind.bind, Except.bind] at h
  repeat' split at h
  all_goals cases h

private theorem simplify_store (m a v : Exp) (e : Endian) (n : Nat) :
    isStoreExp (Bil.simplifyExp (.store m a v e n)) = true := by
  rw [Bil.simplifyExp]
  split
  · rename_i hev
    exact absurd hev (store_not_bits _ _ _ _ _ _ _ _)
  · rfl

private theorem isStore_propJump {c : ConstEnv} {e : Exp} (h : isStoreExp e = true) :
    isStoreExp (propJump c e) = true := by
  cases e with
  | store m a v en n => exact simplify_store _ _ _ _ _
  | _ => simp [isStoreExp] at h

/-- Rewriting definitions under true constants keeps the run: same final environment, every stored
value still stored, and the constants at exit hold. -/
private theorem propStep_sim (defs : List Def) (acc : List Def) (c : ConstEnv) (env : Env)
    (hc : ConstHold env c) {r : Env × List (Var × Value)} (h : execDefs env defs = .ok r) :
    ∃ tail r', (defs.foldl propStep (acc, c)).1 = acc ++ tail ∧ execDefs env tail = .ok r' ∧ r'.1 = r.1 ∧
      r.2.Sublist r'.2 ∧ ConstHold r.1 (defs.foldl propStep (acc, c)).2 := by
  induction defs generalizing acc c env r with
  | nil =>
    simp only [execDefs, Except.ok.injEq] at h
    subst h
    exact ⟨[], (env, []), by simp, rfl, rfl, List.Sublist.refl _, hc⟩
  | cons d ds ih =>
    obtain ⟨v, r₁, hv, hr₁, rfl⟩ := execDefs_cons h
    simp only [List.foldl_cons]
    have hv' := eval_replaced hc hv
    have hc' : ConstHold (Bil.bind env d.var v) (propStep (acc, c) d).2 := by
      intro k cst hm
      simp only [propStep] at hm
      split at hm
      · rename_i cc hof
        by_cases hk : k = d.var
        · subst hk
          rw [lookup_bind_same]
          have hkc : cst = cc := by
            rcases List.mem_cons.1 hm with heq | hm'
            · simp only [Prod.mk.injEq] at heq
              exact heq.2
            · have := (List.mem_filter.1 hm').2
              simp at this
          subst hkc
          have htoExp := Constant.toExp_ofExp hof
          have hv₂ : evalExp env cst.toExp = .ok v := by
            rw [htoExp]
            exact hv'
          have hval : evalExp env cst.toExp = .ok (.bits (BitVec.ofNat cst.width cst.value)) := rfl
          rw [hval] at hv₂
          exact hv₂.symm
        · rw [lookup_bind_ne _ _ hk]
          rcases List.mem_cons.1 hm with heq | hm'
          · simp only [Prod.mk.injEq] at heq
            exact absurd heq.1 hk
          · exact hc k cst (List.mem_filter.1 hm').1
      · have := mem_of_mem_remove hm
        rw [lookup_bind_ne _ _ this.2]
        exact hc k cst this.1
    obtain ⟨tail, r', hfold, hexec, hr, hsub, hout⟩ := ih _ _ _ hc' hr₁
    refine ⟨{ d with rhs := propJump c d.rhs } :: tail,
      (r'.1, if isStoreExp (propJump c d.rhs) then (d.var, v) :: r'.2 else r'.2), ?_, ?_, hr, ?_, hout⟩
    · rw [hfold]
      simp [propStep, propJump]
    · exact execDefs_cons_ok hv' hexec
    · by_cases hs : isStoreExp d.rhs = true
      · simp only [hs, ite_true, isStore_propJump hs]
        exact hsub.cons_cons _
      · simp only [hs, Bool.false_eq_true, ite_false]
        split
        · exact hsub.cons _
        · exact hsub

/-- Expressions a jump evaluates. -/
def labelExps : Label → List Exp
  | .direct _ => []
  | .indirect target => [target]

def jmpExps (jmp : Jmp) : List Exp :=
  jmp.condition.toList ++ match jmp.kind with
    | .goto target | .ret target => labelExps target
    | .call target returnTo => labelExps target ++ (returnTo.map labelExps).getD []
    | .interrupt _ _ => []

theorem jmpExps_mapExp (f : Exp → Exp) (jmp : Jmp) : jmpExps (jmp.mapExp f) = (jmpExps jmp).map f := by
  obtain ⟨tid, condition, kind⟩ := jmp
  have hl : ∀ l : Label, labelExps (l.mapExp f) = (labelExps l).map f := by
    intro l
    cases l <;> rfl
  cases condition <;> cases kind with
  | call target returnTo =>
    cases returnTo <;> simp [jmpExps, Jmp.mapExp, JmpKind.mapExp, hl]
  | _ => simp [jmpExps, Jmp.mapExp, JmpKind.mapExp, hl]

theorem freeVars_of_jmpExps {jmp : Jmp} {e : Exp} (he : e ∈ jmpExps jmp) : Bil.freeVars e ⊆ jmp.freeVars := by
  obtain ⟨tid, condition, kind⟩ := jmp
  intro x hx
  simp only [Jmp.freeVars, List.mem_eraseDups, List.mem_append]
  simp only [jmpExps, List.mem_append] at he
  rcases he with he | he
  · left
    cases condition with
    | none => simp at he
    | some c =>
      simp only [Option.toList_some, List.mem_singleton] at he
      subst he
      simpa using hx
  · right
    have hl : ∀ {l : Label}, e ∈ labelExps l → x ∈ l.freeVars := by
      intro l hel
      cases l with
      | direct _ => simp [labelExps] at hel
      | indirect t =>
        simp only [labelExps, List.mem_singleton] at hel
        subst hel
        exact hx
    cases kind with
    | goto t => exact hl he
    | ret t => exact hl he
    | call t r =>
      simp only [JmpKind.freeVars, List.mem_eraseDups, List.mem_append]
      simp only [List.mem_append] at he
      rcases he with he | he
      · exact Or.inl (hl he)
      · cases r with
        | none => simp at he
        | some l =>
          simp only [Option.map_some, Option.getD_some] at he ⊢
          exact Or.inr (hl he)
    | interrupt _ _ => simp at he

/-- The rewrite of a block under true constants at entry: the rewritten block runs to the same
environment, stores at least the same values, and its jumps evaluate to the same values. -/
theorem propagateBlock_sim {blk : Blk} {c : ConstEnv} {env : Env} (hc : ConstHold env (propEntry blk c))
    {r : Env × List (Var × Value)} (h : execDefs env blk.defs = .ok r) :
    ∃ r', execDefs env (propagateBlock blk c).1.defs = .ok r' ∧ r'.1 = r.1 ∧ r.2.Sublist r'.2 ∧
      ConstHold r.1 (propagateBlock blk c).2 ∧
      ∃ g, (propagateBlock blk c).1.jmps = blk.jmps.map (Jmp.mapExp g) ∧
        ∀ e v, evalExp r.1 e = .ok v → evalExp r.1 (g e) = .ok v := by
  obtain ⟨tail, r', hfold, hexec, hr, hsub, hout⟩ :=
    propStep_sim blk.defs [] (propEntry blk c) env hc h
  have hdefs : (propagateBlock blk c).1.defs = tail := by
    rw [propagateBlock_eq]
    simpa using hfold
  refine ⟨r', by rw [hdefs]; exact hexec, hr, hsub, hout, propJump (propFold blk c).2, ?_, ?_⟩
  · rw [propagateBlock_eq]
  · exact fun e v he => eval_replaced hout he

/-- A run through blocks along CFG edges. A phi on entry may change only the phi's variable. -/
inductive PropRun (cfg : Cfg) : Tid → Env → Prop where
  | start (env : Env) : PropRun cfg cfg.start env
  | step {t t' : Tid} {env env' : Env} {blk blk' : Blk} {r : Env × List (Var × Value)} :
    PropRun cfg t env → cfg.block t = some blk → execDefs env blk.defs = .ok r →
    t' ∈ cfg.successors t → cfg.block t' = some blk' →
    (∀ x, (∀ phi ∈ blk'.phis, phi.var ≠ x) → Bil.lookup env' x = Bil.lookup r.1 x) →
    PropRun cfg t' env'

private theorem mem_join {first : ConstEnv} {rest : List ConstEnv} {e : Var × Constant}
    (h : e ∈ rest.foldl joinEnv first) : e ∈ first ∧ ∀ l ∈ rest, e ∈ l := by
  induction rest generalizing first with
  | nil => simpa using h
  | cons m ms ih =>
    obtain ⟨h₁, h₂⟩ := ih h
    have := (mem_joinEnv first m e).1 h₁
    refine ⟨this.1, ?_⟩
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact get_mem_env' this.2
    · exact h₂ l hl

private theorem entryEnv_mem {cfg : Cfg} {exits : ExitEnvs} {t pred : Tid} {E : ConstEnv} {e : Var × Constant}
    (he : e ∈ entryEnv cfg exits t) (hpred : pred ∈ cfg.predecessors t) (hget : Assoc.get pred exits = some E) :
    e ∈ E := by
  have heq : entryEnv cfg exits t = if t = cfg.start then [] else
      match (cfg.predecessors t).filterMap fun pred => Assoc.get pred exits with
      | [] => []
      | first :: rest => rest.foldl joinEnv first := rfl
  rw [heq] at he
  split at he
  · simp at he
  · have hE : E ∈ (cfg.predecessors t).filterMap fun pred => Assoc.get pred exits :=
      List.mem_filterMap.2 ⟨pred, hpred, hget⟩
    split at he
    · simp at he
    · rename_i first rest hl
      rw [hl] at hE
      obtain ⟨h₁, h₂⟩ := mem_join he
      rcases List.mem_cons.1 hE with rfl | hm
      · exact h₁
      · exact h₂ _ hm

private theorem isSolved_spec {cfg : Cfg} {exits : ExitEnvs} (h : isSolved cfg exits = true) {blk : Blk}
    (hb : blk ∈ cfg.blocks) :
    Assoc.get blk.tid exits = some (propagateBlock blk (entryEnv cfg exits blk.tid)).2 := by
  have := List.all_eq_true.1 h blk hb
  simpa using this

/-- At a fixpoint, the constants the analysis assigns to a block entry hold on every run. -/
theorem fixpoint_constants_hold {cfg : Cfg} {exits : ExitEnvs} (hsolved : isSolved cfg exits = true)
    {t : Tid} {env : Env} (hrun : PropRun cfg t env) {blk : Blk} (hb : cfg.block t = some blk) :
    ConstHold env (propEntry blk (entryEnv cfg exits t)) := by
  induction hrun generalizing blk with
  | start env =>
    intro k c hm
    have heq : entryEnv cfg exits cfg.start = [] := by
      show (if cfg.start = cfg.start then [] else _) = []
      simp
    rw [heq] at hm
    simp at hm
  | @step t t' env env' p p' r _ hp hexec hsucc hp' hagree ih =>
    rw [hp'] at hb
    cases hb
    intro k c hm
    obtain ⟨hentry, hnot⟩ := List.mem_filter.1 hm
    have hnot' : ∀ phi ∈ p'.phis, phi.var ≠ k := by
      intro phi hphi heq
      apply of_decide_eq_true hnot
      exact List.mem_map.2 ⟨phi, hphi, heq⟩
    rw [hagree k hnot']
    have hc := ih hp
    obtain ⟨hmem, htid⟩ := block_some hp
    have hget := isSolved_spec hsolved hmem
    rw [htid] at hget
    obtain ⟨_, _, _, _, hout, _⟩ := propagateBlock_sim hc hexec
    have hpred : t ∈ cfg.predecessors t' := by
      have := (Bap.Graph.successors_mem cfg.graph t t').1 hsucc
      exact (mem_predecessors' _ _ _).2 this
    exact hout k c (entryEnv_mem hentry hpred hget)

private abbrev solution (cfg : Cfg) : ExitEnvs :=
  propagateAux cfg.prune
    (((cfg.prune.blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars).eraseDups.length + 2) *
      (cfg.prune.blocks.length + 2) * (cfg.prune.graph.edges.length + 2)) [] [cfg.prune.start]

private abbrev constAt (cfg : Cfg) (t : Tid) : ConstEnv :=
  if isSolved cfg.prune (solution cfg) then entryEnv cfg.prune (solution cfg) t else []

private theorem propagateConstants_eq (cfg : Cfg) :
    propagateConstants cfg =
      { cfg.prune with blocks := cfg.prune.blocks.map fun blk => (propagateBlock blk (constAt cfg blk.tid)).1 } := rfl

/-- The rewrite only uses constants that hold: on any run reaching a reachable block, the rewritten
block is a correct replacement for the original. This covers loops, where a constant is used only if
every path into the block agrees on it. -/
theorem propagateConstants_correct (cfg : Cfg) {t : Tid} {env : Env} (hrun : PropRun cfg.prune t env)
    {blk : Blk} (hb : cfg.prune.block t = some blk) {r : Env × List (Var × Value)}
    (h : execDefs env blk.defs = .ok r) :
    ∃ blk' ∈ (propagateConstants cfg).blocks, blk'.tid = t ∧ ∃ r',
      execDefs env blk'.defs = .ok r' ∧ r'.1 = r.1 ∧ r.2.Sublist r'.2 ∧
      ∃ g, blk'.jmps = blk.jmps.map (Jmp.mapExp g) ∧
        ∀ e v, evalExp r.1 e = .ok v → evalExp r.1 (g e) = .ok v := by
  obtain ⟨hmem, htid⟩ := block_some hb
  have hc : ConstHold env (propEntry blk (constAt cfg blk.tid)) := by
    by_cases hsolved : isSolved cfg.prune (solution cfg) = true
    · simp only [constAt, hsolved, ↓reduceIte, htid]
      exact fixpoint_constants_hold hsolved hrun hb
    · simp only [constAt, hsolved, ↓reduceIte]
      intro k c hm
      simp at hm
  refine ⟨(propagateBlock blk (constAt cfg blk.tid)).1, ?_, htid, ?_⟩
  · rw [propagateConstants_eq]
    exact List.mem_map.2 ⟨blk, hmem, rfl⟩
  · obtain ⟨r', h₁, h₂, h₃, _, h₄⟩ := propagateBlock_sim hc h
    exact ⟨r', h₁, h₂, h₃, h₄⟩

@[simp] theorem propagateConstants_start (cfg : Cfg) : (propagateConstants cfg).start = cfg.start := rfl

@[simp] theorem propagateConstants_graph (cfg : Cfg) : (propagateConstants cfg).graph = cfg.prune.graph := rfl

theorem propagateConstants_tids (cfg : Cfg) :
    (propagateConstants cfg).blocks.map Blk.tid = cfg.prune.blocks.map Blk.tid := by
  rw [propagateConstants_eq]
  simp only [List.map_map]
  apply List.map_congr_left
  intro b _
  rfl

/-- Constant propagation keeps every surviving block's successors. -/
theorem propagateConstants_successors (cfg : Cfg) :
    (propagateConstants cfg).blocks.map (fun b => (b.tid, b.successors)) =
      cfg.prune.blocks.map fun b => (b.tid, b.successors) := by
  rw [propagateConstants_eq]
  simp only [List.map_map]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp, propagateBlock_successors, propagateBlock_tid]

/-- Rewriting a block changes neither which variables its phis assign nor its definition targets. -/
theorem propagateBlock_shape (blk : Blk) (env : ConstEnv) :
    (propagateBlock blk env).1.phis.map Phi.var = blk.phis.map Phi.var ∧
      (propagateBlock blk env).1.defs.map Def.var = blk.defs.map Def.var := by
  have hfold : ∀ (defs : List Def) (acc : List Def) (c : ConstEnv),
      (defs.foldl propStep (acc, c)).1.map Def.var = acc.map Def.var ++ defs.map Def.var := by
    intro defs
    induction defs with
    | nil => simp
    | cons d ds ih =>
      intro acc c
      simp only [List.foldl_cons]
      rw [show propStep (acc, c) d = (acc ++ [{ d with rhs := propJump c d.rhs }], (propStep (acc, c) d).2) from rfl, ih]
      simp
  rw [propagateBlock_eq]
  refine ⟨by simp [Function.comp_def], ?_⟩
  simpa using hfold blk.defs [] (propEntry blk env)

/-! ### The whole optimizer -/

@[simp] theorem optimize_tid (sub : Sub) : (optimize sub).tid = sub.tid := rfl
@[simp] theorem optimize_name (sub : Sub) : (optimize sub).name = sub.name := rfl
@[simp] theorem optimize_args (sub : Sub) : (optimize sub).args = sub.args := rfl

private theorem optimize_blks (sub : Sub) :
    (optimize sub).blks = (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))).blocks := rfl

/-- `optimize` keeps exactly the reachable blocks, in order. -/
theorem optimize_tids (sub : Sub) :
    (optimize sub).blks.map Blk.tid = (Cfg.fromSub sub).prune.blocks.map Blk.tid := by
  rw [optimize_blks, eliminateDeadCode_tids, propagateConstants_tids]

theorem optimize_blks_reachable {sub : Sub} {blk : Blk} (h : blk ∈ (optimize sub).blks) :
    blk.tid ∈ (Cfg.fromSub sub).reachable := by
  have hm : blk.tid ∈ (optimize sub).blks.map Blk.tid := List.mem_map.2 ⟨blk, h, rfl⟩
  rw [optimize_tids] at hm
  obtain ⟨b, hb, heq⟩ := List.mem_map.1 hm
  rw [← heq]
  exact prune_blocks_reachable hb

private theorem Shrinks.pairs : {a b : List Blk} → Shrinks a b →
    a.map (fun b => (b.tid, b.successors)) = b.map (fun b => (b.tid, b.successors))
  | [], [], _ => rfl
  | x :: xs, y :: ys, ⟨h, t⟩ => by
    have hs : x.successors = y.successors := by simp [Blk.successors, h.2.1]
    simp [h.1, hs, Shrinks.pairs t]

/-- `optimize` leaves the control flow of reachable blocks unchanged. -/
theorem optimize_successors (sub : Sub) :
    (optimize sub).blks.map (fun b => (b.tid, b.successors)) =
      (Cfg.fromSub sub).prune.blocks.map fun b => (b.tid, b.successors) := by
  rw [optimize_blks]
  exact ((eliminateDeadCode_frame _).shrinks.pairs).trans (propagateConstants_successors _)

private theorem prune_single (tid : Tid) (name : String) (args : List Arg) (blk : Blk) :
    (Cfg.fromSub ⟨tid, name, args, [blk]⟩).prune.blocks = [blk] ∧
      (Cfg.fromSub ⟨tid, name, args, [blk]⟩).prune.start = blk.tid := by
  have hstart : (Cfg.fromSub ⟨tid, name, args, [blk]⟩).start = blk.tid := rfl
  refine ⟨?_, hstart⟩
  have hreach : blk.tid ∈ (Cfg.fromSub ⟨tid, name, args, [blk]⟩).reachable :=
    fromSub_start_reachable (sub := ⟨tid, name, args, [blk]⟩) (by simp)
  show [blk].filter (fun b => b.tid ∈ (Cfg.fromSub ⟨tid, name, args, [blk]⟩).prune.graph.nodes) = [blk]
  simp [prune_mem_nodes.2 hreach]

/-- Semantic preservation of `optimize` for a straight-line subroutine, one block run from any
environment. Whenever the original definitions evaluate, the optimized ones do too; every value the
original stores is stored in the same order; and each original jump expression that evaluates has
a rewritten counterpart in the optimized block with the same value. The optimized block may succeed
where the original fails, since a removed definition no longer evaluates. Variables written by the
block and not read by its jumps are not preserved, since `optimize` has no live-out set for the
subroutine's exit (see `optimization_main.ml` for the upstream protected-variable policy). -/
theorem optimize_straight_line (tid : Tid) (name : String) (args : List Arg) (blk : Blk) {env : Env}
    {r : Env × List (Var × Value)} (h : execDefs env blk.defs = .ok r) :
    ∃ opt, (optimize ⟨tid, name, args, [blk]⟩).blks = [opt] ∧ opt.tid = blk.tid ∧
      ∃ r', execDefs env opt.defs = .ok r' ∧ r.2.Sublist r'.2 ∧
        ∃ g, opt.jmps = blk.jmps.map (Jmp.mapExp g) ∧
          ∀ j ∈ blk.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp r.1 e = .ok v → evalExp r'.1 (g e) = .ok v := by
  let sub : Sub := ⟨tid, name, args, [blk]⟩
  obtain ⟨hprune, hstart⟩ := prune_single tid name args blk
  have hconst : ConstHold env (propEntry blk (constAt (Cfg.fromSub sub) blk.tid)) := by
    have hnil : constAt (Cfg.fromSub sub) blk.tid = [] := by
      by_cases hsolved : isSolved (Cfg.fromSub sub).prune (solution (Cfg.fromSub sub)) = true
      · simp only [constAt, hsolved, ↓reduceIte]
        show (if blk.tid = (Cfg.fromSub sub).prune.start then [] else _) = []
        rw [hstart]
        simp
      · simp [constAt, hsolved]
    rw [hnil]
    intro k c hm
    simp at hm
  obtain ⟨r₁, hr₁, heq, hsub, _, g, hg, hgv⟩ := propagateBlock_sim hconst h
  let mid := (propagateBlock blk (constAt (Cfg.fromSub sub) blk.tid)).1
  have hblocks : (propagateConstants (Cfg.fromSub sub)).blocks = [mid] := by
    rw [propagateConstants_eq, hprune]
    rfl
  obtain ⟨x, hx, htid, hj, _, _, _, hsem⟩ :=
    eliminateDeadCode_block_spec (propagateConstants (Cfg.fromSub sub)) (y := mid) (by rw [hblocks]; simp)
  have hlen : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))).blocks.map Blk.tid = [mid.tid] := by
    rw [eliminateDeadCode_tids, hblocks]
    rfl
  have hone : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))).blocks = [x] := by
    match hl : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))).blocks, hx, hlen with
    | [a], hx, _ =>
      rw [List.mem_singleton.1 hx]
    | [], hx, _ => simp at hx
    | _ :: _ :: _, _, hlen =>
      simp at hlen
  obtain ⟨r₂, hr₂, hag, ht⟩ := hsem env r₁ hr₁
  refine ⟨x, hone, htid, r₂, hr₂, ?_, g, ?_, ?_⟩
  · rw [ht]
    exact hsub
  · rw [hj]
    exact hg
  · intro j hj' e he v hv
    have hv₁ : evalExp r₁.1 (g e) = .ok v := by
      rw [heq]
      exact hgv e v hv
    rw [← hv₁]
    refine (Bap.Proofs.Bil.evalExp_congr_freeVars (g e) fun y hy => ?_).symm
    apply hag y
    simp only [jumpVars, List.mem_flatMap]
    refine ⟨j.mapExp g, ?_, ?_⟩
    · show j.mapExp g ∈ mid.jmps
      rw [hg]
      exact List.mem_map.2 ⟨j, hj', rfl⟩
    · refine freeVars_of_jmpExps ?_ hy
      rw [jmpExps_mapExp]
      exact List.mem_map.2 ⟨e, he, rfl⟩

/-! ### Semantic preservation along control-flow paths

`Run cfg t env stores final last` is an execution from block `t`: each block's definitions run, the
successor is chosen freely among the CFG edges (conditions are not modelled as deciding the branch),
and the run ends at any block. It records stored values, the final environment and the last block. -/

inductive Run (cfg : Cfg) : Tid → Env → List (Var × Value) → Env → Blk → Prop where
  | last {t env r blk} : cfg.block t = some blk → execDefs env blk.defs = .ok r → Run cfg t env r.2 r.1 blk
  | next {t t' env r blk stores final lastBlk} : cfg.block t = some blk → execDefs env blk.defs = .ok r →
    t' ∈ cfg.successors t → Run cfg t' r.1 stores final lastBlk → Run cfg t env (r.2 ++ stores) final lastBlk

private theorem Run.block {cfg : Cfg} {t : Tid} {env final : Env} {tr : List (Var × Value)} {f : Blk}
    (h : Run cfg t env tr final f) : ∃ b, cfg.block t = some b := by
  cases h <;> exact ⟨_, ‹_›⟩

private theorem find_map_tid (l : List Blk) (f : Blk → Blk) (hf : ∀ b, (f b).tid = b.tid) (t : Tid) :
    (l.map f).find? (fun b => decide (b.tid = t)) = (l.find? fun b => decide (b.tid = t)).map f := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.find?_cons, hf]
    split
    · rfl
    · exact ih

private theorem dceBlk_tid (cfg : Cfg) (b : Blk) : (dceBlk cfg b).tid = b.tid := rfl

private theorem dcePass_block (cfg : Cfg) {t : Tid} {b : Blk} (h : cfg.block t = some b) :
    (dcePass cfg).block t = some (dceBlk cfg b) := by
  show (cfg.blocks.map (dceBlk cfg)).find? _ = _
  rw [find_map_tid _ _ (dceBlk_tid cfg)]
  have h' : cfg.blocks.find? (fun b => decide (b.tid = t)) = some b := h
  rw [h']
  rfl

private theorem dceDefs_live_subset (defs : List Def) (L : List Var) (x : Var)
    (h : x ∈ (dceDefs defs L).2) : Exposed defs x ∨ (x ∈ L ∧ ∀ d ∈ defs, d.var ≠ x) := by
  induction defs with
  | nil => exact Or.inr ⟨by simpa [dceDefs_nil] using h, by simp⟩
  | cons d ds ih =>
    rw [dceDefs_cons] at h
    split at h
    · simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at h
      rcases h with ⟨hx, hne⟩ | hfv
      · rcases ih hx with he | ⟨hl, hall⟩
        · exact Or.inl (Or.inr ⟨hne, he⟩)
        · refine Or.inr ⟨hl, ?_⟩
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact fun heq => hne heq.symm
          · exact hall c hc
      · exact Or.inl (Or.inl hfv)
    · rename_i hc
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, List.contains_eq_mem,
        decide_eq_false_iff_not] at hc
      have hne : x ≠ d.var := by
        rintro rfl
        exact hc.1 h
      rcases ih h with he | ⟨hl, hall⟩
      · exact Or.inl (Or.inr ⟨hne, he⟩)
      · refine Or.inr ⟨hl, ?_⟩
        intro c hc'
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact fun heq => hne heq.symm
        · exact hall c hc'

/-- The block invariants the path simulation for dead-code elimination relies on. -/
private structure PhiFree (cfg : Cfg) : Prop where
  phis : ∀ b ∈ cfg.blocks, b.phis = []
  nodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes

private theorem PhiFree.pass {cfg : Cfg} (h : PhiFree cfg) : PhiFree (dcePass cfg) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    show c.phis.filter _ = []
    rw [h.phis c hc]
    rfl
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact h.nodes c hc

private theorem dce_step {cfg : Cfg} {t : Tid} {env env' : Env} (ht : t ∈ cfg.reachable)
    (hag : Agree ((Assoc.get t cfg.liveness.1).getD []) env env') {b : Blk} {r : Env × List (Var × Value)}
    (hb : cfg.block t = some b) (hr : execDefs env b.defs = .ok r) :
    ∃ r', execDefs env' (dceBlk cfg b).defs = .ok r' ∧ Agree (dceLive cfg b) r.1 r'.1 ∧ r'.2 = r.2 := by
  refine dceDefs_simulation b.defs (dceLive cfg b) ?_ hr
  intro x hx
  apply hag x
  have htid : b.tid = t := (block_some hb).2
  refine (liveness_equations cfg ht hb x).1.2 ((mem_blockIn _ _ _).2 ?_)
  rcases dceDefs_live_subset _ _ _ hx with he | ⟨hl, hall⟩
  · exact Or.inl he
  · rcases List.mem_append.1 hl with ho | hj
    · rw [htid] at ho
      exact Or.inr (Or.inr ⟨(liveness_equations cfg ht hb x).2.1 ho, hall⟩)
    · exact Or.inr (Or.inl (List.mem_flatMap.1 hj))

/-- One dead-code pass simulates every run from an environment agreeing on the live-in set. -/
private theorem dcePass_run {cfg : Cfg} (hwf : PhiFree cfg) {t : Tid} {env final : Env}
    {tr : List (Var × Value)} {f : Blk} (h : Run cfg t env tr final f) (ht : t ∈ cfg.reachable) {env' : Env}
    (hag : Agree ((Assoc.get t cfg.liveness.1).getD []) env env') :
    ∃ final' f', Run (dcePass cfg) t env' tr final' f' ∧ f'.tid = f.tid ∧ f'.jmps = f.jmps ∧
      Agree (jumpVars f) final final' := by
  induction h generalizing env' with
  | @last t env r blk hb hr =>
    obtain ⟨r', hr', hl, ht'⟩ := dce_step ht hag hb hr
    refine ⟨r'.1, dceBlk cfg blk, ?_, rfl, rfl, fun x hx => hl x (List.mem_append_right _ hx)⟩
    rw [← ht']
    exact .last (dcePass_block cfg hb) hr'
  | @next t t' env r blk stores final lastBlk hb hr hsucc hrest ih =>
    obtain ⟨r', hr', hl, ht'⟩ := dce_step ht hag hb hr
    obtain ⟨b', hb'⟩ := hrest.block
    have hedge : (t, t') ∈ cfg.graph.edges := (Bap.Graph.successors_mem cfg.graph t t').1 hsucc
    have ht'' : t' ∈ cfg.reachable :=
      Bap.Proofs.Graph.reachableFrom_closed cfg.graph _ ht hedge
        ((block_some hb').2 ▸ hwf.nodes b' (block_some hb').1)
    have hag' : Agree ((Assoc.get t' cfg.liveness.1).getD []) r.1 r'.1 := by
      intro x hx
      apply hl x
      refine List.mem_append_left _ ?_
      rw [(block_some hb).2]
      refine (liveness_equations cfg ht hb x).2.2 ((mem_blockOut _ _ _ _).2 ⟨t', hsucc, b', hb', Or.inl ⟨hx, ?_⟩⟩)
      intro phi hphi
      rw [hwf.phis b' (block_some hb').1] at hphi
      simp at hphi
    obtain ⟨final', f', hrun, hft, hfj, hfa⟩ := ih ht'' hag'
    refine ⟨final', f', ?_, hft, hfj, hfa⟩
    rw [← ht']
    exact .next (dcePass_block cfg hb) hr' hsucc hrun

private theorem dceAux_run {cfg : Cfg} (fuel : Nat) (hwf : PhiFree cfg) {t : Tid} {env final : Env}
    {tr : List (Var × Value)} {f : Blk} (h : Run cfg t env tr final f) (ht : t ∈ cfg.reachable) :
    ∃ final' f', Run (dceAux cfg fuel) t env tr final' f' ∧ f'.tid = f.tid ∧ f'.jmps = f.jmps ∧
      Agree (jumpVars f) final final' := by
  induction fuel generalizing cfg final f with
  | zero => exact ⟨final, f, h, rfl, rfl, fun _ _ => rfl⟩
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · exact ⟨final, f, h, rfl, rfl, fun _ _ => rfl⟩
    · obtain ⟨e₁, f₁, h₁, ht₁, hj₁, ha₁⟩ := dcePass_run hwf h ht (env' := env) (fun _ _ => rfl)
      obtain ⟨e₂, f₂, h₂, ht₂, hj₂, ha₂⟩ := ih hwf.pass h₁ ht
      refine ⟨e₂, f₂, h₂, ht₂.trans ht₁, hj₂.trans hj₁, fun x hx => ?_⟩
      rw [ha₁ x hx]
      exact ha₂ x (by simp only [jumpVars, hj₁] at hx ⊢; exact hx)

/-- Runs of a CFG stay in its pruned version when they start from a reachable block. -/
private theorem run_prune {cfg : Cfg} (hnodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes) {t : Tid}
    {env final : Env} {tr : List (Var × Value)} {f : Blk} (h : Run cfg t env tr final f) (ht : t ∈ cfg.reachable) :
    Run cfg.prune t env tr final f := by
  have hblock : ∀ {z : Tid} {b : Blk}, z ∈ cfg.reachable → cfg.block z = some b → cfg.prune.block z = some b := by
    intro z b hz hb
    rw [prune_block]
    simp [hz, hb]
  induction h with
  | last hb hr => exact .last (hblock ht hb) hr
  | @next t t' env r blk stores final lastBlk hb hr hsucc hrest ih =>
    obtain ⟨b', hb'⟩ := hrest.block
    have hedge : (t, t') ∈ cfg.graph.edges := (Bap.Graph.successors_mem cfg.graph t t').1 hsucc
    have ht'' : t' ∈ cfg.reachable :=
      Bap.Proofs.Graph.reachableFrom_closed cfg.graph _ ht hedge
        ((block_some hb').2 ▸ hnodes b' (block_some hb').1)
    refine .next (hblock ht hb) hr ?_ (ih ht'')
    exact (Bap.Graph.successors_mem _ t t').2 (mem_prune_edges.2 ⟨hedge, ht, ht''⟩)

private theorem propagateConstants_block (cfg : Cfg) {t : Tid} {b : Blk} (h : cfg.prune.block t = some b) :
    (propagateConstants cfg).block t = some (propagateBlock b (constAt cfg b.tid)).1 := by
  show (cfg.prune.blocks.map _).find? _ = _
  rw [find_map_tid _ _ (fun b => propagateBlock_tid b _)]
  have h' : cfg.prune.blocks.find? (fun b => decide (b.tid = t)) = some b := h
  rw [h']
  rfl

/-- Constant propagation simulates every run of the pruned CFG. -/
private theorem propagateConstants_run (cfg : Cfg) {t : Tid} {env final : Env} {tr : List (Var × Value)} {f : Blk}
    (h : Run cfg.prune t env tr final f) (hrun : PropRun cfg.prune t env) :
    ∃ tr' f', Run (propagateConstants cfg) t env tr' final f' ∧ tr.Sublist tr' ∧ f'.tid = f.tid ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧ ∀ e v, evalExp final e = .ok v → evalExp final (g e) = .ok v := by
  have hconst : ∀ {z : Tid} {e : Env} {b : Blk}, PropRun cfg.prune z e → cfg.prune.block z = some b →
      ConstHold e (propEntry b (constAt cfg b.tid)) := by
    intro z e b hz hb
    have htid := (block_some hb).2
    by_cases hsolved : isSolved cfg.prune (solution cfg) = true
    · simp only [constAt, hsolved, ↓reduceIte, htid]
      exact fixpoint_constants_hold hsolved hz hb
    · simp only [constAt, hsolved, ↓reduceIte]
      intro k c hm
      simp at hm
  induction h with
  | @last t env r blk hb hr =>
    obtain ⟨r', hr', heq, hsub, _, g, hg, hgv⟩ := propagateBlock_sim (hconst hrun hb) hr
    refine ⟨r'.2, (propagateBlock blk (constAt cfg blk.tid)).1, ?_, hsub, rfl, g, hg, hgv⟩
    rw [← heq]
    exact .last (propagateConstants_block cfg hb) hr'
  | @next t t' env r blk stores final lastBlk hb hr hsucc hrest ih =>
    obtain ⟨r', hr', heq, hsub, _, _⟩ := propagateBlock_sim (hconst hrun hb) hr
    obtain ⟨b', hb'⟩ := hrest.block
    have hnext : PropRun cfg.prune t' r.1 := .step hrun hb hr hsucc hb' (fun _ _ => rfl)
    obtain ⟨tr', f', hrun', hsub', hft, hg⟩ := ih hnext
    refine ⟨r'.2 ++ tr', f', ?_, hsub.append hsub', hft, hg⟩
    refine .next (propagateConstants_block cfg hb) hr' hsucc ?_
    rw [heq]
    exact hrun'

/-- Runs carry over to the CFG rebuilt from the optimized blocks, whose edges come from the jumps. -/
private theorem run_fromSub (sub : Sub) {t : Tid} {env final : Env} {tr : List (Var × Value)} {f : Blk}
    (h : Run (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))) t env tr final f) :
    Run (Cfg.fromSub (optimize sub)) t env tr final f := by
  have hblock : ∀ {z : Tid} {b : Blk}, (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))).block z = some b →
      (Cfg.fromSub (optimize sub)).block z = some b := fun h => h
  induction h with
  | last hb hr => exact .last (hblock hb) hr
  | @next t t' env r blk stores final lastBlk hb hr hsucc hrest ih =>
    refine .next (hblock hb) hr ?_ ih
    have hedge : (t, t') ∈ (Cfg.fromSub sub).prune.graph.edges := by
      have := (Bap.Graph.successors_mem _ t t').1 hsucc
      rwa [eliminateDeadCode_graph, propagateConstants_graph] at this
    obtain ⟨he, htr, _⟩ := mem_prune_edges.1 hedge
    obtain ⟨c, hc, hct, hs⟩ := (fromSub_mem_edges sub t t').1 he
    have hcp : c ∈ (Cfg.fromSub sub).prune.blocks :=
      List.mem_filter.2 ⟨hc, decide_eq_true (prune_mem_nodes.2 (hct ▸ htr))⟩
    have hpair : (c.tid, c.successors) ∈ (optimize sub).blks.map (fun b => (b.tid, b.successors)) := by
      rw [optimize_successors]
      exact List.mem_map.2 ⟨c, hcp, rfl⟩
    obtain ⟨x, hx, heq⟩ := List.mem_map.1 hpair
    simp only [Prod.mk.injEq] at heq
    refine (Bap.Graph.successors_mem _ t t').2 ?_
    refine (fromSub_mem_edges (optimize sub) t t').2 ⟨x, hx, heq.1.trans hct, ?_⟩
    rw [heq.2]
    exact hs

/-- Semantic preservation of `optimize` along control-flow paths, for phi-free subroutines (`optimize`
is also applied before SSA). For any run of the original from the entry, the optimized subroutine has
a run through the same branch choices ending at the same block whose stores include the original's,
in order, and whose final jump expressions have the same values wherever the original's evaluate. It
refines rather than equals: a removed definition can no longer fail. Variables not read by a later
jump or definition are not preserved at the end of the run, as `optimize` takes no live-out set. -/
theorem optimize_preserves_runs (sub : Sub) (hphi : ∀ b ∈ sub.blks, b.phis = []) {env final : Env}
    {tr : List (Var × Value)} {f : Blk} (h : Run (Cfg.fromSub sub) (Cfg.fromSub sub).start env tr final f) :
    ∃ tr' final' f', Run (Cfg.fromSub (optimize sub)) (Cfg.fromSub sub).start env tr' final' f' ∧
      tr.Sublist tr' ∧ f'.tid = f.tid ∧ ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        ∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp final' (g e) = .ok v := by
  let cfg := Cfg.fromSub sub
  have hnodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes := fun b hb => List.mem_map.2 ⟨b, hb, rfl⟩
  have hstart : cfg.start ∈ cfg.reachable := by
    obtain ⟨b, hb⟩ := h.block
    have hb' := block_some hb
    exact start_mem_reachable (hb'.2 ▸ hnodes b hb'.1)
  have hpruned := run_prune hnodes h hstart
  obtain ⟨tr₁, f₁, hrun₁, hsub, hft, g, hg, hgv⟩ := propagateConstants_run cfg hpruned (.start env)
  have hwf : PhiFree (propagateConstants cfg) := by
    refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      have hcs : c ∈ sub.blks := (List.mem_filter.1 hc).1
      show c.phis.map _ = []
      rw [hphi c hcs]
      rfl
    · intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      exact prune_mem_nodes.2 (prune_blocks_reachable (blk := c) hc)
  have hreach : cfg.start ∈ (propagateConstants cfg).reachable :=
    start_mem_reachable (prune_mem_nodes.2 hstart)
  obtain ⟨final₂, f₂, hrun₂, ht₂, hj₂, ha₂⟩ :=
    dceAux_run (weight (propagateConstants cfg).blocks + 1) hwf hrun₁ hreach
  rw [← eliminateDeadCode_eq] at hrun₂
  refine ⟨tr₁, final₂, f₂, run_fromSub sub hrun₂, hsub, ht₂.trans hft, g, by rw [hj₂, hg], ?_⟩
  intro j hj e he v hv
  have hv₁ := hgv e v hv
  rw [← hv₁]
  refine (Bap.Proofs.Bil.evalExp_congr_freeVars (g e) fun y hy => ?_).symm
  apply ha₂ y
  simp only [jumpVars, List.mem_flatMap]
  refine ⟨j.mapExp g, ?_, ?_⟩
  · rw [hg]
    exact List.mem_map.2 ⟨j, hj, rfl⟩
  · refine freeVars_of_jmpExps ?_ hy
    rw [jmpExps_mapExp]
    exact List.mem_map.2 ⟨e, he, rfl⟩

/-! ### Regression samples for the optimizer -/

private def vx : Var := ⟨"x", .imm 8, 0, false⟩
private def vy : Var := ⟨"y", .imm 8, 0, false⟩
private def vz : Var := ⟨"z", .imm 8, 0, false⟩

/-- `x := z; y := x` followed by a use of `y`. -/
private def dceSample : Sub :=
  ⟨1, "dce", [], [
    ⟨1, [], [⟨10, vx, .var vz⟩, ⟨11, vy, .var vx⟩], [⟨12, none, .goto (.direct 2)⟩]⟩,
    ⟨2, [], [], [⟨13, some (.var vy), .ret (.indirect (.var vy))⟩]⟩]⟩

/-- A definition read by a later kept definition in the same block survives. -/
theorem optimize_keeps_used_def :
    ((optimize dceSample).blks.map fun blk =>
      blk.defs.map fun defn => (defn.var, Bil.freeVars defn.rhs)) = [[(vx, [vz]), (vy, [vx])], []] := by
  rfl

/-- `x := 1; goto L; L: y := x; x := 2; if z goto L else M; M: ret y`. -/
private def loopSample : Sub :=
  ⟨1, "loop", [], [
    ⟨1, [], [⟨10, vx, .int (1#8)⟩], [⟨11, none, .goto (.direct 2)⟩]⟩,
    ⟨2, [], [⟨12, vy, .var vx⟩, ⟨13, vx, .int (2#8)⟩],
      [⟨14, some (.var vz), .goto (.direct 2)⟩, ⟨15, none, .goto (.direct 3)⟩]⟩,
    ⟨3, [], [], [⟨16, none, .ret (.indirect (.var vy))⟩]⟩]⟩

private def rhsConstants (blk : Blk) : List (Option Constant) :=
  blk.defs.map fun defn => Constant.ofExp defn.rhs

/-- In a loop the read of `x` stays symbolic, since the two paths into the block disagree on it. -/
theorem propagateConstants_loop_not_folded :
    (propagateConstants (Cfg.fromSub loopSample)).blocks.map rhsConstants =
      [[some ⟨8, 1⟩], [none, some ⟨8, 2⟩], []] := by
  rfl

/-! ### SSA renaming -/

@[simp] theorem Var.base_base (v : Var) : v.base.base = v.base := rfl
@[simp] theorem Var.version_base (v : Var) (i : Nat) : (v.version i).base = v.base := rfl
@[simp] theorem Var.version_index (v : Var) (i : Nat) : (v.version i).index = i := rfl

private abbrev counterOf (st : RenameState) (v : Var) : Nat := (Assoc.get v.base st.counters).getD 1

private theorem newName_fst (v : Var) (st : RenameState) :
    (newName v st).1 = v.base.version (counterOf st v) := rfl

private theorem newName_counters (v : Var) (st : RenameState) :
    (newName v st).2.counters = Assoc.put v.base (counterOf st v + 1) st.counters := rfl

private theorem newName_stacks (v : Var) (st : RenameState) :
    (newName v st).2.stacks = Assoc.put v.base
      ((Assoc.get v.base st.stacks).getD [] ++ [(newName v st).1]) st.stacks := rfl

private theorem topName_eq (v : Var) (st : RenameState) :
    topName v st = match Assoc.get v.base st.stacks with
      | some stack => stack.getLast?.getD v.base
      | none => v.base := rfl

/-- A freshly issued name keeps the base variable and uses the current counter as its version. -/
theorem newName_spec (v : Var) (st : RenameState) :
    (newName v st).1.base = v.base ∧
      (newName v st).1.index = (Assoc.get v.base st.counters).getD 1 := ⟨rfl, rfl⟩

/-- The counter of the renamed base grows by one, and other counters are untouched. -/
theorem newName_counter (v w : Var) (st : RenameState) :
    Assoc.get w.base (newName v st).2.counters =
      if w.base = v.base then some ((Assoc.get v.base st.counters).getD 1 + 1)
      else Assoc.get w.base st.counters := by
  rw [newName_counters, get_put]

/-- After a definition, reads of that variable see the new name. -/
theorem topName_newName (v w : Var) (st : RenameState) (h : w.base = v.base) :
    topName w (newName v st).2 = (newName v st).1 := by
  rw [topName_eq, newName_stacks, h, get_put]
  simp

/-- Renaming one base never affects reads of another. -/
theorem topName_newName_other (v w : Var) (st : RenameState) (h : w.base ≠ v.base) :
    topName w (newName v st).2 = topName w st := by
  rw [topName_eq, topName_eq, newName_stacks, get_put]
  simp only [h, ite_false]

/-- The stack of names visible for a base variable. -/
private abbrev stackOf (st : RenameState) (k : Var) : List Var := (Assoc.get k st.stacks).getD []

private theorem get_popVar_stacks (var : Var) (st : RenameState) (k : Var) :
    Assoc.get k (popVar var st).stacks =
      (Assoc.get k st.stacks).map fun stack => if k = var then stack.dropLast else stack := by
  show List.lookup k (st.stacks.map _) = (List.lookup k st.stacks).map _
  induction st.stacks with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      by_cases hv : k = var <;> simp [hv, List.lookup]
    · have hb : (k == a) = false := by simpa using hk
      by_cases hv : a = var
      · subst hv
        simp [List.lookup, hb, ih]
      · simp [hv, List.lookup, hb, ih]

private theorem stackOf_popVar (var : Var) (st : RenameState) (k : Var) :
    stackOf (popVar var st) k = if k = var then (stackOf st k).dropLast else stackOf st k := by
  simp only [stackOf, get_popVar_stacks]
  cases Assoc.get k st.stacks <;> by_cases hv : k = var <;> simp [hv]

private theorem popVars_cons (v : Var) (vs : List Var) (st : RenameState) :
    popVars (v :: vs) st = popVars vs (popVar v st) := rfl

@[simp] theorem popVars_counters (vars : List Var) (st : RenameState) :
    (popVars vars st).counters = st.counters := by
  induction vars generalizing st with
  | nil => rfl
  | cons v vs ih =>
    rw [popVars_cons, ih]
    rfl

/-- Popping removes one name per occurrence of the base in the list. -/
private theorem stackOf_popVars (vars : List Var) (st : RenameState) (k : Var) :
    stackOf (popVars vars st) k = (stackOf st k).take ((stackOf st k).length - vars.count k) := by
  induction vars generalizing st with
  | nil => simp [show popVars [] st = st from rfl]
  | cons v vs ih =>
    rw [popVars_cons, ih, stackOf_popVar]
    by_cases hv : k = v
    · subst hv
      simp only [↓reduceIte, List.count_cons_self, List.length_dropLast]
      rw [List.dropLast_eq_take, List.take_take]
      congr 1
      omega
    · have hne : (v == k) = false := by simpa using Ne.symm hv
      simp [hv, List.count_cons, hne]

private theorem topName_of_stack (v : Var) (st : RenameState) :
    topName v st = (stackOf st v.base).getLast?.getD v.base := by
  rw [topName_eq]
  cases hg : Assoc.get v.base st.stacks <;> simp [stackOf, hg]

private theorem stackOf_newName (o : Var) (st : RenameState) (k : Var) :
    stackOf (newName o st).2 k =
      if k = o.base then stackOf st k ++ [(newName o st).1] else stackOf st k := by
  simp only [stackOf, newName_stacks, get_put]
  by_cases hk : k = o.base
  · subst hk
    simp
  · simp [hk]

/-- Popping after one definition restores the name visible before it. -/
theorem topName_pop_newName (v : Var) (st : RenameState) :
    topName v (popVars [v.base] (newName v st).2) = topName v st := by
  have hstack : stackOf (popVars [v.base] (newName v st).2) v.base = stackOf st v.base := by
    rw [show popVars [v.base] (newName v st).2 = popVar v.base (newName v st).2 from rfl,
      stackOf_popVar, stackOf_newName]
    simp
  rw [topName_of_stack, topName_of_stack, hstack]

/-- Issue bookkeeping for a run of fresh names between two renaming states. -/
private structure Issued (st st' : RenameState) (vs : List Var) : Prop where
  mono : ∀ w, counterOf st w ≤ counterOf st' w
  range : ∀ v ∈ vs, counterOf st v ≤ v.index ∧ v.index < counterOf st' v
  nodup : vs.Nodup

private theorem counterOf_newName_same (v : Var) (st : RenameState) :
    counterOf (newName v st).2 v = counterOf st v + 1 := by
  simp [counterOf, newName_counter]

private theorem counterOf_newName_mono (v w : Var) (st : RenameState) :
    counterOf st w ≤ counterOf (newName v st).2 w := by
  simp only [counterOf, newName_counter]
  split
  · rename_i h
    simp [h]
  · exact Nat.le_refl _

private theorem Issued.nil (st : RenameState) : Issued st st [] :=
  ⟨fun _ => Nat.le_refl _, by simp, List.nodup_nil⟩

private theorem Issued.cons {o : Var} {st st' : RenameState} {vs : List Var}
    (h : Issued (newName o st).2 st' vs) : Issued st st' ((newName o st).1 :: vs) := by
  have hbase : (newName o st).1.base = o.base := rfl
  have hc0 : counterOf st (newName o st).1 = counterOf st o := rfl
  have hc1 : counterOf (newName o st).2 (newName o st).1 = counterOf st o + 1 :=
    counterOf_newName_same o st
  have hidx : (newName o st).1.index = counterOf st o := rfl
  refine ⟨fun w => Nat.le_trans (counterOf_newName_mono o w st) (h.mono w), ?_, ?_⟩
  · intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · have := h.mono (newName o st).1
      omega
    · have := h.range v hv
      have := counterOf_newName_mono o v st
      omega
  · refine List.nodup_cons.2 ⟨?_, h.nodup⟩
    intro hm
    have := (h.range _ hm).1
    omega

private theorem Issued.append {a b c : RenameState} {xs ys : List Var} (h₁ : Issued a b xs)
    (h₂ : Issued b c ys) : Issued a c (xs ++ ys) := by
  refine ⟨fun w => Nat.le_trans (h₁.mono w) (h₂.mono w), ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · have := h₁.range v hv
      have := h₂.mono v
      omega
    · have := h₂.range v hv
      have := h₁.mono v
      omega
  · refine List.nodup_append.2 ⟨h₁.nodup, h₂.nodup, ?_⟩
    rintro x hx y hy rfl
    have := h₁.range x hx
    have := h₂.range x hy
    omega

private theorem renamePhis_cons (phi : Phi) (rest : List Phi) (st : RenameState) :
    renamePhis (phi :: rest) st =
      ({ phi with var := (newName phi.var st).1 } :: (renamePhis rest (newName phi.var st).2).1,
        (renamePhis rest (newName phi.var st).2).2) := rfl

private theorem renameDefs_cons (defn : Def) (rest : List Def) (st : RenameState) :
    renameDefs (defn :: rest) st =
      ({ defn with var := (newName defn.var st).1, rhs := renameExp st defn.rhs } ::
          (renameDefs rest (newName defn.var st).2).1,
        (renameDefs rest (newName defn.var st).2).2) := rfl

private theorem issued_renamePhis (phis : List Phi) (st : RenameState) :
    Issued st (renamePhis phis st).2 ((renamePhis phis st).1.map Phi.var) := by
  induction phis generalizing st with
  | nil => exact Issued.nil _
  | cons p ps ih =>
    rw [renamePhis_cons]
    exact Issued.cons (ih _)

private theorem issued_renameDefs (defs : List Def) (st : RenameState) :
    Issued st (renameDefs defs st).2 ((renameDefs defs st).1.map Def.var) := by
  induction defs generalizing st with
  | nil => exact Issued.nil _
  | cons d ds ih =>
    rw [renameDefs_cons]
    exact Issued.cons (ih _)

/-- Renaming a block's statements assigns pairwise distinct names, all with versions in the range
of counters consumed by that block. -/
theorem rename_single_assignment (phis : List Phi) (defs : List Def) (st : RenameState) :
    let r₁ := renamePhis phis st
    let r₂ := renameDefs defs r₁.2
    let names := r₁.1.map Phi.var ++ r₂.1.map Def.var
    names.Nodup ∧ ∀ v ∈ names,
      (Assoc.get v.base st.counters).getD 1 ≤ v.index ∧ v.index < (Assoc.get v.base r₂.2.counters).getD 1 :=
  have h := (issued_renamePhis phis st).append (issued_renameDefs defs (renamePhis phis st).2)
  ⟨h.nodup, h.range⟩

/-- Starting from the empty state no issued name is the unversioned base. -/
theorem rename_versions_positive (phis : List Phi) (defs : List Def) :
    let r₁ := renamePhis phis {}
    let r₂ := renameDefs defs r₁.2
    ∀ v ∈ r₁.1.map Phi.var ++ r₂.1.map Def.var, v.index ≠ 0 := by
  intro r₁ r₂ v hv
  have := ((rename_single_assignment phis defs {}).2 v hv).1
  have h1 : (Assoc.get v.base ({} : RenameState).counters).getD 1 = 1 := rfl
  omega

theorem renamePhis_shape (phis : List Phi) (st : RenameState) :
    ((renamePhis phis st).1.map fun phi => (phi.tid, phi.var.base, phi.values.length)) =
      phis.map fun phi => (phi.tid, phi.var.base, phi.values.length) := by
  induction phis generalizing st with
  | nil => rfl
  | cons p ps ih =>
    rw [renamePhis_cons]
    simp only [List.map_cons, ih]
    rfl

theorem renameDefs_shape (defs : List Def) (st : RenameState) :
    ((renameDefs defs st).1.map fun defn => (defn.tid, defn.var.base)) =
      defs.map fun defn => (defn.tid, defn.var.base) := by
  induction defs generalizing st with
  | nil => rfl
  | cons d ds ih =>
    rw [renameDefs_cons]
    simp only [List.map_cons, ih]
    rfl

/-! ### SSA construction frames -/

private abbrev pairs (blocks : List Blk) : List (Tid × List Tid) :=
  blocks.map fun b => (b.tid, b.successors)

private abbrev tidsOf (blocks : List Blk) : List Tid := blocks.map Blk.tid

/-- Replacing the only block carrying a tid by one with the same identity preserves the pair table. -/
private theorem pairs_update (l : List Blk) (t : Tid) (found new : Blk) (hnd : (tidsOf l).Nodup)
    (hfound : found ∈ l) (ht : found.tid = t) (hnew : new.tid = found.tid)
    (hs : new.successors = found.successors) :
    pairs (l.map fun blk => if blk.tid = t then new else blk) = pairs l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.cons.injEq]
    replace hnd : b.tid ∉ tidsOf bs ∧ (tidsOf bs).Nodup := by simpa [tidsOf] using hnd
    by_cases hb : b.tid = t
    · have hbf : b = found := by
        rcases List.mem_cons.1 hfound with h | h
        · exact h.symm
        · exfalso
          apply hnd.1
          rw [hb, ← ht]
          exact List.mem_map.2 ⟨found, h, rfl⟩
      subst hbf
      have hrest : (bs.map fun blk => if blk.tid = t then new else blk) = bs := by
        have hmap : (bs.map fun blk => if blk.tid = t then new else blk) = bs.map id := by
          apply List.map_congr_left
          intro c hc
          have : c.tid ≠ t := by
            intro hc'
            apply hnd.1
            rw [hb, ← hc']
            exact List.mem_map.2 ⟨c, hc, rfl⟩
          simp [this]
        simpa using hmap
      simp [hb, hnew, hs, hrest, ht]
    · simp only [hb, ite_false, true_and]
      rcases List.mem_cons.1 hfound with h | h
      · subst h
        exact absurd ht hb
      · exact ih hnd.2 h

/-- Frame of every pass that rewrites blocks in place. -/
private structure PropFrame (a b : Cfg) : Prop where
  start : b.start = a.start
  graph : b.graph = a.graph
  tids : tidsOf b.blocks = tidsOf a.blocks
  pairs : (tidsOf a.blocks).Nodup → pairs b.blocks = pairs a.blocks

private theorem PropFrame.refl (a : Cfg) : PropFrame a a := ⟨rfl, rfl, rfl, fun _ => rfl⟩

private theorem PropFrame.trans {a b c : Cfg} (h : PropFrame a b) (h' : PropFrame b c) : PropFrame a c :=
  ⟨h'.start.trans h.start, h'.graph.trans h.graph, h'.tids.trans h.tids, fun hnd =>
    (h'.pairs (by rw [h.tids]; exact hnd)).trans (h.pairs hnd)⟩

private theorem eq_of_tid_eq {l : List Blk} (hnd : (tidsOf l).Nodup) {a b : Blk} (ha : a ∈ l) (hb : b ∈ l)
    (h : a.tid = b.tid) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c cs ih =>
    have hnd' : c.tid ∉ tidsOf cs ∧ (tidsOf cs).Nodup := by simpa [tidsOf] using hnd
    rcases List.mem_cons.1 ha with ha' | ha <;> rcases List.mem_cons.1 hb with hb' | hb
    · exact ha'.trans hb'.symm
    · exact absurd (by rw [← ha', h]; exact List.mem_map.2 ⟨b, hb, rfl⟩) hnd'.1
    · exact absurd (by rw [← hb', ← h]; exact List.mem_map.2 ⟨a, ha, rfl⟩) hnd'.1
    · exact ih hnd'.2 ha hb

/-- Any in-place edit that keeps identity and successors of the edited blocks is a frame step. -/
private theorem frame_update (cfg : Cfg) (t : Tid) (f : Blk → Blk)
    (ht : ∀ b, b.tid = t → (f b).tid = b.tid) (hs : ∀ b, b.tid = t → (f b).successors = b.successors) :
    PropFrame cfg (cfg.updateBlock t f) := by
  refine ⟨rfl, rfl, updateBlock_tids cfg t f ht, fun _ => ?_⟩
  show (cfg.blocks.map _).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp]
  split
  · rename_i h
    rw [ht b h, hs b h]
  · rfl

private theorem frame_modify (cfg : Cfg) {t : Tid} {found : Blk} (f : Blk → Blk) (hb : cfg.block t = some found)
    (ht : ∀ b, (f b).tid = b.tid) (hs : (f found).successors = found.successors) :
    PropFrame cfg (cfg.updateBlock t f) := by
  obtain ⟨hfound, htid⟩ := block_some hb
  refine ⟨rfl, rfl, updateBlock_tids cfg t f (fun b _ => ht b), fun hnd => ?_⟩
  have hcongr : (cfg.blocks.map fun blk => if blk.tid = t then f blk else blk) =
      cfg.blocks.map fun blk => if blk.tid = t then f found else blk := by
    apply List.map_congr_left
    intro c hc
    split
    · rename_i hct
      have : c = found := by
        exact eq_of_tid_eq hnd hc hfound (hct.trans htid.symm)
      rw [this]
    · rfl
  show pairs (cfg.blocks.map _) = _
  rw [hcongr]
  exact pairs_update _ _ _ _ hnd hfound htid (ht found) hs

private abbrev phiStep (var : Var) (state : Cfg × List Tid × List Tid) (join : Tid) :
    Cfg × List Tid × List Tid :=
  if join ∈ state.2.1 then state
  else
    let predecessors := state.1.predecessors join
    let phi : Phi := ⟨join, var, predecessors.map fun pred => (pred, .var var)⟩
    (state.1.updateBlock join fun blk => { blk with phis := blk.phis ++ [phi] },
      join :: state.2.1, join :: state.2.2)

private theorem insertPhisForVar_succ (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Var) (fuel : Nat)
    (t : Tid) (work inserted : List Tid) :
    insertPhisForVar cfg frontier var (fuel + 1) (t :: work) inserted =
      insertPhisForVar
        (((Assoc.get t frontier).getD []).foldl (phiStep var) (cfg, inserted, work)).1 frontier var fuel
        (((Assoc.get t frontier).getD []).foldl (phiStep var) (cfg, inserted, work)).2.2
        (((Assoc.get t frontier).getD []).foldl (phiStep var) (cfg, inserted, work)).2.1 := by
  rfl

private theorem phiFold_frame (var : Var) (joins : List Tid) (state : Cfg × List Tid × List Tid) :
    PropFrame state.1 (joins.foldl (phiStep var) state).1 := by
  induction joins generalizing state with
  | nil => exact PropFrame.refl _
  | cons j js ih =>
    simp only [List.foldl_cons]
    refine PropFrame.trans ?_ (ih _)
    simp only [phiStep]
    split
    · exact PropFrame.refl _
    · refine frame_update _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private theorem insertPhisForVar_frame (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Var) (fuel : Nat)
    (work inserted : List Tid) : PropFrame cfg (insertPhisForVar cfg frontier var fuel work inserted) := by
  induction fuel generalizing cfg work inserted with
  | zero => exact PropFrame.refl _
  | succ fuel ih =>
    match work with
    | [] => exact PropFrame.refl _
    | t :: work =>
      rw [insertPhisForVar_succ]
      exact PropFrame.trans (phiFold_frame var _ (cfg, inserted, work)) (ih ..)

private theorem insertAllPhis_cons (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Var) (rest : List Var) :
    insertAllPhis cfg frontier (var :: rest) =
      insertAllPhis (insertPhisForVar cfg frontier var (cfg.blocks.length * 2 + 1)
        (cfg.blocks.filterMap fun blk => if blk.definesBase var then some blk.tid else none) []) frontier rest := rfl

private theorem insertAllPhis_frame (cfg : Cfg) (frontier : List (Tid × List Tid)) (vars : List Var) :
    PropFrame cfg (insertAllPhis cfg frontier vars) := by
  induction vars generalizing cfg with
  | nil => exact PropFrame.refl _
  | cons v vs ih =>
    rw [insertAllPhis_cons]
    exact PropFrame.trans (insertPhisForVar_frame ..) (ih _)

private theorem updatePhiInputs_frame (source successor : Tid) (st : RenameState) (cfg : Cfg) :
    PropFrame cfg (updatePhiInputs source successor st cfg) :=
  frame_update cfg successor _ (fun _ _ => rfl) (fun _ _ => rfl)

private theorem updatePhi_fold_frame (source : Tid) (st : RenameState) (succs : List Tid) (cfg : Cfg) :
    PropFrame cfg (succs.foldl (fun cfg successor => updatePhiInputs source successor st cfg) cfg) := by
  induction succs generalizing cfg with
  | nil => exact PropFrame.refl _
  | cons s ss ih =>
    simp only [List.foldl_cons]
    exact PropFrame.trans (updatePhiInputs_frame ..) (ih _)

private theorem renameBlock_succ (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg) (st : RenameState) :
    renameBlock idom (fuel + 1) t cfg st =
      match cfg.block t with
      | none => (cfg, st)
      | some block =>
        let r₁ := renamePhis block.phis st
        let r₂ := renameDefs block.defs r₁.2
        let jmps := block.jmps.map (Jmp.mapExp (renameExp r₂.2))
        let c₁ := cfg.updateBlock t fun block => { block with phis := r₁.1, defs := r₂.1, jmps := jmps }
        let c₂ := (c₁.successors t).foldl (fun cfg successor => updatePhiInputs t successor r₂.2 cfg) c₁
        let r₃ := ((idom.filter fun entry => entry.2 = t).map Prod.fst).foldl
          (fun current child => renameBlock idom fuel child current.1 current.2) (c₂, r₂.2)
        (r₃.1, popVars (block.phis.map (·.var.base) ++ block.defs.map (·.var.base)) r₃.2) := rfl

private theorem counterOf_popVars (vars : List Var) (st : RenameState) (w : Var) :
    counterOf (popVars vars st) w = counterOf st w := by
  simp only [counterOf, popVars_counters]

private abbrev renameEdit (block : Blk) (st : RenameState) (b : Blk) : Blk :=
  { b with
    phis := (renamePhis block.phis st).1
    defs := (renameDefs block.defs (renamePhis block.phis st).2).1
    jmps := block.jmps.map (Jmp.mapExp (renameExp (renameDefs block.defs (renamePhis block.phis st).2).2)) }

private theorem renameBlock_frame (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg) (st : RenameState) :
    PropFrame cfg (renameBlock idom fuel t cfg st).1 ∧
      ∀ w, counterOf st w ≤ counterOf (renameBlock idom fuel t cfg st).2 w := by
  induction fuel generalizing t cfg st with
  | zero => exact ⟨PropFrame.refl _, fun _ => Nat.le_refl _⟩
  | succ fuel ih =>
    rw [renameBlock_succ]
    split
    · exact ⟨PropFrame.refl _, fun _ => Nat.le_refl _⟩
    · rename_i block hb
      simp only
      have hchildren : ∀ (children : List Tid) (state : Cfg × RenameState),
          PropFrame state.1 (children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).1 ∧
          ∀ w, counterOf state.2 w ≤ counterOf (children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).2 w := by
        intro children
        induction children with
        | nil => exact fun _ => ⟨PropFrame.refl _, fun _ => Nat.le_refl _⟩
        | cons c cs ihc =>
          intro state
          simp only [List.foldl_cons]
          have h₁ := ih c state.1 state.2
          have h₂ := ihc (renameBlock idom fuel c state.1 state.2)
          exact ⟨h₁.1.trans h₂.1, fun w => Nat.le_trans (h₁.2 w) (h₂.2 w)⟩
      have hedit := frame_modify cfg (renameEdit block st) hb (fun _ => rfl) (by
        simp only [renameEdit, Blk.successors, List.flatMap_map, Jmp.successors_mapExp])
      have hc := hchildren ((idom.filter fun entry => entry.2 = t).map Prod.fst)
        ((((cfg.updateBlock t (renameEdit block st)).successors t).foldl
            (fun cfg successor => updatePhiInputs t successor (renameDefs block.defs (renamePhis block.phis st).2).2 cfg)
            (cfg.updateBlock t (renameEdit block st))),
          (renameDefs block.defs (renamePhis block.phis st).2).2)
      have hi := (issued_renamePhis block.phis st).append
        (issued_renameDefs block.defs (renamePhis block.phis st).2)
      refine ⟨hedit.trans ((updatePhi_fold_frame ..).trans hc.1), fun w => ?_⟩
      rw [counterOf_popVars]
      exact Nat.le_trans (hi.mono w) (hc.2 w)

/-- The renaming walk never lowers a version counter, so names issued later stay fresh. -/
theorem renameBlock_counters_mono (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg) (st : RenameState)
    (w : Var) : (Assoc.get w.base st.counters).getD 1 ≤
      (Assoc.get w.base (renameBlock idom fuel t cfg st).2.counters).getD 1 :=
  (renameBlock_frame idom fuel t cfg st).2 w

private def ssaCfg (sub : Sub) : Cfg :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let vars := (cfg.blocks.flatMap fun blk =>
    (blk.definedVars ++ blk.freeVars).map Var.base).eraseDups
  let cfg := insertAllPhis cfg frontier vars
  (renameBlock idom (cfg.blocks.length + 1) cfg.start cfg {}).1

private theorem toSsa_eq (sub : Sub) :
    toSsa sub = { sub with blks := sub.blks.filterMap fun blk => (ssaCfg sub).block blk.tid } := rfl

private theorem ssaCfg_frame (sub : Sub) : PropFrame (Cfg.connected sub) (ssaCfg sub) :=
  (insertAllPhis_frame ..).trans (renameBlock_frame ..).1

@[simp] theorem toSsa_args (sub : Sub) : (toSsa sub).args = sub.args := rfl

private theorem connected_tids_mem (sub : Sub) {blk : Blk} (h : blk ∈ sub.blks) :
    blk.tid ∈ (ssaCfg sub).blocks.map Blk.tid := by
  have : (ssaCfg sub).blocks.map Blk.tid = (Cfg.connected sub).blocks.map Blk.tid := (ssaCfg_frame sub).tids
  rw [this, connected_blocks]
  refine List.mem_map.2 ⟨blk, ?_, rfl⟩
  simp [h]

/-- SSA construction keeps exactly the blocks of the input, in order. -/
theorem toSsa_tids (sub : Sub) : (toSsa sub).blks.map Blk.tid = sub.blks.map Blk.tid := by
  rw [toSsa_eq]
  have key : ∀ l : List Blk, (∀ b ∈ l, b ∈ sub.blks) →
      (l.filterMap fun blk => (ssaCfg sub).block blk.tid).map Blk.tid = l.map Blk.tid := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons b bs ih =>
      intro hl
      obtain ⟨x, hx⟩ := block_exists (connected_tids_mem sub (hl b (by simp)))
      simp only [List.filterMap_cons, hx, List.map_cons, ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)),
        (block_some hx).2]
  exact key _ (fun _ h => h)

/-- With unique tids distinct from the pseudo nodes, SSA construction preserves control flow. -/
theorem toSsa_successors (sub : Sub)
    (hnd : (pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit]).Nodup) :
    (toSsa sub).blks.map (fun b => (b.tid, b.successors)) =
      sub.blks.map fun b => (b.tid, b.successors) := by
  have hblocks : (Cfg.connected sub).blocks.map Blk.tid = pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit] := by
    rw [connected_blocks]
    simp [pseudoStart, pseudoExit]
  have hnd' : (tidsOf (Cfg.connected sub).blocks).Nodup := by
    show ((Cfg.connected sub).blocks.map Blk.tid).Nodup
    rw [hblocks]
    exact hnd
  have hpairs := (ssaCfg_frame sub).pairs hnd'
  have hone : ∀ b ∈ sub.blks, ∀ x, (ssaCfg sub).block b.tid = some x → x.successors = b.successors := by
    intro b hb x hx
    obtain ⟨hxm, hxt⟩ := block_some hx
    have hin : (x.tid, x.successors) ∈ pairs (ssaCfg sub).blocks := List.mem_map.2 ⟨x, hxm, rfl⟩
    rw [hpairs] at hin
    obtain ⟨c, hc, heq⟩ := List.mem_map.1 hin
    simp only [Prod.mk.injEq] at heq
    have hbc : b ∈ (Cfg.connected sub).blocks := by
      rw [connected_blocks]
      simp [hb]
    have : c = b := eq_of_tid_eq hnd' hc hbc (heq.1.trans hxt)
    rw [← heq.2, this]
  rw [toSsa_eq]
  have key : ∀ l : List Blk, (∀ b ∈ l, b ∈ sub.blks) →
      (l.filterMap fun blk => (ssaCfg sub).block blk.tid).map (fun b => (b.tid, b.successors)) =
        l.map fun b => (b.tid, b.successors) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons b bs ih =>
      intro hl
      have hbm := hl b (by simp)
      obtain ⟨x, hx⟩ := block_exists (connected_tids_mem sub hbm)
      simp only [List.filterMap_cons, hx, List.map_cons, ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)),
        (block_some hx).2, hone b hbm x hx]
  exact key _ (fun _ h => h)

/-! ### Scoped renaming and single assignment -/

private theorem stackOf_renamePhis (phis : List Phi) (st : RenameState) (k : Var) :
    stackOf (renamePhis phis st).2 k =
      stackOf st k ++ ((renamePhis phis st).1.map Phi.var).filter (fun v => v.base = k) := by
  induction phis generalizing st with
  | nil => simp [show renamePhis [] st = ([], st) from rfl]
  | cons p ps ih =>
    rw [renamePhis_cons]
    simp only [List.map_cons]
    rw [ih, stackOf_newName]
    have hb : (newName p.var st).1.base = p.var.base := rfl
    by_cases hk : k = p.var.base
    · subst hk
      simp [List.filter_cons, hb]
    · have hk' : ¬ p.var.base = k := fun h => hk h.symm
      simp [List.filter_cons, hb, hk, hk']

private theorem stackOf_renameDefs (defs : List Def) (st : RenameState) (k : Var) :
    stackOf (renameDefs defs st).2 k =
      stackOf st k ++ ((renameDefs defs st).1.map Def.var).filter (fun v => v.base = k) := by
  induction defs generalizing st with
  | nil => simp [show renameDefs [] st = ([], st) from rfl]
  | cons d ds ih =>
    rw [renameDefs_cons]
    simp only [List.map_cons]
    rw [ih, stackOf_newName]
    have hb : (newName d.var st).1.base = d.var.base := rfl
    by_cases hk : k = d.var.base
    · subst hk
      simp [List.filter_cons, hb]
    · have hk' : ¬ d.var.base = k := fun h => hk h.symm
      simp [List.filter_cons, hb, hk, hk']

private theorem renamePhis_bases (phis : List Phi) (st : RenameState) :
    ((renamePhis phis st).1.map Phi.var).map Var.base = phis.map (·.var.base) := by
  induction phis generalizing st with
  | nil => rfl
  | cons p ps ih =>
    rw [renamePhis_cons]
    simp only [List.map_cons, ih]
    rfl

private theorem renameDefs_bases (defs : List Def) (st : RenameState) :
    ((renameDefs defs st).1.map Def.var).map Var.base = defs.map (·.var.base) := by
  induction defs generalizing st with
  | nil => rfl
  | cons d ds ih =>
    rw [renameDefs_cons]
    simp only [List.map_cons, ih]
    rfl

private theorem length_filter_base (l : List Var) (k : Var) :
    (l.filter fun v => v.base = k).length = (l.map Var.base).count k := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases ha : a.base = k
    · simp [List.filter_cons, ha, ih]
    · simp [List.filter_cons, ha, ih, List.count_cons]

/-- Renaming a block and its dominator subtree leaves every name stack as it found it, so a sibling
block sees the names visible at their common dominator. -/
theorem renameBlock_stacks_restored (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg)
    (st : RenameState) (k : Var) :
    (Assoc.get k (renameBlock idom fuel t cfg st).2.stacks).getD [] = (Assoc.get k st.stacks).getD [] := by
  induction fuel generalizing t cfg st with
  | zero => rfl
  | succ fuel ih =>
    rw [renameBlock_succ]
    split
    · rfl
    · rename_i block _
      simp only
      have hchildren : ∀ (children : List Tid) (state : Cfg × RenameState),
          stackOf (children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).2 k =
            stackOf state.2 k := by
        intro children
        induction children with
        | nil => exact fun _ => rfl
        | cons c cs ihc =>
          intro state
          simp only [List.foldl_cons]
          rw [ihc]
          exact ih c state.1 state.2
      show stackOf (popVars _ _) k = stackOf st k
      rw [stackOf_popVars, hchildren, stackOf_renameDefs, stackOf_renamePhis]
      have hcount : (block.phis.map (·.var.base) ++ block.defs.map (·.var.base)).count k =
          (((renamePhis block.phis st).1.map Phi.var).filter fun v => v.base = k).length +
            (((renameDefs block.defs (renamePhis block.phis st).2).1.map Def.var).filter
              fun v => v.base = k).length := by
        rw [length_filter_base, length_filter_base, renamePhis_bases, renameDefs_bases, List.count_append]
      rw [hcount]
      simp only [List.length_append, List.append_assoc]
      generalize ((renamePhis block.phis st).1.map Phi.var).filter (fun v => decide (v.base = k)) = xs
      generalize ((renameDefs block.defs (renamePhis block.phis st).2).1.map Def.var).filter
        (fun v => decide (v.base = k)) = ys
      rw [show (stackOf st k).length + (xs.length + ys.length) - (xs.length + ys.length) =
        (stackOf st k).length by omega]
      simp

/-- Variables a block assigns, in order. -/
def defNames (blk : Blk) : List Var := blk.phis.map Phi.var ++ blk.defs.map Def.var

private structure SAInv (cfg : Cfg) (st : RenameState) (V : Tid → Prop) : Prop where
  pos : ∀ w, 1 ≤ counterOf st w
  bound : ∀ b ∈ cfg.blocks, V b.tid → ∀ v ∈ defNames b, 1 ≤ v.index ∧ v.index < counterOf st v
  nd : ∀ b ∈ cfg.blocks, V b.tid → (defNames b).Nodup
  cross : ∀ b ∈ cfg.blocks, ∀ c ∈ cfg.blocks, V b.tid → V c.tid → b.tid ≠ c.tid →
    ∀ v ∈ defNames b, v ∉ defNames c

/-- Frame for assigned names: blocks keep their tids and assigned variables. -/
private abbrev nameTable (cfg : Cfg) : List (Tid × List Var) := cfg.blocks.map fun b => (b.tid, defNames b)

private theorem SAInv.of_table {a b : Cfg} {st : RenameState} {V : Tid → Prop} (h : SAInv a st V)
    (ht : nameTable b = nameTable a) : SAInv b st V := by
  have hmem : ∀ x ∈ b.blocks, ∃ y ∈ a.blocks, y.tid = x.tid ∧ defNames y = defNames x := by
    intro x hx
    have : (x.tid, defNames x) ∈ nameTable a := by
      rw [← ht]
      exact List.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := List.mem_map.1 this
    simp only [Prod.mk.injEq] at heq
    exact ⟨y, hy, heq.1, heq.2⟩
  refine ⟨h.pos, ?_, ?_, ?_⟩
  · intro x hx hv v hm
    obtain ⟨y, hy, h1, h2⟩ := hmem x hx
    exact h.bound y hy (h1 ▸ hv) v (h2 ▸ hm)
  · intro x hx hv
    obtain ⟨y, hy, h1, h2⟩ := hmem x hx
    exact h2 ▸ h.nd y hy (h1 ▸ hv)
  · intro x hx z hz hvx hvz hne v hm
    obtain ⟨y, hy, h1, h2⟩ := hmem x hx
    obtain ⟨w, hw, h3, h4⟩ := hmem z hz
    rw [← h4]
    exact h.cross y hy w hw (h1 ▸ hvx) (h3 ▸ hvz) (by rw [h1, h3]; exact hne) v (h2 ▸ hm)

private theorem updatePhiInputs_table (source successor : Tid) (st : RenameState) (cfg : Cfg) :
    nameTable (updatePhiInputs source successor st cfg) = nameTable cfg := by
  show ((cfg.blocks.map _).map _) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  simp only [Function.comp]
  split
  · simp [defNames, Function.comp_def]
  · rfl

private theorem updatePhi_fold_table (source : Tid) (st : RenameState) (succs : List Tid) (cfg : Cfg) :
    nameTable (succs.foldl (fun cfg successor => updatePhiInputs source successor st cfg) cfg) = nameTable cfg := by
  induction succs generalizing cfg with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons]
    rw [ih, updatePhiInputs_table]

private theorem SAInv.mono {cfg : Cfg} {st st' : RenameState} {V : Tid → Prop} (h : SAInv cfg st V)
    (hm : ∀ w, counterOf st w ≤ counterOf st' w) : SAInv cfg st' V :=
  ⟨fun w => Nat.le_trans (h.pos w) (hm w),
    fun b hb hv v hv' => ⟨(h.bound b hb hv v hv').1, Nat.lt_of_lt_of_le (h.bound b hb hv v hv').2 (hm v)⟩,
    h.nd, h.cross⟩

/-- Renaming the statements of block `t` makes `t` a visited block. -/
private theorem SAInv.edit {cfg : Cfg} {st : RenameState} {V : Tid → Prop} (h : SAInv cfg st V) (t : Tid)
    (block : Blk) :
    SAInv (cfg.updateBlock t (renameEdit block st)) (renameDefs block.defs (renamePhis block.phis st).2).2
      (fun x => V x ∨ x = t) := by
  have hi := (issued_renamePhis block.phis st).append
    (issued_renameDefs block.defs (renamePhis block.phis st).2)
  have hnames : ∀ b, defNames (renameEdit block st b) =
      (renamePhis block.phis st).1.map Phi.var ++
        (renameDefs block.defs (renamePhis block.phis st).2).1.map Def.var := fun _ => rfl
  have hcases : ∀ b ∈ (cfg.updateBlock t (renameEdit block st)).blocks,
      (b.tid = t ∧ defNames b = (renamePhis block.phis st).1.map Phi.var ++
        (renameDefs block.defs (renamePhis block.phis st).2).1.map Def.var) ∨ (b ∈ cfg.blocks ∧ b.tid ≠ t) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    by_cases hct : c.tid = t
    · have heq : (if c.tid = t then renameEdit block st c else c) = renameEdit block st c := by simp [hct]
      rw [heq]
      exact Or.inl ⟨hct, hnames c⟩
    · have heq : (if c.tid = t then renameEdit block st c else c) = c := by simp [hct]
      rw [heq]
      exact Or.inr ⟨hc, hct⟩
  refine ⟨fun w => Nat.le_trans (h.pos w) (hi.mono w), ?_, ?_, ?_⟩
  · intro b hb hv v hm
    rcases hcases b hb with ⟨_, hn⟩ | ⟨hold, hne⟩
    · rw [hn] at hm
      have := hi.range v hm
      have := h.pos v
      exact ⟨by omega, by omega⟩
    · have hvb : V b.tid := hv.resolve_right hne
      have := h.bound b hold hvb v hm
      have := hi.mono v
      exact ⟨by omega, by omega⟩
  · intro b hb hv
    rcases hcases b hb with ⟨_, hn⟩ | ⟨hold, hne⟩
    · rw [hn]
      exact hi.nodup
    · exact h.nd b hold (hv.resolve_right hne)
  · intro b hb c hc hvb hvc hne v hm hm'
    rcases hcases b hb with ⟨hbt, hn⟩ | ⟨hold, hbne⟩ <;> rcases hcases c hc with ⟨hct, hn'⟩ | ⟨hold', hcne⟩
    · exact hne (hbt.trans hct.symm)
    · rw [hn] at hm
      have h1 := hi.range v hm
      have h2 := h.bound c hold' (hvc.resolve_right hcne) v hm'
      omega
    · rw [hn'] at hm'
      have h1 := hi.range v hm'
      have h2 := h.bound b hold (hvb.resolve_right hbne) v hm
      omega
    · exact h.cross b hold c hold' (hvb.resolve_right hbne) (hvc.resolve_right hcne) hne v hm hm'

/-- Dominator-tree paths from a block down to a descendant. -/
private inductive TreeFrom (idom : List (Tid × Tid)) : Tid → Nat → Tid → Prop where
  | self (t : Tid) : TreeFrom idom t 0 t
  | child {t c k n} : (c, t) ∈ idom → TreeFrom idom c k n → TreeFrom idom t (k + 1) n

private theorem TreeFrom.snoc {idom : List (Tid × Tid)} {t p n : Tid} {k : Nat} (h : TreeFrom idom t k p)
    (he : (n, p) ∈ idom) : TreeFrom idom t (k + 1) n := by
  induction h with
  | self t => exact .child he (.self n)
  | child hc _ ih => exact .child hc (ih he)

/-- Renaming from `t` visits every dominator-tree descendant within the fuel. -/
private theorem renameBlock_visits (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg)
    (st : RenameState) (V : Tid → Prop) (h : SAInv cfg st V)
    (hidom : ∀ e ∈ idom, e.1 ∈ cfg.blocks.map Blk.tid) (ht : t ∈ cfg.blocks.map Blk.tid) :
    ∃ V', SAInv (renameBlock idom fuel t cfg st).1 (renameBlock idom fuel t cfg st).2 V' ∧ (∀ x, V x → V' x) ∧
      ∀ k n, k < fuel → TreeFrom idom t k n → V' n := by
  induction fuel generalizing t cfg st V with
  | zero => exact ⟨V, h, fun _ h => h, fun k n hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ fuel ih =>
    obtain ⟨block, hb⟩ := block_exists ht
    rw [renameBlock_succ]
    simp only [hb]
    have hedit := h.edit t block
    let c₁ := cfg.updateBlock t (renameEdit block st)
    have hc₁ : c₁.blocks.map Blk.tid = cfg.blocks.map Blk.tid :=
      updateBlock_tids cfg t _ (fun _ _ => rfl)
    let st₂ := (renameDefs block.defs (renamePhis block.phis st).2).2
    let c₂ := (c₁.successors t).foldl (fun cfg successor => updatePhiInputs t successor st₂ cfg) c₁
    have hc₂ : c₂.blocks.map Blk.tid = cfg.blocks.map Blk.tid :=
      ((updatePhi_fold_frame t st₂ (c₁.successors t) c₁).tids).trans hc₁
    have hsa₂ : SAInv c₂ st₂ (fun x => V x ∨ x = t) :=
      hedit.of_table (updatePhi_fold_table t st₂ _ c₁)
    have hchildren : ∀ (children : List Tid) (state : Cfg × RenameState) (W : Tid → Prop),
        SAInv state.1 state.2 W → state.1.blocks.map Blk.tid = cfg.blocks.map Blk.tid →
        (∀ c ∈ children, c ∈ cfg.blocks.map Blk.tid) →
        ∃ W', SAInv (children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).1
          (children.foldl (fun current child => renameBlock idom fuel child current.1 current.2) state).2 W' ∧
          (∀ x, W x → W' x) ∧ ∀ c ∈ children, ∀ k n, k < fuel → TreeFrom idom c k n → W' n := by
      intro children
      induction children with
      | nil => exact fun state W hW _ _ => ⟨W, hW, fun _ h => h, by simp⟩
      | cons c cs ihc =>
        intro state W hW htids hcs
        simp only [List.foldl_cons]
        obtain ⟨W₁, h₁, hm₁, hv₁⟩ := ih c state.1 state.2 W hW (by rw [htids]; exact hidom)
          (by rw [htids]; exact hcs c (by simp))
        have htids' : (renameBlock idom fuel c state.1 state.2).1.blocks.map Blk.tid = cfg.blocks.map Blk.tid :=
          ((renameBlock_frame idom fuel c state.1 state.2).1.tids).trans htids
        obtain ⟨W₂, h₂, hm₂, hv₂⟩ := ihc (renameBlock idom fuel c state.1 state.2) W₁ h₁ htids'
          (fun z hz => hcs z (List.mem_cons_of_mem _ hz))
        refine ⟨W₂, h₂, fun x hx => hm₂ x (hm₁ x hx), ?_⟩
        intro z hz k n hk htree
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hm₂ n (hv₁ k n hk htree)
        · exact hv₂ z hz k n hk htree
    have hkids : ∀ c ∈ (idom.filter fun entry => entry.2 = t).map Prod.fst, c ∈ cfg.blocks.map Blk.tid := by
      intro c hc
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      exact hidom e (List.mem_filter.1 he).1
    obtain ⟨W, hW, hmW, hcov⟩ := hchildren _ (c₂, st₂) _ hsa₂ hc₂ hkids
    refine ⟨W, ?_, fun x hx => hmW x (Or.inl hx), ?_⟩
    · exact hW.mono (fun w => Nat.le_of_eq (counterOf_popVars _ _ w).symm)
    · intro k n hk htree
      cases htree with
      | self => exact hmW t (Or.inr rfl)
      | @child _ c k' _ he hsub =>
        refine hcov c ?_ k' n (by omega) hsub
        exact List.mem_map.2 ⟨(c, t), List.mem_filter.2 ⟨he, by simp⟩, rfl⟩

private def phiCfg (sub : Sub) : Cfg :=
  let cfg := Cfg.connected sub
  insertAllPhis cfg cfg.dominanceFrontier
    (cfg.blocks.flatMap fun blk => (blk.definedVars ++ blk.freeVars).map Var.base).eraseDups

private theorem ssaCfg_eq (sub : Sub) :
    ssaCfg sub = (renameBlock (Cfg.connected sub).immediateDominators ((phiCfg sub).blocks.length + 1)
      (phiCfg sub).start (phiCfg sub) {}).1 := rfl

private theorem phiCfg_frame (sub : Sub) : PropFrame (Cfg.connected sub) (phiCfg sub) := insertAllPhis_frame ..

private theorem connected_tids_eq_nodes (sub : Sub) :
    (Cfg.connected sub).blocks.map Blk.tid = (Cfg.connected sub).graph.nodes := by
  rw [connected_blocks, connected_nodes]
  simp [pseudoStart, pseudoExit]

/-- Every block of the output of `toSsa` was renamed: whole-subroutine single assignment. With unique
block tids, no variable is assigned twice anywhere and no assigned name is an unversioned base. -/
theorem toSsa_single_assignment (sub : Sub) (hnd : (sub.blks.map Blk.tid).Nodup) :
    ((toSsa sub).blks.flatMap defNames).Nodup ∧ ∀ blk ∈ (toSsa sub).blks, ∀ v ∈ defNames blk, v.index ≠ 0 := by
  let idom := (Cfg.connected sub).immediateDominators
  have hempty : SAInv (phiCfg sub) ({} : RenameState) (fun _ => False) :=
    ⟨fun _ => Nat.le_refl _, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
  have htids : (phiCfg sub).blocks.map Blk.tid = (Cfg.connected sub).graph.nodes :=
    ((phiCfg_frame sub).tids).trans (connected_tids_eq_nodes sub)
  have hstart : (phiCfg sub).start = pseudoStart := by
    rw [(phiCfg_frame sub).start, connected_start]
  have hkeys : ∀ e ∈ idom, e.1 ∈ (phiCfg sub).blocks.map Blk.tid := by
    rintro ⟨n, i⟩ he
    rw [htids]
    exact Bap.Proofs.Graph.reachableFrom_subset_nodes _ _
      (Bap.Proofs.Graph.immediateDominators_spec he).1
  have hst : (phiCfg sub).start ∈ (phiCfg sub).blocks.map Blk.tid := by
    rw [htids, hstart, connected_nodes]
    simp
  obtain ⟨V, hinv, -, hcov⟩ := renameBlock_visits idom ((phiCfg sub).blocks.length + 1)
    (phiCfg sub).start (phiCfg sub) {} (fun _ => False) hempty hkeys hst
  have hchain : ∀ k n, Bap.Proofs.Graph.IdomChain (Cfg.connected sub).graph (Cfg.connected sub).start k n →
      TreeFrom idom (phiCfg sub).start k n := by
    intro k n hc
    induction hc with
    | start =>
      rw [hstart, connected_start]
      exact .self _
    | step he _ ih => exact ih.snoc he
  have hvisited : ∀ b ∈ sub.blks, V b.tid := by
    intro b hb
    have hr := connected_all_reachable sub (List.mem_map.2 ⟨b, hb, rfl⟩)
    obtain ⟨k, hk, hc⟩ := Bap.Proofs.Graph.idomChain_exists hr
    refine hcov k b.tid ?_ (hchain k b.tid hc)
    have hlen : (phiCfg sub).blocks.length = (Cfg.connected sub).graph.nodes.length := by
      rw [← htids]
      simp
    omega
  have hinv' : SAInv (ssaCfg sub) (renameBlock idom ((phiCfg sub).blocks.length + 1)
      (phiCfg sub).start (phiCfg sub) {}).2 V := hinv
  -- each output block is the renamed block found under the tid of an input block
  have hout : ∀ x ∈ (toSsa sub).blks, x ∈ (ssaCfg sub).blocks ∧ V x.tid := by
    intro x hx
    rw [toSsa_eq] at hx
    obtain ⟨b, hb, hfind⟩ := List.mem_filterMap.1 hx
    obtain ⟨hm, ht⟩ := block_some hfind
    exact ⟨hm, ht ▸ hvisited b hb⟩
  have hnd' : ((toSsa sub).blks.map Blk.tid).Nodup := by
    rw [toSsa_tids]
    exact hnd
  refine ⟨?_, ?_⟩
  · have key : ∀ l : List Blk, (l.map Blk.tid).Nodup → (∀ x ∈ l, x ∈ (ssaCfg sub).blocks ∧ V x.tid) →
        (l.flatMap defNames).Nodup := by
      intro l
      induction l with
      | nil => intro _ _; simp
      | cons a as ih =>
        intro hl hall
        have hl' : a.tid ∉ as.map Blk.tid ∧ (as.map Blk.tid).Nodup := by simpa using hl
        have ha := hall a (by simp)
        simp only [List.flatMap_cons]
        refine List.nodup_append.2 ⟨hinv'.nd a ha.1 ha.2,
          ih hl'.2 (fun x hx => hall x (List.mem_cons_of_mem _ hx)), ?_⟩
        rintro y hy z hz rfl
        obtain ⟨c, hc, hyc⟩ := List.mem_flatMap.1 hz
        have hcv := hall c (List.mem_cons_of_mem _ hc)
        have hne : a.tid ≠ c.tid := by
          intro heq
          exact hl'.1 (heq ▸ List.mem_map.2 ⟨c, hc, rfl⟩)
        exact hinv'.cross a ha.1 c hcv.1 ha.2 hcv.2 hne y hy hyc
    exact key _ hnd' hout
  · intro blk hblk v hv
    obtain ⟨hm, hvis⟩ := hout blk hblk
    have := (hinv'.bound blk hm hvis v hv).1
    omega

/-- Blocks 2 and 3 are siblings under block 1; block 2 assigns `x` twice and block 3 reads `x`. -/
private def ssaSample : Sub :=
  ⟨1, "ssa", [], [
    ⟨1, [], [], [⟨20, none, .goto (.direct 2)⟩, ⟨21, none, .goto (.direct 3)⟩]⟩,
    ⟨2, [], [⟨10, vx, .int (1#8)⟩, ⟨11, vx, .int (2#8)⟩], []⟩,
    ⟨3, [], [⟨12, vy, .var vx⟩], []⟩]⟩

/-- Block 3 reads the unversioned `x`, not a name defined in its sibling. -/
theorem toSsa_sibling_definition_hidden :
    ((toSsa ssaSample).blks.map fun blk =>
      blk.defs.map fun defn => (defn.var, Bil.freeVars defn.rhs)) =
      [[], [(vx.version 1, []), (vx.version 2, [])], [(vy.version 1, [vx])]] := by
  rfl

/-! ### Wire round trips -/

private theorem nat_repr_roundtrip (n : Nat) : Sexp.nat (.atom n.repr) = .ok n := by
  simp [Sexp.nat, Sexp.asAtom, Bind.bind, Except.bind, Nat.toNat?_repr]

private theorem hexDigit_digitChar : ∀ d : Fin 16, hexDigit (Nat.digitChar d.val) = some d.val := by
  decide

private theorem parseHexLoop_nil (acc : Nat) : parseHexLoop [] acc = .ok acc := rfl

private theorem parseHexLoop_cons {c : Char} {d : Nat} (rest : List Char) (acc : Nat) (hc : hexDigit c = some d) :
    parseHexLoop (c :: rest) acc = parseHexLoop rest (acc * 16 + d) := by
  show (match hexDigit c with
    | some digit => parseHexLoop rest (acc * 16 + digit)
    | none => .error s!"invalid hexadecimal digit {c}") = _
  rw [hc]

private theorem parseHexLoop_snoc (xs : List Char) (c : Char) (d acc r : Nat)
    (hdig : ∀ x ∈ xs, ∃ v, hexDigit x = some v)
    (hxs : parseHexLoop xs acc = .ok r) (hc : hexDigit c = some d) :
    parseHexLoop (xs ++ [c]) acc = .ok (r * 16 + d) := by
  induction xs generalizing acc with
  | nil =>
    have : acc = r := by
      rw [parseHexLoop_nil] at hxs
      simpa using hxs
    subst this
    simp only [List.nil_append]
    rw [parseHexLoop_cons _ _ hc, parseHexLoop_nil]
  | cons x xs ih =>
    obtain ⟨v, hv⟩ := hdig x (by simp)
    rw [parseHexLoop_cons _ _ hv] at hxs
    rw [List.cons_append, parseHexLoop_cons _ _ hv]
    exact ih _ (fun y hy => hdig y (List.mem_cons_of_mem _ hy)) hxs

private theorem hexDigit_of_lt {d : Nat} (h : d < 16) : hexDigit (Nat.digitChar d) = some d :=
  hexDigit_digitChar ⟨d, h⟩

private theorem parseHexLoop_toDigits (n : Nat) :
    (∀ x ∈ Nat.toDigits 16 n, ∃ v, hexDigit x = some v) ∧ parseHexLoop (Nat.toDigits 16 n) 0 = .ok n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hn : n < 16
    · rw [Nat.toDigits_of_lt_base hn]
      refine ⟨?_, ?_⟩
      · simp only [List.mem_singleton]
        rintro x rfl
        exact ⟨_, hexDigit_of_lt hn⟩
      · rw [parseHexLoop_cons _ _ (hexDigit_of_lt hn), parseHexLoop_nil]
        simp
    · rw [Nat.toDigits_of_base_le (by omega) (by omega)]
      obtain ⟨hall, hval⟩ := ih (n / 16) (by omega)
      have hmod := hexDigit_of_lt (d := n % 16) (by omega)
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hall x h
        · rw [List.mem_singleton.1 h]
          exact ⟨_, hmod⟩
      · rw [parseHexLoop_snoc _ _ _ _ _ hall hval hmod]
        congr 1
        omega

/-- Hexadecimal printing of a word parses back to its value. -/
theorem parseHex_toHex {width : Nat} (value : BitVec width) :
    parseHex (Word.toHex value) = .ok value.toNat := by
  have hne : (String.ofList (Nat.toDigits 16 value.toNat)).isEmpty = false := by
    simp
  unfold parseHex Word.toHex Word.toNat
  rw [hne]
  simpa using (parseHexLoop_toDigits value.toNat).2

theorem parseTyp_printTyp (typ : Typ) : parseTyp (printTyp typ) = .ok typ := by
  cases typ <;>
    simp [parseTyp, printTyp, Sexp.tagged, nat_repr_roundtrip, Bind.bind, Except.bind, pure]

private theorem parseVar_printVar' (var : Var) : parseVar
    (.list [.atom "var", .atom var.name, .atom var.index.repr, printTyp var.typ,
      .atom (if var.isVirtual = true then "1" else "0")]) = .ok var := by
  obtain ⟨name, typ, index, virt⟩ := var
  cases virt <;>
    simp [parseVar, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, nat_repr_roundtrip,
      parseTyp_printTyp, Bind.bind, Except.bind, pure]

theorem parseVar_printVar (var : Var) : parseVar (printVar var) = .ok var :=
  parseVar_printVar' var

theorem parseEndian_printEndian (e : Endian) : parseEndian (printEndian e) = .ok e := by
  cases e <;> rfl

theorem parseCast_printCast (c : Cast) : parseCast (printCast c) = .ok c := by
  cases c <;> rfl

theorem parseUnOp_printUnOp (o : UnOp) : parseUnOp (printUnOp o) = .ok o := by
  cases o <;> rfl

theorem parseBinOp_printBinOp (o : BinOp) : parseBinOp (printBinOp o) = .ok o := by
  cases o <;> rfl

/-- Printing then parsing any BIL expression returns it unchanged. -/
theorem parseExp_printExp (exp : Exp) : parseExp (printExp exp) = .ok exp := by
  induction exp with
  | int value =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, parseHex_toHex, Nat.toNat?_repr, value.isLt]
  | var var =>
    simp [printExp, printVar, parseExp, Sexp.tagged, Bind.bind, Except.bind, parseVar_printVar']
  | load _ _ endian size ih1 ih2 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseEndian_printEndian, nat_repr_roundtrip]
  | store _ _ _ endian size ih1 ih2 ih3 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseEndian_printEndian, nat_repr_roundtrip]
  | bin op _ _ ih1 ih2 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseBinOp_printBinOp]
  | un op _ ih =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseUnOp_printUnOp]
  | cast kind width _ ih =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseCast_printCast, nat_repr_roundtrip]
  | letIn var _ _ ih1 ih2 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, parseVar_printVar]
  | ite _ _ _ ih1 ih2 ih3 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *]
  | extract high low _ ih =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *, nat_repr_roundtrip]
  | concat _ _ ih1 ih2 =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, *]
  | unknown message typ =>
    simp [printExp, parseExp, Sexp.tagged, Bind.bind, Except.bind, Sexp.asAtom, parseTyp_printTyp]

private theorem mapM_roundtrip {α : Type} {print : α → Sexp} {parse : Sexp → Except String α}
    (h : ∀ a, parse (print a) = .ok a) (l : List α) :
    (l.map print).mapM parse = .ok l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp [List.mapM_cons, h, ih, Bind.bind, Except.bind, pure, Except.pure]

theorem parseLabel_printLabel (label : Label) : parseLabel (printLabel label) = .ok label := by
  cases label <;>
    simp [printLabel, parseLabel, Sexp.tagged, Bind.bind, Except.bind, nat_repr_roundtrip, parseExp_printExp]

theorem parseOptionalLabel_printOptionalLabel (label : Option Label) :
    parseOptionalLabel (printOptionalLabel label) = .ok label := by
  cases label <;>
    simp [printOptionalLabel, parseOptionalLabel, Sexp.tagged, Bind.bind, Except.bind, parseLabel_printLabel]

private theorem parseDef_printDef (tag : String) (defn : Def) :
    parseDefWithTag tag (printDefWithTag tag defn) = .ok defn := by
  unfold_parseDefWithTag
  simp [Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, pure, Except.pure,
    nat_repr_roundtrip, parseVar_printVar, parseExp_printExp]

private theorem mapM_ok {α : Type} {g : α → Except String α} (l : List α) (h : ∀ a, g a = .ok a) :
    l.mapM g = .ok l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, h, ih, Bind.bind, Except.bind, pure, Except.pure]

theorem parsePhi_printPhi (phi : Phi) : parsePhi (printPhi phi) = .ok phi := by
  obtain ⟨tid, var, values⟩ := phi
  simp only [printPhi, parsePhi, Sexp.tagged]
  simp [Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, pure, Except.pure, nat_repr_roundtrip,
    parseVar_printVar]
  rw [mapM_ok]
  rintro ⟨t, v⟩
  simp [nat_repr_roundtrip, parseExp_printExp]

theorem parseJmp_printJmp (jmp : Jmp) : parseJmp (printJmp jmp) = .ok jmp := by
  obtain ⟨tid, condition, kind⟩ := jmp
  cases condition <;> cases kind <;>
    simp [printJmp, parseJmp, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, pure, Except.pure, nat_repr_roundtrip, parseLabel_printLabel, parseOptionalLabel_printOptionalLabel, parseExp_printExp]

theorem parseBlk_printBlk (blk : Blk) : parseBlk (printBlk blk) = .ok blk := by
  obtain ⟨tid, phis, defs, jmps⟩ := blk
  simp [printBlk, parseBlk, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, pure,
    Except.pure, nat_repr_roundtrip, mapM_roundtrip parsePhi_printPhi, mapM_roundtrip parseJmp_printJmp,
    mapM_roundtrip (parseDef_printDef "def")]

/-- Printing then parsing a whole subroutine returns it unchanged. -/
theorem parseSub_printSub (sub : Sub) : parseSub (printSub sub) = .ok sub := by
  obtain ⟨tid, name, args, blks⟩ := sub
  simp [printSub, parseSub, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, Bind.bind, Except.bind,
    pure, Except.pure, nat_repr_roundtrip, mapM_roundtrip parseBlk_printBlk,
    mapM_roundtrip (parseDef_printDef "arg")]

end Bap.Proofs.IR
