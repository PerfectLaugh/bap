import Bap.IR.Ssa
import Bap.IR.Optimize
import Bap.IR.Wire
import Bap.Proofs.Graph
import Bap.Proofs.Bil
import Bap.Proofs.Liveness

namespace Bap.Proofs.IR

open Bap Bap.Bil Bap.IR Bap.Bil.Wire Bap.IR.Wire



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

local macro "unfold_blockOut_with " h:term : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockOut)):ident, $h:term])
local macro "livenessRaw" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessRaw)
local macro "livenessFromRaw" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessFromRaw)
local macro "rowsOf" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.rowsOf)

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
local macro "ssaReplacements" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.replacements)
local macro "initialState" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Ssa) 0 ++ `Bap.IR.initialState)
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
          simp [this, hr]
        · have : b.tid ∉ cfg.prune.graph.nodes := fun h => hr (prune_mem_nodes.1 h)
          simp only [List.filter_cons, this, decide_false, Bool.false_eq_true, ite_false, ih, hr]
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
        ((sub.blks.map Blk.tid).head?.toList ++
          (sub.blks.map Blk.tid |>.filter fun tid => ((Cfg.fromSub sub).predecessors tid).isEmpty)).map
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
definitions run in order under `Bil.evalExp`, and the values of memory writes are recorded.

A definition writes memory when its value is the memory a store produced, directly or selected through
a `let` or an `ite`. BIL expressions are pure: a store whose result is only read through, as in
`load (store m a v) a'`, or discarded leaves memory as it was, so it is not an effect at all. -/

/-- Is this expression a plain variable read? -/
def isVarExp : Exp → Bool
  | .var _ => true
  | _ => false

/-- A branch condition as a truth value, with the rule of `ite` and `if`: it must be one bit. -/
def valueTruth (value : Value) : Except String Bool :=
  match Value.asBits value with
  | .error message => .error message
  | .ok ⟨width, bits⟩ =>
    if h : width = 1 then .ok (decide ((h ▸ bits : BitVec 1) = 1)) else .error "condition must be one bit"

/-- Is the value of this expression, in this environment, the result of a store? -/
def writesMemory (env : Env) : Exp → Bool
  | .store _ _ _ _ _ => true
  | .letIn var value body =>
    match evalExp env value with
    | .ok result => writesMemory (Bil.bind env var result) body
    | .error _ => false
  | .ite condition yes no =>
    match evalExp env condition with
    | .error _ => false
    | .ok value =>
      match valueTruth value with
      | .ok true => writesMemory env yes
      | .ok false => writesMemory env no
      | .error _ => false
  | _ => false

/-- Runs definitions in order, returning the final environment and the values written to memory. -/
def execDefs (env : Env) : List Def → Except String (Env × List (Var × Value))
  | [] => .ok (env, [])
  | defn :: rest =>
    match evalExp env defn.rhs with
    | .error message => .error message
    | .ok value =>
      match execDefs (Bil.bind env defn.var value) rest with
      | .error message => .error message
      | .ok result => .ok (result.1, if writesMemory env defn.rhs then (defn.var, value) :: result.2 else result.2)

private theorem execDefs_cons {env : Env} {d : Def} {ds : List Def} {r : Env × List (Var × Value)}
    (h : execDefs env (d :: ds) = .ok r) :
    ∃ v r', evalExp env d.rhs = .ok v ∧ execDefs (Bil.bind env d.var v) ds = .ok r' ∧
      r = (r'.1, if writesMemory env d.rhs then (d.var, v) :: r'.2 else r'.2) := by
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
      .ok (r'.1, if writesMemory env d.rhs then (d.var, v) :: r'.2 else r'.2) := by
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
        simp [hv, ih]
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

/-- A write is visible in the syntax of the expression, so dead-code elimination never removes it. -/
private theorem hasSideEffect_of_writes (env : Env) {e : Exp} (h : writesMemory env e = true) : hasSideEffect e = true := by
  induction e generalizing env with
  | store _ _ _ _ _ => rfl
  | letIn v val body _ ih₂ =>
    simp only [writesMemory] at h
    split at h
    · unfold_hasSideEffect
      simp [ih₂ _ h]
    · cases h
  | ite c y n _ ih₂ ih₃ =>
    simp only [writesMemory] at h
    split at h
    · cases h
    · split at h
      · unfold_hasSideEffect
        simp [ih₂ _ h]
      · unfold_hasSideEffect
        simp [ih₃ _ h]
      · cases h
  | _ => simp [writesMemory] at h

/-- Whether an expression writes depends only on its free variables. -/
theorem writesMemory_congr (e : Exp) {env env' : Env} (h : ∀ x ∈ Bil.freeVars e, Bil.lookup env x = Bil.lookup env' x) :
    writesMemory env e = writesMemory env' e := by
  induction e generalizing env env' with
  | letIn v val body _ ih₂ =>
    have hval : evalExp env val = evalExp env' val := Bap.Proofs.Bil.evalExp_congr_freeVars val fun x hx => h x (by
      rw [Bap.Proofs.Bil.mem_freeVars_iff] at hx ⊢
      simp [Bil.occursFree, hx])
    simp only [writesMemory, hval]
    split
    · apply ih₂
      intro x hx
      by_cases hxv : x = v
      · subst hxv
        rw [lookup_bind_same, lookup_bind_same]
      · rw [lookup_bind_ne _ _ hxv, lookup_bind_ne _ _ hxv]
        apply h
        rw [Bap.Proofs.Bil.mem_freeVars_iff] at hx ⊢
        simp [Bil.occursFree, hx, Ne.symm hxv]
    · rfl
  | ite c y n _ ih₂ ih₃ =>
    have hmem : ∀ x z, (z = c ∨ z = y ∨ z = n) → x ∈ Bil.freeVars z → x ∈ Bil.freeVars (.ite c y n) := by
      intro x z hz hx
      rw [Bap.Proofs.Bil.mem_freeVars_iff] at hx ⊢
      rcases hz with rfl | rfl | rfl <;> simp [Bil.occursFree, hx]
    have hc : evalExp env c = evalExp env' c :=
      Bap.Proofs.Bil.evalExp_congr_freeVars c fun x hx => h x (hmem x c (Or.inl rfl) hx)
    simp only [writesMemory, hc]
    rw [ih₂ (fun x hx => h x (hmem x y (Or.inr (Or.inl rfl)) hx)), ih₃ (fun x hx => h x (hmem x n (Or.inr (Or.inr rfl)) hx))]
  | _ => rfl

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

/-- The last definition of a variable live at the end of the block is kept, with everything after
it scanned as if the prefix were absent; the kept suffix is a sublist of `post`, so it stays last. -/
theorem dceDefs_keeps_last_def (pre post : List Def) (d : Def) (live : List Var) (hlive : d.var ∈ live)
    (hlast : ∀ c ∈ post, c.var ≠ d.var) :
    ∃ pre', pre'.Sublist pre ∧ (dceDefs (pre ++ d :: post) live).1 = pre' ++ d :: (dceDefs post live).1 := by
  induction pre with
  | nil =>
    have hmem : d.var ∈ (dceDefs post live).2 :=
      (mem_dceDefs_live post live d.var).2
        (Or.inr ⟨hlive, fun c hc => hlast c ((dceDefs_sublist post live).subset hc)⟩)
    refine ⟨[], List.Sublist.refl _, ?_⟩
    rw [List.nil_append, dceDefs_cons]
    simp [hmem]
  | cons p ps ih =>
    obtain ⟨pre', hsub, heq⟩ := ih
    rw [List.cons_append, dceDefs_cons]
    split
    · exact ⟨p :: pre', hsub.cons_cons _, by simp only [heq, List.cons_append]⟩
    · exact ⟨pre', hsub.cons _, heq⟩

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
      have hw : writesMemory env' d.rhs = writesMemory env d.rhs :=
        (writesMemory_congr d.rhs fun x hx => hag x (List.mem_append_right _ hx)).symm
      simp only [ht, hw]
    · rename_i hc
      simp only [hc]
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
      have hns : writesMemory env d.rhs = false := by
        cases hs : writesMemory env d.rhs with
        | false => rfl
        | true =>
          have := hasSideEffect_of_writes env hs
          rw [this] at hc
          cases hc.2
      simp only [hns, Bool.false_eq_true, ite_false, ht]

private abbrev dceLive (ps : List Var) (cfg : Cfg) (blk : Blk) : List Var :=
  (Assoc.get blk.tid cfg.liveness.2).getD [] ++ blk.jmps.flatMap Jmp.freeVars ++ ps

private def dceBlk (ps : List Var) (cfg : Cfg) (blk : Blk) : Blk :=
  { blk with
    defs := (dceDefs blk.defs (dceLive ps cfg blk)).1
    phis := blk.phis.filter fun phi => (dceDefs blk.defs (dceLive ps cfg blk)).2.contains phi.var }

private theorem dcePass_eq (ps : List Var) (cfg : Cfg) : dcePass ps cfg = { cfg with blocks := cfg.blocks.map (dceBlk ps cfg) } := rfl

/-- A phi is removed only if its variable is not live on block entry. -/
theorem dcePass_phi_removed_unused (ps : List Var) (cfg : Cfg) {blk : Blk} {phi : Phi} (hphi : phi ∈ blk.phis)
    (hremoved : phi ∉ (dceBlk ps cfg blk).phis) : phi.var ∉ (dceDefs blk.defs (dceLive ps cfg blk)).2 := by
  intro hlive
  apply hremoved
  exact List.mem_filter.2 ⟨hphi, by simpa using hlive⟩

private abbrev weight (blocks : List Blk) : Nat :=
  (blocks.map fun blk => blk.defs.length + blk.phis.length).sum

private theorem dceAux_succ (ps : List Var) (cfg : Cfg) (fuel : Nat) :
    dceAux ps cfg (fuel + 1) =
      if (cfg.blocks.map fun blk => (blk.defs.length, blk.phis.length)) =
          ((dcePass ps cfg).blocks.map fun blk => (blk.defs.length, blk.phis.length))
      then cfg else dceAux ps (dcePass ps cfg) fuel := rfl

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

private theorem eliminateDeadCode_eq (ps : List Var) (cfg : Cfg) : eliminateDeadCode cfg ps = dceAux ps cfg (weight cfg.blocks + 1) := by
  show dceAux ps cfg (cfg.blocks.foldl _ 0 + 1) = _
  rw [foldl_count, Nat.zero_add]

private theorem dceBlk_defs_le (ps : List Var) (cfg : Cfg) (b : Blk) : (dceBlk ps cfg b).defs.length ≤ b.defs.length :=
  (dceDefs_sublist ..).length_le

private theorem dceBlk_phis_le (ps : List Var) (cfg : Cfg) (b : Blk) : (dceBlk ps cfg b).phis.length ≤ b.phis.length :=
  List.length_filter_le ..

private theorem weight_dce_le (ps : List Var) (cfg : Cfg) (l : List Blk) : weight (l.map (dceBlk ps cfg)) ≤ weight l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    rw [List.map_cons, weight_cons, weight_cons]
    have := dceBlk_defs_le ps cfg b
    have := dceBlk_phis_le ps cfg b
    omega

private theorem weight_dce_lt (ps : List Var) (cfg : Cfg) (l : List Blk)
    (h : (l.map fun blk => (blk.defs.length, blk.phis.length)) ≠
      ((l.map (dceBlk ps cfg)).map fun blk => (blk.defs.length, blk.phis.length))) :
    weight (l.map (dceBlk ps cfg)) < weight l := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rw [List.map_cons, weight_cons, weight_cons]
    have h1 := dceBlk_defs_le ps cfg b
    have h2 := dceBlk_phis_le ps cfg b
    have h3 := weight_dce_le ps cfg bs
    by_cases hb : (b.defs.length, b.phis.length) = ((dceBlk ps cfg b).defs.length, (dceBlk ps cfg b).phis.length)
    · have htail : (bs.map fun blk => (blk.defs.length, blk.phis.length)) ≠
          ((bs.map (dceBlk ps cfg)).map fun blk => (blk.defs.length, blk.phis.length)) := by
        intro heq
        apply h
        simp only [List.map_cons, heq, hb]
      have := ih htail
      omega
    · have : (dceBlk ps cfg b).defs.length < b.defs.length ∨ (dceBlk ps cfg b).phis.length < b.phis.length := by
        refine Classical.byContradiction fun hc => hb ?_
        simp only [Prod.mk.injEq]
        omega
      omega

private theorem dce_self_of_shape (ps : List Var) (cfg : Cfg) (l : List Blk)
    (h : (l.map fun blk => (blk.defs.length, blk.phis.length)) =
      ((l.map (dceBlk ps cfg)).map fun blk => (blk.defs.length, blk.phis.length))) :
    l.map (dceBlk ps cfg) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hd, hp⟩, ht⟩ := h
    rw [List.map_cons, ih ht]
    congr 1
    have hd' : (dceDefs b.defs (dceLive ps cfg b)).1 = b.defs :=
      (dceDefs_sublist ..).eq_of_length hd.symm
    have hp' := List.filter_eq_self.2 (List.length_filter_eq_length_iff.1 hp.symm)
    simp only [dceBlk, hd', hp']

/-- With fuel above the number of definitions, dead-code elimination reaches a pass fixpoint. -/
private theorem dceAux_fixpoint (ps : List Var) (cfg : Cfg) (fuel : Nat) (hfuel : weight cfg.blocks < fuel) :
    dcePass ps (dceAux ps cfg fuel) = dceAux ps cfg fuel := by
  induction fuel generalizing cfg with
  | zero => omega
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · rename_i heq
      rw [dcePass_eq]
      have := dce_self_of_shape ps cfg cfg.blocks heq
      simp only [this]
    · rename_i hne
      apply ih
      have := weight_dce_lt ps cfg cfg.blocks hne
      show weight (cfg.blocks.map (dceBlk ps cfg)) < fuel
      omega

/-- The output of dead-code elimination is stable under one more pass. -/
theorem dcePass_eliminateDeadCode (ps : List Var) (cfg : Cfg) :
    dcePass ps (eliminateDeadCode cfg ps) = eliminateDeadCode cfg ps := by
  rw [eliminateDeadCode_eq]
  exact dceAux_fixpoint ps cfg _ (Nat.lt_succ_self _)

/-- Dead-code elimination is idempotent. -/
theorem eliminateDeadCode_idempotent (ps : List Var) (cfg : Cfg) :
    eliminateDeadCode (eliminateDeadCode cfg ps) ps = eliminateDeadCode cfg ps := by
  conv => lhs; rw [eliminateDeadCode_eq ps (eliminateDeadCode cfg ps)]
  rw [dceAux_succ, dcePass_eliminateDeadCode]
  simp

/-- Variables read by the jumps of a block. -/
abbrev jumpVars (blk : Blk) : List Var := blk.jmps.flatMap Jmp.freeVars

/-- One-to-one block relation: same identity and jumps, statements only removed, effects kept, the
last definition of each protected variable kept and still last, and every successful run of the
original is matched by the smaller block on everything the jumps read and on the protected variables. -/
private def DceRel (ps : List Var) (x y : Blk) : Prop :=
  x.tid = y.tid ∧ x.jmps = y.jmps ∧ x.defs.Sublist y.defs ∧ x.phis.Sublist y.phis ∧
    (∀ d ∈ y.defs, hasSideEffect d.rhs = true → d ∈ x.defs) ∧
    (∀ pre d post, y.defs = pre ++ d :: post → d.var ∈ ps → (∀ c ∈ post, c.var ≠ d.var) →
      ∃ pre' post', x.defs = pre' ++ d :: post' ∧ pre'.Sublist pre ∧ post'.Sublist post) ∧
    ∀ env r, execDefs env y.defs = .ok r → ∃ r', execDefs env x.defs = .ok r' ∧
      Agree (jumpVars y ++ ps) r.1 r'.1 ∧ r'.2 = r.2

private def Shrinks (ps : List Var) : List Blk → List Blk → Prop
  | [], [] => True
  | x :: xs, y :: ys => DceRel ps x y ∧ Shrinks ps xs ys
  | _, _ => False

private theorem Shrinks.refl (ps : List Var) : (l : List Blk) → Shrinks ps l l
  | [] => trivial
  | _b :: bs => ⟨⟨rfl, rfl, List.Sublist.refl _, List.Sublist.refl _, fun _ h _ => h,
      fun pre _d post h _ _ => ⟨pre, post, h, List.Sublist.refl _, List.Sublist.refl _⟩,
      fun _env r h => ⟨r, h, fun _ _ => rfl, rfl⟩⟩, Shrinks.refl ps bs⟩

private theorem DceRel.trans {ps : List Var} {a b c : Blk} (h₁ : DceRel ps a b) (h₂ : DceRel ps b c) :
    DceRel ps a c := by
  obtain ⟨t₁, j₁, d₁, p₁, e₁, k₁, s₁⟩ := h₁
  obtain ⟨t₂, j₂, d₂, p₂, e₂, k₂, s₂⟩ := h₂
  refine ⟨t₁.trans t₂, j₁.trans j₂, d₁.trans d₂, p₁.trans p₂, fun d hd hs => e₁ d (e₂ d hd hs) hs, ?_, ?_⟩
  · intro pre d post hy hd hl
    obtain ⟨pre', post', hb, hp, hq⟩ := k₂ pre d post hy hd hl
    obtain ⟨pre'', post'', ha, hp', hq'⟩ := k₁ pre' d post' hb hd fun c hc => hl c (hq.subset hc)
    exact ⟨pre'', post'', ha, hp'.trans hp, hq'.trans hq⟩
  intro env r hr
  obtain ⟨r', hr', ha, ht⟩ := s₂ env r hr
  obtain ⟨r'', hr'', ha', ht'⟩ := s₁ env r' hr'
  refine ⟨r'', hr'', fun x hx => ?_, ht'.trans ht⟩
  rw [ha x hx]
  exact ha' x (by simp only [jumpVars, j₂] at hx ⊢; exact hx)

private theorem Shrinks.trans {ps : List Var} : {a b c : List Blk} → Shrinks ps a b → Shrinks ps b c → Shrinks ps a c
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, t₁⟩, ⟨h₂, t₂⟩ => ⟨h₁.trans h₂, Shrinks.trans t₁ t₂⟩

private theorem Shrinks.tids {ps : List Var} : {a b : List Blk} → Shrinks ps a b → a.map Blk.tid = b.map Blk.tid
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, t⟩ => by simp [h.1, Shrinks.tids t]

/-- Agreement on the live seed of a block covers what its jumps read and the protected variables. -/
private theorem dceLive_agree {ps : List Var} {cfg : Cfg} {b : Blk} {e₁ e₂ : Env}
    (h : Agree (dceLive ps cfg b) e₁ e₂) : Agree (jumpVars b ++ ps) e₁ e₂ := by
  intro x hx
  apply h x
  rcases List.mem_append.1 hx with hj | hp
  · exact List.mem_append_left _ (List.mem_append_right _ hj)
  · exact List.mem_append_right _ hp

private theorem dceBlk_rel (ps : List Var) (cfg : Cfg) (b : Blk) : DceRel ps (dceBlk ps cfg b) b := by
  refine ⟨rfl, rfl, dceDefs_sublist .., List.filter_sublist, ?_, ?_, ?_⟩
  · intro d hd hs
    exact dceDefs_keeps_effects _ _ hd hs
  · intro pre d post hy hd hl
    obtain ⟨pre', hs, he⟩ := dceDefs_keeps_last_def pre post d (dceLive ps cfg b) (List.mem_append_right _ hd) hl
    refine ⟨pre', _, ?_, hs, dceDefs_sublist post (dceLive ps cfg b)⟩
    show (dceDefs b.defs (dceLive ps cfg b)).1 = _
    rw [hy]
    exact he
  · intro env r hr
    obtain ⟨r', hr', ha, ht⟩ := dceDefs_simulation b.defs (dceLive ps cfg b)
      (env := env) (env' := env) (fun _ _ => rfl) hr
    exact ⟨r', hr', dceLive_agree ha, ht⟩

private theorem shrinks_dce (ps : List Var) (cfg : Cfg) (l : List Blk) : Shrinks ps (l.map (dceBlk ps cfg)) l := by
  induction l with
  | nil => trivial
  | cons b bs ih => exact ⟨dceBlk_rel ps cfg b, ih⟩

private structure DceFrame (ps : List Var) (a b : Cfg) : Prop where
  start : b.start = a.start
  graph : b.graph = a.graph
  shrinks : Shrinks ps b.blocks a.blocks

private theorem dceAux_frame (ps : List Var) (cfg : Cfg) (fuel : Nat) : DceFrame ps cfg (dceAux ps cfg fuel) := by
  induction fuel generalizing cfg with
  | zero => exact ⟨rfl, rfl, Shrinks.refl ps _⟩
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · exact ⟨rfl, rfl, Shrinks.refl ps _⟩
    · have h := ih (dcePass ps cfg)
      exact ⟨h.start, h.graph, Shrinks.trans h.shrinks (shrinks_dce ps cfg cfg.blocks)⟩

private theorem eliminateDeadCode_frame (ps : List Var) (cfg : Cfg) : DceFrame ps cfg (eliminateDeadCode cfg ps) := by
  rw [eliminateDeadCode_eq]
  exact dceAux_frame ps cfg _

@[simp] theorem eliminateDeadCode_start (ps : List Var) (cfg : Cfg) : (eliminateDeadCode cfg ps).start = cfg.start :=
  (eliminateDeadCode_frame ps cfg).start

@[simp] theorem eliminateDeadCode_graph (ps : List Var) (cfg : Cfg) : (eliminateDeadCode cfg ps).graph = cfg.graph :=
  (eliminateDeadCode_frame ps cfg).graph

theorem eliminateDeadCode_tids (ps : List Var) (cfg : Cfg) :
    (eliminateDeadCode cfg ps).blocks.map Blk.tid = cfg.blocks.map Blk.tid :=
  (eliminateDeadCode_frame ps cfg).shrinks.tids

private theorem Shrinks.pointwise {ps : List Var} {a b : List Blk} (h : Shrinks ps a b) {y : Blk} (hy : y ∈ b) :
    ∃ x ∈ a, DceRel ps x y := by
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
sublist of the input, which holds every side-effecting definition and, still last, the last definition
of each protected variable, and which simulates the input: any successful run succeeds on the output,
agrees on what the jumps read and on the protected variables, and stores the same. -/
theorem eliminateDeadCode_block_spec (ps : List Var) (cfg : Cfg) {y : Blk} (hy : y ∈ cfg.blocks) :
    ∃ x ∈ (eliminateDeadCode cfg ps).blocks, x.tid = y.tid ∧ x.jmps = y.jmps ∧
      x.defs.Sublist y.defs ∧ x.phis.Sublist y.phis ∧
      (∀ d ∈ y.defs, hasSideEffect d.rhs = true → d ∈ x.defs) ∧
      (∀ pre d post, y.defs = pre ++ d :: post → d.var ∈ ps → (∀ c ∈ post, c.var ≠ d.var) →
        ∃ pre' post', x.defs = pre' ++ d :: post' ∧ pre'.Sublist pre ∧ post'.Sublist post) ∧
      ∀ env r, execDefs env y.defs = .ok r → ∃ r', execDefs env x.defs = .ok r' ∧
        Agree (jumpVars y ++ ps) r.1 r'.1 ∧ r'.2 = r.2 :=
  (eliminateDeadCode_frame ps cfg).shrinks.pointwise hy

/-- The last definition of a protected variable in any block survives the whole pipeline, still last. -/
theorem eliminateDeadCode_keeps_last_protected (ps : List Var) (cfg : Cfg) {y : Blk} (hy : y ∈ cfg.blocks)
    {pre post : List Def} {d : Def} (hdefs : y.defs = pre ++ d :: post) (hd : d.var ∈ ps)
    (hlast : ∀ c ∈ post, c.var ≠ d.var) :
    ∃ x ∈ (eliminateDeadCode cfg ps).blocks, x.tid = y.tid ∧
      ∃ pre' post', x.defs = pre' ++ d :: post' ∧ pre'.Sublist pre ∧ post'.Sublist post := by
  obtain ⟨x, hx, ht, _, _, _, _, hk, _⟩ := eliminateDeadCode_block_spec ps cfg hy
  exact ⟨x, hx, ht, hk pre d post hdefs hd hlast⟩

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

private theorem get_filter_other (rs : List (Var × Exp)) {w v : Var} (hw : w ≠ v) :
    Assoc.get w (rs.filter fun r => r.1 != v) = Assoc.get w rs := by
  have key : ∀ l : List (Var × Exp), List.lookup w (l.filter fun r => r.1 != v) = List.lookup w l := by
    intro l
    induction l with
    | nil => rfl
    | cons e es ih =>
      obtain ⟨a, b⟩ := e
      by_cases ha : a = v
      · subst ha
        have hb : (w == a) = false := by simpa using hw
        simp [List.lookup, hb, ih]
      · have hb : (a != v) = true := by simpa using ha
        simp [hb, List.lookup, ih]
  exact key rs

private theorem get_filter_same (rs : List (Var × Exp)) (v : Var) : Assoc.get v (rs.filter fun r => r.1 != v) = none := by
  have key : ∀ l : List (Var × Exp), List.lookup v (l.filter fun r => r.1 != v) = none := by
    intro l
    induction l with
    | nil => rfl
    | cons e es ih =>
      obtain ⟨a, b⟩ := e
      by_cases ha : a = v
      · subst ha
        simpa [List.filter_cons] using ih
      · have hb : (a != v) = true := by simpa using ha
        have hb' : (v == a) = false := by simpa using Ne.symm ha
        simp [hb, List.lookup, hb', ih]
  exact key rs

private theorem substitute_let_body (rs : List (Var × Exp)) (var : Var) (value body : Exp) {env env' : Env} (result : Value)
    (hbody : ∀ v, Bil.occursFree v body = true → v ≠ var → match Assoc.get v rs with
      | some r => evalExp env r = Bil.lookup env' v
      | none => Bil.lookup env v = Bil.lookup env' v) :
    ∃ var' rs', Bil.substitute rs (.letIn var value body) = .letIn var' (Bil.substitute rs value) (Bil.substitute rs' body) ∧
      (∀ e ∈ rs', e ∈ rs ∨ isVarExp e.2 = true) ∧
      ∀ v, Bil.occursFree v body = true → match Assoc.get v rs' with
        | some r => evalExp (Bil.bind env var' result) r = Bil.lookup (Bil.bind env' var result) v
        | none => Bil.lookup (Bil.bind env var' result) v = Bil.lookup (Bil.bind env' var result) v := by
  simp only [Bil.substitute]
  split
  · rename_i hcapture
    generalize hfresh : Bil.freshVersion var
      ((rs.filter fun r => r.1 != var).flatMap (Bil.freeVars ·.2) ++ Bil.freeVars body) = fresh
    have hnot := Bap.Proofs.Bil.freshVersion_not_mem var
      ((rs.filter fun r => r.1 != var).flatMap (Bil.freeVars ·.2) ++ Bil.freeVars body)
    rw [hfresh] at hnot
    refine ⟨fresh, (var, .var fresh) :: rs.filter fun r => r.1 != var, rfl, ?_, ?_⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr rfl
      · exact Or.inl (List.mem_filter.1 he).1
    · intro v hv
      by_cases he : v = var
      · subst he
        simp [Assoc.get, List.lookup, evalExp, lookup_bind_same]
      · have hb : (v == var) = false := by simpa using he
        have hget : Assoc.get v ((var, Exp.var fresh) :: rs.filter fun r => r.1 != var) = Assoc.get v rs := by
          simp only [Assoc.get, List.lookup, hb]
          exact get_filter_other rs he
        rw [hget, lookup_bind_ne _ _ he]
        have hvf : v ≠ fresh := by
          rintro rfl
          exact hnot (List.mem_append_right _ ((Bap.Proofs.Bil.mem_freeVars_iff _ _).2 hv))
        have := hbody v hv he
        cases hg : Assoc.get v rs with
        | none =>
          simp only [hg] at this ⊢
          rw [lookup_bind_ne _ _ hvf]
          exact this
        | some r =>
          simp only [hg] at this ⊢
          rw [← this]
          apply Bap.Proofs.Bil.evalExp_congr_freeVars
          intro u hu
          apply lookup_bind_ne
          rintro rfl
          refine hnot (List.mem_append_left _ (List.mem_flatMap.2 ⟨(v, r), ?_, hu⟩))
          exact List.mem_filter.2 ⟨get_mem_env hg, by simpa using he⟩
  · rename_i hcapture
    refine ⟨var, rs.filter fun r => r.1 != var, rfl, fun e he => Or.inl (List.mem_filter.1 he).1, ?_⟩
    intro v hv
    by_cases he : v = var
    · subst he
      rw [show Assoc.get v (rs.filter fun r => r.1 != v) = none from get_filter_same rs v]
      simp only [lookup_bind_same]
    · rw [get_filter_other rs he]
      have := hbody v hv he
      rw [lookup_bind_ne _ _ he]
      cases hg : Assoc.get v rs with
      | none =>
        simp only [hg] at this ⊢
        rw [lookup_bind_ne _ _ he]
        exact this
      | some r =>
        simp only [hg] at this ⊢
        rw [← this]
        apply Bap.Proofs.Bil.evalExp_congr_freeVars
        intro u hu
        apply lookup_bind_ne
        rintro rfl
        exact hcapture (List.any_eq_true.2 ⟨(v, r), List.mem_filter.2 ⟨get_mem_env hg, by simpa using he⟩,
          by simp [(Bap.Proofs.Bil.mem_freeVars_iff _ _).1 hu, hv]⟩)

/-- Replacing variables by atoms changes neither the path nor whether the value comes from a store. -/
private theorem writesMemory_substitute (e : Exp) (rs : List (Var × Exp)) (env env' : Env)
    (hatom : ∀ r ∈ rs, ∀ E, writesMemory E r.2 = false)
    (hr : ∀ v, Bil.occursFree v e = true → match Assoc.get v rs with
      | some r => evalExp env r = Bil.lookup env' v
      | none => Bil.lookup env v = Bil.lookup env' v) :
    writesMemory env (Bil.substitute rs e) = writesMemory env' e := by
  induction e generalizing rs env env' with
  | var v =>
    simp only [Bil.substitute]
    cases hg : Assoc.get v rs with
    | none => rfl
    | some r =>
      simpa [writesMemory] using hatom _ (get_mem_env hg) env
  | letIn v val body _ ih₂ =>
    have hval : evalExp env (Bil.substitute rs val) = evalExp env' val :=
      Bap.Proofs.Bil.evalExp_substitute val rs env env' fun x hx => hr x (by simp [Bil.occursFree, hx])
    cases hres : evalExp env' val with
    | error m =>
      have : writesMemory env' (.letIn v val body) = false := by simp [writesMemory, hres]
      rw [this]
      simp only [Bil.substitute]
      split <;> simp [writesMemory, hval, hres]
    | ok result =>
      obtain ⟨v', rs', hsub, hmem, hrs⟩ := substitute_let_body rs v val body (env := env) (env' := env') result
        (fun x hx hne => hr x (by simp [Bil.occursFree, hx, Ne.symm hne]))
      have hw : writesMemory env' (.letIn v val body) = writesMemory (Bil.bind env' v result) body := by
        simp [writesMemory, hres]
      rw [hw, hsub]
      simp only [writesMemory, hval, hres]
      apply ih₂ rs' _ _ _ hrs
      intro r hrm E
      rcases hmem r hrm with h | h
      · exact hatom r h E
      · cases hr₂ : r.2 <;> simp_all [isVarExp, writesMemory]
  | ite c y n _ ih₂ ih₃ =>
    have hc : evalExp env (Bil.substitute rs c) = evalExp env' c :=
      Bap.Proofs.Bil.evalExp_substitute c rs env env' fun x hx => hr x (by simp [Bil.occursFree, hx])
    simp only [Bil.substitute, writesMemory, hc]
    rw [ih₂ rs env env' hatom (fun x hx => hr x (by simp [Bil.occursFree, hx])),
      ih₃ rs env env' hatom (fun x hx => hr x (by simp [Bil.occursFree, hx]))]
  | _ => rfl

private theorem eval_ite_truth {env : Env} {c y n : Exp} {value : Value} {b : Bool} (hv : evalExp env c = .ok value)
    (ht : valueTruth value = .ok b) : evalExp env (.ite c y n) = if b then evalExp env y else evalExp env n := by
  simp only [evalExp, Bind.bind, Except.bind, hv]
  simp only [valueTruth] at ht
  cases hb : Value.asBits value with
  | error m => simp [hb] at ht
  | ok bits =>
    obtain ⟨width, c'⟩ := bits
    simp only [hb] at ht ⊢
    by_cases hw : width = 1
    · subst hw
      simp only [↓reduceDIte, Except.ok.injEq] at ht ⊢
      subst ht
      by_cases h1 : c' = 1 <;> simp [h1]
    · simp [hw] at ht

/-- The value of an expression that writes memory is never a bit vector. -/
private theorem writes_not_bits {env : Env} {e : Exp} (h : writesMemory env e = true) {w : Nat} (b : BitVec w) :
    evalExp env e ≠ .ok (.bits b) := by
  induction e generalizing env with
  | store m a v en n => exact store_not_bits env m a v en n w b
  | letIn v val body _ ih₂ =>
    simp only [writesMemory] at h
    split at h
    · rename_i r hr
      intro he
      simp only [evalExp, Bind.bind, Except.bind, hr] at he
      exact ih₂ h he
    · cases h
  | ite c y n _ ih₂ ih₃ =>
    simp only [writesMemory] at h
    split at h
    · cases h
    · rename_i value hv
      cases ht : valueTruth value with
      | error m => simp [ht] at h
      | ok b =>
        simp only [ht] at h
        rw [eval_ite_truth hv ht]
        cases b with
        | true => exact ih₂ h
        | false => exact ih₃ h
  | _ => simp [writesMemory] at h

/-- Simplification keeps a write that happens. -/
private theorem writesMemory_simplify {env : Env} {e : Exp} (h : writesMemory env e = true) :
    writesMemory env (Bil.simplifyExp e) = true := by
  have hclosed : ∀ {w : Nat} (b : BitVec w), evalExp [] e ≠ .ok (.bits b) := by
    intro w b he
    exact writes_not_bits h b (Bap.Proofs.Bil.evalExp_extends (Bap.Proofs.Bil.nil_extends env) _ he)
  induction e generalizing env with
  | store m a v en n =>
    rw [Bil.simplifyExp]
    split
    · rename_i hev
      exact absurd hev (hclosed _)
    · rfl
  | letIn v val body _ ih₂ =>
    rw [Bil.simplifyExp]
    split
    · rename_i hev
      exact absurd hev (hclosed _)
    · simp only [writesMemory] at h ⊢
      split at h
      · rename_i r hr
        rw [Bap.Proofs.Bil.evalExp_simplifyExp env val hr]
        exact ih₂ h fun b he => writes_not_bits h b (Bap.Proofs.Bil.evalExp_extends (Bap.Proofs.Bil.nil_extends _) _ he)
      · cases h
  | ite c y n _ ih₂ ih₃ =>
    rw [Bil.simplifyExp]
    split
    · rename_i hev
      exact absurd hev (hclosed _)
    · simp only [writesMemory] at h
      split at h
      · cases h
      · rename_i value hv
        have hc := Bap.Proofs.Bil.evalExp_simplifyExp env c hv
        have hbranch : ∀ b, valueTruth value = .ok b → writesMemory env (if b then y else n) = true →
            writesMemory env (Bil.simplifyExp (if b then y else n)) = true := by
          intro b _ hw
          cases b with
          | true => exact ih₂ hw fun b he => writes_not_bits hw b (Bap.Proofs.Bil.evalExp_extends (Bap.Proofs.Bil.nil_extends _) _ he)
          | false => exact ih₃ hw fun b he => writes_not_bits hw b (Bap.Proofs.Bil.evalExp_extends (Bap.Proofs.Bil.nil_extends _) _ he)
        cases ht : valueTruth value with
        | error m => simp [ht] at h
        | ok b =>
          simp only [ht] at h
          have hw := hbranch b ht (by cases b <;> simpa using h)
          dsimp only
          split
          · rename_i value₁ heq
            rw [heq] at hc
            simp only [evalExp, Except.ok.injEq] at hc
            subst hc
            have hb : decide (value₁ = 1) = b := by
              simpa [valueTruth, Value.asBits] using ht
            cases b with
            | true =>
              have : value₁ = 1 := by simpa using hb
              simpa [this] using hw
            | false =>
              have : ¬ value₁ = 1#1 := by simpa using hb
              simpa [this] using hw
          · simp only [writesMemory, hc, ht]
            cases b <;> simpa using hw
  | _ => simp [writesMemory] at h

private theorem writes_propJump {c : ConstEnv} {env : Env} (hc : ConstHold env c) {e : Exp} (h : writesMemory env e = true) :
    writesMemory env (propJump c e) = true := by
  apply writesMemory_simplify
  rw [writesMemory_substitute e (constReplacements c) env env]
  · exact h
  · intro r hr E
    obtain ⟨entry, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · intro x _
    cases hg : Assoc.get x (constReplacements c) with
    | none => rfl
    | some r =>
      have hm := get_mem_env' hg
      obtain ⟨⟨k, cst⟩, hk, heq⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hc _ _ hk]
      rfl

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
      simp only at hm
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
      (r'.1, if writesMemory env (propJump c d.rhs) then (d.var, v) :: r'.2 else r'.2), ?_, ?_, hr, ?_, hout⟩
    · rw [hfold]
      simp [propJump]
    · exact execDefs_cons_ok hv' hexec
    · by_cases hs : writesMemory env d.rhs = true
      · simp only [hs, ite_true, writes_propJump hc hs]
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
    · simp only [constAt, hsolved]
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

@[simp] theorem optimize_tid (sub : Sub) (ps : List Var) : (optimize sub ps).tid = sub.tid := rfl
@[simp] theorem optimize_name (sub : Sub) (ps : List Var) : (optimize sub ps).name = sub.name := rfl
@[simp] theorem optimize_args (sub : Sub) (ps : List Var) : (optimize sub ps).args = sub.args := rfl

private theorem optimize_blks (sub : Sub) (ps : List Var) :
    (optimize sub ps).blks =
      (eliminateDeadCode (propagateConstants (Cfg.fromSub sub))
        ((propagateConstants (Cfg.fromSub sub)).protectedNames ps)).blocks := rfl

/-- `optimize` keeps exactly the reachable blocks, in order. -/
theorem optimize_tids (sub : Sub) (ps : List Var) :
    (optimize sub ps).blks.map Blk.tid = (Cfg.fromSub sub).prune.blocks.map Blk.tid := by
  rw [optimize_blks, eliminateDeadCode_tids, propagateConstants_tids]

theorem optimize_blks_reachable {sub : Sub} {ps : List Var} {blk : Blk} (h : blk ∈ (optimize sub ps).blks) :
    blk.tid ∈ (Cfg.fromSub sub).reachable := by
  have hm : blk.tid ∈ (optimize sub ps).blks.map Blk.tid := List.mem_map.2 ⟨blk, h, rfl⟩
  rw [optimize_tids] at hm
  obtain ⟨b, hb, heq⟩ := List.mem_map.1 hm
  rw [← heq]
  exact prune_blocks_reachable hb

private theorem Shrinks.pairs {ps : List Var} : {a b : List Blk} → Shrinks ps a b →
    a.map (fun b => (b.tid, b.successors)) = b.map (fun b => (b.tid, b.successors))
  | [], [], _ => rfl
  | x :: xs, y :: ys, ⟨h, t⟩ => by
    have hs : x.successors = y.successors := by simp [Blk.successors, h.2.1]
    simp [h.1, hs, Shrinks.pairs t]

/-- `optimize` leaves the control flow of reachable blocks unchanged. -/
theorem optimize_successors (sub : Sub) (ps : List Var) :
    (optimize sub ps).blks.map (fun b => (b.tid, b.successors)) =
      (Cfg.fromSub sub).prune.blocks.map fun b => (b.tid, b.successors) := by
  rw [optimize_blks]
  exact ((eliminateDeadCode_frame _ _).shrinks.pairs).trans (propagateConstants_successors _)

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
block and not read by its jumps are preserved only if they are in `ps`: at the end of the block every
protected variable has the same value in both runs. The caller lists the subroutine's outputs there. -/
theorem optimize_straight_line (tid : Tid) (name : String) (args : List Arg) (blk : Blk) (ps : List Var) {env : Env}
    {r : Env × List (Var × Value)} (h : execDefs env blk.defs = .ok r) :
    ∃ opt, (optimize ⟨tid, name, args, [blk]⟩ ps).blks = [opt] ∧ opt.tid = blk.tid ∧
      ∃ r', execDefs env opt.defs = .ok r' ∧ r.2.Sublist r'.2 ∧ Agree ps r.1 r'.1 ∧
        ∃ g, opt.jmps = blk.jmps.map (Jmp.mapExp g) ∧
          ∀ j ∈ blk.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp r.1 e = .ok v → evalExp r'.1 (g e) = .ok v := by
  let sub : Sub := ⟨tid, name, args, [blk]⟩
  let names := (propagateConstants (Cfg.fromSub sub)).protectedNames ps
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
  obtain ⟨x, hx, htid, hj, _, _, _, _, hsem⟩ :=
    eliminateDeadCode_block_spec names (propagateConstants (Cfg.fromSub sub)) (y := mid) (by rw [hblocks]; simp)
  have hlen : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub)) names).blocks.map Blk.tid = [mid.tid] := by
    rw [eliminateDeadCode_tids, hblocks]
    rfl
  have hone : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub)) names).blocks = [x] := by
    match hl : (eliminateDeadCode (propagateConstants (Cfg.fromSub sub)) names).blocks, hx, hlen with
    | [a], hx, _ =>
      rw [List.mem_singleton.1 hx]
    | [], hx, _ => simp at hx
    | _ :: _ :: _, _, hlen =>
      simp at hlen
  obtain ⟨r₂, hr₂, hag, ht⟩ := hsem env r₁ hr₁
  refine ⟨x, hone, htid, r₂, hr₂, ?_, ?_, g, ?_, ?_⟩
  · rw [ht]
    exact hsub
  · intro y hy
    rw [← heq]
    refine hag y (List.mem_append_right _ ?_)
    cases hps : ps with
    | nil => simp [hps] at hy
    | cons p rest =>
      simp only [names, Cfg.protectedNames, hps, List.mem_append]
      exact Or.inl (hps ▸ hy)
  · rw [hj]
    exact hg
  · intro j hj' e he v hv
    have hv₁ : evalExp r₁.1 (g e) = .ok v := by
      rw [heq]
      exact hgv e v hv
    rw [← hv₁]
    refine (Bap.Proofs.Bil.evalExp_congr_freeVars (g e) fun y hy => ?_).symm
    apply hag y
    refine List.mem_append_left _ ?_
    simp only [jumpVars, List.mem_flatMap]
    refine ⟨j.mapExp g, ?_, ?_⟩
    · show j.mapExp g ∈ mid.jmps
      rw [hg]
      exact List.mem_map.2 ⟨j, hj', rfl⟩
    · refine freeVars_of_jmpExps ?_ hy
      rw [jmpExps_mapExp]
      exact List.mem_map.2 ⟨e, he, rfl⟩

/-! ### Phis and jumps

A phi selects the input of the block the run came from, and all phis of a block read the environment
on entry to the block, however they are ordered. Copying an unbound variable leaves the phi's variable
unbound instead of failing: on a path where a variable was never assigned, the phi that SSA construction
adds at a join copies "undefined", as in any SSA semantics with undefined registers, and nothing has
gone wrong unless the value is then used. Any other input that fails to evaluate is a failure.

Jumps are tried in order: the first whose condition holds is taken, and a jump without a condition
always holds. -/

/-- The value a phi input gives on entry to the block, `none` when it copies an unbound variable. -/
def phiValue (env : Env) (exp : Exp) : Except String (Option Value) :=
  match evalExp env exp with
  | .ok value => .ok (some value)
  | .error message => if isVarExp exp then .ok none else .error message

/-- Assigns a phi's value, or removes a stale binding when the phi copied an undefined value. -/
def assignPhi (env : Env) (var : Var) : Option Value → Env
  | some value => Bil.bind env var value
  | none => env.filter fun binding => binding.1 != var

/-- Runs the phis of a block entered from `pred`. Every input is read from `read`, the environment on
entry, whatever the earlier phis assigned in the accumulator. A phi without an input for `pred` fails. -/
def execPhis (pred : Tid) (read : Env) : List Phi → Env → Except String Env
  | [], acc => .ok acc
  | phi :: rest, acc =>
    match Assoc.get pred phi.values with
    | none => .error "phi has no input for the predecessor"
    | some exp =>
      match phiValue read exp with
      | .error message => .error message
      | .ok value => execPhis pred read rest (assignPhi acc phi.var value)

/-- The jump a block takes in an environment: the first whose condition holds, if any. -/
def selectJmp (env : Env) : List Jmp → Except String (Option Jmp)
  | [] => .ok none
  | jmp :: rest =>
    match jmp.condition with
    | none => .ok (some jmp)
    | some condition =>
      match evalExp env condition with
      | .error message => .error message
      | .ok value =>
        match valueTruth value with
        | .error message => .error message
        | .ok true => .ok (some jmp)
        | .ok false => selectJmp env rest

private theorem lookup_error {env : Env} {v : Var} {m : String} (h : Bil.lookup env v = .error m) :
    m = s!"unbound variable {v.name}" := by
  simp only [Bil.lookup] at h
  split at h
  · cases h
  · simpa using h.symm

/-- Reading a phi's variable right after it was assigned. -/
def phiResult (v : Var) : Option Value → Except String Value
  | some value => .ok value
  | none => .error s!"unbound variable {v.name}"

private theorem lookup_assignPhi_same (env : Env) (v : Var) (r : Option Value) :
    Bil.lookup (assignPhi env v r) v = phiResult v r := by
  cases r with
  | some value => exact lookup_bind_same env v value
  | none =>
    have key : ∀ l : Env, (l.filter fun b => b.1 != v).find? (fun b => b.1 == v) = none := by
      intro l
      induction l with
      | nil => rfl
      | cons e es ih =>
        obtain ⟨a, val⟩ := e
        by_cases ha : a = v
        · subst ha
          simp [ih]
        · have hb : (a != v) = true := by simpa using ha
          have hb' : (a == v) = false := by simpa using ha
          simp only [List.filter_cons, hb, ite_true, List.find?_cons, hb', ih]
    simp only [Bil.lookup, assignPhi, key, phiResult]

private theorem lookup_assignPhi_ne (env : Env) {v x : Var} (r : Option Value) (h : x ≠ v) :
    Bil.lookup (assignPhi env v r) x = Bil.lookup env x := by
  cases r with
  | some value => exact lookup_bind_ne env value h
  | none =>
    have key : ∀ l : Env, (l.filter fun b => b.1 != v).find? (fun b => b.1 == x) = l.find? fun b => b.1 == x := by
      intro l
      induction l with
      | nil => rfl
      | cons e es ih =>
        obtain ⟨a, val⟩ := e
        by_cases ha : a = v
        · subst ha
          have hv : (a == x) = false := by simpa using Ne.symm h
          simp [hv, ih]
        · have hb : (a != v) = true := by simpa using ha
          simp only [List.filter_cons, hb, ite_true, List.find?_cons, ih]
    simp only [Bil.lookup, assignPhi, key]

private theorem phiResult_of_lookup {env : Env} {w : Var} (v : Var) (hn : v.name = w.name) :
    phiResult v (match Bil.lookup env w with
      | .ok value => some value
      | .error _ => none) = Bil.lookup env w := by
  cases h : Bil.lookup env w with
  | ok value => rfl
  | error m =>
    have := lookup_error h
    simp only [phiResult, this, hn]

private theorem phiValue_var (env : Env) (w : Var) :
    phiValue env (.var w) = .ok (match Bil.lookup env w with
      | .ok value => some value
      | .error _ => none) := by
  simp only [phiValue, evalExp, isVarExp]
  cases Bil.lookup env w <;> rfl

private theorem phiValue_of_eval {env : Env} {e : Exp} {v : Value} (h : evalExp env e = .ok v) :
    phiValue env e = .ok (some v) := by
  simp only [phiValue, h]

private theorem phiValue_congr {env env' : Env} {e e' : Exp} (h : evalExp env e = evalExp env' e')
    (hv : isVarExp e = isVarExp e') : phiValue env e = phiValue env' e' := by
  simp only [phiValue, h, hv]

private theorem phiValue_agree {env env' : Env} (e : Exp)
    (h : ∀ x ∈ Bil.freeVars e, Bil.lookup env x = Bil.lookup env' x) : phiValue env e = phiValue env' e :=
  phiValue_congr (Bap.Proofs.Bil.evalExp_congr_freeVars e h) rfl

private theorem simplify_var (w : Var) : Bil.simplifyExp (.var w) = .var w := by
  rw [Bil.simplifyExp]
  rfl

private theorem phiValue_simplify {env : Env} {e : Exp} {r : Option Value} (h : phiValue env e = .ok r) :
    phiValue env (Bil.simplifyExp e) = .ok r := by
  cases he : evalExp env e with
  | ok v =>
    simp only [phiValue, he, Except.ok.injEq] at h
    subst h
    exact phiValue_of_eval (Bap.Proofs.Bil.evalExp_simplifyExp env e he)
  | error m =>
    cases e with
    | var w => rwa [simplify_var]
    | _ => simp [phiValue, he, isVarExp] at h

/-- Phi inputs are read from the entry environment: a later phi of the block never sees what an
earlier one assigned, so the phis of a block read simultaneously and their order only matters when two
assign the same variable. -/
theorem execPhis_cons_reads_entry (pred : Tid) (read acc : Env) (phi : Phi) (rest : List Phi) (exp : Exp)
    (value : Option Value) (hget : Assoc.get pred phi.values = some exp) (hv : phiValue read exp = .ok value) :
    execPhis pred read (phi :: rest) acc = execPhis pred read rest (assignPhi acc phi.var value) := by
  simp only [execPhis, hget, hv]

/-- Phis with distinct variables can be listed in either order: they read simultaneously. -/
theorem execPhis_swap {pred : Tid} {read acc r : Env} {a b : Phi} {rest : List Phi} (hne : a.var ≠ b.var)
    (h : execPhis pred read (a :: b :: rest) acc = .ok r) :
    ∃ r', execPhis pred read (b :: a :: rest) acc = .ok r' ∧ ∀ x, Bil.lookup r' x = Bil.lookup r x := by
  have hcongr : ∀ (phis : List Phi) {acc₁ acc₂ r₁ : Env}, (∀ x, Bil.lookup acc₂ x = Bil.lookup acc₁ x) →
      execPhis pred read phis acc₁ = .ok r₁ →
      ∃ r₂, execPhis pred read phis acc₂ = .ok r₂ ∧ ∀ x, Bil.lookup r₂ x = Bil.lookup r₁ x := by
    intro phis
    induction phis with
    | nil =>
      intro acc₁ acc₂ r₁ hl hr
      simp only [execPhis, Except.ok.injEq] at hr
      subst hr
      exact ⟨acc₂, rfl, hl⟩
    | cons p ps ih =>
      intro acc₁ acc₂ r₁ hl hr
      simp only [execPhis] at hr ⊢
      cases he : Assoc.get pred p.values with
      | none => simp [he] at hr
      | some e =>
        simp only [he] at hr ⊢
        cases hv : phiValue read e with
        | error m => simp [hv] at hr
        | ok v =>
          simp only [hv] at hr ⊢
          refine ih ?_ hr
          intro x
          by_cases hx : x = p.var
          · subst hx
            rw [lookup_assignPhi_same, lookup_assignPhi_same]
          · rw [lookup_assignPhi_ne _ _ hx, lookup_assignPhi_ne _ _ hx]
            exact hl x
  simp only [execPhis] at h ⊢
  cases ha : Assoc.get pred a.values with
  | none => simp [ha] at h
  | some ea =>
    simp only [ha] at h
    cases hva : phiValue read ea with
    | error m => simp [hva] at h
    | ok va =>
      simp only [hva] at h
      cases hb : Assoc.get pred b.values with
      | none => simp [hb] at h
      | some eb =>
        simp only [hb] at h ⊢
        cases hvb : phiValue read eb with
        | error m => simp [hvb] at h
        | ok vb =>
          simp only [hvb, hva] at h ⊢
          refine hcongr rest ?_ h
          intro x
          by_cases hxa : x = a.var
          · subst hxa
            rw [lookup_assignPhi_same, lookup_assignPhi_ne _ _ hne, lookup_assignPhi_same]
          · by_cases hxb : x = b.var
            · subst hxb
              rw [lookup_assignPhi_ne _ _ hxa, lookup_assignPhi_same, lookup_assignPhi_same]
            · rw [lookup_assignPhi_ne _ _ hxa, lookup_assignPhi_ne _ _ hxb, lookup_assignPhi_ne _ _ hxb,
                lookup_assignPhi_ne _ _ hxa]

/-- A variable no phi assigns keeps its value across the phis. -/
theorem lookup_execPhis_other {pred : Tid} {read : Env} {phis : List Phi} {acc r : Env}
    (h : execPhis pred read phis acc = .ok r) {x : Var} (hx : ∀ phi ∈ phis, phi.var ≠ x) :
    Bil.lookup r x = Bil.lookup acc x := by
  induction phis generalizing acc with
  | nil =>
    simp only [execPhis, Except.ok.injEq] at h
    rw [h]
  | cons p ps ih =>
    simp only [execPhis] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [ih h fun phi hphi => hx phi (List.mem_cons_of_mem _ hphi)]
        exact lookup_assignPhi_ne _ _ (Ne.symm (hx p (by simp)))

private theorem get_map_snd {α : Type} [DecidableEq α] (f : Exp → Exp) (k : α) (l : List (α × Exp)) :
    Assoc.get k (l.map fun input => (input.1, f input.2)) = (Assoc.get k l).map f := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      simp [Assoc.get]
    · have hb : (k == a) = false := by simpa using hk
      have ih' : List.lookup k (es.map fun input => (input.1, f input.2)) = (List.lookup k es).map f := ih
      simp [Assoc.get, List.lookup, hb, ih']

/-- Simplifying the inputs of phis does not change what they assign. -/
private theorem execPhis_simplify {pred : Tid} {read : Env} {phis : List Phi} {acc r : Env}
    (h : execPhis pred read phis acc = .ok r) :
    execPhis pred read (phis.map fun phi =>
      { phi with values := phi.values.map fun input => (input.1, Bil.simplifyExp input.2) }) acc = .ok r := by
  induction phis generalizing acc with
  | nil => exact h
  | cons p ps ih =>
    simp only [execPhis] at h
    split at h
    · cases h
    · rename_i exp hexp
      split at h
      · cases h
      · rename_i value hval
        simp only [List.map_cons, execPhis, get_map_snd, hexp, Option.map_some, phiValue_simplify hval]
        exact ih h

/-- Runs on two environments and input lists that agree give equal results for kept phis; removed phis
assign only variables that are not live. -/
private theorem execPhis_filter (pred : Tid) (keep : Var → Bool) {live : List Var}
    (hlive : ∀ x ∈ live, keep x = true) {read read' : Env} {phis : List Phi}
    (hread : ∀ phi ∈ phis, ∀ e, Assoc.get pred phi.values = some e →
      ∀ x ∈ Bil.freeVars e, Bil.lookup read x = Bil.lookup read' x)
    {acc acc' r : Env} (hacc : ∀ x ∈ live, (∀ phi ∈ phis, phi.var ≠ x) → Bil.lookup acc x = Bil.lookup acc' x)
    (h : execPhis pred read phis acc = .ok r) :
    ∃ r', execPhis pred read' (phis.filter fun phi => keep phi.var) acc' = .ok r' ∧
      ∀ x ∈ live, Bil.lookup r x = Bil.lookup r' x := by
  induction phis generalizing acc acc' with
  | nil =>
    simp only [execPhis, Except.ok.injEq] at h
    subst h
    exact ⟨acc', rfl, fun x hx => hacc x hx (by simp)⟩
  | cons p ps ih =>
    simp only [execPhis] at h
    split at h
    · cases h
    · rename_i exp hexp
      split at h
      · cases h
      · rename_i value hval
        have hrest := fun phi (hphi : phi ∈ ps) => hread phi (List.mem_cons_of_mem _ hphi)
        by_cases hk : keep p.var = true
        · have hval' : phiValue read' exp = .ok value := by
            rw [← phiValue_agree exp (hread p (by simp) exp hexp)]
            exact hval
          have hacc' : ∀ x ∈ live, (∀ phi ∈ ps, phi.var ≠ x) →
              Bil.lookup (assignPhi acc p.var value) x = Bil.lookup (assignPhi acc' p.var value) x := by
            intro x hx hn
            by_cases hxp : x = p.var
            · subst hxp
              rw [lookup_assignPhi_same, lookup_assignPhi_same]
            · rw [lookup_assignPhi_ne _ _ hxp, lookup_assignPhi_ne _ _ hxp]
              refine hacc x hx ?_
              intro phi hphi
              rcases List.mem_cons.1 hphi with rfl | hphi
              · exact Ne.symm hxp
              · exact hn phi hphi
          obtain ⟨r', hr', ha⟩ := ih hrest hacc' h
          refine ⟨r', ?_, ha⟩
          simp only [List.filter_cons, hk, ite_true, execPhis, hexp, hval']
          exact hr'
        · have hacc' : ∀ x ∈ live, (∀ phi ∈ ps, phi.var ≠ x) →
              Bil.lookup (assignPhi acc p.var value) x = Bil.lookup acc' x := by
            intro x hx hn
            have hxp : x ≠ p.var := by
              rintro rfl
              exact hk (hlive _ hx)
            rw [lookup_assignPhi_ne _ _ hxp]
            refine hacc x hx ?_
            intro phi hphi
            rcases List.mem_cons.1 hphi with rfl | hphi
            · exact Ne.symm hxp
            · exact hn phi hphi
          obtain ⟨r', hr', ha⟩ := ih hrest hacc' h
          refine ⟨r', ?_, ha⟩
          simp only [List.filter_cons, hk, Bool.false_eq_true, ite_false]
          exact hr'

/-- The selected jump is one of the block's jumps. -/
theorem selectJmp_mem {env : Env} {jmps : List Jmp} {j : Jmp} (h : selectJmp env jmps = .ok (some j)) : j ∈ jmps := by
  induction jmps with
  | nil => simp [selectJmp] at h
  | cons a as ih =>
    simp only [selectJmp] at h
    split at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      simp
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Option.some.injEq] at h
          subst h
          simp
        · exact List.mem_cons_of_mem _ (ih h)

/-- Rewriting jump expressions in a way that keeps the values of the original's conditions selects the
rewrite of the same jump, at the same position, and finds no jump exactly when the original does. -/
theorem selectJmp_mapExp {env env' : Env} {g : Exp → Exp} {jmps : List Jmp} {o : Option Jmp}
    (hg : ∀ j ∈ jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp env e = .ok v → evalExp env' (g e) = .ok v)
    (h : selectJmp env jmps = .ok o) :
    selectJmp env' (jmps.map (Jmp.mapExp g)) = .ok (o.map (Jmp.mapExp g)) := by
  induction jmps with
  | nil =>
    simp only [selectJmp, Except.ok.injEq] at h
    subst h
    rfl
  | cons a as ih =>
    obtain ⟨atid, acond, akind⟩ := a
    cases acond with
    | none =>
      simp only [selectJmp, Except.ok.injEq] at h
      subst h
      rfl
    | some c =>
      simp only [selectJmp] at h
      have hc : c ∈ jmpExps ⟨atid, some c, akind⟩ := by simp [jmpExps]
      split at h
      · cases h
      · rename_i value hval
        have hval' := hg _ (by simp) c hc value hval
        have hrest := ih (fun j hj => hg j (List.mem_cons_of_mem _ hj))
        show selectJmp env' (Jmp.mapExp g ⟨atid, some c, akind⟩ :: as.map (Jmp.mapExp g)) = _
        simp only [selectJmp, Jmp.mapExp, Option.map_some, hval']
        cases hvt : valueTruth value with
        | error m => simp [hvt] at h
        | ok b =>
          cases b with
          | true =>
            simp only [hvt, Except.ok.injEq] at h
            subst h
            rfl
          | false =>
            simp only [hvt] at h
            exact hrest h

/-- A failing choice of jump fails under an evaluation-preserving rewrite too. -/
theorem selectJmp_mapExp_error {env env' : Env} {g : Exp → Exp} {jmps : List Jmp} {m : String}
    (hg : ∀ j ∈ jmps, ∀ e ∈ jmpExps j, evalExp env' (g e) = evalExp env e) (h : selectJmp env jmps = .error m) :
    selectJmp env' (jmps.map (Jmp.mapExp g)) = .error m := by
  induction jmps with
  | nil => simp [selectJmp] at h
  | cons a as ih =>
    obtain ⟨atid, acond, akind⟩ := a
    cases acond with
    | none => simp [selectJmp] at h
    | some c =>
      simp only [selectJmp] at h
      have hc : c ∈ jmpExps ⟨atid, some c, akind⟩ := by simp [jmpExps]
      show selectJmp env' (Jmp.mapExp g ⟨atid, some c, akind⟩ :: as.map (Jmp.mapExp g)) = _
      simp only [selectJmp, Jmp.mapExp, Option.map_some]
      rw [hg _ (by simp) c hc]
      cases hval : evalExp env c with
      | error m' =>
        simp only [hval] at h ⊢
        exact h
      | ok value =>
        simp only [hval] at h ⊢
        cases hvt : valueTruth value with
        | error m' =>
          simp only [hvt] at h ⊢
          exact h
        | ok b =>
          cases b with
          | true => simp [hvt] at h
          | false =>
            simp only [hvt] at h ⊢
            exact ih (fun j hj => hg j (List.mem_cons_of_mem _ hj)) h

/-- Agreeing on what the jumps read selects the same jump. -/
theorem selectJmp_agree {env env' : Env} {jmps : List Jmp} {o : Option Jmp}
    (ha : ∀ j ∈ jmps, ∀ x ∈ j.freeVars, Bil.lookup env x = Bil.lookup env' x)
    (h : selectJmp env jmps = .ok o) : selectJmp env' jmps = .ok o := by
  have := selectJmp_mapExp (env' := env') (g := id) (jmps := jmps) (fun j hj e he v hv => by
    rw [id, ← hv]
    exact (Bap.Proofs.Bil.evalExp_congr_freeVars e fun x hx => ha j hj x (freeVars_of_jmpExps he hx)).symm) h
  simpa [Function.comp_def, show Jmp.mapExp id = id from funext Jmp.mapExp_id] using this

/-! ### Semantic preservation along control-flow paths

`Run cfg pred t env path stores final last` is an execution of block `t` entered from `pred`, the
previous block (`pseudoStart` for the entry): the block's phis run, then its definitions, and either
the run ends or the jump the conditions select takes it to its target. The path is every block visited.
The run may end after any block, so runs also cover prefixes of non-terminating executions. A jump with
no static target leaves the subroutine and so ends the run. A call continues at its return block with
the environment unchanged: callees are not modelled, here or in the liveness analysis. -/

inductive Run (cfg : Cfg) : Tid → Tid → Env → List Tid → List (Var × Value) → Env → Blk → Prop where
  | last {pred t env env₁ r blk} : cfg.block t = some blk → execPhis pred env blk.phis env = .ok env₁ →
    execDefs env₁ blk.defs = .ok r → Run cfg pred t env [t] r.2 r.1 blk
  | next {pred t t' env env₁ r blk j path stores final lastBlk} : cfg.block t = some blk →
    execPhis pred env blk.phis env = .ok env₁ → execDefs env₁ blk.defs = .ok r →
    selectJmp r.1 blk.jmps = .ok (some j) → t' ∈ j.successors → t' ∈ cfg.successors t →
    Run cfg t t' r.1 path stores final lastBlk → Run cfg pred t env (t :: path) (r.2 ++ stores) final lastBlk

private theorem Run.block {cfg : Cfg} {pred t : Tid} {env final : Env} {path : List Tid} {tr : List (Var × Value)}
    {f : Blk} (h : Run cfg pred t env path tr final f) : ∃ b, cfg.block t = some b := by
  cases h <;> exact ⟨_, ‹_›⟩

private theorem Run.path_ne_nil {cfg : Cfg} {pred t : Tid} {env final : Env} {path : List Tid}
    {tr : List (Var × Value)} {f : Blk} (h : Run cfg pred t env path tr final f) : path ≠ [] := by
  cases h <;> simp

/-- In a CFG built from a subroutine, the target of a selected jump is always an edge: the graph side
condition of `Run.next` restricts nothing. -/
theorem fromSub_jump_edge {sub : Sub} {t t' : Tid} {blk : Blk} {j : Jmp}
    (hb : (Cfg.fromSub sub).block t = some blk) (hj : j ∈ blk.jmps) (ht : t' ∈ j.successors) :
    t' ∈ (Cfg.fromSub sub).successors t :=
  (fromSub_successors sub t t').2
    ⟨blk, (block_some hb).1, (block_some hb).2, (mem_blk_successors blk t').2 ⟨j, hj, ht⟩⟩

/-- A jump has at most one static target. -/
theorem Jmp.successors_subsingleton (j : Jmp) {a b : Tid} (ha : a ∈ j.successors) (hb : b ∈ j.successors) : a = b := by
  obtain ⟨tid, condition, kind⟩ := j
  cases kind with
  | goto target => cases target <;> simp_all [Jmp.successors, Label.directTarget]
  | ret target => cases target <;> simp_all [Jmp.successors, Label.directTarget]
  | call target returnTo =>
    cases returnTo with
    | none => simp [Jmp.successors] at ha
    | some l => cases l <;> simp_all [Jmp.successors, Label.directTarget]
  | interrupt n r => simp_all [Jmp.successors]

/-- Branch conditions decide the path: two runs from the same state visit the same blocks for as long as
both go on, and one that visits the same blocks as the other ends in the same state with the same stores. -/
theorem Run.deterministic {cfg : Cfg} {pred t : Tid} {env final final' : Env} {p p' : List Tid}
    {tr tr' : List (Var × Value)} {f f' : Blk} (h : Run cfg pred t env p tr final f)
    (h' : Run cfg pred t env p' tr' final' f') :
    (p <+: p' ∨ p' <+: p) ∧ (p = p' → tr = tr' ∧ final = final' ∧ f = f') := by
  induction h generalizing p' tr' final' f' with
  | @last pred t env env₁ r blk hb hp hd =>
    cases h' with
    | @last _ _ _ env₂ r₂ _ hb₂ hp₂ hd₂ =>
      rw [hb] at hb₂
      cases hb₂
      rw [hp] at hp₂
      cases hp₂
      rw [hd] at hd₂
      cases hd₂
      exact ⟨Or.inl (List.prefix_refl _), fun _ => ⟨rfl, rfl, rfl⟩⟩
    | @next _ _ _ _ _ _ _ _ path _ _ _ _ _ _ _ _ _ hrest =>
      refine ⟨Or.inl ⟨path, rfl⟩, fun heq => ?_⟩
      simp only [List.cons.injEq] at heq
      exact absurd heq.2.symm hrest.path_ne_nil
  | @next pred t t₁ env env₁ r blk j path stores final lastBlk hb hp hd hs ht he hrest ih =>
    cases h' with
    | last hb₂ _ _ =>
      refine ⟨Or.inr ⟨path, rfl⟩, fun heq => ?_⟩
      simp only [List.cons.injEq] at heq
      exact absurd heq.2 hrest.path_ne_nil
    | @next _ _ t₂ _ env₂ r₂ blk₂ j₂ path₂ stores₂ final₂ last₂ hb₂ hp₂ hd₂ hs₂ ht₂ _ hrest₂ =>
      rw [hb] at hb₂
      cases hb₂
      rw [hp] at hp₂
      cases hp₂
      rw [hd] at hd₂
      cases hd₂
      rw [hs] at hs₂
      cases hs₂
      have := Jmp.successors_subsingleton j ht ht₂
      subst this
      obtain ⟨h₁, h₂⟩ := ih hrest₂
      refine ⟨?_, fun heq => ?_⟩
      · rcases h₁ with h₁ | h₁
        · exact Or.inl ((List.prefix_cons_inj _).2 h₁)
        · exact Or.inr ((List.prefix_cons_inj _).2 h₁)
      · simp only [List.cons.injEq, true_and] at heq
        obtain ⟨a, b, c⟩ := h₂ heq
        exact ⟨by rw [a], b, c⟩

private theorem find_map_tid (l : List Blk) (f : Blk → Blk) (hf : ∀ b, (f b).tid = b.tid) (t : Tid) :
    (l.map f).find? (fun b => decide (b.tid = t)) = (l.find? fun b => decide (b.tid = t)).map f := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.find?_cons, hf]
    split
    · rfl
    · exact ih

private theorem dceBlk_tid (ps : List Var) (cfg : Cfg) (b : Blk) : (dceBlk ps cfg b).tid = b.tid := rfl

private theorem dcePass_block (ps : List Var) (cfg : Cfg) {t : Tid} {b : Blk} (h : cfg.block t = some b) :
    (dcePass ps cfg).block t = some (dceBlk ps cfg b) := by
  show (cfg.blocks.map (dceBlk ps cfg)).find? _ = _
  rw [find_map_tid _ _ (dceBlk_tid ps cfg)]
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

/-- Blocks of the CFG are nodes of its graph. -/
private abbrev BlocksAreNodes (cfg : Cfg) : Prop := ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes

private theorem BlocksAreNodes.pass {ps : List Var} {cfg : Cfg} (h : BlocksAreNodes cfg) :
    BlocksAreNodes (dcePass ps cfg) := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
  exact h c hc

/-- What the block needs on entry from `pred`: the live-in set, the inputs selected for this edge and
the protected variables. -/
private def EntryNeeds (ps : List Var) (cfg : Cfg) (pred t : Tid) (blk : Blk) (x : Var) : Prop :=
  x ∈ (Assoc.get t cfg.liveness.1).getD [] ∨ x ∈ ps ∨
    ∃ phi ∈ blk.phis, ∃ e, Assoc.get pred phi.values = some e ∧ x ∈ Bil.freeVars e

private theorem dce_step {ps : List Var} {cfg : Cfg} {pred t : Tid} {env env' env₁ : Env} (ht : t ∈ cfg.reachable)
    {b : Blk} (hb : cfg.block t = some b)
    (hag : ∀ x, EntryNeeds ps cfg pred t b x → Bil.lookup env x = Bil.lookup env' x)
    (hp : execPhis pred env b.phis env = .ok env₁) {r : Env × List (Var × Value)}
    (hr : execDefs env₁ b.defs = .ok r) :
    ∃ env₁' r', execPhis pred env' (dceBlk ps cfg b).phis env' = .ok env₁' ∧
      execDefs env₁' (dceBlk ps cfg b).defs = .ok r' ∧ Agree (dceLive ps cfg b) r.1 r'.1 ∧ r'.2 = r.2 := by
  have htid : b.tid = t := (block_some hb).2
  have hneeds : ∀ x ∈ (dceDefs b.defs (dceLive ps cfg b)).2, (∀ phi ∈ b.phis, phi.var ≠ x) →
      Bil.lookup env x = Bil.lookup env' x := by
    intro x hx hnp
    apply hag x
    rcases dceDefs_live_subset _ _ _ hx with he | ⟨hl, hall⟩
    · exact Or.inl ((liveness_equations cfg ht hb x).1.2 ((mem_blockIn _ _ _).2 ⟨hnp, Or.inl he⟩))
    · rcases List.mem_append.1 hl with hl | hp
      · refine Or.inl ((liveness_equations cfg ht hb x).1.2 ((mem_blockIn _ _ _).2 ⟨hnp, Or.inr ⟨?_, hall⟩⟩))
        rcases List.mem_append.1 hl with ho | hj
        · rw [htid] at ho
          exact Or.inr ((liveness_equations cfg ht hb x).2.1 ho)
        · exact Or.inl (List.mem_flatMap.1 hj)
      · exact Or.inr (Or.inl hp)
  obtain ⟨env₁', hp', ha⟩ := execPhis_filter pred (fun v => (dceDefs b.defs (dceLive ps cfg b)).2.contains v)
    (live := (dceDefs b.defs (dceLive ps cfg b)).2) (fun x hx => by simpa using hx)
    (read := env) (read' := env') (phis := b.phis)
    (fun phi hphi e hget x hx => hag x (Or.inr (Or.inr ⟨phi, hphi, e, hget, hx⟩)))
    hneeds hp
  refine ⟨env₁', ?_⟩
  obtain ⟨r', hr', hl, ht'⟩ := dceDefs_simulation b.defs (dceLive ps cfg b) (env := env₁) (env' := env₁') ha hr
  exact ⟨r', hp', hr', hl, ht'⟩

/-- One dead-code pass simulates every run from an environment agreeing on what the block needs, and
ends agreeing on the final jumps' reads and the protected variables. -/
private theorem dcePass_run {ps : List Var} {cfg : Cfg} (hwf : BlocksAreNodes cfg) {pred t : Tid} {env final : Env}
    {path : List Tid} {tr : List (Var × Value)} {f : Blk} (h : Run cfg pred t env path tr final f)
    (ht : t ∈ cfg.reachable) {env' : Env}
    (hag : ∀ b, cfg.block t = some b → ∀ x, EntryNeeds ps cfg pred t b x → Bil.lookup env x = Bil.lookup env' x) :
    ∃ final' f', Run (dcePass ps cfg) pred t env' path tr final' f' ∧ f'.tid = f.tid ∧ f'.jmps = f.jmps ∧
      Agree (jumpVars f ++ ps) final final' := by
  induction h generalizing env' with
  | @last pred t env env₁ r blk hb hp hr =>
    obtain ⟨env₁', r', hp', hr', hl, ht'⟩ := dce_step ht hb (hag blk hb) hp hr
    refine ⟨r'.1, dceBlk ps cfg blk, ?_, rfl, rfl, dceLive_agree hl⟩
    rw [← ht']
    exact .last (dcePass_block ps cfg hb) hp' hr'
  | @next pred t t' env env₁ r blk j path stores final lastBlk hb hp hr hs hj hsucc hrest ih =>
    obtain ⟨env₁', r', hp', hr', hl, ht'⟩ := dce_step ht hb (hag blk hb) hp hr
    obtain ⟨b', hb'⟩ := hrest.block
    have hedge : (t, t') ∈ cfg.graph.edges := (Bap.Graph.successors_mem cfg.graph t t').1 hsucc
    have ht'' : t' ∈ cfg.reachable :=
      Bap.Proofs.Graph.reachableFrom_closed cfg.graph _ ht hedge
        ((block_some hb').2 ▸ hwf b' (block_some hb').1)
    have hag' : ∀ b, cfg.block t' = some b → ∀ x, EntryNeeds ps cfg t t' b x → Bil.lookup r.1 x = Bil.lookup r'.1 x := by
      intro b hb₂ x hx
      rw [hb'] at hb₂
      cases hb₂
      have hout : ∀ {y}, LiveEdge cfg cfg.liveness.1 t t' y → y ∈ dceLive ps cfg blk := by
        intro y hy
        refine List.mem_append_left _ (List.mem_append_left _ ?_)
        rw [(block_some hb).2]
        exact (liveness_equations cfg ht hb y).2.2 ((mem_blockOut _ _ _ _).2 ⟨t', hsucc, hy⟩)
      apply hl x
      rcases hx with hx | hx | ⟨phi, hphi, e, hget, hfv⟩
      · refine hout ⟨b', hb', Or.inl ⟨hx, ?_⟩⟩
        exact ((liveness_equations cfg ht'' hb' x).1.1 hx |> (mem_blockIn _ _ _).1).1
      · exact List.mem_append_right _ hx
      · exact hout ⟨b', hb', Or.inr ⟨phi, hphi, e, hget, hfv⟩⟩
    obtain ⟨final', f', hrun, hft, hfj, hfa⟩ := ih ht'' hag'
    refine ⟨final', f', ?_, hft, hfj, hfa⟩
    rw [← ht']
    have hsel : selectJmp r'.1 blk.jmps = .ok (some j) := by
      refine selectJmp_agree (fun a ha x hx => hl x ?_) hs
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, hx⟩))
    exact .next (dcePass_block ps cfg hb) hp' hr' hsel hj hsucc hrun

private theorem dceAux_run {ps : List Var} {cfg : Cfg} (fuel : Nat) (hwf : BlocksAreNodes cfg) {pred t : Tid}
    {env final : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk} (h : Run cfg pred t env path tr final f)
    (ht : t ∈ cfg.reachable) :
    ∃ final' f', Run (dceAux ps cfg fuel) pred t env path tr final' f' ∧ f'.tid = f.tid ∧ f'.jmps = f.jmps ∧
      Agree (jumpVars f ++ ps) final final' := by
  induction fuel generalizing cfg final f with
  | zero => exact ⟨final, f, h, rfl, rfl, fun _ _ => rfl⟩
  | succ fuel ih =>
    rw [dceAux_succ]
    split
    · exact ⟨final, f, h, rfl, rfl, fun _ _ => rfl⟩
    · obtain ⟨e₁, f₁, h₁, ht₁, hj₁, ha₁⟩ := dcePass_run hwf h ht (env' := env) (fun _ _ _ _ => rfl)
      obtain ⟨e₂, f₂, h₂, ht₂, hj₂, ha₂⟩ := ih hwf.pass h₁ ht
      refine ⟨e₂, f₂, h₂, ht₂.trans ht₁, hj₂.trans hj₁, fun x hx => ?_⟩
      rw [ha₁ x hx]
      exact ha₂ x (by simp only [jumpVars, hj₁] at hx ⊢; exact hx)

/-- Runs of a CFG stay in its pruned version when they start from a reachable block. -/
private theorem run_prune {cfg : Cfg} (hnodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes) {pred t : Tid}
    {env final : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk} (h : Run cfg pred t env path tr final f)
    (ht : t ∈ cfg.reachable) : Run cfg.prune pred t env path tr final f := by
  have hblock : ∀ {z : Tid} {b : Blk}, z ∈ cfg.reachable → cfg.block z = some b → cfg.prune.block z = some b := by
    intro z b hz hb
    rw [prune_block]
    simp [hz, hb]
  induction h with
  | last hb hp hr => exact .last (hblock ht hb) hp hr
  | @next pred t t' env env₁ r blk j path stores final lastBlk hb hp hr hs hj hsucc hrest ih =>
    obtain ⟨b', hb'⟩ := hrest.block
    have hedge : (t, t') ∈ cfg.graph.edges := (Bap.Graph.successors_mem cfg.graph t t').1 hsucc
    have ht'' : t' ∈ cfg.reachable :=
      Bap.Proofs.Graph.reachableFrom_closed cfg.graph _ ht hedge
        ((block_some hb').2 ▸ hnodes b' (block_some hb').1)
    refine .next (hblock ht hb) hp hr hs hj ?_ (ih ht'')
    exact (Bap.Graph.successors_mem _ t t').2 (mem_prune_edges.2 ⟨hedge, ht, ht''⟩)

private theorem propagateConstants_block (cfg : Cfg) {t : Tid} {b : Blk} (h : cfg.prune.block t = some b) :
    (propagateConstants cfg).block t = some (propagateBlock b (constAt cfg b.tid)).1 := by
  show (cfg.prune.blocks.map _).find? _ = _
  rw [find_map_tid _ _ (fun b => propagateBlock_tid b _)]
  have h' : cfg.prune.blocks.find? (fun b => decide (b.tid = t)) = some b := h
  rw [h']
  rfl

private theorem propagateBlock_phis (blk : Blk) (env : ConstEnv) :
    (propagateBlock blk env).1.phis = blk.phis.map fun phi =>
      { phi with values := phi.values.map fun input => (input.1, Bil.simplifyExp input.2) } := by
  rw [propagateBlock_eq]

/-- Constant propagation simulates every run of the pruned CFG. -/
private theorem propagateConstants_run (cfg : Cfg) {pred t : Tid} {env final : Env} {path : List Tid}
    {tr : List (Var × Value)} {f : Blk} (h : Run cfg.prune pred t env path tr final f)
    (hrun : ∀ blk env₁, cfg.prune.block t = some blk → execPhis pred env blk.phis env = .ok env₁ →
      PropRun cfg.prune t env₁) :
    ∃ tr' f', Run (propagateConstants cfg) pred t env path tr' final f' ∧ tr.Sublist tr' ∧ f'.tid = f.tid ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧ ∀ e v, evalExp final e = .ok v → evalExp final (g e) = .ok v := by
  have hconst : ∀ {z : Tid} {e : Env} {b : Blk}, PropRun cfg.prune z e → cfg.prune.block z = some b →
      ConstHold e (propEntry b (constAt cfg b.tid)) := by
    intro z e b hz hb
    have htid := (block_some hb).2
    by_cases hsolved : isSolved cfg.prune (solution cfg) = true
    · simp only [constAt, hsolved, ↓reduceIte, htid]
      exact fixpoint_constants_hold hsolved hz hb
    · simp only [constAt, hsolved]
      intro k c hm
      simp at hm
  induction h with
  | @last pred t env env₁ r blk hb hp hr =>
    obtain ⟨r', hr', heq, hsub, _, g, hg, hgv⟩ := propagateBlock_sim (hconst (hrun blk env₁ hb hp) hb) hr
    refine ⟨r'.2, (propagateBlock blk (constAt cfg blk.tid)).1, ?_, hsub, rfl, g, hg, hgv⟩
    rw [← heq]
    refine .last (propagateConstants_block cfg hb) ?_ hr'
    rw [propagateBlock_phis]
    exact execPhis_simplify hp
  | @next pred t t' env env₁ r blk j path stores final lastBlk hb hp hr hs hj hsucc hrest ih =>
    have hrun₁ := hrun blk env₁ hb hp
    obtain ⟨r', hr', heq, hsub, _, g₁, hg₁, hgv₁⟩ := propagateBlock_sim (hconst hrun₁ hb) hr
    have hnext : ∀ b' env₂, cfg.prune.block t' = some b' → execPhis t r.1 b'.phis r.1 = .ok env₂ →
        PropRun cfg.prune t' env₂ := fun b' env₂ hb' hp₂ =>
      .step hrun₁ hb hr hsucc hb' (fun _ hx => lookup_execPhis_other hp₂ hx)
    obtain ⟨tr', f', hrun', hsub', hft, hg⟩ := ih hnext
    refine ⟨r'.2 ++ tr', f', ?_, hsub.append hsub', hft, hg⟩
    refine .next (j := j.mapExp g₁) (propagateConstants_block cfg hb) ?_ hr' ?_ ?_ hsucc ?_
    · rw [propagateBlock_phis]
      exact execPhis_simplify hp
    · rw [heq, hg₁]
      exact selectJmp_mapExp (fun _ _ e _ v hv => hgv₁ e v hv) hs
    · rw [Jmp.successors_mapExp]
      exact hj
    · rw [heq]
      exact hrun'

/-- A run of a CFG whose blocks are the subroutine's is a run of the CFG rebuilt from them. -/
private theorem run_fromSub_of_blocks {cfg : Cfg} {sub : Sub} (hblocks : cfg.blocks = sub.blks) {pred t : Tid}
    {env final : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk} (h : Run cfg pred t env path tr final f) :
    Run (Cfg.fromSub sub) pred t env path tr final f := by
  have hblock : ∀ {z : Tid} {b : Blk}, cfg.block z = some b → (Cfg.fromSub sub).block z = some b := by
    intro z b hb
    show sub.blks.find? _ = _
    rw [← hblocks]
    exact hb
  induction h with
  | last hb hp hr => exact .last (hblock hb) hp hr
  | next hb hp hr hs hj hsucc hrest ih =>
    exact .next (hblock hb) hp hr hs hj (fromSub_jump_edge (hblock hb) (selectJmp_mem hs) hj) ih

private theorem propagateBlock_definedVars (blk : Blk) (c : ConstEnv) :
    (propagateBlock blk c).1.definedVars = blk.definedVars := by
  have hfold : ∀ (defs acc : List Def) (st : ConstEnv), (defs.foldl propStep (acc, st)).1.map Def.var =
      acc.map Def.var ++ defs.map Def.var := by
    intro defs
    induction defs with
    | nil => simp
    | cons d ds ih =>
      intro acc st
      simp only [List.foldl_cons]
      have : (propStep (acc, st) d) = (acc ++ [{ d with rhs := propJump st d.rhs }], (propStep (acc, st) d).2) := rfl
      rw [this, ih]
      simp
  rw [propagateBlock_eq]
  simp only [Blk.definedVars, List.map_map, Function.comp_def, hfold]
  simp

/-- The variables the protected names cover. -/
theorem mem_protectedNames (cfg : Cfg) (ps : List Var) {x : Var} :
    x ∈ cfg.protectedNames ps ↔ x ∈ ps ∨ (x.base ∈ ps ∧ ∃ b ∈ cfg.blocks, x ∈ b.definedVars) := by
  cases ps with
  | nil => simp [Cfg.protectedNames]
  | cons p rest =>
    simp only [Cfg.protectedNames, List.mem_append, List.mem_filter, List.mem_flatMap, List.contains_iff_mem,
      ]
    grind

/-- Semantic preservation of `optimize` along control-flow paths, phis included, whichever way a run
enters the entry block. For any run of the original from the entry, the optimized subroutine has a run
along the same path, ending in the same block, whose stores include the original's in order, and which
selects the rewrite of the same jump at the end. It refines rather than equals: a removed definition can
no longer fail. At the end of the run every protected variable has the same value in both runs, as does
every assigned version of an unversioned protected variable; other variables not read by a later jump or
definition are not preserved, so the caller lists the subroutine's outputs in `ps`. -/
theorem optimize_preserves_runs (sub : Sub) (ps : List Var) {pred : Tid} {env final : Env} {path : List Tid}
    {tr : List (Var × Value)} {f : Blk} (h : Run (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env path tr final f) :
    ∃ tr' final' f', Run (Cfg.fromSub (optimize sub ps)) pred (Cfg.fromSub sub).start env path tr' final' f' ∧
      tr.Sublist tr' ∧ f'.tid = f.tid ∧
      (∀ x, x ∈ ps ∨ (x.base ∈ ps ∧ ∃ b ∈ (Cfg.fromSub sub).prune.blocks, x ∈ b.definedVars) →
        Bil.lookup final x = Bil.lookup final' x) ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        (∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp final' (g e) = .ok v) ∧
        ∀ o, selectJmp final f.jmps = .ok o → selectJmp final' f'.jmps = .ok (o.map (Jmp.mapExp g)) := by
  let cfg := Cfg.fromSub sub
  let names := (propagateConstants cfg).protectedNames ps
  have hnodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes := fun b hb => List.mem_map.2 ⟨b, hb, rfl⟩
  have hstart : cfg.start ∈ cfg.reachable := by
    obtain ⟨b, hb⟩ := h.block
    have hb' := block_some hb
    exact start_mem_reachable (hb'.2 ▸ hnodes b hb'.1)
  have hpruned := run_prune hnodes h hstart
  obtain ⟨tr₁, f₁, hrun₁, hsub, hft, g, hg, hgv⟩ :=
    propagateConstants_run cfg hpruned (fun _ env₁ _ _ => .start env₁)
  have hwf : BlocksAreNodes (propagateConstants cfg) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact prune_mem_nodes.2 (prune_blocks_reachable (blk := c) hc)
  have hreach : cfg.start ∈ (propagateConstants cfg).reachable :=
    start_mem_reachable (prune_mem_nodes.2 hstart)
  obtain ⟨final₂, f₂, hrun₂, ht₂, hj₂, ha₂⟩ :=
    dceAux_run (ps := names) (weight (propagateConstants cfg).blocks + 1) hwf hrun₁ hreach
  rw [← eliminateDeadCode_eq] at hrun₂
  have hexp : ∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp final₂ (g e) = .ok v := by
    intro j hj e he v hv
    have hv₁ := hgv e v hv
    rw [← hv₁]
    refine (Bap.Proofs.Bil.evalExp_congr_freeVars (g e) fun y hy => ?_).symm
    apply ha₂ y
    refine List.mem_append_left _ ?_
    simp only [jumpVars, List.mem_flatMap]
    refine ⟨j.mapExp g, ?_, ?_⟩
    · rw [hg]
      exact List.mem_map.2 ⟨j, hj, rfl⟩
    · refine freeVars_of_jmpExps ?_ hy
      rw [jmpExps_mapExp]
      exact List.mem_map.2 ⟨e, he, rfl⟩
  refine ⟨tr₁, final₂, f₂, run_fromSub_of_blocks rfl hrun₂, hsub, ht₂.trans hft, ?_, g, by rw [hj₂, hg], hexp, ?_⟩
  · intro x hx
    refine ha₂ x (List.mem_append_right _ ((mem_protectedNames _ _).2 ?_))
    rcases hx with hx | ⟨hb, b, hbm, hd⟩
    · exact Or.inl hx
    · refine Or.inr ⟨hb, (propagateBlock b (constAt cfg b.tid)).1, List.mem_map.2 ⟨b, hbm, rfl⟩, ?_⟩
      rw [propagateBlock_definedVars]
      exact hd
  · intro o ho
    rw [hj₂, hg]
    exact selectJmp_mapExp hexp ho

/-! ### Runs of the output

Every run of the optimized subroutine is a run of the original, unless the original fails: a removed
definition, or an expression folded to something simpler, can no longer fail. `RunFails` says how far the
original gets. -/

/-- A run gets as far as the last block of the path and fails there: in its phis, in its definitions, or
choosing a jump. -/
inductive RunFails (cfg : Cfg) : Tid → Tid → Env → List Tid → Prop where
  | phis {pred t env blk m} : cfg.block t = some blk → execPhis pred env blk.phis env = .error m →
    RunFails cfg pred t env [t]
  | defs {pred t env env₁ blk m} : cfg.block t = some blk → execPhis pred env blk.phis env = .ok env₁ →
    execDefs env₁ blk.defs = .error m → RunFails cfg pred t env [t]
  | jump {pred t env env₁ r blk m} : cfg.block t = some blk → execPhis pred env blk.phis env = .ok env₁ →
    execDefs env₁ blk.defs = .ok r → selectJmp r.1 blk.jmps = .error m → RunFails cfg pred t env [t]
  | next {pred t t' env env₁ r blk j path} : cfg.block t = some blk → execPhis pred env blk.phis env = .ok env₁ →
    execDefs env₁ blk.defs = .ok r → selectJmp r.1 blk.jmps = .ok (some j) → t' ∈ j.successors →
    t' ∈ cfg.successors t → RunFails cfg t t' r.1 path → RunFails cfg pred t env (t :: path)

private theorem Run.last_block {cfg : Cfg} {p t : Tid} {E F : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    (h : Run cfg p t E path tr F f) : cfg.block f.tid = some f := by
  induction h with
  | last hb _ _ =>
    rw [(block_some hb).2]
    exact hb
  | next _ _ _ _ _ _ _ ih => exact ih

/-- A run goes on with one more block. -/
private theorem Run.snoc {cfg : Cfg} {p t t' : Tid} {E F E₁ : Env} {path : List Tid} {tr : List (Var × Value)} {f b : Blk}
    {j : Jmp} {r : Env × List (Var × Value)} (h : Run cfg p t E path tr F f) (hsel : selectJmp F f.jmps = .ok (some j))
    (ht : t' ∈ j.successors) (hsucc : t' ∈ cfg.successors f.tid) (hb : cfg.block t' = some b)
    (hp : execPhis f.tid F b.phis F = .ok E₁) (hd : execDefs E₁ b.defs = .ok r) :
    Run cfg p t E (path ++ [t']) (tr ++ r.2) r.1 b := by
  induction h with
  | last hb₀ hp₀ hd₀ =>
    have htid := (block_some hb₀).2
    rw [htid] at hsucc hp
    exact .next hb₀ hp₀ hd₀ hsel ht hsucc (.last hb hp hd)
  | next hb₀ hp₀ hd₀ hsel₀ ht₀ hsucc₀ _ ih =>
    rw [List.append_assoc]
    exact .next hb₀ hp₀ hd₀ hsel₀ ht₀ hsucc₀ (ih hsel hsucc hp)

private theorem Run.fails_jump {cfg : Cfg} {p t : Tid} {E F : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    {m : String} (h : Run cfg p t E path tr F f) (hsel : selectJmp F f.jmps = .error m) : RunFails cfg p t E path := by
  induction h with
  | last hb hp hd => exact .jump hb hp hd hsel
  | next hb hp hd hsel₀ ht hsucc _ ih => exact .next hb hp hd hsel₀ ht hsucc (ih hsel)

private theorem Run.fails_snoc {cfg : Cfg} {p t t' : Tid} {E F : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    {j : Jmp} (h : Run cfg p t E path tr F f) (hsel : selectJmp F f.jmps = .ok (some j))
    (ht : t' ∈ j.successors) (hsucc : t' ∈ cfg.successors f.tid) (hf : RunFails cfg f.tid t' F [t']) :
    RunFails cfg p t E (path ++ [t']) := by
  induction h with
  | last hb₀ hp₀ hd₀ =>
    have htid := (block_some hb₀).2
    rw [htid] at hsucc hf
    exact .next hb₀ hp₀ hd₀ hsel ht hsucc hf
  | next hb₀ hp₀ hd₀ hsel₀ ht₀ hsucc₀ _ ih =>
    exact .next hb₀ hp₀ hd₀ hsel₀ ht₀ hsucc₀ (ih hsel hsucc hf)

/-- A run with more than one block is a run with one less, and a step. -/
private theorem Run.split {cfg : Cfg} {p t t' : Tid} {E F' : Env} {path : List Tid} {tr' : List (Var × Value)} {f' : Blk}
    (hne : path ≠ []) (h : Run cfg p t E (path ++ [t']) tr' F' f') :
    ∃ tr F f j b, Run cfg p t E path tr F f ∧ selectJmp F f.jmps = .ok (some j) ∧ t' ∈ j.successors ∧
      t' ∈ cfg.successors f.tid ∧ cfg.block t' = some b := by
  induction path generalizing p t E tr' with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    simp only [List.cons_append] at h
    generalize hq : rest ++ [t'] = tail at h
    cases h with
    | @next _ _ t₁ _ E₁ r blk j _ stores _ _ hb hp hd hsel ht hsucc hrest =>
      subst hq
      by_cases hrn : rest = []
      · subst hrn
        have hatid := (block_some hb).2
        cases hrest with
        | last hb₁ _ _ =>
          exact ⟨r.2, r.1, blk, j, _, .last hb hp hd, hsel, ht, by rw [hatid]; exact hsucc, hb₁⟩
        | next _ _ _ _ _ _ hr' => exact absurd hr'.path_ne_nil (by simp_all)
      · obtain ⟨tr, F, f, j', b, hrun, hs, hj, hsucc', hbk⟩ := ih hrn hrest
        exact ⟨_, F, f, j', b, .next hb hp hd hsel ht hsucc hrun, hs, hj, hsucc', hbk⟩
    | last _ _ _ => simp at hq

private theorem optimize_block_input {sub : Sub} {ps : List Var} {t : Tid} {b : Blk}
    (h : (Cfg.fromSub (optimize sub ps)).block t = some b) : ∃ o, (Cfg.fromSub sub).block t = some o := by
  have hm := block_some h
  have ht : t ∈ (optimize sub ps).blks.map Blk.tid := List.mem_map.2 ⟨b, hm.1, hm.2⟩
  rw [optimize_tids] at ht
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ht
  exact block_exists (List.mem_map.2 ⟨c, (prune_blocks_sublist _).subset hc, rfl⟩)

/-- Either the input fails at a block, or it runs the block. -/
private theorem step_or_fails (cfg : Cfg) (pred t : Tid) (env : Env) {o : Blk} (ho : cfg.block t = some o) :
    (∃ E₁ r, execPhis pred env o.phis env = .ok E₁ ∧ execDefs E₁ o.defs = .ok r) ∨ RunFails cfg pred t env [t] := by
  cases hp : execPhis pred env o.phis env with
  | error m => exact .inr (.phis ho hp)
  | ok E₁ =>
    cases hd : execDefs E₁ o.defs with
    | error m => exact .inr (.defs ho hp hd)
    | ok r => exact .inl ⟨E₁, r, rfl, hd⟩

/-- A run of the output along a path is a run of the input along it, or the input fails on the way. -/
private theorem optimize_run_back (sub : Sub) (ps : List Var) (pred : Tid) (env : Env) (path : List Tid) :
    ∀ {tr' final' f'}, Run (Cfg.fromSub (optimize sub ps)) pred (Cfg.fromSub sub).start env path tr' final' f' →
      (∃ tr final f, Run (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env path tr final f) ∨
        ∃ failed, failed <+: path ∧ RunFails (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env failed := by
  induction hlen : path.length generalizing path with
  | zero =>
    intro _ _ _ h
    exact absurd (List.length_eq_zero_iff.1 hlen) h.path_ne_nil
  | succ n ih =>
    intro tr' final' f' h
    obtain ⟨q, t', rfl⟩ : ∃ q t', path = q ++ [t'] := by
      rcases List.eq_nil_or_concat path with hp | hp
      · simp [hp] at hlen
      · obtain ⟨l, b, rfl⟩ := hp
        exact ⟨l, b, by simp⟩
    have hqlen : q.length = n := by simpa using hlen
    by_cases hq : q = []
    · subst hq
      simp only [List.nil_append] at h
      cases h with
      | last hb _ _ =>
        obtain ⟨o, ho⟩ := optimize_block_input hb
        rcases step_or_fails _ pred _ env ho with ⟨E₁, r, hp, hd⟩ | hf
        · exact .inl ⟨_, _, _, .last ho hp hd⟩
        · exact .inr ⟨_, List.prefix_refl _, hf⟩
      | next _ _ _ _ _ _ hr => exact absurd hr.path_ne_nil (by simp_all)
    · obtain ⟨tr₀, F₀, f₀, j, b, hrun₀, hsel₀, ht, hsucc₀, hbk⟩ := Run.split hq h
      rcases ih q hqlen hrun₀ with ⟨tr, final, f, hr⟩ | ⟨failed, hpre, hf⟩
      · obtain ⟨tr₁, F₁, f₁, hrun₁, _, _, _, g, hjm, _, hselg⟩ := optimize_preserves_runs sub ps hr
        obtain ⟨_, hdet⟩ := Run.deterministic hrun₁ hrun₀
        obtain ⟨rfl, rfl, rfl⟩ := hdet rfl
        cases hs : selectJmp final f.jmps with
        | error m => exact .inr ⟨q, List.prefix_append _ _, hr.fails_jump hs⟩
        | ok o =>
          have hsel' := hselg o hs
          rw [hsel₀] at hsel'
          cases o with
          | none => simp at hsel'
          | some j₀ =>
            have hj : j = j₀.mapExp g := by simpa using hsel'
            have ht₀ : t' ∈ j₀.successors := by
              rw [hj, Jmp.successors_mapExp] at ht
              exact ht
            have hsucc : t' ∈ (Cfg.fromSub sub).successors f.tid :=
              fromSub_jump_edge hr.last_block (selectJmp_mem hs) ht₀
            obtain ⟨o, ho⟩ := optimize_block_input hbk
            rcases step_or_fails _ f.tid _ final ho with ⟨E₁, r, hp, hd⟩ | hf
            · exact .inl ⟨_, _, _, hr.snoc hs ht₀ hsucc ho hp hd⟩
            · exact .inr ⟨_, List.prefix_refl _, hr.fails_snoc hs ht₀ hsucc hf⟩
      · exact .inr ⟨failed, hpre.trans (List.prefix_append _ _), hf⟩

/-- The converse of `optimize_preserves_runs`. A run of the optimized subroutine from the entry is a run of
the original along the same path, related as that theorem says, unless the original fails on the way:
`optimize` refines the original, since a removed definition or a folded expression can no longer fail. -/
theorem optimize_reflects_runs (sub : Sub) (ps : List Var) {pred : Tid} {env final' : Env} {path : List Tid}
    {tr' : List (Var × Value)} {f' : Blk}
    (h : Run (Cfg.fromSub (optimize sub ps)) pred (Cfg.fromSub sub).start env path tr' final' f') :
    (∃ tr final f, Run (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env path tr final f ∧
      tr.Sublist tr' ∧ f'.tid = f.tid ∧
      (∀ x, x ∈ ps ∨ (x.base ∈ ps ∧ ∃ b ∈ (Cfg.fromSub sub).prune.blocks, x ∈ b.definedVars) →
        Bil.lookup final x = Bil.lookup final' x) ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        (∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp final' (g e) = .ok v) ∧
        ∀ o, selectJmp final f.jmps = .ok o → selectJmp final' f'.jmps = .ok (o.map (Jmp.mapExp g))) ∨
    ∃ failed, failed <+: path ∧ RunFails (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env failed := by
  rcases optimize_run_back sub ps pred env path h with ⟨tr, final, f, hr⟩ | hf
  · obtain ⟨tr₁, F₁, f₁, hrun₁, hs, ht, hl, g, hg⟩ := optimize_preserves_runs sub ps hr
    obtain ⟨_, hdet⟩ := Run.deterministic hrun₁ h
    obtain ⟨rfl, rfl, rfl⟩ := hdet rfl
    exact .inl ⟨tr, final, f, hr, hs, ht, hl, g, hg⟩
  · exact .inr hf

/-- Where the original doesn't fail, `optimize` has exactly its runs. -/
theorem optimize_runs_iff (sub : Sub) (ps : List Var) {pred : Tid} {env : Env} {path : List Tid}
    (hsafe : ∀ failed, failed <+: path → ¬ RunFails (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env failed) :
    (∃ tr final f, Run (Cfg.fromSub sub) pred (Cfg.fromSub sub).start env path tr final f) ↔
      ∃ tr final f, Run (Cfg.fromSub (optimize sub ps)) pred (Cfg.fromSub sub).start env path tr final f := by
  constructor
  · rintro ⟨tr, final, f, h⟩
    obtain ⟨tr', final', f', h', _⟩ := optimize_preserves_runs sub ps h
    exact ⟨tr', final', f', h'⟩
  · rintro ⟨tr, final, f, h⟩
    rcases optimize_run_back sub ps pred env path h with hr | ⟨failed, hpre, hf⟩
    · exact hr
    · exact absurd hf (hsafe failed hpre)

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

/-- `x := z; ret y`: the write to `x` is read by nothing in the subroutine. -/
private def outputSample : Sub :=
  ⟨1, "output", [], [⟨1, [], [⟨10, vx, .var vz⟩], [⟨11, none, .ret (.indirect (.var vy))⟩]⟩]⟩

/-- `optimize` keeps an otherwise dead write to a protected output. -/
theorem optimize_keeps_protected_output :
    ((optimize outputSample [vx]).blks.map fun blk => blk.defs.map Def.var) = [[vx]] := by
  rfl

/-- With no protected variables that write is removed: listing outputs is the caller's responsibility. -/
theorem optimize_removes_unprotected_output :
    ((optimize outputSample).blks.map fun blk => blk.defs.map Def.var) = [[]] := by
  rfl

/-- A sample whose dead definition fails: `x := y` with `y` unbound. -/
private def failingSample : Sub := ⟨1, "failing", [], [⟨1, [], [⟨10, vx, .var vy⟩], []⟩]⟩

/-- `optimize` removes the definition, so its output runs where the original fails: why
`optimize_reflects_runs` has to allow for failure. -/
theorem optimize_forgives_removed_failure :
    RunFails (Cfg.fromSub failingSample) pseudoStart (Cfg.fromSub failingSample).start [] [1] ∧
      ∃ tr final f, Run (Cfg.fromSub (optimize failingSample)) pseudoStart (Cfg.fromSub failingSample).start [] [1] tr final f := by
  have hstart : (Cfg.fromSub failingSample).start = 1 := rfl
  rw [hstart]
  refine ⟨.defs (env₁ := []) (blk := ⟨1, [], [⟨10, vx, .var vy⟩], []⟩) (m := "unbound variable y") rfl rfl ?_, [], [], ⟨1, [], [], []⟩,
    .last (env₁ := []) (r := ([], [])) rfl rfl rfl⟩
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
    (newName v st).1 = v.version (counterOf st v) := rfl

private theorem newName_counters (v : Var) (st : RenameState) :
    (newName v st).2.counters = Assoc.put v.base (counterOf st v + 1) st.counters := rfl

private theorem newName_stacks (v : Var) (st : RenameState) :
    (newName v st).2.stacks = Assoc.put v
      ((newName v st).1 :: (Assoc.get v st.stacks).getD []) st.stacks := rfl

private theorem topName_eq (v : Var) (st : RenameState) :
    topName v st = match Assoc.get v st.stacks with
      | some stack => stack.head?.getD v
      | none => v := rfl

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
theorem topName_newName (v : Var) (st : RenameState) :
    topName v (newName v st).2 = (newName v st).1 := by
  rw [topName_eq, newName_stacks, get_put]
  simp

/-- Renaming one variable never affects reads of another, even another version of the same base. -/
theorem topName_newName_other (v w : Var) (st : RenameState) (h : w ≠ v) :
    topName w (newName v st).2 = topName w st := by
  rw [topName_eq, topName_eq, newName_stacks, get_put]
  simp only [h, ite_false]

/-- The stack of names visible for a variable. -/
private abbrev stackOf (st : RenameState) (k : Var) : List Var := (Assoc.get k st.stacks).getD []

private theorem get_popVar_stacks (var : Var) (st : RenameState) (k : Var) :
    Assoc.get k (popVar var st).stacks =
      (Assoc.get k st.stacks).map fun stack => if k = var then stack.tail else stack := by
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
    stackOf (popVar var st) k = if k = var then (stackOf st k).tail else stackOf st k := by
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
    stackOf (popVars vars st) k = (stackOf st k).drop (vars.count k) := by
  induction vars generalizing st with
  | nil => simp [show popVars [] st = st from rfl]
  | cons v vs ih =>
    rw [popVars_cons, ih, stackOf_popVar]
    by_cases hv : k = v
    · subst hv
      simp only [↓reduceIte, List.count_cons_self, List.drop_tail]
    · have hne : (v == k) = false := by simpa using Ne.symm hv
      simp [hv, List.count_cons, hne]

private theorem topName_of_stack (v : Var) (st : RenameState) :
    topName v st = (stackOf st v).head?.getD v := by
  rw [topName_eq]
  cases hg : Assoc.get v st.stacks <;> simp [stackOf, hg]

private theorem stackOf_newName (o : Var) (st : RenameState) (k : Var) :
    stackOf (newName o st).2 k =
      if k = o then (newName o st).1 :: stackOf st k else stackOf st k := by
  simp only [stackOf, newName_stacks, get_put]
  by_cases hk : k = o
  · subst hk
    simp
  · simp [hk]

/-- Popping after one definition restores the name visible before it. -/
theorem topName_pop_newName (v : Var) (st : RenameState) :
    topName v (popVars [v] (newName v st).2) = topName v st := by
  have hstack : stackOf (popVars [v] (newName v st).2) v = stackOf st v := by
    rw [show popVars [v] (newName v st).2 = popVar v (newName v st).2 from rfl,
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
      simp [hb, hnew, hs, hrest]
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

/-- The insertion of a phi unless the block already has one for the variable. -/
private abbrev phiInsert (var : Var) (phi : Phi) (blk : Blk) : Blk :=
  if blk.phis.any (·.var == var) then blk else { blk with phis := blk.phis ++ [phi] }

private abbrev phiStep (var : Var) (state : Cfg × List Tid × List Tid) (join : Tid) :
    Cfg × List Tid × List Tid :=
  if join ∈ state.2.1 then state
  else
    (state.1.updateBlock join (phiInsert var ⟨join, var, (state.1.predecessors join).map fun pred => (pred, .var var)⟩),
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
    · refine frame_update _ _ _ (fun b _ => ?_) (fun b _ => ?_) <;> simp only [phiInsert] <;> split <;> rfl

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
        (cfg.blocks.filterMap fun blk => if blk.defines var then some blk.tid else none) []) frontier rest := rfl

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
        (r₃.1, popVars (block.phis.map (·.var) ++ block.defs.map (·.var)) r₃.2) := rfl

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
        simp only [Blk.successors, List.flatMap_map, Jmp.successors_mapExp])
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
  let state := initialState cfg.blocks
  let cfg := insertAllPhis cfg frontier (cfg.blocks.flatMap Blk.definedVars).eraseDups
  (renameBlock idom (cfg.blocks.length + 1) cfg.start cfg state).1

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
    ∃ xs, stackOf (renamePhis phis st).2 k = xs ++ stackOf st k ∧ xs.length = (phis.map Phi.var).count k ∧
      xs ⊆ (renamePhis phis st).1.map Phi.var := by
  induction phis generalizing st with
  | nil => exact ⟨[], by simp [show renamePhis [] st = ([], st) from rfl], rfl, by simp⟩
  | cons p ps ih =>
    rw [renamePhis_cons]
    obtain ⟨xs, hx, hl, hsub⟩ := ih (newName p.var st).2
    rw [stackOf_newName] at hx
    by_cases hk : k = p.var
    · subst hk
      refine ⟨xs ++ [(newName p.var st).1], by simpa using hx, ?_, ?_⟩
      · simp [hl]
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact List.mem_cons_of_mem _ (hsub hy)
        · rw [List.mem_singleton.1 hy]
          simp
    · have hne : (p.var == k) = false := by simpa using Ne.symm hk
      refine ⟨xs, by simpa [hk] using hx, ?_, fun y hy => List.mem_cons_of_mem _ (hsub hy)⟩
      simp [hl, List.count_cons, hne]

private theorem stackOf_renameDefs (defs : List Def) (st : RenameState) (k : Var) :
    ∃ xs, stackOf (renameDefs defs st).2 k = xs ++ stackOf st k ∧ xs.length = (defs.map Def.var).count k ∧
      xs ⊆ (renameDefs defs st).1.map Def.var := by
  induction defs generalizing st with
  | nil => exact ⟨[], by simp [show renameDefs [] st = ([], st) from rfl], rfl, by simp⟩
  | cons d ds ih =>
    rw [renameDefs_cons]
    obtain ⟨xs, hx, hl, hsub⟩ := ih (newName d.var st).2
    rw [stackOf_newName] at hx
    by_cases hk : k = d.var
    · subst hk
      refine ⟨xs ++ [(newName d.var st).1], by simpa using hx, ?_, ?_⟩
      · simp [hl]
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact List.mem_cons_of_mem _ (hsub hy)
        · rw [List.mem_singleton.1 hy]
          simp
    · have hne : (d.var == k) = false := by simpa using Ne.symm hk
      refine ⟨xs, by simpa [hk] using hx, ?_, fun y hy => List.mem_cons_of_mem _ (hsub hy)⟩
      simp [hl, List.count_cons, hne]

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
      rw [stackOf_popVars, hchildren]
      obtain ⟨xs, hxs, hxl, -⟩ := stackOf_renamePhis block.phis st k
      obtain ⟨ys, hys, hyl, -⟩ := stackOf_renameDefs block.defs (renamePhis block.phis st).2 k
      have hstack : stackOf (renameDefs block.defs (renamePhis block.phis st).2).2 k = (ys ++ xs) ++ stackOf st k := by
        rw [hys, hxs, List.append_assoc]
      have hc : (block.phis.map (·.var) ++ block.defs.map (·.var)).count k = (ys ++ xs).length := by
        rw [List.count_append, ← hxl, ← hyl, List.length_append]
        omega
      show (stackOf (renameDefs block.defs (renamePhis block.phis st).2).2 k).drop _ = _
      rw [hc, hstack]
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
  insertAllPhis cfg cfg.dominanceFrontier (cfg.blocks.flatMap Blk.definedVars).eraseDups

private theorem initialState_fold_counter (vars : List Var) (seed : List (Var × Nat))
    (hseed : ∀ w : Var, 1 ≤ (Assoc.get w.base seed).getD 1) (w : Var) :
    1 ≤ (Assoc.get w.base (vars.foldl (init := seed) fun counters var =>
      if var.index = 0 then counters
      else Assoc.put var.base (max ((Assoc.get var.base counters).getD 1) (var.index + 1)) counters)).getD 1 := by
  induction vars generalizing seed with
  | nil => exact hseed w
  | cons v vs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro z
    split
    · exact hseed z
    · rw [get_put]
      split
      · simp only [Option.getD_some]
        have := hseed v
        omega
      · exact hseed z

/-- Every version counter starts at one or above, so no issued name is an unversioned variable. -/
private theorem initialState_counter_pos (blocks : List Blk) (w : Var) :
    1 ≤ counterOf (initialState blocks) w :=
  initialState_fold_counter _ [] (fun _ => by simp) w

private theorem ssaCfg_eq (sub : Sub) :
    ssaCfg sub = (renameBlock (Cfg.connected sub).immediateDominators ((phiCfg sub).blocks.length + 1)
      (phiCfg sub).start (phiCfg sub) (initialState (Cfg.connected sub).blocks)).1 := rfl

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
  have hempty : SAInv (phiCfg sub) (initialState (Cfg.connected sub).blocks) (fun _ => False) :=
    ⟨fun w => initialState_counter_pos _ w, fun _ _ h => h.elim, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩
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
    (phiCfg sub).start (phiCfg sub) (initialState (Cfg.connected sub).blocks) (fun _ => False) hempty hkeys hst
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
      (phiCfg sub).start (phiCfg sub) (initialState (Cfg.connected sub).blocks)).2 V := hinv
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

/-! ### Phi placement -/

/-- Everything the connected CFG adds is an edge out of the pseudo start or into the pseudo exit. -/
private theorem grows_starts_edges (actual : List Tid) (cfg : Cfg) (fuel : Nat) {a b : Tid}
    (h : (a, b) ∈ (connectMissingStarts actual cfg fuel).graph.edges) :
    (a, b) ∈ cfg.graph.edges ∨ (a = pseudoStart ∧ b ∈ actual) := by
  induction fuel generalizing cfg with
  | zero => exact Or.inl h
  | succ fuel ih =>
    rw [connectMissingStarts_succ] at h
    split at h
    · exact Or.inl h
    · rename_i tid hsome
      rcases ih _ h with h | h
      · rcases List.mem_cons.1 h with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact Or.inr ⟨rfl, List.mem_of_find?_eq_some hsome⟩
        · exact Or.inl h
      · exact Or.inr h

private theorem grows_exits_edges (actual : List Tid) (cfg : Cfg) (fuel : Nat) {a b : Tid}
    (h : (a, b) ∈ (connectMissingExits actual cfg fuel).graph.edges) :
    (a, b) ∈ cfg.graph.edges ∨ (a ∈ actual ∧ b = pseudoExit) := by
  induction fuel generalizing cfg with
  | zero => exact Or.inl h
  | succ fuel ih =>
    rw [connectMissingExits_succ] at h
    split at h
    · exact Or.inl h
    · rename_i tid hsome
      rcases ih _ h with h | h
      · rcases List.mem_cons.1 h with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact Or.inr ⟨List.mem_of_find?_eq_some hsome, rfl⟩
        · exact Or.inl h
      · exact Or.inr h

/-- Every edge of the connected CFG is an edge of the plain CFG, leaves the pseudo start for a block,
or enters the pseudo exit from a block. -/
theorem connected_edge_cases (sub : Sub) {a b : Tid} (h : (a, b) ∈ (Cfg.connected sub).graph.edges) :
    (a, b) ∈ (Cfg.fromSub sub).graph.edges ∨ (a = pseudoStart ∧ b ∈ sub.blks.map Blk.tid) ∨
      (a ∈ sub.blks.map Blk.tid ∧ b = pseudoExit) := by
  rw [connected_eq] at h
  rcases grows_exits_edges _ _ _ h with h | h
  · rcases grows_starts_edges _ _ _ h with h | h
    · simp only [List.mem_append, List.mem_map, Prod.mk.injEq] at h
      rcases h with (h | h) | h
      · exact Or.inl h
      · obtain ⟨t, ht, rfl, rfl⟩ := h
        refine Or.inr (Or.inl ⟨rfl, ?_⟩)
        rcases ht with ht | ht
        · cases hl : sub.blks.map Blk.tid with
          | nil => simp [hl] at ht
          | cons x xs =>
            simp only [hl, List.head?_cons, Option.toList_some, List.mem_singleton] at ht
            subst ht
            simp
        · exact (List.mem_filter.1 ht).1
      · obtain ⟨t, ht, rfl, rfl⟩ := h
        exact Or.inr (Or.inr ⟨(List.mem_filter.1 ht).1, rfl⟩)
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The pseudo start always has an edge to the entry block, which a loop back to the entry or a jump
from another root does not replace: a run enters there whatever else jumps to it. -/
theorem connected_entry_edge {sub : Sub} (h : sub.blks ≠ []) :
    (pseudoStart, (Cfg.fromSub sub).start) ∈ (Cfg.connected sub).graph.edges := by
  refine (connected_grows sub).edges ?_
  match hb : sub.blks, h with
  | blk :: rest, _ =>
    simp [hb, Cfg.fromSub]

/-- Tids of a subroutine that can be told apart from each other and from the pseudo nodes, with no
jump back to the pseudo start. -/
structure SubWf (sub : Sub) : Prop where
  nodup : (pseudoStart :: sub.blks.map Blk.tid ++ [pseudoExit]).Nodup
  noStart : ∀ b ∈ sub.blks, pseudoStart ∉ b.successors

section SubWfFacts

variable {sub : Sub}

private theorem SubWf.start_ne {b : Blk} (h : SubWf sub) (hb : b ∈ sub.blks) : b.tid ≠ pseudoStart := by
  rintro heq
  have := h.nodup
  simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_map, not_or, not_exists, not_and] at this
  exact this.1.1 b hb heq

private theorem SubWf.exit_ne {b : Blk} (h : SubWf sub) (hb : b ∈ sub.blks) : b.tid ≠ pseudoExit := by
  rintro heq
  have := h.nodup
  simp only [List.cons_append, List.nodup_cons, List.nodup_append] at this
  exact this.2.2.2 _ (List.mem_map.2 ⟨b, hb, rfl⟩) _ (by simp) heq

private theorem pseudoStart_ne_exit : pseudoStart ≠ pseudoExit := by decide

private theorem SubWf.no_edge_to_start (h : SubWf sub) {a : Tid} : (a, pseudoStart) ∉ (Cfg.connected sub).graph.edges := by
  intro he
  rcases connected_edge_cases sub he with he | ⟨_, hb⟩ | ⟨_, hb⟩
  · obtain ⟨b, hb, _, hs⟩ := (fromSub_mem_edges sub a pseudoStart).1 he
    exact h.noStart b hb hs
  · obtain ⟨b, hb', heq⟩ := List.mem_map.1 hb
    exact h.start_ne hb' heq
  · exact pseudoStart_ne_exit hb

private theorem SubWf.no_edge_from_exit (h : SubWf sub) {b : Tid} : (pseudoExit, b) ∉ (Cfg.connected sub).graph.edges := by
  intro he
  rcases connected_edge_cases sub he with he | ⟨hb, _⟩ | ⟨hb, _⟩
  · obtain ⟨c, hc, ht, _⟩ := (fromSub_mem_edges sub pseudoExit b).1 he
    exact h.exit_ne hc ht
  · exact pseudoStart_ne_exit hb.symm
  · obtain ⟨c, hc, ht⟩ := List.mem_map.1 hb
    exact h.exit_ne hc ht

private theorem connected_nodes_nodup (h : SubWf sub) : (Cfg.connected sub).graph.nodes.Nodup := by
  rw [connected_nodes]
  exact h.nodup

/-- A block of the subroutine has the same contents in the connected CFG. -/
private theorem connected_block_real (h : SubWf sub) {t : Tid} {b : Blk} (hb : (Cfg.fromSub sub).block t = some b) :
    (Cfg.connected sub).block t = some b := by
  have hm := block_some hb
  have htne : t ≠ pseudoStart := hm.2 ▸ h.start_ne hm.1
  have hfind : sub.blks.find? (fun blk => decide (blk.tid = t)) = some b := hb
  show (Cfg.connected sub).blocks.find? _ = _
  rw [connected_blocks]
  simp [List.find?_cons, List.find?_append, Ne.symm htne, hfind]

private theorem connected_block_start : (Cfg.connected sub).block pseudoStart = some ⟨pseudoStart, [], [], []⟩ := by
  show (Cfg.connected sub).blocks.find? _ = _
  rw [connected_blocks]
  simp

end SubWfFacts

/-- `b` grows from `a` by phis for variables in `allowed`, each listing every predecessor with a copy of
its own variable, added only to blocks that have no phi for that variable yet. -/
private structure PhiGrow (allowed : Var → Prop) (a b : Cfg) : Prop where
  start : b.start = a.start
  graph : b.graph = a.graph
  blocks : ∀ n x, a.block n = some x → ∃ ins, b.block n = some { x with phis := x.phis ++ ins } ∧
    ∀ φ ∈ ins, allowed φ.var ∧ φ.var ∉ x.phis.map Phi.var ∧
      φ.values = (a.predecessors n).map fun pred => (pred, Exp.var φ.var)
  none : ∀ n, a.block n = none → b.block n = none
  tids : b.blocks.map Blk.tid = a.blocks.map Blk.tid
  mem : ∀ y ∈ b.blocks, ∃ x ∈ a.blocks, y.tid = x.tid ∧ y.defs = x.defs ∧ ∀ φ ∈ y.phis, φ ∈ x.phis ∨ allowed φ.var

private theorem PhiGrow.refl (allowed : Var → Prop) (a : Cfg) : PhiGrow allowed a a :=
  ⟨rfl, rfl, fun n x h => ⟨[], by simp [h], by simp⟩, fun _ h => h, rfl,
    fun y hy => ⟨y, hy, rfl, rfl, fun _ h => Or.inl h⟩⟩

private theorem PhiGrow.trans {allowed : Var → Prop} {a b c : Cfg} (h : PhiGrow allowed a b) (h' : PhiGrow allowed b c) :
    PhiGrow allowed a c := by
  refine ⟨h'.start.trans h.start, h'.graph.trans h.graph, ?_, fun n hn => h'.none n (h.none n hn),
    h'.tids.trans h.tids, ?_⟩
  rotate_left
  · intro y hy
    obtain ⟨z, hz, h₁, h₂, h₃⟩ := h'.mem y hy
    obtain ⟨x, hx, h₄, h₅, h₆⟩ := h.mem z hz
    refine ⟨x, hx, h₁.trans h₄, h₂.trans h₅, fun φ hφ => ?_⟩
    rcases h₃ φ hφ with h | h
    · exact h₆ φ h
    · exact Or.inr h
  intro n x hx
  obtain ⟨i₁, h₁, hi₁⟩ := h.blocks n x hx
  obtain ⟨i₂, h₂, hi₂⟩ := h'.blocks n _ h₁
  refine ⟨i₁ ++ i₂, by simpa [List.append_assoc] using h₂, ?_⟩
  intro φ hφ
  rcases List.mem_append.1 hφ with hφ | hφ
  · exact hi₁ φ hφ
  · obtain ⟨p₁, p₂, p₃⟩ := hi₂ φ hφ
    refine ⟨p₁, ?_, ?_⟩
    · intro hm
      apply p₂
      simp only [List.map_append]
      exact List.mem_append_left _ hm
    · rw [p₃]
      show (Bap.Graph.predecessors b.graph n).map _ = (Bap.Graph.predecessors a.graph n).map _
      rw [h.graph]

private theorem PhiGrow.mono {p q : Var → Prop} (hpq : ∀ v, p v → q v) {a b : Cfg} (h : PhiGrow p a b) : PhiGrow q a b :=
  ⟨h.start, h.graph, fun n x hx => by
    obtain ⟨i, hi, hall⟩ := h.blocks n x hx
    exact ⟨i, hi, fun φ hφ => ⟨hpq _ (hall φ hφ).1, (hall φ hφ).2⟩⟩, h.none, h.tids, fun y hy => by
    obtain ⟨x, hx, h₁, h₂, h₃⟩ := h.mem y hy
    exact ⟨x, hx, h₁, h₂, fun φ hφ => (h₃ φ hφ).imp_right (hpq _)⟩⟩

private theorem phiInsert_tid (var : Var) (phi : Phi) (b : Blk) : (phiInsert var phi b).tid = b.tid := by
  simp only [phiInsert]
  split <;> rfl

private theorem phiStep_grow (var : Var) (state : Cfg × List Tid × List Tid) (join : Tid) :
    PhiGrow (· = var) state.1 (phiStep var state join).1 := by
  simp only [phiStep]
  split
  · exact PhiGrow.refl _ _
  · refine ⟨rfl, rfl, ?_, ?_, updateBlock_tids _ _ _ (fun b _ => phiInsert_tid _ _ b), ?_⟩
    rotate_left 2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      refine ⟨x, hx, ?_⟩
      split
      · simp only [phiInsert]
        split
        · exact ⟨rfl, rfl, fun _ h => Or.inl h⟩
        · refine ⟨rfl, rfl, fun φ hφ => ?_⟩
          rcases List.mem_append.1 hφ with h | h
          · exact Or.inl h
          · rw [List.mem_singleton.1 h]
            exact Or.inr rfl
      · exact ⟨rfl, rfl, fun _ h => Or.inl h⟩
    · intro n x hx
      by_cases hn : n = join
      · subst hn
        rw [block_updateBlock_same _ _ _ (fun b _ => phiInsert_tid _ _ b), hx]
        by_cases hany : x.phis.any (·.var == var) = true
        · refine ⟨[], ?_, by simp⟩
          rw [Option.map_some, phiInsert, ite_eq_left hany, List.append_nil]
        · refine ⟨[⟨n, var, (state.1.predecessors n).map fun pred => (pred, Exp.var var)⟩], ?_, ?_⟩
          · rw [Option.map_some, phiInsert, ite_eq_right hany]
          · intro φ hφ
            rw [List.mem_singleton.1 hφ]
            refine ⟨rfl, ?_, rfl⟩
            intro hm
            apply hany
            obtain ⟨ψ, hψ, heq⟩ := List.mem_map.1 hm
            exact List.any_eq_true.2 ⟨ψ, hψ, by simpa using heq⟩
      · rw [block_updateBlock_ne _ _ (fun b _ => phiInsert_tid _ _ b) hn, hx]
        exact ⟨[], by simp, by simp⟩
    · intro n hn
      by_cases hj : n = join
      · subst hj
        rw [block_updateBlock_same _ _ _ (fun b _ => phiInsert_tid _ _ b), hn]
        rfl
      · rw [block_updateBlock_ne _ _ (fun b _ => phiInsert_tid _ _ b) hj, hn]

/-- The block has a phi for the variable, or does not exist. -/
private abbrev HasPhi (cfg : Cfg) (var : Var) (j : Tid) : Prop :=
  ∀ c, cfg.block j = some c → ∃ φ ∈ c.phis, φ.var = var

private theorem HasPhi.grow {allowed : Var → Prop} {a b : Cfg} {var : Var} {j : Tid} (h : HasPhi a var j)
    (hg : PhiGrow allowed a b) : HasPhi b var j := by
  intro c hc
  cases hx : a.block j with
  | none =>
    rw [hg.none j hx] at hc
    cases hc
  | some x =>
    obtain ⟨i, hi, _⟩ := hg.blocks j x hx
    rw [hi] at hc
    cases hc
    obtain ⟨φ, hφ, heq⟩ := h x hx
    exact ⟨φ, List.mem_append_left _ hφ, heq⟩

/-- A block gained a phi for the variable only if the loop inserted at it. -/
private abbrev OnlyAt (a b : Cfg) (var : Var) (I : List Tid) : Prop :=
  ∀ n x c, a.block n = some x → b.block n = some c → (∃ φ ∈ c.phis, φ.var = var) →
    (∃ φ ∈ x.phis, φ.var = var) ∨ n ∈ I

private structure PhiFold (var : Var) (nodes : List Tid) (joins : List Tid) (s s' : Cfg × List Tid × List Tid) : Prop where
  grow : PhiGrow (· = var) s.1 s'.1
  inserted : s.2.1 ⊆ s'.2.1
  joined : joins ⊆ s'.2.1
  added : ∀ j ∈ s'.2.1, j ∈ s.2.1 ∨ (HasPhi s'.1 var j ∧ j ∈ s'.2.2)
  work : s.2.2 ⊆ s'.2.2
  measure : s'.2.2.length + nodes.countP (fun t => decide (t ∉ s'.2.1)) ≤
    s.2.2.length + nodes.countP (fun t => decide (t ∉ s.2.1))
  only : OnlyAt s.1 s'.1 var s'.2.1
  fromJoins : ∀ j ∈ s'.2.1, j ∈ s.2.1 ∨ j ∈ joins
  workJoins : ∀ j ∈ s'.2.2, j ∈ s.2.2 ∨ j ∈ joins

private theorem phiFold_spec (var : Var) (nodes : List Tid) (joins : List Tid) (hj : joins ⊆ nodes)
    (s : Cfg × List Tid × List Tid) : PhiFold var nodes joins s (joins.foldl (phiStep var) s) := by
  induction joins generalizing s with
  | nil =>
    exact ⟨PhiGrow.refl _ _, List.Subset.refl _, by simp, fun j h => Or.inl h, List.Subset.refl _, Nat.le_refl _,
      fun n x c hx hc hp => by
        simp only [List.foldl_nil] at hc
        rw [hx] at hc
        cases hc
        exact Or.inl hp, fun _ h => Or.inl h, fun _ h => Or.inl h⟩
  | cons j js ih =>
    simp only [List.foldl_cons]
    have hstep := phiStep_grow var s j
    have hr := ih (fun x hx => hj (List.mem_cons_of_mem _ hx)) (phiStep var s j)
    by_cases hin : j ∈ s.2.1
    · have heq : phiStep var s j = s := by simp [phiStep, hin]
      rw [heq] at hr ⊢
      exact ⟨hr.grow, hr.inserted, fun x hx => (List.mem_cons.1 hx).elim (fun h => h ▸ hr.inserted hin) (fun h => hr.joined h),
        hr.added, hr.work, hr.measure, hr.only,
        fun x hx => (hr.fromJoins x hx).imp_right (List.mem_cons_of_mem _),
        fun x hx => (hr.workJoins x hx).imp_right (List.mem_cons_of_mem _)⟩
    · have heq : phiStep var s j = (s.1.updateBlock j (phiInsert var ⟨j, var, (s.1.predecessors j).map fun pred => (pred, .var var)⟩),
          j :: s.2.1, j :: s.2.2) := by simp [phiStep, hin]
      have hg₁ : PhiGrow (· = var) s.1 (phiStep var s j).1 := hstep
      rw [heq] at hr hg₁ ⊢
      have hjm : j ∈ (js.foldl (phiStep var) (s.1.updateBlock j (phiInsert var ⟨j, var, (s.1.predecessors j).map fun pred => (pred, .var var)⟩),
          j :: s.2.1, j :: s.2.2)).2.1 := hr.inserted (by simp)
      refine ⟨hg₁.trans hr.grow, fun x hx => hr.inserted (List.mem_cons_of_mem _ hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hjm
        · exact hr.joined hx
      · intro x hx
        rcases hr.added x hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine Or.inr ⟨?_, hr.work (by simp)⟩
            refine HasPhi.grow ?_ hr.grow
            intro c hc
            rw [block_updateBlock_same _ _ _ (fun b _ => phiInsert_tid _ _ b)] at hc
            cases hb : s.1.block x with
            | none => simp [hb] at hc
            | some b =>
              simp only [hb, Option.map_some, Option.some.injEq] at hc
              subst hc
              simp only [phiInsert]
              split
              · rename_i hany
                obtain ⟨φ, hφ, he⟩ := List.any_eq_true.1 hany
                exact ⟨φ, hφ, by simpa using he⟩
              · exact ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl⟩
          · exact Or.inl hx
        · exact Or.inr hx
      · intro x hx
        exact hr.work (List.mem_cons_of_mem _ hx)
      · have hm := hr.measure
        simp only at hm
        have hlt : nodes.countP (fun t => decide (t ∉ j :: s.2.1)) < nodes.countP (fun t => decide (t ∉ s.2.1)) := by
          apply countP_lt
          · intro y _ hy
            simp only [List.mem_cons, not_or, decide_eq_true_eq] at hy ⊢
            exact hy.2
          · refine ⟨j, hj (by simp), by simpa using hin, by simp⟩
        simp only [List.length_cons] at hm
        omega
      · intro n x c hx hc hp
        obtain ⟨i, hi, hall⟩ := hg₁.blocks n x hx
        rcases hr.only n _ c hi hc hp with h | h
        · obtain ⟨φ, hφ, he⟩ := h
          rcases List.mem_append.1 hφ with hφ | hφ
          · exact Or.inl ⟨φ, hφ, he⟩
          · refine Or.inr ?_
            -- only the block named by the step gained a phi
            by_cases hnj : n = j
            · subst hnj
              exact hjm
            · exfalso
              rw [block_updateBlock_ne _ _ (fun b _ => phiInsert_tid _ _ b) hnj, hx] at hi
              simp only [Option.some.injEq] at hi
              have hl : (x.phis ++ i).length = x.phis.length := by
                have := congrArg Blk.phis hi
                simpa using (congrArg List.length this).symm
              have hi0 : i = [] := by
                simpa using hl
              rw [hi0] at hφ
              simp at hφ
        · exact Or.inr h
      · intro x hx
        rcases hr.fromJoins x hx with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (by simp)
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro x hx
        rcases hr.workJoins x hx with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (by simp)
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The iterated dominance frontier of a set of blocks. -/
inductive IteratedFrontier (frontier : List (Tid × List Tid)) (D : Tid → Prop) : Tid → Prop where
  | base {u j} : D u → j ∈ (Assoc.get u frontier).getD [] → IteratedFrontier frontier D j
  | step {u j} : IteratedFrontier frontier D u → j ∈ (Assoc.get u frontier).getD [] → IteratedFrontier frontier D j

/-- What one variable's worklist loop establishes. -/
private structure PhiLoop (var : Var) (frontier : List (Tid × List Tid)) (cfg out : Cfg) (work I : List Tid) (I' : List Tid) : Prop where
  grow : PhiGrow (· = var) cfg out
  inserted : I ⊆ I'
  phi : ∀ j ∈ I', j ∈ I ∨ HasPhi out var j
  closed : ∀ u, (u ∈ work ∨ (u ∈ I' ∧ u ∉ I)) → ∀ j ∈ (Assoc.get u frontier).getD [], j ∈ I'
  only : OnlyAt cfg out var I'
  iter : ∀ D : Tid → Prop, (∀ u ∈ work, D u ∨ IteratedFrontier frontier D u) →
    ∀ j ∈ I', j ∈ I ∨ IteratedFrontier frontier D j

private theorem insertPhisForVar_spec (var : Var) (frontier : List (Tid × List Tid)) (nodes : List Tid)
    (hF : ∀ u, ∀ j ∈ (Assoc.get u frontier).getD [], j ∈ nodes) (fuel : Nat) (cfg : Cfg) (work I : List Tid)
    (hfuel : work.length + nodes.countP (fun t => decide (t ∉ I)) < fuel) :
    ∃ I', PhiLoop var frontier cfg (insertPhisForVar cfg frontier var fuel work I) work I I' := by
  induction fuel generalizing cfg work I with
  | zero => omega
  | succ fuel ih =>
    match work with
    | [] =>
      refine ⟨I, PhiGrow.refl _ _, List.Subset.refl _, fun j h => Or.inl h, ?_, ?_, fun _ _ j h => Or.inl h⟩
      · rintro u (h | ⟨h, hn⟩)
        · simp at h
        · exact absurd h hn
      · intro n x c hx hc hp
        have hc' : cfg.block n = some c := hc
        rw [hx] at hc'
        cases hc'
        exact Or.inl hp
    | t :: work =>
      rw [insertPhisForVar_succ]
      have hfold := phiFold_spec var nodes ((Assoc.get t frontier).getD []) (fun j hj => hF t j hj) (cfg, I, work)
      generalize hS : ((Assoc.get t frontier).getD []).foldl (phiStep var) (cfg, I, work) = S at hfold ⊢
      have hm : S.2.2.length + nodes.countP (fun x => decide (x ∉ S.2.1)) < fuel := by
        have := hfold.measure
        simp only [List.length_cons] at hfuel
        simp only at this
        omega
      obtain ⟨I', hl⟩ := ih S.1 S.2.2 S.2.1 hm
      refine ⟨I', hfold.grow.trans hl.grow, fun x hx => hl.inserted (hfold.inserted hx), ?_, ?_, ?_, ?_⟩
      · intro j hj
        by_cases hjs : j ∈ S.2.1
        · rcases hfold.added j hjs with h | ⟨h, _⟩
          · exact Or.inl h
          · exact Or.inr (HasPhi.grow h hl.grow)
        · rcases hl.phi j hj with h | h
          · exact absurd h hjs
          · exact Or.inr h
      · rintro u (h | ⟨h, hn⟩)
        · rcases List.mem_cons.1 h with rfl | h
          · exact fun j hj => hl.inserted (hfold.joined hj)
          · exact hl.closed u (Or.inl (hfold.work h))
        · by_cases hus : u ∈ S.2.1
          · rcases hfold.added u hus with h' | ⟨_, hw⟩
            · exact absurd h' hn
            · exact hl.closed u (Or.inl hw)
          · exact hl.closed u (Or.inr ⟨h, hus⟩)
      · intro n x c hx hc hp
        obtain ⟨i, hi, _⟩ := hfold.grow.blocks n x hx
        rcases hl.only n _ c hi hc hp with h | h
        · rcases hfold.only n x _ hx hi h with h | h
          · exact Or.inl h
          · exact Or.inr (hl.inserted h)
        · exact Or.inr h
      · intro D hD j hj
        have hjoin : ∀ x ∈ (Assoc.get t frontier).getD [], IteratedFrontier frontier D x := by
          intro x hx
          rcases hD t (by simp) with h | h
          · exact .base h hx
          · exact .step h hx
        rcases hl.iter D (by
            intro u hu
            rcases hfold.workJoins u hu with h | h
            · exact hD u (List.mem_cons_of_mem _ h)
            · exact Or.inr (hjoin u h)) j hj with h | h
        · rcases hfold.fromJoins j h with h | h
          · exact Or.inl h
          · exact Or.inr (hjoin j h)
        · exact Or.inr h

/-- Phi placement is closed under the dominance frontier: a block defining a variable has a phi for
it at every block in its frontier. -/
private abbrev FrontierClosed (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Var) : Prop :=
  ∀ u x, cfg.block u = some x → var ∈ x.definedVars → ∀ j ∈ (Assoc.get u frontier).getD [], HasPhi cfg var j

private theorem FrontierClosed.grow {allowed : Var → Prop} {a b : Cfg} {F : List (Tid × List Tid)} {var : Var}
    (h : FrontierClosed a F var) (hg : PhiGrow allowed a b) (hv : ¬ allowed var) : FrontierClosed b F var := by
  intro u x hx hd j hj
  cases ha : a.block u with
  | none =>
    rw [hg.none u ha] at hx
    cases hx
  | some y =>
    obtain ⟨i, hi, hall⟩ := hg.blocks u y ha
    rw [hi] at hx
    cases hx
    refine HasPhi.grow (h u y ha ?_ j hj) hg
    rw [mem_definedVars] at hd ⊢
    rcases hd with ⟨φ, hφ, he⟩ | hd
    · rcases List.mem_append.1 hφ with hφ | hφ
      · exact Or.inl ⟨φ, hφ, he⟩
      · exact absurd (he ▸ (hall φ hφ).1) hv
    · exact Or.inr hd

private theorem IteratedFrontier.mono {F : List (Tid × List Tid)} {D D' : Tid → Prop} (hD : ∀ u, D u → D' u) {j : Tid}
    (h : IteratedFrontier F D j) : IteratedFrontier F D' j := by
  induction h with
  | base hu hj => exact .base (hD _ hu) hj
  | step _ hj ih => exact .step ih hj

/-- The blocks of a CFG that assign a variable. -/
private abbrev DefSites (cfg : Cfg) (var : Var) (u : Tid) : Prop := ∃ y ∈ cfg.blocks, y.tid = u ∧ var ∈ y.definedVars

private theorem DefSites.of_grow {allowed : Var → Prop} {a b : Cfg} {var : Var} (hg : PhiGrow allowed a b)
    (hv : ¬ allowed var) {u : Tid} (h : DefSites b var u) : DefSites a var u := by
  obtain ⟨y, hy, ht, hd⟩ := h
  obtain ⟨x, hx, h₁, h₂, h₃⟩ := hg.mem y hy
  refine ⟨x, hx, h₁.symm.trans ht, ?_⟩
  rw [mem_definedVars] at hd ⊢
  rcases hd with ⟨φ, hφ, he⟩ | ⟨d, hd, he⟩
  · rcases h₃ φ hφ with h | h
    · exact Or.inl ⟨φ, h, he⟩
    · exact absurd (he ▸ h) hv
  · exact Or.inr ⟨d, h₂ ▸ hd, he⟩

private theorem insertAllPhis_spec (frontier : List (Tid × List Tid)) (nodes : List Tid)
    (hF : ∀ u, ∀ j ∈ (Assoc.get u frontier).getD [], j ∈ nodes) (vars : List Var) (hnd : vars.Nodup) (cfg : Cfg)
    (hnodes : nodes.length = cfg.blocks.length) :
    PhiGrow (· ∈ vars) cfg (insertAllPhis cfg frontier vars) ∧
      (∀ var ∈ vars, FrontierClosed (insertAllPhis cfg frontier vars) frontier var) ∧
      ∀ var ∈ vars, ∀ n x c, cfg.block n = some x → (insertAllPhis cfg frontier vars).block n = some c →
        (∃ φ ∈ c.phis, φ.var = var) → (∃ φ ∈ x.phis, φ.var = var) ∨ IteratedFrontier frontier (DefSites cfg var) n := by
  induction vars generalizing cfg with
  | nil => exact ⟨PhiGrow.refl _ _, by simp, by simp⟩
  | cons v vs ih =>
    rw [insertAllPhis_cons]
    obtain ⟨hvn, hvs⟩ := List.nodup_cons.1 hnd
    let defs := cfg.blocks.filterMap fun blk => if blk.defines v then some blk.tid else none
    have hlen : defs.length ≤ cfg.blocks.length := by
      exact List.length_filterMap_le _ _
    obtain ⟨I', hl⟩ := insertPhisForVar_spec v frontier nodes hF (cfg.blocks.length * 2 + 1) cfg defs [] (by
      have := List.countP_le_length (l := nodes) (p := fun t => decide (t ∉ ([] : List Tid)))
      omega)
    have hdefs : insertPhisForVar cfg frontier v (cfg.blocks.length * 2 + 1)
        (cfg.blocks.filterMap fun blk => if blk.defines v then some blk.tid else none) [] =
        insertPhisForVar cfg frontier v (cfg.blocks.length * 2 + 1) defs [] := rfl
    rw [hdefs]
    generalize hout : insertPhisForVar cfg frontier v (cfg.blocks.length * 2 + 1) defs [] = c₁ at hl
    have hlen₁ : nodes.length = c₁.blocks.length := by
      have := congrArg List.length hl.grow.tids
      simp only [List.length_map] at this
      omega
    obtain ⟨hg, hc, hmin⟩ := ih hvs c₁ hlen₁
    have hdefsites : ∀ u ∈ defs, DefSites cfg v u := by
      intro u hu
      obtain ⟨y, hy, hyu⟩ := List.mem_filterMap.1 hu
      split at hyu
      · rename_i hd
        cases hyu
        exact ⟨y, hy, rfl, (defines_iff y v).1 hd⟩
      · cases hyu
    refine ⟨(hl.grow.mono (fun x hx => by simp [hx])).trans (hg.mono fun x hx => List.mem_cons_of_mem _ hx), ?_, ?_⟩
    · have hclosed₁ : FrontierClosed c₁ frontier v := by
        intro u x hx hd j hj
        have hmem : j ∈ I' := by
          cases ha : cfg.block u with
          | none =>
            rw [hl.grow.none u ha] at hx
            cases hx
          | some y =>
            obtain ⟨i, hi, hall⟩ := hl.grow.blocks u y ha
            rw [hi] at hx
            simp only [Option.some.injEq] at hx
            subst hx
            refine hl.closed u ?_ j hj
            by_cases hdy : v ∈ y.definedVars
            · refine Or.inl ?_
              have hm := block_some ha
              refine List.mem_filterMap.2 ⟨y, hm.1, ?_⟩
              simp [(defines_iff y v).2 hdy, hm.2]
            · refine Or.inr ⟨?_, by simp⟩
              rw [mem_definedVars] at hd hdy
              have hp : ∃ φ ∈ (y.phis ++ i), φ.var = v := by
                rcases hd with h | h
                · exact h
                · exact absurd (Or.inr h) hdy
              rcases hl.only u y _ ha hi hp with h | h
              · exact absurd (Or.inl h) hdy
              · exact h
        rcases hl.phi j hmem with h | h
        · simp at h
        · exact h
      intro var hvar
      rcases List.mem_cons.1 hvar with rfl | hvar
      · exact hclosed₁.grow hg hvn
      · exact hc var hvar
    · intro var hvar n x c hx hcb hp
      obtain ⟨i, hi, hall⟩ := hl.grow.blocks n x hx
      rcases List.mem_cons.1 hvar with rfl | hvar
      · obtain ⟨i₂, hi₂, hall₂⟩ := hg.blocks n _ hi
        rw [hi₂] at hcb
        cases hcb
        have hp' : ∃ φ ∈ x.phis ++ i, φ.var = var := by
          obtain ⟨φ, hφ, he⟩ := hp
          rcases List.mem_append.1 hφ with hφ | hφ
          · exact ⟨φ, hφ, he⟩
          · exact absurd (he ▸ (hall₂ φ hφ).1) hvn
        rcases hl.only n x _ hx hi hp' with h | h
        · exact Or.inl h
        · rcases hl.iter (DefSites cfg var) (fun u hu => Or.inl (hdefsites u hu)) n h with h | h
          · simp at h
          · exact Or.inr h
      · have hne : var ≠ v := fun heq => hvn (heq ▸ hvar)
        rcases hmin var hvar n _ c hi hcb hp with h | h
        · obtain ⟨φ, hφ, he⟩ := h
          rcases List.mem_append.1 hφ with hφ | hφ
          · exact Or.inl ⟨φ, hφ, he⟩
          · exact absurd (he.symm.trans (hall φ hφ).1) hne
        · refine Or.inr (h.mono fun u hu => ?_)
          exact DefSites.of_grow hl.grow (fun heq => hne heq) hu

/-! ### Correctness of renaming -/

/-- Variables whose value the SSA form tracks: those the subroutine mentions and all unversioned ones.
Versions that nothing mentions may be reused for issued names. -/
def Tracked (U : List Var) (w : Var) : Prop := w.index = 0 ∨ w ∈ U

/-- Variables a subroutine mentions in its connected CFG. -/
private abbrev mentioned (blocks : List Blk) : List Var := blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars

/-- What a renaming state guarantees: one stack per variable, stacks hold versions of their variable
below the counter, and counters are above every tracked variable. -/
private structure RenameWf (U : List Var) (st : RenameState) : Prop where
  keys : (st.stacks.map Prod.fst).Nodup
  stack : ∀ k, ∀ y ∈ stackOf st k, y.base = k.base ∧ y.index < counterOf st k
  seed : ∀ w, Tracked U w → w.index < counterOf st w

private theorem RenameWf.of_stack {U : List Var} {st st' : RenameState} (h : RenameWf U st)
    (hk : (st'.stacks.map Prod.fst).Nodup) (hs : ∀ k, stackOf st' k = stackOf st k)
    (hc : ∀ w, counterOf st w ≤ counterOf st' w) : RenameWf U st' :=
  ⟨hk, fun k y hy => by
    rw [hs] at hy
    have := h.stack k y hy
    have := hc k
    exact ⟨(h.stack k y hy).1, by omega⟩,
    fun w hw => Nat.lt_of_lt_of_le (h.seed w hw) (hc w)⟩

private theorem keys_put {β : Type} (k : Var) (v : β) (l : List (Var × β)) (h : (l.map Prod.fst).Nodup) :
    ((Assoc.put k v l).map Prod.fst).Nodup := by
  simp only [Assoc.put, List.map_cons, List.nodup_cons]
  constructor
  · simp only [List.mem_map, List.mem_filter, not_exists, not_and]
    rintro ⟨a, b⟩ ⟨_, hne⟩ rfl
    simp at hne
  · exact (List.filter_sublist.map Prod.fst).nodup h

private theorem keys_newName (o : Var) (st : RenameState) (h : (st.stacks.map Prod.fst).Nodup) :
    ((newName o st).2.stacks.map Prod.fst).Nodup := by
  rw [newName_stacks]
  exact keys_put _ _ _ h

private theorem keys_renamePhis (phis : List Phi) (st : RenameState) (h : (st.stacks.map Prod.fst).Nodup) :
    ((renamePhis phis st).2.stacks.map Prod.fst).Nodup := by
  induction phis generalizing st with
  | nil => exact h
  | cons p ps ih =>
    rw [renamePhis_cons]
    exact ih _ (keys_newName _ _ h)

private theorem keys_renameDefs (defs : List Def) (st : RenameState) (h : (st.stacks.map Prod.fst).Nodup) :
    ((renameDefs defs st).2.stacks.map Prod.fst).Nodup := by
  induction defs generalizing st with
  | nil => exact h
  | cons d ds ih =>
    rw [renameDefs_cons]
    exact ih _ (keys_newName _ _ h)

private theorem keys_popVars (vars : List Var) (st : RenameState) :
    (popVars vars st).stacks.map Prod.fst = st.stacks.map Prod.fst := by
  induction vars generalizing st with
  | nil => rfl
  | cons v vs ih =>
    rw [popVars_cons, ih]
    show (st.stacks.map _).map Prod.fst = _
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    simp only [Function.comp]
    split <;> rfl

private theorem renameBlock_keys (idom : List (Tid × Tid)) (fuel : Nat) (t : Tid) (cfg : Cfg) (st : RenameState)
    (h : (st.stacks.map Prod.fst).Nodup) : ((renameBlock idom fuel t cfg st).2.stacks.map Prod.fst).Nodup := by
  induction fuel generalizing t cfg st with
  | zero => exact h
  | succ fuel ih =>
    rw [renameBlock_succ]
    split
    · exact h
    · rename_i block _
      simp only
      rw [keys_popVars]
      have hchildren : ∀ (children : List Tid) (state : Cfg × RenameState),
          (state.2.stacks.map Prod.fst).Nodup → ((children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).2.stacks.map Prod.fst).Nodup := by
        intro children
        induction children with
        | nil => exact fun _ h => h
        | cons c cs ihc =>
          intro state hs
          simp only [List.foldl_cons]
          exact ihc _ (ih c state.1 state.2 hs)
      exact hchildren _ _ (keys_renameDefs _ _ (keys_renamePhis _ _ h))

private theorem RenameWf.push {U : List Var} {st : RenameState} (h : RenameWf U st) (o : Var) :
    RenameWf U (newName o st).2 := by
  refine ⟨keys_newName _ _ h.keys, ?_, fun w hw => ?_⟩
  · intro k y hy
    rw [stackOf_newName] at hy
    split at hy
    · rename_i hk
      subst hk
      rcases List.mem_cons.1 hy with hy | hy
      · rw [hy]
        have := counterOf_newName_same k st
        refine ⟨rfl, ?_⟩
        have hi : (newName k st).1.index = counterOf st k := rfl
        omega
      · have := h.stack _ y hy
        have := counterOf_newName_mono k k st
        exact ⟨(h.stack _ y hy).1, by omega⟩
    · have := h.stack _ y hy
      have := counterOf_newName_mono o k st
      exact ⟨(h.stack _ y hy).1, by omega⟩
  · have := h.seed w hw
    have := counterOf_newName_mono o w st
    omega

private theorem topName_cases (w : Var) (st : RenameState) : topName w st = w ∨ topName w st ∈ stackOf st w := by
  rw [topName_of_stack]
  cases hl : (stackOf st w).head? with
  | none => exact Or.inl rfl
  | some y =>
    refine Or.inr ?_
    simpa using List.mem_of_head? hl

private theorem RenameWf.top {U : List Var} {st : RenameState} (h : RenameWf U st) {w : Var} (hw : Tracked U w) :
    (topName w st).base = w.base ∧ (topName w st).index < counterOf st w := by
  rcases topName_cases w st with he | hm
  · rw [he]
    exact ⟨rfl, h.seed w hw⟩
  · exact h.stack w _ hm

/-- A freshly issued name differs from what every tracked variable currently reads. -/
private theorem RenameWf.fresh {U : List Var} {st : RenameState} (h : RenameWf U st) (o : Var) {w : Var}
    (hw : Tracked U w) : topName w st ≠ (newName o st).1 := by
  intro heq
  obtain ⟨hb, hi⟩ := h.top hw
  rw [heq] at hb hi
  have hidx : (newName o st).1.index = counterOf st o := rfl
  have hc : counterOf st w = counterOf st o := by
    have hb' : w.base = o.base := hb.symm
    simp only [counterOf, hb']
  omega

private theorem get_ssaReplacements (st : RenameState) (h : (st.stacks.map Prod.fst).Nodup) (v : Var) :
    Assoc.get v (ssaReplacements st) = (stackOf st v).head?.map Exp.var := by
  have key : ∀ l : List (Var × List Var), (l.map Prod.fst).Nodup →
      List.lookup v (l.filterMap fun entry => entry.2.head?.map fun var => (entry.1, Exp.var var)) =
        ((List.lookup v l).getD []).head?.map Exp.var := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e es ih =>
      intro hl
      obtain ⟨a, s⟩ := e
      simp only [List.map_cons, List.nodup_cons] at hl
      by_cases hv : v = a
      · subst hv
        have hnone : List.lookup v es = none := by
          cases hg : List.lookup v es with
          | none => rfl
          | some x =>
            exact absurd (List.mem_map.2 ⟨(v, x), get_mem_env' (k := v) (T := es) hg, rfl⟩) hl.1
        have hih := ih hl.2
        rw [hnone] at hih
        cases hs : s.head? with
        | none => simp [hs, hih]
        | some y => simp [hs]
      · have hb : (v == a) = false := by simpa using hv
        have hih := ih hl.2
        cases hs : s.head? with
        | none => simp [hs, hb, hih, List.lookup]
        | some y => simp [hs, hb, hih, List.lookup]
  exact key st.stacks h

private theorem ssaReplacements_vars (st : RenameState) {e : Var × Exp} (he : e ∈ ssaReplacements st) :
    isVarExp e.2 = true := by
  obtain ⟨entry, _, hm⟩ := List.mem_filterMap.1 he
  obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hm
  rfl

/-- Renaming a tracked read gives the value of the original variable in the renamed run. -/
private theorem eval_renameExp {U : List Var} {st : RenameState} (h : RenameWf U st) {E E' : Env} (e : Exp)
    (hI : ∀ w, Tracked U w → Bil.lookup E' (topName w st) = Bil.lookup E w)
    (hU : ∀ x ∈ Bil.freeVars e, Tracked U x) : evalExp E' (renameExp st e) = evalExp E e := by
  apply Bap.Proofs.Bil.evalExp_substitute
  intro v hv
  have htrack := hU v ((Bap.Proofs.Bil.mem_freeVars_iff v e).2 hv)
  have hrw := hI v htrack
  rw [topName_of_stack] at hrw
  rw [get_ssaReplacements st h.keys]
  cases hl : (stackOf st v).head? with
  | none =>
    rw [hl] at hrw
    exact hrw
  | some y =>
    rw [hl] at hrw
    exact hrw

/-- Replacing variables by variables keeps the shape of an expression at its root. -/
private theorem substitute_shape (rs : List (Var × Exp)) (hrs : ∀ e ∈ rs, isVarExp e.2 = true) (e : Exp) :
    isVarExp (Bil.substitute rs e) = isVarExp e := by
  cases e with
  | var v =>
    simp only [Bil.substitute]
    cases hg : Assoc.get v rs with
    | none => rfl
    | some r =>
      have := hrs _ (get_mem_env hg)
      simp only [Option.getD_some]
      cases r <;> simp_all [isVarExp]
  | letIn v val body =>
    simp only [Bil.substitute]
    split <;> rfl
  | _ => rfl

private theorem phiValue_renameExp {U : List Var} {st : RenameState} (h : RenameWf U st) {E E' : Env} (e : Exp)
    (hI : ∀ w, Tracked U w → Bil.lookup E' (topName w st) = Bil.lookup E w)
    (hU : ∀ x ∈ Bil.freeVars e, Tracked U x) : phiValue E' (renameExp st e) = phiValue E e :=
  phiValue_congr (eval_renameExp h e hI hU) (substitute_shape _ (fun _ he => ssaReplacements_vars st he) e)

/-- Renaming keeps a definition's value and base; only the version of its variable changes. -/
private abbrev storeShape (tr : List (Var × Value)) : List (Var × Value) := tr.map fun e => (e.1.base, e.2)

/-- Renamed definitions run in step with the original ones. -/
private theorem renameDefs_sim {U : List Var} (defs : List Def) (hreads : ∀ d ∈ defs, ∀ x ∈ Bil.freeVars d.rhs, Tracked U x)
    {st : RenameState} (hst : RenameWf U st) {E E' : Env}
    (hI : ∀ w, Tracked U w → Bil.lookup E' (topName w st) = Bil.lookup E w)
    {r : Env × List (Var × Value)} (h : execDefs E defs = .ok r) :
    ∃ r', execDefs E' (renameDefs defs st).1 = .ok r' ∧
      (∀ w, Tracked U w → Bil.lookup r'.1 (topName w (renameDefs defs st).2) = Bil.lookup r.1 w) ∧
      storeShape r'.2 = storeShape r.2 := by
  induction defs generalizing st E E' r with
  | nil =>
    simp only [execDefs, Except.ok.injEq] at h
    subst h
    exact ⟨(E', []), rfl, hI, rfl⟩
  | cons d ds ih =>
    obtain ⟨v, r₁, hv, hr₁, rfl⟩ := execDefs_cons h
    have hv' : evalExp E' (renameExp st d.rhs) = .ok v := by
      rw [eval_renameExp hst d.rhs hI (hreads d (by simp))]
      exact hv
    have hI' : ∀ w, Tracked U w → Bil.lookup (Bil.bind E' (newName d.var st).1 v) (topName w (newName d.var st).2) =
        Bil.lookup (Bil.bind E d.var v) w := by
      intro w hw
      by_cases hwd : w = d.var
      · subst hwd
        rw [topName_newName, lookup_bind_same, lookup_bind_same]
      · rw [topName_newName_other _ _ _ hwd, lookup_bind_ne _ _ (hst.fresh d.var hw), lookup_bind_ne _ _ hwd]
        exact hI w hw
    obtain ⟨r', hr', hl, hs⟩ := ih (fun c hc => hreads c (List.mem_cons_of_mem _ hc)) (hst.push d.var) hI' hr₁
    rw [renameDefs_cons]
    refine ⟨_, execDefs_cons_ok hv' hr', hl, ?_⟩
    have hshape' : writesMemory E' (renameExp st d.rhs) = writesMemory E d.rhs := by
      refine writesMemory_substitute d.rhs _ E' E ?_ ?_
      · intro r hr F
        have := ssaReplacements_vars st hr
        cases hr₂ : r.2 <;> simp_all [isVarExp, writesMemory]
      · intro v hv
        have hrw := hI v (hreads d (by simp) v ((Bap.Proofs.Bil.mem_freeVars_iff _ _).2 hv))
        rw [topName_of_stack] at hrw
        rw [get_ssaReplacements st hst.keys]
        cases hl : (stackOf st v).head? with
        | none =>
          rw [hl] at hrw
          exact hrw
        | some y =>
          rw [hl] at hrw
          exact hrw
    simp only [hshape']
    split
    · simp only [storeShape, List.map_cons, hs]
      rfl
    · exact hs

/-- A phi with its inputs rewritten. -/
private abbrev setVals (f : Tid × Exp → Tid × Exp) (phi : Phi) : Phi := { phi with values := phi.values.map f }

private theorem renamePhis_setVals (f : Tid × Exp → Tid × Exp) (phis : List Phi) (st : RenameState) :
    renamePhis (phis.map (setVals f)) st = ((renamePhis phis st).1.map (setVals f), (renamePhis phis st).2) := by
  induction phis generalizing st with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, renamePhis_cons, renamePhis_cons, ih]
    rfl

private theorem renamePhis_nil (st : RenameState) : renamePhis [] st = ([], st) := rfl
private theorem renameDefs_nil (st : RenameState) : renameDefs [] st = ([], st) := rfl

/-- Renamed phis read their renamed inputs and assign the current names. -/
private theorem renamePhis_sim {U : List Var} (pred : Tid) (rn : Exp → Exp) (f : Tid × Exp → Tid × Exp)
    (hf : ∀ phi : Phi, Assoc.get pred (phi.values.map f) = (Assoc.get pred phi.values).map rn)
    {read read' : Env} (phis : List Phi)
    (hval : ∀ phi ∈ phis, ∀ e, Assoc.get pred phi.values = some e → phiValue read' (rn e) = phiValue read e)
    {st : RenameState} (hst : RenameWf U st) {acc acc' r : Env}
    (hI : ∀ w, Tracked U w → (∀ phi ∈ phis, phi.var ≠ w) → Bil.lookup acc' (topName w st) = Bil.lookup acc w)
    (h : execPhis pred read phis acc = .ok r) :
    ∃ r', execPhis pred read' ((renamePhis phis st).1.map (setVals f)) acc' = .ok r' ∧
      ∀ w, Tracked U w → Bil.lookup r' (topName w (renamePhis phis st).2) = Bil.lookup r w := by
  induction phis generalizing st acc acc' with
  | nil =>
    simp only [execPhis, Except.ok.injEq] at h
    subst h
    exact ⟨acc', rfl, fun w hw => hI w hw (by simp)⟩
  | cons p ps ih =>
    simp only [execPhis] at h
    split at h
    · cases h
    · rename_i e hget
      split at h
      · cases h
      · rename_i value hv
        have hv' : phiValue read' (rn e) = .ok value := by
          rw [hval p (by simp) e hget]
          exact hv
        have hI' : ∀ w, Tracked U w → (∀ phi ∈ ps, phi.var ≠ w) →
            Bil.lookup (assignPhi acc' (newName p.var st).1 value) (topName w (newName p.var st).2) =
              Bil.lookup (assignPhi acc p.var value) w := by
          intro w hw hn
          by_cases hwp : w = p.var
          · subst hwp
            rw [topName_newName, lookup_assignPhi_same, lookup_assignPhi_same]
            cases value <;> rfl
          · rw [topName_newName_other _ _ _ hwp, lookup_assignPhi_ne _ _ (hst.fresh p.var hw),
              lookup_assignPhi_ne _ _ hwp]
            refine hI w hw ?_
            intro phi hphi
            rcases List.mem_cons.1 hphi with rfl | hphi
            · exact Ne.symm hwp
            · exact hn phi hphi
        obtain ⟨r', hr', hl⟩ := ih (fun phi hphi => hval phi (List.mem_cons_of_mem _ hphi)) (hst.push p.var) hI' h
        rw [renamePhis_cons]
        refine ⟨r', ?_, hl⟩
        simp only [List.map_cons, execPhis]
        have hg : Assoc.get pred (setVals f { p with var := (newName p.var st).1 }).values = some (rn e) := by
          show Assoc.get pred (p.values.map f) = _
          rw [hf, hget]
          rfl
        rw [hg]
        simp only [hv']
        exact hr'

private theorem execPhis_error_append {pred : Tid} {read : Env} {xs : List Phi} (ys : List Phi) {acc : Env} {m : String}
    (h : execPhis pred read xs acc = .error m) : execPhis pred read (xs ++ ys) acc = .error m := by
  induction xs generalizing acc with
  | nil => simp [execPhis] at h
  | cons p ps ih =>
    simp only [execPhis, List.cons_append] at h ⊢
    cases he : Assoc.get pred p.values with
    | none =>
      simp only [he] at h ⊢
      exact h
    | some e =>
      simp only [he] at h ⊢
      cases hv : phiValue read e with
      | error m' =>
        simp only [hv] at h ⊢
        exact h
      | ok v =>
        simp only [hv] at h ⊢
        exact ih h

/-- A failing phi fails under the renaming too, as a phi reads nothing but the environment on entry. -/
private theorem renamePhis_error (pred : Tid) (rn : Exp → Exp) (f : Tid × Exp → Tid × Exp)
    (hf : ∀ phi : Phi, Assoc.get pred (phi.values.map f) = (Assoc.get pred phi.values).map rn)
    {read read' : Env} (phis : List Phi)
    (hval : ∀ phi ∈ phis, ∀ e, Assoc.get pred phi.values = some e → phiValue read' (rn e) = phiValue read e)
    (st : RenameState) {acc acc' : Env} {m : String} (h : execPhis pred read phis acc = .error m) :
    execPhis pred read' ((renamePhis phis st).1.map (setVals f)) acc' = .error m := by
  induction phis generalizing st acc acc' with
  | nil => simp [execPhis] at h
  | cons p ps ih =>
    rw [renamePhis_cons]
    simp only [List.map_cons, execPhis]
    have hg : Assoc.get pred (setVals f { p with var := (newName p.var st).1 }).values = (Assoc.get pred p.values).map rn := hf p
    rw [hg]
    simp only [execPhis] at h
    cases he : Assoc.get pred p.values with
    | none =>
      simp only [he] at h
      exact h
    | some e =>
      simp only [he, Option.map_some] at h ⊢
      rw [hval p (by simp) e he]
      cases hv : phiValue read e with
      | error m' =>
        simp only [hv] at h ⊢
        exact h
      | ok v =>
        simp only [hv] at h ⊢
        exact ih (fun phi hphi => hval phi (List.mem_cons_of_mem _ hphi)) _ h

/-- A failing definition fails under the renaming too. -/
private theorem renameDefs_error {U : List Var} (defs : List Def) (hreads : ∀ d ∈ defs, ∀ x ∈ Bil.freeVars d.rhs, Tracked U x)
    {st : RenameState} (hst : RenameWf U st) {E E' : Env}
    (hI : ∀ w, Tracked U w → Bil.lookup E' (topName w st) = Bil.lookup E w)
    {m : String} (h : execDefs E defs = .error m) : execDefs E' (renameDefs defs st).1 = .error m := by
  induction defs generalizing st E E' with
  | nil => simp [execDefs] at h
  | cons d ds ih =>
    rw [renameDefs_cons]
    simp only [execDefs] at h ⊢
    rw [eval_renameExp hst d.rhs hI (hreads d (by simp))]
    cases hv : evalExp E d.rhs with
    | error m' =>
      simp only [hv] at h ⊢
      exact h
    | ok v =>
      simp only [hv] at h ⊢
      have hI' : ∀ w, Tracked U w → Bil.lookup (Bil.bind E' (newName d.var st).1 v) (topName w (newName d.var st).2) =
          Bil.lookup (Bil.bind E d.var v) w := by
        intro w hw
        by_cases hwd : w = d.var
        · subst hwd
          rw [topName_newName, lookup_bind_same, lookup_bind_same]
        · rw [topName_newName_other _ _ _ hwd, lookup_bind_ne _ _ (hst.fresh d.var hw), lookup_bind_ne _ _ hwd]
          exact hI w hw
      cases hr : execDefs (Bil.bind E d.var v) ds with
      | error m' =>
        rw [hr] at h
        simp only at h
        cases h
        rw [ih (fun c hc => hreads c (List.mem_cons_of_mem _ hc)) (hst.push d.var) hI' hr]
      | ok r =>
        rw [hr] at h
        simp at h

private theorem get_trivial_values (pred : Tid) (preds : List Tid) (hp : pred ∈ preds) (var : Var) :
    Assoc.get pred (preds.map fun p => (p, Exp.var var)) = some (.var var) := by
  induction preds with
  | nil => simp at hp
  | cons a as ih =>
    by_cases ha : pred = a
    · subst ha
      simp [Assoc.get]
    · have hb : (pred == a) = false := by simpa using ha
      have hm := (List.mem_cons.1 hp).resolve_left ha
      have ih' : List.lookup pred (as.map fun p => (p, Exp.var var)) = some (.var var) := ih hm
      simp [Assoc.get, List.lookup, hb, ih']

/-- Inserted phis only copy each variable to itself, so they change no variable's value. -/
private theorem execPhis_insert (pred : Tid) (read : Env) (ins : List Phi) {acc : Env}
    (hins : ∀ φ ∈ ins, Assoc.get pred φ.values = some (.var φ.var) ∧ Bil.lookup acc φ.var = Bil.lookup read φ.var) :
    ∃ r, execPhis pred read ins acc = .ok r ∧ ∀ w, Bil.lookup r w = Bil.lookup acc w := by
  induction ins generalizing acc with
  | nil => exact ⟨acc, rfl, fun _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨hget, hl⟩ := hins p (by simp)
    have hsame : ∀ w, Bil.lookup (assignPhi acc p.var (match Bil.lookup read p.var with
        | .ok value => some value
        | .error _ => none)) w = Bil.lookup acc w := by
      intro w
      by_cases hw : w = p.var
      · subst hw
        rw [lookup_assignPhi_same, phiResult_of_lookup _ rfl, hl]
      · exact lookup_assignPhi_ne _ _ hw
    have hrest : ∀ φ ∈ ps, Assoc.get pred φ.values = some (.var φ.var) ∧
        Bil.lookup (assignPhi acc p.var (match Bil.lookup read p.var with
          | .ok value => some value
          | .error _ => none)) φ.var = Bil.lookup read φ.var := by
      intro φ hφ
      obtain ⟨h₁, h₂⟩ := hins φ (List.mem_cons_of_mem _ hφ)
      exact ⟨h₁, by rw [hsame, h₂]⟩
    obtain ⟨r, hr, hw⟩ := ih hrest
    refine ⟨r, ?_, fun w => by rw [hw, hsame]⟩
    simp only [execPhis, hget, phiValue_var]
    exact hr

private theorem execPhis_append {pred : Tid} {read : Env} {xs ys : List Phi} {acc mid r : Env}
    (h₁ : execPhis pred read xs acc = .ok mid) (h₂ : execPhis pred read ys mid = .ok r) :
    execPhis pred read (xs ++ ys) acc = .ok r := by
  induction xs generalizing acc with
  | nil =>
    simp only [execPhis, Except.ok.injEq] at h₁
    subst h₁
    exact h₂
  | cons p ps ih =>
    simp only [execPhis, List.cons_append] at h₁ ⊢
    cases he : Assoc.get pred p.values with
    | none => simp [he] at h₁
    | some e =>
      simp only [he] at h₁ ⊢
      cases hv : phiValue read e with
      | error m => simp [hv] at h₁
      | ok v =>
        simp only [hv] at h₁ ⊢
        exact ih h₁

open Classical in
/-- Phi inputs after renaming: those of an edge whose source has been processed are renamed under the
names at the exit of that source. Inputs for other sources are left as they were. -/
private noncomputable def doneInput (D : Tid → Prop) (ex : Tid → RenameState) (input : Tid × Exp) : Tid × Exp :=
  if D input.1 then (input.1, renameExp (ex input.1) input.2) else input

private theorem doneInput_congr {D D' : Tid → Prop} {ex ex' : Tid → RenameState}
    (hD : ∀ s, D s ↔ D' s) (hex : ∀ s, D s → ex s = ex' s) : doneInput D ex = doneInput D' ex' := by
  funext input
  by_cases h : D input.1
  · have h' := (hD _).1 h
    rw [doneInput, doneInput, ite_eq_left h, ite_eq_left h', hex _ h]
  · have h' : ¬ D' input.1 := fun x => h ((hD _).2 x)
    rw [doneInput, doneInput, ite_eq_right h, ite_eq_right h']

/-- A block with its phi inputs rewritten. -/
private abbrev withInputs (f : Tid × Exp → Tid × Exp) (b : Blk) : Blk :=
  { b with phis := b.phis.map (setVals f) }

private theorem withInputs_comp (f g : Tid × Exp → Tid × Exp) (b : Blk) :
    { withInputs f b with phis := (withInputs f b).phis.map (fun phi => { phi with values := phi.values.map g }) } =
      withInputs (g ∘ f) b := by
  simp only [withInputs, List.map_map, Function.comp_def]

/-- The state at the exit of a block renamed from `st`. -/
private abbrev exitOf (b : Blk) (st : RenameState) : RenameState := (renameDefs b.defs (renamePhis b.phis st).2).2

/-- A block with its statements renamed from `st`, phi inputs apart. -/
private abbrev renamedStmts (b : Blk) (st ex : RenameState) : Blk :=
  { b with
    phis := (renamePhis b.phis st).1
    defs := (renameDefs b.defs (renamePhis b.phis st).2).1
    jmps := b.jmps.map (Jmp.mapExp (renameExp ex)) }

open Classical in
private noncomputable def stmtForm (V : Tid → Prop) (en ex : Tid → RenameState) (n : Tid) (b : Blk) : Blk :=
  if V n then renamedStmts b (en n) (ex n) else b

/-- Tree facts of an immediate dominator table, as a relation on tids. -/
private abbrev Desc (idom : List (Tid × Tid)) (t n : Tid) : Prop := ∃ k, TreeFrom idom t k n

private structure TreeFacts (idom : List (Tid × Tid)) : Prop where
  fn : ∀ c p q, (c, p) ∈ idom → (c, q) ∈ idom → p = q
  disj : ∀ t c₁ c₂ n, (c₁, t) ∈ idom → (c₂, t) ∈ idom → c₁ ≠ c₂ → Desc idom c₁ n → ¬ Desc idom c₂ n
  up : ∀ c t, (c, t) ∈ idom → ¬ Desc idom c t
  nodup : (idom.map Prod.fst).Nodup

/-- State of the renaming walk. `V` holds the blocks whose statements are renamed; `en n` and `ex n`
are the states on entry to and at the exit of each of them; `Done s n` holds when the inputs of the
phis of `n` for the edge from `s` are renamed. -/
private structure RenameSpec (P cfg : Cfg) (U : List Var) (idom : List (Tid × Tid)) (V : Tid → Prop)
    (Done : Tid → Tid → Prop) (en ex : Tid → RenameState) : Prop where
  graph : cfg.graph = P.graph
  absent : ∀ n, P.block n = none → cfg.block n = none
  block : ∀ n b, P.block n = some b → cfg.block n = some (withInputs (doneInput (Done · n) ex) (stmtForm V en ex n b))
  exits : ∀ n b, P.block n = some b → V n → ex n = exitOf b (en n)
  wf : ∀ n, V n → RenameWf U (en n)
  tree : ∀ c p, (c, p) ∈ idom → V c → V p → ∀ k, stackOf (en c) k = stackOf (ex p) k

/-- The phi inputs a finished visit leaves done: every edge out of a visited block. -/
private abbrev Canon (P : Cfg) (V : Tid → Prop) (s n : Tid) : Prop := V s ∧ n ∈ P.successors s

private abbrev editOf (b : Blk) (st : RenameState) (f : Tid × Exp → Tid × Exp) : Blk → Blk :=
  fun block => { block with
    phis := (renamePhis (b.phis.map (setVals f)) st).1
    defs := (renameDefs b.defs (renamePhis (b.phis.map (setVals f)) st).2).1
    jmps := b.jmps.map (Jmp.mapExp (renameExp (renameDefs b.defs (renamePhis (b.phis.map (setVals f)) st).2).2)) }

private abbrev tableAdd {β : Type} (table : Tid → β) (t : Tid) (v : β) : Tid → β :=
  fun n => if n = t then v else table n

/-- Renaming the statements of an unvisited block. -/
private theorem RenameSpec.visit {P cfg : Cfg} {U : List Var} {idom : List (Tid × Tid)} {V : Tid → Prop}
    {Done : Tid → Tid → Prop} {en ex : Tid → RenameState} (h : RenameSpec P cfg U idom V Done en ex)
    {t : Tid} {b : Blk} (hb : P.block t = some b) (ht : ¬ V t) (hdone : ∀ s n, Done s n → V s)
    {st : RenameState} (hst : RenameWf U st)
    (hpar : ∀ p, (t, p) ∈ idom → V p → ∀ k, stackOf st k = stackOf (ex p) k)
    (hkids : ∀ c, (c, t) ∈ idom → ¬ V c) (hself : (t, t) ∉ idom) :
    RenameSpec P (cfg.updateBlock t (editOf b st (doneInput (Done · t) ex))) U idom (fun n => V n ∨ n = t) Done
      (tableAdd en t st) (tableAdd ex t (exitOf b st)) := by
  have hcongr : ∀ n, doneInput (Done · n) (tableAdd ex t (exitOf b st)) = doneInput (Done · n) ex := by
    intro n
    refine doneInput_congr (fun _ => Iff.rfl) ?_
    intro s hs
    have hne : s ≠ t := fun heq => ht (heq ▸ hdone s n hs)
    simp [tableAdd, hne]
  have hedit_tid : ∀ x, x.tid = t → (editOf b st (doneInput (Done · t) ex) x).tid = x.tid := fun _ _ => rfl
  have hform : ∀ n c, n ≠ t → P.block n = some c →
      stmtForm (fun n => V n ∨ n = t) (tableAdd en t st) (tableAdd ex t (exitOf b st)) n c = stmtForm V en ex n c := by
    intro n c hn _
    unfold stmtForm
    by_cases hv : V n
    · rw [ite_eq_left (Or.inl hv), ite_eq_left hv]
      simp [tableAdd, hn]
    · rw [ite_eq_right (by simp [hv, hn]), ite_eq_right hv]
  refine ⟨h.graph, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hnt : n ≠ t := by
      rintro rfl
      rw [hb] at hn
      cases hn
    rw [block_updateBlock_ne _ _ hedit_tid hnt]
    exact h.absent n hn
  · intro n c hc
    by_cases hnt : n = t
    · subst hnt
      rw [hb] at hc
      cases hc
      rw [block_updateBlock_same _ _ _ hedit_tid, h.block n b hb, hcongr n]
      simp only [Option.map_some, Option.some.injEq]
      have hf : stmtForm (fun m => V m ∨ m = n) (tableAdd en n st) (tableAdd ex n (exitOf b st)) n b =
          renamedStmts b st (exitOf b st) := by
        unfold stmtForm
        rw [ite_eq_left (Or.inr rfl)]
        simp [tableAdd]
      have hb' : stmtForm V en ex n b = b := by
        unfold stmtForm
        rw [ite_eq_right ht]
      rw [hf, hb']
      simp only [editOf, withInputs, exitOf, renamePhis_setVals]
    · rw [block_updateBlock_ne _ _ hedit_tid hnt, h.block n c hc, hcongr n, hform n c hnt hc]
  · intro n c hc hv
    by_cases hnt : n = t
    · subst hnt
      rw [hb] at hc
      cases hc
      simp [tableAdd]
    · have := h.exits n c hc (hv.resolve_right hnt)
      simp [tableAdd, hnt, this]
  · intro n hv
    by_cases hnt : n = t
    · subst hnt
      simpa [tableAdd] using hst
    · simpa [tableAdd, hnt] using h.wf n (hv.resolve_right hnt)
  · intro c p he hc hp k
    by_cases hct : c = t
    · subst hct
      have hpt : p ≠ c := by
        rintro rfl
        exact hself he
      have hpv : V p := hp.resolve_right hpt
      simpa [tableAdd, hpt] using hpar p he hpv k
    · have hcv := hc.resolve_right hct
      have hpv : V p := by
        refine hp.resolve_right ?_
        rintro rfl
        exact hkids c he hcv
      have hpt : p ≠ t := fun heq => ht (heq ▸ hpv)
      simpa [tableAdd, hct, hpt] using h.tree c p he hcv hpv k

private theorem RenameSpec.congr_done {P cfg : Cfg} {U : List Var} {idom : List (Tid × Tid)} {V : Tid → Prop}
    {D D' : Tid → Tid → Prop} {en ex : Tid → RenameState} (h : RenameSpec P cfg U idom V D en ex)
    (hD : ∀ s n, D s n ↔ D' s n) : RenameSpec P cfg U idom V D' en ex := by
  have : D = D' := by
    funext s n
    exact propext (hD s n)
  exact this ▸ h

/-- Renaming the inputs for one edge out of a visited block. -/
private theorem RenameSpec.input {P cfg : Cfg} {U : List Var} {idom : List (Tid × Tid)} {V : Tid → Prop}
    {Done : Tid → Tid → Prop} {en ex : Tid → RenameState} (h : RenameSpec P cfg U idom V Done en ex)
    (t si : Tid) (hnd : ¬ Done t si) :
    RenameSpec P (updatePhiInputs t si (ex t) cfg) U idom V (fun s n => Done s n ∨ (s = t ∧ n = si)) en ex := by
  have htid : ∀ b : Blk, b.tid = si → ({ b with phis := b.phis.map fun phi => { phi with values := phi.values.map fun input =>
      if input.1 = t then (t, renameExp (ex t) input.2) else input } } : Blk).tid = b.tid := fun _ _ => rfl
  refine ⟨h.graph, ?_, ?_, h.exits, h.wf, h.tree⟩
  · intro n hn
    show (cfg.updateBlock si _).block n = none
    by_cases hs : n = si
    · subst hs
      rw [block_updateBlock_same _ _ _ htid, h.absent n hn]
      rfl
    · rw [block_updateBlock_ne _ _ htid hs]
      exact h.absent n hn
  · intro n b hb
    show (cfg.updateBlock si _).block n = _
    by_cases hs : n = si
    · subst hs
      rw [block_updateBlock_same _ _ _ htid, h.block n b hb]
      simp only [Option.map_some, Option.some.injEq]
      rw [withInputs_comp]
      congr 2
      funext input
      obtain ⟨src, e⟩ := input
      by_cases hsrc : src = t
      · subst hsrc
        simp [doneInput, hnd]
      · by_cases hd : Done src n
        · simp [doneInput, hd, hsrc]
        · simp [doneInput, hd, hsrc]
    · rw [block_updateBlock_ne _ _ htid hs, h.block n b hb]
      have : doneInput (Done · n) ex = doneInput (fun s => Done s n ∨ (s = t ∧ n = si)) ex :=
        doneInput_congr (fun s => by simp [hs]) (fun _ _ => rfl)
      rw [this]

private theorem RenameSpec.inputs {P : Cfg} {U : List Var} {idom : List (Tid × Tid)} {V : Tid → Prop}
    {en ex : Tid → RenameState} (t : Tid) (succs : List Tid) (hnd : succs.Nodup) {cfg : Cfg}
    {Done : Tid → Tid → Prop} (h : RenameSpec P cfg U idom V Done en ex) (hfree : ∀ n ∈ succs, ¬ Done t n) :
    RenameSpec P (succs.foldl (fun cfg successor => updatePhiInputs t successor (ex t) cfg) cfg) U idom V
      (fun s n => Done s n ∨ (s = t ∧ n ∈ succs)) en ex := by
  induction succs generalizing cfg Done with
  | nil => exact h.congr_done (by simp)
  | cons x xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 hnd
    have h₁ := h.input t x (hfree x (by simp))
    have h₂ := ih hxs h₁ (by
      intro n hn hd
      rcases hd with hd | ⟨_, rfl⟩
      · exact hfree n (List.mem_cons_of_mem _ hn) hd
      · exact hx hn)
    refine h₂.congr_done ?_
    intro s n
    simp only [List.mem_cons]
    grind

private theorem RenameWf.renamePhis {U : List Var} (phis : List Phi) {st : RenameState} (h : RenameWf U st) :
    RenameWf U (renamePhis phis st).2 := by
  induction phis generalizing st with
  | nil => exact h
  | cons p ps ih =>
    rw [renamePhis_cons]
    exact ih (h.push p.var)

private theorem RenameWf.renameDefs {U : List Var} (defs : List Def) {st : RenameState} (h : RenameWf U st) :
    RenameWf U (renameDefs defs st).2 := by
  induction defs generalizing st with
  | nil => exact h
  | cons d ds ih =>
    rw [renameDefs_cons]
    exact ih (h.push d.var)

/-- Everything the walk from `t` leaves behind: every block below `t` within the fuel is visited, every
visited block has the rename of its statements, and the inputs of every edge out of it are renamed. -/
private theorem renameBlock_spec {P : Cfg} {U : List Var} {idom : List (Tid × Tid)} (T : TreeFacts idom)
    (hkeys : ∀ e ∈ idom, ∃ b, P.block e.1 = some b) (fuel : Nat) (t : Tid) (cfg : Cfg) (st : RenameState)
    (V : Tid → Prop) (en ex : Tid → RenameState) (h : RenameSpec P cfg U idom V (Canon P V) en ex)
    (hex : ∃ b, P.block t = some b) (hfree : ∀ n, V n → ¬ Desc idom t n)
    (hpar : ∀ p, (t, p) ∈ idom → V p → ∀ k, stackOf st k = stackOf (ex p) k) (hst : RenameWf U st) :
    ∃ V' en' ex', RenameSpec P (renameBlock idom fuel t cfg st).1 U idom V' (Canon P V') en' ex' ∧
      (∀ n, V n → V' n) ∧ (∀ n, V' n → V n ∨ Desc idom t n) ∧ (∀ k n, k < fuel → TreeFrom idom t k n → V' n) ∧
      (∀ n, V n → en' n = en n ∧ ex' n = ex n) ∧ (V' t → en' t = st) := by
  induction fuel generalizing t cfg st V en ex with
  | zero =>
    refine ⟨V, en, ex, h, fun _ h => h, fun _ h => Or.inl h, fun k n hk => absurd hk (Nat.not_lt_zero _),
      fun _ _ => ⟨rfl, rfl⟩, fun hv => absurd ⟨0, .self t⟩ (hfree t hv)⟩
  | succ fuel ih =>
    obtain ⟨b, hb⟩ := hex
    have htv : ¬ V t := fun hv => hfree t hv ⟨0, .self t⟩
    have hform : stmtForm V en ex t b = b := by
      unfold stmtForm
      rw [ite_eq_right htv]
    have hc := h.block t b hb
    rw [hform] at hc
    rw [renameBlock_succ]
    simp only [hc]
    have hdone : ∀ s n, Canon P V s n → V s := fun _ _ h => h.1
    have hkids : ∀ c, (c, t) ∈ idom → ¬ V c := fun c he hv => hfree c hv ⟨1, .child he (.self c)⟩
    have hself : (t, t) ∉ idom := fun he => T.up t t he ⟨0, .self t⟩
    let dm := doneInput (Canon P V · t) ex
    let ext := exitOf b st
    have h₁ := h.visit hb htv hdone hst hpar hkids hself
    let en₁ := tableAdd en t st
    let ex₁ := tableAdd ex t ext
    have hext : ex₁ t = ext := by simp [ex₁, tableAdd]
    let c₁ := cfg.updateBlock t (editOf b st dm)
    have h₂ : RenameSpec P ((P.successors t).foldl (fun cfg successor => updatePhiInputs t successor ext cfg) c₁) U idom
        (fun n => V n ∨ n = t) (Canon P (fun n => V n ∨ n = t)) en₁ ex₁ := by
      have := RenameSpec.inputs t (P.successors t) (Bap.Proofs.Graph.successors_nodup _ _) h₁
        (fun n _ hd => htv hd.1)
      rw [show tableAdd ex t (exitOf b st) t = ext by simp [tableAdd, ext]] at this
      refine this.congr_done ?_
      intro s n
      simp only [Canon]
      constructor
      · rintro (⟨hv, hn⟩ | ⟨rfl, hn⟩)
        · exact ⟨Or.inl hv, hn⟩
        · exact ⟨Or.inr rfl, hn⟩
      · rintro ⟨hv | rfl, hn⟩
        · exact Or.inl ⟨hv, hn⟩
        · exact Or.inr ⟨rfl, hn⟩
    -- the children, one by one
    have hchildren : ∀ (children : List Tid) (state : Cfg × RenameState) (W : Tid → Prop) (enw exw : Tid → RenameState),
        RenameSpec P state.1 U idom W (Canon P W) enw exw → W t → exw t = ext →
        (∀ c ∈ children, (c, t) ∈ idom) → children.Nodup → (∀ c ∈ children, ∀ n, W n → ¬ Desc idom c n) →
        (∀ k, stackOf state.2 k = stackOf ext k) → RenameWf U state.2 →
        ∃ W' en' ex', RenameSpec P (children.foldl
            (fun current child => renameBlock idom fuel child current.1 current.2) state).1 U idom W' (Canon P W') en' ex' ∧
          (∀ n, W n → W' n) ∧ (∀ n, W' n → W n ∨ ∃ c ∈ children, Desc idom c n) ∧
          (∀ c ∈ children, ∀ k n, k < fuel → TreeFrom idom c k n → W' n) ∧
          (∀ n, W n → en' n = enw n ∧ ex' n = exw n) := by
      intro children
      induction children with
      | nil =>
        intro state W enw exw hs _ _ _ _ _ _ _
        exact ⟨W, enw, exw, hs, fun _ h => h, fun _ h => Or.inl h, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
      | cons c cs ihc =>
        intro state W enw exw hs hWt hexw hcs hnd hfr hstack hwf
        simp only [List.foldl_cons]
        obtain ⟨hcnot, hcsnd⟩ := List.nodup_cons.1 hnd
        have hct := hcs c (by simp)
        obtain ⟨W₁, en₂, ex₂, hs₁, hm₁, hb₁, hcov₁, hst₁, _⟩ := ih c state.1 state.2 W enw exw hs
          (hkeys (c, t) hct) (hfr c (by simp))
          (by
            intro p hp _ k
            have hpt := T.fn c p t hp hct
            subst hpt
            rw [hstack, hexw])
          hwf
        have hstack₁ : ∀ k, stackOf (renameBlock idom fuel c state.1 state.2).2 k = stackOf ext k := by
          intro k
          rw [← hstack k]
          exact renameBlock_stacks_restored idom fuel c state.1 state.2 k
        have hwf₁ : RenameWf U (renameBlock idom fuel c state.1 state.2).2 :=
          hwf.of_stack (renameBlock_keys _ _ _ _ _ hwf.keys)
            (fun k => renameBlock_stacks_restored idom fuel c state.1 state.2 k)
            (fun w => renameBlock_counters_mono idom fuel c state.1 state.2 w)
        obtain ⟨W₂, en₃, ex₃, hs₂, hm₂, hb₂, hcov₂, hst₂⟩ := ihc (renameBlock idom fuel c state.1 state.2) W₁ en₂ ex₂ hs₁
          (hm₁ t hWt) (by rw [(hst₁ t hWt).2]; exact hexw)
          (fun z hz => hcs z (List.mem_cons_of_mem _ hz)) hcsnd
          (by
            intro z hz n hn
            rcases hb₁ n hn with hn | hd
            · exact hfr z (List.mem_cons_of_mem _ hz) n hn
            · exact T.disj t c z n hct (hcs z (List.mem_cons_of_mem _ hz))
                (fun heq => hcnot (heq ▸ hz)) hd)
          hstack₁ hwf₁
        refine ⟨W₂, en₃, ex₃, hs₂, fun n hn => hm₂ n (hm₁ n hn), ?_, ?_, ?_⟩
        · intro n hn
          rcases hb₂ n hn with hn | ⟨z, hz, hd⟩
          · rcases hb₁ n hn with hn | hd
            · exact Or.inl hn
            · exact Or.inr ⟨c, by simp, hd⟩
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, hd⟩
        · intro z hz k n hk htree
          rcases List.mem_cons.1 hz with rfl | hz
          · exact hm₂ n (hcov₁ k n hk htree)
          · exact hcov₂ z hz k n hk htree
        · intro n hn
          obtain ⟨a₁, a₂⟩ := hst₁ n hn
          obtain ⟨b₁, b₂⟩ := hst₂ n (hm₁ n hn)
          exact ⟨b₁.trans a₁, b₂.trans a₂⟩
    have hmemkids : ∀ c ∈ (idom.filter fun entry => entry.2 = t).map Prod.fst, (c, t) ∈ idom := by
      intro c hc
      obtain ⟨⟨x, y⟩, he, rfl⟩ := List.mem_map.1 hc
      obtain ⟨hm, hy⟩ := List.mem_filter.1 he
      have hy' : y = t := by simpa using hy
      subst hy'
      exact hm
    have hwfext : RenameWf U ext := (hst.renamePhis b.phis).renameDefs b.defs
    have hphisnd : (renamePhis (b.phis.map (setVals dm)) st).2 = (renamePhis b.phis st).2 := by
      rw [renamePhis_setVals]
    obtain ⟨W, en₂, ex₂, hs, hm, hbd, hcov, hstab⟩ := hchildren ((idom.filter fun entry => entry.2 = t).map Prod.fst)
      ((P.successors t).foldl (fun cfg successor => updatePhiInputs t successor ext cfg) c₁, ext)
      (fun n => V n ∨ n = t) en₁ ex₁ h₂ (Or.inr rfl) hext hmemkids
      ((List.filter_sublist.map Prod.fst).nodup T.nodup)
      (by
        intro c hc n hn hd
        rcases hn with hn | rfl
        · exact hfree n hn (by
            obtain ⟨k, hk⟩ := hd
            exact ⟨k + 1, .child (hmemkids c hc) hk⟩)
        · exact T.up c n (hmemkids c hc) hd)
      (fun _ => rfl) hwfext
    refine ⟨W, en₂, ex₂, ?_, fun n hn => hm n (Or.inl hn), ?_, ?_, ?_, ?_⟩
    · have hp' : (renamePhis (b.phis.map (setVals (doneInput (fun x => Canon P V x t) ex))) st).2 =
          (renamePhis b.phis st).2 := hphisnd
      have hs' : ∀ f : Blk → Blk, (cfg.updateBlock t f).successors t = P.successors t := by
        intro f
        show Bap.Graph.successors cfg.graph t = Bap.Graph.successors P.graph t
        rw [h.graph]
      have he : editOf b st (doneInput (fun x => Canon P V x t) ex) = fun block => { block with
          phis := (renamePhis (b.phis.map (setVals (doneInput (fun x => Canon P V x t) ex))) st).1
          defs := (renameDefs b.defs (renamePhis b.phis st).2).1
          jmps := b.jmps.map (Jmp.mapExp (renameExp (renameDefs b.defs (renamePhis b.phis st).2).2)) } := by
        funext block
        simp only [editOf, hp']
      simp only [hp', hs']
      simp only [c₁, dm, he] at hs
      exact hs
    · intro n hn
      rcases hbd n hn with hn | ⟨c, hc, k, hk⟩
      · rcases hn with hn | rfl
        · exact Or.inl hn
        · exact Or.inr ⟨0, .self n⟩
      · exact Or.inr ⟨k + 1, .child (hmemkids c hc) hk⟩
    · intro k n hk htree
      cases htree with
      | self => exact hm t (Or.inr rfl)
      | @child _ c k' _ he hsub =>
        refine hcov c ?_ k' n (by omega) hsub
        exact List.mem_map.2 ⟨(c, t), List.mem_filter.2 ⟨he, by simp⟩, rfl⟩
    · intro n hn
      have hnt : n ≠ t := fun heq => htv (heq ▸ hn)
      obtain ⟨a, b⟩ := hstab n (Or.inl hn)
      simp only [en₁, ex₁, tableAdd, hnt, ite_false] at a b
      exact ⟨a, b⟩
    · intro _
      have := (hstab t (Or.inr rfl)).1
      simpa [en₁, tableAdd] using this

/-! ### The dominator tree of the connected CFG -/

section ConnectedFacts

variable {sub : Sub}

private abbrev connG (sub : Sub) : Bap.Graph.Graph Tid := (Cfg.connected sub).graph
private abbrev idomOf (sub : Sub) : List (Tid × Tid) := (Cfg.connected sub).immediateDominators
private abbrev DomC (sub : Sub) (n d : Tid) : Prop := Bap.Proofs.Graph.Dom (connG sub) pseudoStart n d
private abbrev Reach (sub : Sub) (n : Tid) : Prop := n ∈ (Cfg.connected sub).reachable

private theorem idomOf_spec {n i : Tid} (h : (n, i) ∈ idomOf sub) :
    Reach sub n ∧ n ≠ pseudoStart ∧ i ≠ n ∧ DomC sub n i ∧ ∀ c, c ≠ n → DomC sub n c → DomC sub i c := by
  have : idomOf sub = Bap.Graph.immediateDominators (connG sub) pseudoStart := by
    show Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start = _
    rw [connected_start]
  rw [this] at h
  have hr := Bap.Proofs.Graph.immediateDominators_spec h
  refine ⟨?_, hr.2⟩
  show n ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
  rw [connected_start]
  exact hr.1

private theorem reach_eq : Bap.Graph.reachable (connG sub) pseudoStart = (Cfg.connected sub).reachable := by
  show _ = Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
  rw [connected_start]

private theorem reach_iff {n : Tid} : Reach sub n ↔ n ∈ Bap.Graph.reachable (connG sub) pseudoStart := by
  rw [reach_eq]

private theorem dom_reach {n d : Tid} (hn : Reach sub n) (h : DomC sub n d) : Reach sub d := by
  obtain ⟨w, hw⟩ := (Bap.Proofs.Graph.mem_reachable_iff_walk n).1 (reach_iff.1 hn)
  exact reach_iff.2 (hw.subset_reachable (h w hw))

private theorem tree_dom {t n : Tid} {k : Nat} (h : TreeFrom (idomOf sub) t k n) : DomC sub n t := by
  induction h with
  | self t => exact Bap.Proofs.Graph.Dom.refl _
  | child he _ ih => exact Bap.Proofs.Graph.Dom.trans ih (idomOf_spec he).2.2.2.1

private theorem tree_reach {t n : Tid} {k : Nat} (h : TreeFrom (idomOf sub) t k n) (ht : Reach sub t) : Reach sub n := by
  induction h with
  | self t => exact ht
  | child he _ ih => exact ih (idomOf_spec he).1

private theorem dom_antisymm {a b : Tid} (ha : Reach sub a) (hab : DomC sub a b) (hba : DomC sub b a) : a = b :=
  Bap.Proofs.Graph.Dom.antisymm (reach_iff.1 ha) hab hba

private theorem connected_treeFacts (hwf : SubWf sub) : TreeFacts (idomOf sub) := by
  have heq : idomOf sub = Bap.Graph.immediateDominators (connG sub) pseudoStart := by
    show Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start = _
    rw [connected_start]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c p q hp hq
    rw [heq] at hp hq
    exact Bap.Proofs.Graph.immediateDominators_unique hp hq
  · rintro t c₁ c₂ n h₁ h₂ hne ⟨k₁, hd₁⟩ ⟨k₂, hd₂⟩
    have hr₁ := idomOf_spec h₁
    have hr₂ := idomOf_spec h₂
    have hnr := tree_reach hd₁ hr₁.1
    rcases Bap.Proofs.Graph.Dom.chain (reach_iff.1 hnr) (tree_dom hd₁) (tree_dom hd₂) with hd | hd
    · have hdt : DomC sub t c₂ := hr₁.2.2.2.2 c₂ (Ne.symm hne) hd
      have htr : Reach sub t := dom_reach hr₂.1 hr₂.2.2.2.1
      exact hr₂.2.2.1 (dom_antisymm htr hdt hr₂.2.2.2.1)
    · have hdt : DomC sub t c₁ := hr₂.2.2.2.2 c₁ hne hd
      have htr : Reach sub t := dom_reach hr₁.1 hr₁.2.2.2.1
      exact hr₁.2.2.1 (dom_antisymm htr hdt hr₁.2.2.2.1)
  · rintro c t he ⟨k, hd⟩
    have hr := idomOf_spec he
    exact hr.2.2.1 (dom_antisymm hr.1 hr.2.2.2.1 (tree_dom hd)).symm
  · rw [heq]
    exact Bap.Proofs.Graph.immediateDominators_keys_nodup (connected_nodes_nodup hwf)

private abbrev phiVars (sub : Sub) : List Var := ((Cfg.connected sub).blocks.flatMap Blk.definedVars).eraseDups

private theorem phiCfg_spec (sub : Sub) :
    PhiGrow (· ∈ phiVars sub) (Cfg.connected sub) (phiCfg sub) ∧
      (∀ var ∈ phiVars sub, FrontierClosed (phiCfg sub) (Cfg.connected sub).dominanceFrontier var) ∧
      ∀ var ∈ phiVars sub, ∀ n x c, (Cfg.connected sub).block n = some x → (phiCfg sub).block n = some c →
        (∃ φ ∈ c.phis, φ.var = var) →
          (∃ φ ∈ x.phis, φ.var = var) ∨
            IteratedFrontier (Cfg.connected sub).dominanceFrontier (DefSites (Cfg.connected sub) var) n := by
  refine insertAllPhis_spec _ (Cfg.connected sub).graph.nodes ?_ _ (Bap.Proofs.Graph.nodup_eraseDups _) _ ?_
  · intro u j hj
    cases hg : Assoc.get u (Cfg.connected sub).dominanceFrontier with
    | none =>
      rw [hg] at hj
      simp at hj
    | some f =>
      rw [hg] at hj
      have hu := get_mem_env' hg
      exact Bap.Proofs.Graph.reachableFrom_subset_nodes _ _
        (Bap.Proofs.Graph.dominanceFrontier_target hu hj).1
  · rw [← connected_tids_eq_nodes]
    simp

private theorem get_of_mem_keys {β : Type} {k : Tid} {l : List (Tid × β)} (h : k ∈ l.map Prod.fst) :
    ∃ v, Assoc.get k l = some v := by
  induction l with
  | nil => simp at h
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      exact ⟨b, by simp [Assoc.get]⟩
    · have hb : (k == a) = false := by simpa using hk
      have hm : k ∈ es.map Prod.fst := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h hk
        · exact h
      obtain ⟨v, hv⟩ := ih hm
      refine ⟨v, ?_⟩
      have hv' : List.lookup k es = some v := hv
      simp [Assoc.get, List.lookup, hb, hv']

private theorem phi_block_exists {n : Tid} (hn : n ∈ (Cfg.connected sub).graph.nodes) :
    ∃ b, (phiCfg sub).block n = some b := by
  apply block_exists
  rw [(phiCfg_spec sub).1.tids, connected_tids_eq_nodes]
  exact hn

/-- Facts about reads: every variable a block reads is mentioned. -/
private theorem read_exposed_or_defined {x : Var} {defs : List Def} {d : Def} (hd : d ∈ defs) (hx : x ∈ Bil.freeVars d.rhs) :
    Exposed defs x ∨ ∃ c ∈ defs, c.var = x := by
  induction defs with
  | nil => simp at hd
  | cons c cs ih =>
    rcases List.mem_cons.1 hd with rfl | hd
    · exact Or.inl (Or.inl hx)
    · rcases ih hd with h | ⟨e, he, hv⟩
      · by_cases hc : x = c.var
        · exact Or.inr ⟨c, by simp, hc.symm⟩
        · exact Or.inl (Or.inr ⟨hc, h⟩)
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, hv⟩

private theorem mem_mentioned {blocks : List Blk} {o : Blk} (ho : o ∈ blocks) {x : Var}
    (hx : x ∈ o.definedVars ∨ x ∈ o.freeVars) : x ∈ mentioned blocks :=
  List.mem_flatMap.2 ⟨o, ho, List.mem_append.2 hx⟩

private theorem def_read_mentioned {blocks : List Blk} {o : Blk} (ho : o ∈ blocks) {d : Def} (hd : d ∈ o.defs) {x : Var}
    (hx : x ∈ Bil.freeVars d.rhs) : x ∈ mentioned blocks := by
  apply mem_mentioned ho
  by_cases hphi : ∃ phi ∈ o.phis, phi.var = x
  · exact Or.inl ((mem_definedVars _ _).2 (Or.inl hphi))
  · rcases read_exposed_or_defined hd hx with h | ⟨c, hc, hv⟩
    · exact Or.inr ((mem_blk_freeVars _ _).2 (Or.inl ⟨fun phi hp he => hphi ⟨phi, hp, he⟩, Or.inl h⟩))
    · exact Or.inl ((mem_definedVars _ _).2 (Or.inr ⟨c, hc, hv⟩))

private theorem jump_read_mentioned {blocks : List Blk} {o : Blk} (ho : o ∈ blocks) {j : Jmp} (hj : j ∈ o.jmps) {x : Var}
    (hx : x ∈ j.freeVars) : x ∈ mentioned blocks := by
  apply mem_mentioned ho
  by_cases hd : x ∈ o.definedVars
  · exact Or.inl hd
  · rw [mem_definedVars] at hd
    simp only [not_or, not_exists, not_and] at hd
    exact Or.inr ((mem_blk_freeVars _ _).2 (Or.inl ⟨fun phi hp he => hd.1 phi hp he,
      Or.inr ⟨⟨j, hj, hx⟩, fun c hc he => hd.2 c hc he⟩⟩))

private theorem phi_read_mentioned {blocks : List Blk} {o : Blk} (ho : o ∈ blocks) {phi : Phi} (hp : phi ∈ o.phis)
    {input : Tid × Exp} (hi : input ∈ phi.values) {x : Var} (hx : x ∈ Bil.freeVars input.2) : x ∈ mentioned blocks :=
  mem_mentioned ho (Or.inr ((mem_blk_freeVars _ _).2 (Or.inr ⟨phi, hp, input, hi, hx⟩)))

private abbrev mentionedOf (sub : Sub) : List Var := mentioned (Cfg.connected sub).blocks

private theorem initial_fold (vars : List Var) (seed : List (Var × Nat)) (hseed : ∀ w : Var, 1 ≤ (Assoc.get w.base seed).getD 1) :
    (∀ w ∈ vars, w.index < (Assoc.get w.base (vars.foldl (init := seed) fun counters var =>
      if var.index = 0 then counters
      else Assoc.put var.base (max ((Assoc.get var.base counters).getD 1) (var.index + 1)) counters)).getD 1) ∧
    ∀ z : Var, (Assoc.get z.base seed).getD 1 ≤ (Assoc.get z.base (vars.foldl (init := seed) fun counters var =>
      if var.index = 0 then counters
      else Assoc.put var.base (max ((Assoc.get var.base counters).getD 1) (var.index + 1)) counters)).getD 1 := by
  induction vars generalizing seed with
  | nil => exact ⟨by simp, fun _ => Nat.le_refl _⟩
  | cons v vs ih =>
    simp only [List.foldl_cons]
    have hstep : ∀ z : Var, (Assoc.get z.base seed).getD 1 ≤ (Assoc.get z.base
        (if v.index = 0 then seed else Assoc.put v.base (max ((Assoc.get v.base seed).getD 1) (v.index + 1)) seed)).getD 1 := by
      intro z
      split
      · exact Nat.le_refl _
      · rw [get_put]
        split
        · rename_i hz
          rw [hz]
          simp only [Option.getD_some]
          omega
        · exact Nat.le_refl _
    have hseed' : ∀ w : Var, 1 ≤ (Assoc.get w.base
        (if v.index = 0 then seed else Assoc.put v.base (max ((Assoc.get v.base seed).getD 1) (v.index + 1)) seed)).getD 1 :=
      fun w => Nat.le_trans (hseed w) (hstep w)
    obtain ⟨h₁, h₂⟩ := ih _ hseed'
    refine ⟨?_, fun z => Nat.le_trans (hstep z) (h₂ z)⟩
    intro w hw
    rcases List.mem_cons.1 hw with heq | hw
    · subst heq
      refine Nat.lt_of_lt_of_le ?_ (h₂ w)
      by_cases h0 : w.index = 0
      · rw [ite_eq_left h0]
        have := hseed w
        omega
      · rw [ite_eq_right h0, get_put, ite_eq_left rfl]
        simp only [Option.getD_some]
        omega
    · exact h₁ w hw

private theorem initial_wf (sub : Sub) : RenameWf (mentionedOf sub) (initialState (Cfg.connected sub).blocks) := by
  refine ⟨List.nodup_nil, ?_, ?_⟩
  · intro k y hy
    have : stackOf (initialState (Cfg.connected sub).blocks) k = [] := rfl
    rw [this] at hy
    simp at hy
  · rintro w (h0 | hw)
    · have := initialState_counter_pos (Cfg.connected sub).blocks w
      omega
    · exact (initial_fold _ [] (fun _ => by simp)).1 w hw

private theorem phi_simple_base (sub : Sub) :
    RenameSpec (phiCfg sub) (phiCfg sub) (mentionedOf sub) (idomOf sub) (fun _ => False)
      (Canon (phiCfg sub) (fun _ => False)) (fun _ => initialState (Cfg.connected sub).blocks)
      (fun _ => initialState (Cfg.connected sub).blocks) := by
  refine ⟨rfl, fun _ h => h, ?_, fun _ _ _ h => h.elim, fun _ h => h.elim, fun _ _ _ h => h.elim⟩
  intro m c hc
  have hid : doneInput (Canon (phiCfg sub) (fun _ => False) · m)
      (fun _ => initialState (Cfg.connected sub).blocks) = id := by
    funext input
    rw [doneInput, ite_eq_right (fun h => h.1)]
    rfl
  have hform : stmtForm (fun _ => False) (fun _ => initialState (Cfg.connected sub).blocks)
      (fun _ => initialState (Cfg.connected sub).blocks) m c = c := by
    unfold stmtForm
    rw [ite_eq_right (fun h => h)]
  have hset : setVals id = id := by
    funext p
    simp [setVals]
  rw [hid, hform, hc]
  simp only [withInputs, hset, List.map_id]

/-- The tables of the whole renaming walk. -/
private structure SsaTables (sub : Sub) (en ex : Tid → RenameState) : Prop where
  spec : RenameSpec (phiCfg sub) (ssaCfg sub) (mentionedOf sub) (idomOf sub) (Reach sub) (Canon (phiCfg sub) (Reach sub)) en ex
  entry : en pseudoStart = initialState (Cfg.connected sub).blocks

private theorem ssa_tables (hwf : SubWf sub) : ∃ en ex, SsaTables sub en ex := by
  have hT := connected_treeFacts hwf
  have hkeys : ∀ e ∈ idomOf sub, ∃ b, (phiCfg sub).block e.1 = some b := by
    rintro ⟨n, i⟩ he
    exact phi_block_exists (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ (idomOf_spec he).1)
  have hstart : (phiCfg sub).start = pseudoStart := by
    rw [(phiCfg_spec sub).1.start, connected_start]
  have hs₀ : ∃ b, (phiCfg sub).block pseudoStart = some b := phi_block_exists (by rw [connected_nodes]; simp)
  obtain ⟨b₀, hb₀⟩ := hs₀
  obtain ⟨V, en, ex, hs, -, hbd, hcov, -, hen⟩ := renameBlock_spec hT hkeys ((phiCfg sub).blocks.length + 1) pseudoStart
    (phiCfg sub) (initialState (Cfg.connected sub).blocks) (fun _ => False) _ _ (phi_simple_base sub) ⟨b₀, hb₀⟩
    (fun _ h => h.elim) (fun _ _ h => h.elim) (initial_wf sub)
  have hreach₀ : Reach sub pseudoStart := by
    have : pseudoStart = (Cfg.connected sub).start := (connected_start sub).symm
    show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact start_mem_reachable (by rw [connected_nodes]; simp)
  have hchain : ∀ k n, Bap.Proofs.Graph.IdomChain (connG sub) pseudoStart k n → TreeFrom (idomOf sub) pseudoStart k n := by
    intro k n hc
    induction hc with
    | start => exact .self _
    | step he _ ih =>
      refine ih.snoc ?_
      show (_, _) ∈ Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start
      rw [connected_start]
      exact he
  have hV : V = Reach sub := by
    funext n
    apply propext
    constructor
    · intro hn
      rcases hbd n hn with h | ⟨k, hk⟩
      · exact h.elim
      · exact tree_reach hk hreach₀
    · intro hn
      obtain ⟨k, hk, hc⟩ := Bap.Proofs.Graph.idomChain_exists (reach_iff.1 hn)
      refine hcov k n ?_ (hchain k n hc)
      have hlen : (phiCfg sub).blocks.length = (connG sub).nodes.length := by
        rw [← connected_tids_eq_nodes, ← List.length_map (f := Blk.tid), (phiCfg_spec sub).1.tids]
      omega
  subst hV
  refine ⟨en, ex, ?_, hen hreach₀⟩
  have hsrw : ssaCfg sub = (renameBlock (idomOf sub) ((phiCfg sub).blocks.length + 1) pseudoStart (phiCfg sub)
      (initialState (Cfg.connected sub).blocks)).1 := by
    rw [ssaCfg_eq, hstart]
  rw [hsrw]
  exact hs

/-- A tracked read is what the name stacks at the end of a block say. -/
private theorem top_of_stack {st st' : RenameState} (w : Var) (h : stackOf st w = stackOf st' w) :
    topName w st = topName w st' := by
  rw [topName_of_stack, topName_of_stack, h]

private theorem count_zero_stack {st : RenameState} {k : Var} (phis : List Phi) (hp : ∀ phi ∈ phis, phi.var ≠ k) :
    stackOf (renamePhis phis st).2 k = stackOf st k := by
  obtain ⟨xs, hx, hl, -⟩ := stackOf_renamePhis phis st k
  have h0 : (phis.map Phi.var).count k = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨phi, hphi, he⟩ := List.mem_map.1 hm
    exact hp phi hphi he
  rw [hx, List.eq_nil_of_length_eq_zero (hl.trans h0)]
  simp

private theorem count_zero_stack_defs {st : RenameState} {k : Var} (defs : List Def) (hp : ∀ d ∈ defs, d.var ≠ k) :
    stackOf (renameDefs defs st).2 k = stackOf st k := by
  obtain ⟨xs, hx, hl, -⟩ := stackOf_renameDefs defs st k
  have h0 : (defs.map Def.var).count k = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    obtain ⟨d, hd, he⟩ := List.mem_map.1 hm
    exact hp d hd he
  rw [hx, List.eq_nil_of_length_eq_zero (hl.trans h0)]
  simp

/-- The heart of SSA construction. Across an edge into a block with no phi for a variable, the name the
source leaves visible is the name visible on entry to the block. Going up the dominator tree from the
source to the immediate dominator of the target, no block assigns the variable: each one dominates the
source without strictly dominating the target, which puts the target in its dominance frontier, where
assigning the variable would have forced a phi. -/
private theorem edge_names {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {p n : Tid}
    (he : (p, n) ∈ (connG sub).edges) (hp : Reach sub p) (hn : n ∈ (connG sub).nodes) (var : Var)
    (hnophi : ∀ b, (phiCfg sub).block n = some b → ∀ φ ∈ b.phis, φ.var ≠ var) :
    stackOf (ex p) var = stackOf (en n) var := by
  have hnr : n ∈ Bap.Graph.reachable (connG sub) pseudoStart :=
    Bap.Proofs.Graph.reachableFrom_closed _ _ (reach_iff.1 hp) he hn
  have hne : n ≠ pseudoStart := by
    rintro rfl
    exact hwf.no_edge_to_start he
  obtain ⟨i, hi⟩ : ∃ i, (n, i) ∈ idomOf sub := by
    have := Bap.Proofs.Graph.immediateDominators_exists hnr hne
    show ∃ i, (n, i) ∈ Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact this
  obtain ⟨hnr', _, hin, hdn, hmin⟩ := idomOf_spec hi
  have hdp : DomC sub p i := by
    intro w hw
    have hw' := Bap.Proofs.Graph.Walk.cons hw he hn
    rcases List.mem_cons.1 (hdn _ hw') with h | h
    · exact absurd h hin
    · exact h
  have hbases : ∀ u, Reach sub u → DomC sub p u → DomC sub u i → u ≠ i → stackOf (ex u) var = stackOf (en u) var := by
    intro u hu hup hui hne
    obtain ⟨x, hx⟩ := phi_block_exists (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hu)
    have hnot : var ∉ x.definedVars := by
      intro hdef
      have hvars : var ∈ phiVars sub := by
        cases hc : (Cfg.connected sub).block u with
        | none =>
          obtain ⟨o, ho⟩ := block_exists (by rw [connected_tids_eq_nodes]; exact Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hu : u ∈ (Cfg.connected sub).blocks.map Blk.tid)
          rw [hc] at ho
          cases ho
        | some o =>
          obtain ⟨ins, hi', hall⟩ := (phiCfg_spec sub).1.blocks u o hc
          rw [hi'] at hx
          cases hx
          rw [mem_definedVars] at hdef
          have hod : var ∈ o.definedVars ∨ ∃ φ ∈ ins, φ.var = var := by
            rcases hdef with ⟨φ, hφ, hv⟩ | hd
            · rcases List.mem_append.1 hφ with hφ | hφ
              · exact Or.inl ((mem_definedVars _ _).2 (Or.inl ⟨φ, hφ, hv⟩))
              · exact Or.inr ⟨φ, hφ, hv⟩
            · exact Or.inl ((mem_definedVars _ _).2 (Or.inr hd))
          rcases hod with hod | ⟨φ, hφ, hv⟩
          · exact List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨o, (block_some hc).1, hod⟩)
          · exact hv ▸ (hall φ hφ).1
      obtain ⟨f, hf⟩ := get_of_mem_keys (k := u) (l := (Cfg.connected sub).dominanceFrontier) (by
        show u ∈ (Bap.Graph.dominanceFrontier _ _).map Prod.fst
        rw [Bap.Proofs.Graph.dominanceFrontier_keys]
        exact Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hu)
      have hfm := get_mem_env' hf
      have hmem : n ∈ (Assoc.get u (Cfg.connected sub).dominanceFrontier).getD [] := by
        rw [hf]
        refine (Bap.Proofs.Graph.mem_dominanceFrontier_iff (g := connG sub) (s := (Cfg.connected sub).start) hfm hu).2
          ⟨p, he, hp, hn, by rw [connected_start]; exact hup, ?_⟩
        intro hun hdom
        rw [connected_start] at hdom
        exact hne (dom_antisymm hu hui (hmin u hun hdom))
      obtain ⟨c, hc⟩ := phi_block_exists hn
      obtain ⟨φ, hφ, hv⟩ := (phiCfg_spec sub).2.1 var hvars u x hx hdef n hmem c hc
      exact hnophi c hc φ hφ hv
    rw [mem_definedVars] at hnot
    simp only [not_or, not_exists, not_and] at hnot
    rw [F.spec.exits u x hx hu, count_zero_stack_defs _ (fun d hd he => hnot.2 d hd he),
      count_zero_stack _ (fun φ hφ he => hnot.1 φ hφ he)]
  have hup : ∀ k u, Bap.Proofs.Graph.IdomChain (connG sub) pseudoStart k u → DomC sub p u → DomC sub u i →
      stackOf (ex u) var = stackOf (ex i) var := by
    intro k u hc
    induction hc with
    | start =>
      intro _ hui
      have hsn : pseudoStart ∈ (connG sub).nodes := by rw [connected_nodes]; simp
      have := List.mem_singleton.1 (hui _ (.nil hsn))
      rw [this]
    | @step k u q hq _ ih =>
      intro hup hui
      have hq' : (u, q) ∈ idomOf sub := by
        show _ ∈ Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start
        rw [connected_start]
        exact hq
      obtain ⟨hur, _, hqu, hdq, hminq⟩ := idomOf_spec hq'
      by_cases hui' : u = i
      · rw [hui']
      · rw [hbases u hur hup hui hui', F.spec.tree u q hq' hur (dom_reach hur hdq) var]
        exact ih (Bap.Proofs.Graph.Dom.trans hup hdq) (hminq i (Ne.symm hui') hui)
  have hirreach : Reach sub i := dom_reach hnr' hdn
  obtain ⟨k, _, hc⟩ := Bap.Proofs.Graph.idomChain_exists (reach_iff.1 hp)
  rw [hup k p hc (Bap.Proofs.Graph.Dom.refl _) hdp, F.spec.tree n i hi hnr' hirreach var]

private theorem get_doneInput {D : Tid → Prop} (ex : Tid → RenameState) {pred : Tid} (hD : D pred) (l : List (Tid × Exp)) :
    Assoc.get pred (l.map (doneInput D ex)) = (Assoc.get pred l).map (renameExp (ex pred)) := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : pred = a
    · subst ha
      have : doneInput D ex (pred, b) = (pred, renameExp (ex pred) b) := by
        rw [doneInput, ite_eq_left hD]
      show List.lookup pred (doneInput D ex (pred, b) :: es.map (doneInput D ex)) = (List.lookup pred ((pred, b) :: es)).map _
      rw [this]
      simp only [List.lookup, beq_self_eq_true, Option.map_some]
    · have hb : (pred == a) = false := by simpa using ha
      have hfst : (doneInput D ex (a, b)).1 = a := by
        unfold doneInput
        split <;> rfl
      have hih : List.lookup pred (es.map (doneInput D ex)) = (List.lookup pred es).map (renameExp (ex pred)) := ih
      have hlook : List.lookup pred (doneInput D ex (a, b) :: es.map (doneInput D ex)) =
          List.lookup pred (es.map (doneInput D ex)) := by
        rw [show doneInput D ex (a, b) = (a, (doneInput D ex (a, b)).2) from Prod.ext hfst rfl]
        simp [List.lookup, hb]
      simp only [List.map_cons, Assoc.get]
      rw [hlook, hih]
      simp [List.lookup, hb]

/-- The block `t` of the output, for a block of the input. -/
private theorem phi_block_real (hwf : SubWf sub) {t : Tid} {o : Blk} (ho : (Cfg.fromSub sub).block t = some o) :
    ∃ ins, (phiCfg sub).block t = some { o with phis := o.phis ++ ins } ∧ ∀ φ ∈ ins, φ.var ∈ phiVars sub ∧
      φ.var ∉ o.phis.map Phi.var ∧ φ.values = ((Cfg.connected sub).predecessors t).map fun pred => (pred, Exp.var φ.var) :=
  (phiCfg_spec sub).1.blocks t o (connected_block_real hwf ho)

private theorem real_reach {t : Tid} {o : Blk} (ho : (Cfg.fromSub sub).block t = some o) : Reach sub t := by
  have hm := block_some ho
  exact connected_all_reachable sub (List.mem_map.2 ⟨o, hm.1, hm.2⟩)

private theorem real_mem_connected {o : Blk} (ho : o ∈ sub.blks) : o ∈ (Cfg.connected sub).blocks := by
  rw [connected_blocks]
  simp [ho]

private theorem mem_phiVars_mentioned {x : Var} (h : x ∈ phiVars sub) : x ∈ mentionedOf sub := by
  obtain ⟨b, hb, hx⟩ := List.mem_flatMap.1 (List.mem_eraseDups.1 h)
  exact mem_mentioned hb (Or.inl hx)

/-- The names a table gives at the exit of a reachable block obey the renaming invariant. -/
private theorem exit_wf {en ex : Tid → RenameState} (F : SsaTables sub en ex) {n : Tid} (hn : Reach sub n) :
    RenameWf (mentionedOf sub) (ex n) := by
  obtain ⟨x, hx⟩ := phi_block_exists (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hn)
  rw [F.spec.exits n x hx hn]
  exact ((F.spec.wf n hn).renamePhis _).renameDefs _

/-- One block of the output runs in step with the input, from environments that agree through the
names at the exit of the predecessor. -/
private theorem ssa_block_sim {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {p t : Tid}
    (he : (p, t) ∈ (connG sub).edges) (hp : Reach sub p) {o : Blk} (ho : (Cfg.fromSub sub).block t = some o) {E E' E₁ : Env}
    {r : Env × List (Var × Value)}
    (hI : ∀ w, Tracked (mentionedOf sub) w → Bil.lookup E' (topName w (ex p)) = Bil.lookup E w)
    (hphis : execPhis p E o.phis E = .ok E₁) (hdefs : execDefs E₁ o.defs = .ok r) :
    ∃ sb E₁' r', (ssaCfg sub).block t = some sb ∧ execPhis p E' sb.phis E' = .ok E₁' ∧ execDefs E₁' sb.defs = .ok r' ∧
      storeShape r'.2 = storeShape r.2 ∧
      (∀ w, Tracked (mentionedOf sub) w → Bil.lookup r'.1 (topName w (ex t)) = Bil.lookup r.1 w) ∧
      sb.jmps = o.jmps.map (Jmp.mapExp (renameExp (ex t))) := by
  obtain ⟨ins, hb, hins⟩ := phi_block_real hwf ho
  have htreach := real_reach ho
  have hom : o ∈ (Cfg.connected sub).blocks := real_mem_connected (block_some ho).1
  have hpredmem : p ∈ (Cfg.connected sub).predecessors t := (mem_predecessors' _ _ _).2 he
  let b : Blk := { o with phis := o.phis ++ ins }
  -- the inserted phis change no value
  obtain ⟨r₂, hr₂, hsame⟩ : ∃ r₂, execPhis p E b.phis E = .ok r₂ ∧ ∀ w, Bil.lookup r₂ w = Bil.lookup E₁ w := by
    obtain ⟨r₂, hr₂, hsame⟩ := execPhis_insert p E ins (acc := E₁) (by
      intro φ hφ
      obtain ⟨_, hnot, hval⟩ := hins φ hφ
      refine ⟨by rw [hval]; exact get_trivial_values _ _ hpredmem _, ?_⟩
      exact lookup_execPhis_other hphis fun phi hphi heq => hnot (List.mem_map.2 ⟨phi, hphi, heq⟩))
    exact ⟨r₂, execPhis_append hphis hr₂, hsame⟩
  have hwfp := exit_wf F hp
  have hstart : RenameWf (mentionedOf sub) (en t) := F.spec.wf t htreach
  let f := doneInput (Canon (phiCfg sub) (Reach sub) · t) ex
  have hval : ∀ phi ∈ b.phis, ∀ e, Assoc.get p phi.values = some e →
      phiValue E' (renameExp (ex p) e) = phiValue E e := by
    intro phi hphi e hget
    refine phiValue_renameExp hwfp e hI ?_
    intro x hx
    refine Or.inr ?_
    rcases List.mem_append.1 hphi with hphi | hphi
    · exact phi_read_mentioned hom hphi (get_mem_env' hget) hx
    · obtain ⟨hv, _, hvals⟩ := hins phi hphi
      rw [hvals, get_trivial_values _ _ hpredmem] at hget
      cases hget
      have hx' : x = phi.var := by
        have := (Bap.Proofs.Bil.mem_freeVars_iff x (.var phi.var)).1 hx
        simp only [Bil.occursFree, beq_iff_eq] at this
        exact this.symm
      exact hx' ▸ mem_phiVars_mentioned hv
  have hphi₀ : ∀ w, Tracked (mentionedOf sub) w → (∀ phi ∈ b.phis, phi.var ≠ w) →
      Bil.lookup E' (topName w (en t)) = Bil.lookup E w := by
    intro w hw hn
    have hst : stackOf (ex p) w = stackOf (en t) w :=
      edge_names hwf F he hp (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ htreach) w (by
        intro c hc φ hφ
        rw [hb] at hc
        cases hc
        exact hn φ hφ)
    rw [← top_of_stack w hst]
    exact hI w hw
  obtain ⟨E₁', hE₁', hI₁⟩ := renamePhis_sim (U := mentionedOf sub) p (renameExp (ex p)) f
    (fun phi => get_doneInput ex ⟨hp, (Bap.Graph.successors_mem _ _ _).2 (by
      rw [(phiCfg_spec sub).1.graph]
      exact he)⟩ phi.values) b.phis hval hstart hphi₀ hr₂
  have hI₁' : ∀ w, Tracked (mentionedOf sub) w →
      Bil.lookup E₁' (topName w (renamePhis b.phis (en t)).2) = Bil.lookup E₁ w :=
    fun w hw => by rw [hI₁ w hw, hsame]
  obtain ⟨r', hr', hl, hs⟩ := renameDefs_sim (U := mentionedOf sub) b.defs
    (fun d hd x hx => Or.inr (def_read_mentioned hom hd hx)) (hstart.renamePhis b.phis) hI₁' hdefs
  have hform : stmtForm (Reach sub) en ex t b = renamedStmts b (en t) (ex t) := by
    unfold stmtForm
    rw [ite_eq_left htreach]
  have hS := F.spec.block t b hb
  rw [hform] at hS
  refine ⟨_, E₁', r', hS, hE₁', hr', hs, ?_, rfl⟩
  rw [F.spec.exits t b hb htreach]
  exact hl

/-- A block of the output subroutine is the renamed block of the walk. -/
private theorem toSsa_block {t : Tid} {o : Blk} (ho : (Cfg.fromSub sub).block t = some o) :
    (Cfg.fromSub (toSsa sub)).block t = (ssaCfg sub).block t := by
  have key : ∀ l : List Blk, (∀ b ∈ l, b ∈ sub.blks) → t ∈ l.map Blk.tid →
      (l.filterMap fun blk => (ssaCfg sub).block blk.tid).find? (fun b => decide (b.tid = t)) = (ssaCfg sub).block t := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro hl ht
      obtain ⟨x, hx⟩ := block_exists (connected_tids_mem sub (hl b (by simp)))
      have hxt : x.tid = b.tid := (block_some hx).2
      simp only [List.filterMap_cons, hx, List.find?_cons]
      by_cases hbt : b.tid = t
      · subst hbt
        simp [hxt, hx]
      · have : (decide (x.tid = t)) = false := by simp [hxt, hbt]
        rw [this]
        refine ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) ?_
        rcases List.mem_cons.1 ht with h | h
        · exact absurd h.symm hbt
        · exact h
  have hm := block_some ho
  exact key sub.blks (fun _ h => h) (List.mem_map.2 ⟨o, hm.1, hm.2⟩)

private theorem storeShape_append (a b : List (Var × Value)) : storeShape (a ++ b) = storeShape a ++ storeShape b := by
  simp [storeShape]

private theorem jump_rename {en ex : Tid → RenameState} (F : SsaTables sub en ex) {t : Tid} {o : Blk}
    (ho : (Cfg.fromSub sub).block t = some o) (htr : Reach sub t) {E E' : Env}
    (hI : ∀ w, Tracked (mentionedOf sub) w → Bil.lookup E' (topName w (ex t)) = Bil.lookup E w)
    {j : Jmp} (hj : j ∈ o.jmps) {e : Exp} (he : e ∈ jmpExps j) :
    evalExp E' (renameExp (ex t) e) = evalExp E e :=
  eval_renameExp (exit_wf F htr) e hI fun _ hx =>
    Or.inr (jump_read_mentioned (real_mem_connected (block_some ho).1) hj (freeVars_of_jmpExps he hx))

/-- The simulation along a path: a run of the input from a block is a run of the output along the same
path, with every tracked variable readable under the name the output keeps it in. -/
private theorem ssa_run_sim {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {p t : Tid} {E F₀ : Env}
    {path : List Tid} {tr : List (Var × Value)} {f : Blk} (h : Run (Cfg.fromSub sub) p t E path tr F₀ f)
    (he : (p, t) ∈ (connG sub).edges) (hp : Reach sub p) {E' : Env}
    (hI : ∀ w, Tracked (mentionedOf sub) w → Bil.lookup E' (topName w (ex p)) = Bil.lookup E w) :
    ∃ tr' F' f', Run (Cfg.fromSub (toSsa sub)) p t E' path tr' F' f' ∧ storeShape tr' = storeShape tr ∧ f'.tid = f.tid ∧
      (Cfg.fromSub sub).block f.tid = some f ∧
      (∀ w, Tracked (mentionedOf sub) w → Bil.lookup F' (topName w (ex f.tid)) = Bil.lookup F₀ w) ∧
      f'.jmps = f.jmps.map (Jmp.mapExp (renameExp (ex f.tid))) := by
  induction h generalizing E' with
  | @last p t E E₁ r blk hb hphis hdefs =>
    obtain ⟨sb, E₁', r', hS, hp', hd', hs, hl, hj⟩ := ssa_block_sim hwf F he hp hb hI hphis hdefs
    have hbt := (block_some hb).2
    have hsbt := (block_some hS).2
    refine ⟨r'.2, r'.1, sb, .last (by rw [toSsa_block hb]; exact hS) hp' hd', hs, by rw [hsbt, hbt], by rw [hbt]; exact hb, ?_, ?_⟩
    · rw [hbt]
      exact hl
    · rw [hbt]
      exact hj
  | @next p t t' E E₁ r blk j path stores final lastBlk hb hphis hdefs hsel htarget hsucc hrest ih =>
    obtain ⟨sb, E₁', r', hS, hp', hd', hs, hl, hj⟩ := ssa_block_sim hwf F he hp hb hI hphis hdefs
    have htr := real_reach hb
    have hS' : (Cfg.fromSub (toSsa sub)).block t = some sb := by
      rw [toSsa_block hb]
      exact hS
    have hedge : (t, t') ∈ (connG sub).edges :=
      connected_edges_superset sub ((Bap.Graph.successors_mem _ _ _).1 hsucc)
    obtain ⟨tr', F', f', hrun, hshape, hft, hfb, hfl, hfj⟩ := ih hedge htr hl
    have hsel' : selectJmp r'.1 sb.jmps = .ok (some (j.mapExp (renameExp (ex t)))) := by
      rw [hj]
      have := selectJmp_mapExp (env := r.1) (env' := r'.1) (g := renameExp (ex t)) (jmps := blk.jmps) (o := some j)
        (fun a ha e he v hv => by
          rw [jump_rename F hb htr hl ha he]
          exact hv) hsel
      simpa using this
    have htarget' : t' ∈ (j.mapExp (renameExp (ex t))).successors := by
      rw [Jmp.successors_mapExp]
      exact htarget
    refine ⟨r'.2 ++ tr', F', f', .next hS' hp' hd' hsel' htarget'
      (fromSub_jump_edge hS' (selectJmp_mem hsel') htarget') hrun, ?_, hft, hfb, hfl, hfj⟩
    rw [storeShape_append, storeShape_append, hs, hshape]

/-- Variables an unversioned read of the input may be renamed to: the name keeps the base. -/
private theorem exit_name_base {en ex : Tid → RenameState} (F : SsaTables sub en ex) {n : Tid} (hn : Reach sub n) {w : Var}
    (hw : Tracked (mentionedOf sub) w) : (topName w (ex n)).base = w.base :=
  ((exit_wf F hn).top hw).1

private theorem fromSub_start_block {t : Tid} {b : Blk} (h : (Cfg.fromSub sub).block t = some b) : sub.blks ≠ [] := by
  intro he
  have := (block_some h).1
  rw [show (Cfg.fromSub sub).blocks = sub.blks from rfl, he] at this
  simp at this

/-- Nothing is ever inserted at the pseudo start: no edge enters it, so it is in no frontier. -/
private theorem phi_block_start (hwf : SubWf sub) : (phiCfg sub).block pseudoStart = some ⟨pseudoStart, [], [], []⟩ := by
  obtain ⟨ins, hi, hall⟩ := (phiCfg_spec sub).1.blocks pseudoStart _ connected_block_start
  have hnil : ins = [] := by
    cases ins with
    | nil => rfl
    | cons φ rest =>
      exfalso
      have hv := (hall φ (by simp)).1
      rcases (phiCfg_spec sub).2.2 φ.var hv pseudoStart _ _ connected_block_start hi ⟨φ, by simp, rfl⟩ with h | h
      · obtain ⟨ψ, hψ, _⟩ := h
        simp at hψ
      · have hany : ∃ u, pseudoStart ∈ (Assoc.get u (Cfg.connected sub).dominanceFrontier).getD [] := by
          cases h with
          | base _ hj => exact ⟨_, hj⟩
          | step _ hj => exact ⟨_, hj⟩
        obtain ⟨u, hu⟩ := hany
        cases hg : Assoc.get u (Cfg.connected sub).dominanceFrontier with
        | none =>
          rw [hg] at hu
          simp at hu
        | some f =>
          rw [hg] at hu
          obtain ⟨_, p, hp⟩ := Bap.Proofs.Graph.dominanceFrontier_target (get_mem_env' hg) hu
          exact hwf.no_edge_to_start hp
  rw [hi, hnil]
  rfl

/-- At the exit of the pseudo start every variable reads itself. -/
private theorem start_names {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) (w : Var) :
    topName w (ex pseudoStart) = w := by
  have hr : Reach sub pseudoStart := by
    show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact start_mem_reachable (by rw [connected_nodes]; simp)
  rw [F.spec.exits _ _ (phi_block_start hwf) hr, F.entry]
  rfl

/-- Reads under renaming: a free variable of a renamed expression is what a free variable of the original
reads. -/
private theorem occursFree_substitute (rs : List (Var × Exp)) (e : Exp) (x : Var) (h : Bil.occursFree x (Bil.substitute rs e) = true) :
    ∃ w, Bil.occursFree w e = true ∧ match Assoc.get w rs with
      | some r => Bil.occursFree x r = true
      | none => x = w := by
  induction e generalizing rs with
  | int v => simp [Bil.substitute, Bil.occursFree] at h
  | unknown m t => simp [Bil.substitute, Bil.occursFree] at h
  | var v =>
    refine ⟨v, by simp [Bil.occursFree], ?_⟩
    simp only [Bil.substitute] at h
    cases hg : Assoc.get v rs with
    | none =>
      simp only [hg, Option.getD_none, Bil.occursFree, beq_iff_eq] at h
      exact h.symm
    | some r => simpa [hg] using h
  | load m a _ _ ih₁ ih₂ =>
    simp only [Bil.substitute, Bil.occursFree, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨w, hw, hr⟩ := ih₁ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₂ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
  | store m a v _ _ ih₁ ih₂ ih₃ =>
    simp only [Bil.substitute, Bil.occursFree, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · obtain ⟨w, hw, hr⟩ := ih₁ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₂ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₃ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
  | bin _ l r ih₁ ih₂ =>
    simp only [Bil.substitute, Bil.occursFree, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨w, hw, hr⟩ := ih₁ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₂ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
  | concat l r ih₁ ih₂ =>
    simp only [Bil.substitute, Bil.occursFree, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨w, hw, hr⟩ := ih₁ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₂ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
  | un _ v ih =>
    simp only [Bil.substitute, Bil.occursFree] at h
    obtain ⟨w, hw, hr⟩ := ih rs h
    exact ⟨w, by simpa [Bil.occursFree] using hw, hr⟩
  | cast _ _ v ih =>
    simp only [Bil.substitute, Bil.occursFree] at h
    obtain ⟨w, hw, hr⟩ := ih rs h
    exact ⟨w, by simpa [Bil.occursFree] using hw, hr⟩
  | extract _ _ v ih =>
    simp only [Bil.substitute, Bil.occursFree] at h
    obtain ⟨w, hw, hr⟩ := ih rs h
    exact ⟨w, by simpa [Bil.occursFree] using hw, hr⟩
  | ite c y n ih₁ ih₂ ih₃ =>
    simp only [Bil.substitute, Bil.occursFree, Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · obtain ⟨w, hw, hr⟩ := ih₁ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₂ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
    · obtain ⟨w, hw, hr⟩ := ih₃ rs h
      exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
  | letIn v val body ih₁ ih₂ =>
    have hfilter : ∀ w, w ≠ v → Assoc.get w (rs.filter fun r => r.1 != v) = Assoc.get w rs := by
      intro w hw
      have key : ∀ l : List (Var × Exp), List.lookup w (l.filter fun r => r.1 != v) = List.lookup w l := by
        intro l
        induction l with
        | nil => rfl
        | cons e es ih =>
          obtain ⟨a, b⟩ := e
          by_cases ha : a = v
          · subst ha
            have hb : (w == a) = false := by simpa using hw
            simp [List.lookup, hb, ih]
          · have hb : (a != v) = true := by simpa using ha
            simp [hb, List.lookup, ih]
      exact key rs
    simp only [Bil.substitute] at h
    split at h
    · simp only [Bil.occursFree, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hne, h⟩
      · obtain ⟨w, hw, hr⟩ := ih₁ rs h
        exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
      · obtain ⟨w, hw, hr⟩ := ih₂ _ h
        by_cases hwv : w = v
        · subst hwv
          simp only [Assoc.get, List.lookup, beq_self_eq_true, Bil.occursFree, beq_iff_eq] at hr
          simp at hne
          exact absurd hr hne
        · have hb : (w == v) = false := by simpa using hwv
          refine ⟨w, ?_, ?_⟩
          · simp [Bil.occursFree, hw, Ne.symm hwv]
          · have hget : Assoc.get w ((v, Exp.var (Bil.freshVersion v
                ((rs.filter fun r => r.1 != v).flatMap (Bil.freeVars ·.2) ++ Bil.freeVars body))) ::
                rs.filter fun r => r.1 != v) = Assoc.get w rs := by
              simp only [Assoc.get, List.lookup, hb]
              exact hfilter w hwv
            rwa [hget] at hr
    · simp only [Bil.occursFree, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨hne, h⟩
      · obtain ⟨w, hw, hr⟩ := ih₁ rs h
        exact ⟨w, by simp [Bil.occursFree, hw], hr⟩
      · obtain ⟨w, hw, hr⟩ := ih₂ _ h
        by_cases hwv : w = v
        · subst hwv
          have hnone : Assoc.get w (rs.filter fun r => r.1 != w) = none := by
            have key : ∀ l : List (Var × Exp), List.lookup w (l.filter fun r => r.1 != w) = none := by
              intro l
              induction l with
              | nil => rfl
              | cons e es ih =>
                obtain ⟨a, b⟩ := e
                by_cases ha : a = w
                · subst ha
                  simpa [List.filter_cons] using ih
                · have hb : (a != w) = true := by simpa using ha
                  have hb' : (w == a) = false := by simpa using Ne.symm ha
                  simp [hb, List.lookup, hb', ih]
            exact key rs
          rw [hnone] at hr
          simp at hne
          exact absurd hr.symm hne
        · refine ⟨w, ?_, ?_⟩
          · simp [Bil.occursFree, hw, Ne.symm hwv]
          · rwa [hfilter w hwv] at hr

/-- A free variable of a renamed expression is the current name of a free variable of the original. -/
private theorem freeVars_renameExp {st : RenameState} (hk : (st.stacks.map Prod.fst).Nodup) {e : Exp} {x : Var}
    (h : x ∈ Bil.freeVars (renameExp st e)) : ∃ w ∈ Bil.freeVars e, x = topName w st := by
  obtain ⟨w, hw, hr⟩ := occursFree_substitute _ e x ((Bap.Proofs.Bil.mem_freeVars_iff _ _).1 h)
  refine ⟨w, (Bap.Proofs.Bil.mem_freeVars_iff _ _).2 hw, ?_⟩
  rw [get_ssaReplacements st hk] at hr
  rw [topName_of_stack]
  cases hl : (stackOf st w).head? with
  | none =>
    rw [hl] at hr
    exact hr
  | some y =>
    rw [hl] at hr
    simp only [Option.map_some, Bil.occursFree, beq_iff_eq] at hr
    simp [hr]

theorem mem_jmp_freeVars {jmp : Jmp} {x : Var} (h : x ∈ jmp.freeVars) : ∃ e ∈ jmpExps jmp, x ∈ Bil.freeVars e := by
  obtain ⟨tid, condition, kind⟩ := jmp
  simp only [Jmp.freeVars, List.mem_eraseDups, List.mem_append] at h
  have hl : ∀ {l : Label}, x ∈ l.freeVars → ∃ e ∈ labelExps l, x ∈ Bil.freeVars e := by
    intro l hx
    cases l with
    | direct _ => simp [Label.freeVars] at hx
    | indirect t => exact ⟨t, by simp [labelExps], hx⟩
  rcases h with h | h
  · cases condition with
    | none => simp at h
    | some c => exact ⟨c, by simp [jmpExps], by simpa using h⟩
  · cases kind with
    | goto t =>
      obtain ⟨e, he, hx⟩ := hl h
      exact ⟨e, by simp [jmpExps, he], hx⟩
    | ret t =>
      obtain ⟨e, he, hx⟩ := hl h
      exact ⟨e, by simp [jmpExps, he], hx⟩
    | call t r =>
      simp only [JmpKind.freeVars, List.mem_eraseDups, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨e, he, hx⟩ := hl h
        exact ⟨e, by simp [jmpExps, he], hx⟩
      · cases r with
        | none => simp at h
        | some l =>
          obtain ⟨e, he, hx⟩ := hl (by simpa using h)
          exact ⟨e, by simp [jmpExps, he], hx⟩
    | interrupt _ _ => simp [JmpKind.freeVars] at h

private theorem issued_ne_tracked {U : List Var} {st : RenameState} (h : RenameWf U st) (phis : List Phi) (defs : List Def)
    {y w : Var} (hy : y ∈ (renamePhis phis st).1.map Phi.var ++ (renameDefs defs (renamePhis phis st).2).1.map Def.var)
    (hw : Tracked U w) : y ≠ w := by
  rintro rfl
  have hr := ((issued_renamePhis phis st).append (issued_renameDefs defs (renamePhis phis st).2)).range y hy
  have := h.seed y hw
  omega

/-- The names a renamed block assigns. -/
private theorem defNames_renamed (f : Tid × Exp → Tid × Exp) (b : Blk) (st ex : RenameState) :
    defNames (withInputs f (renamedStmts b st ex)) =
      (renamePhis b.phis st).1.map Phi.var ++ (renameDefs b.defs (renamePhis b.phis st).2).1.map Def.var := by
  simp [defNames, Function.comp_def]

/-- The output block of a reachable block, as the walk left it. -/
private theorem ssa_block_form {en ex : Tid → RenameState} (F : SsaTables sub en ex) {n : Tid} (hn : Reach sub n) {b : Blk}
    (hb : (phiCfg sub).block n = some b) :
    (ssaCfg sub).block n = some (withInputs (doneInput (Canon (phiCfg sub) (Reach sub) · n) ex)
      (renamedStmts b (en n) (ex n))) := by
  have hform : stmtForm (Reach sub) en ex n b = renamedStmts b (en n) (ex n) := by
    unfold stmtForm
    rw [ite_eq_left hn]
  have hS := F.spec.block n b hb
  rwa [hform] at hS

/-- Every name on a stack at the exit of a block was assigned by a dominator of that block. -/
private theorem stack_scope {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) (k : Nat) (n : Tid)
    (hc : Bap.Proofs.Graph.IdomChain (connG sub) pseudoStart k n) (w y : Var) (hy : y ∈ stackOf (ex n) w) :
    ∃ a sb, DomC sub n a ∧ (ssaCfg sub).block a = some sb ∧ y ∈ defNames sb := by
  have hentry : ∀ m, (Reach sub m) → ∀ b, (phiCfg sub).block m = some b → ∀ y, y ∈ stackOf (ex m) w →
      y ∈ stackOf (en m) w ∨ ∃ sb, (ssaCfg sub).block m = some sb ∧ y ∈ defNames sb := by
    intro m hm b hb y hy
    rw [F.spec.exits m b hb hm] at hy
    obtain ⟨ys, hys, _, hsy⟩ := stackOf_renameDefs b.defs (renamePhis b.phis (en m)).2 w
    obtain ⟨xs, hxs, _, hsx⟩ := stackOf_renamePhis b.phis (en m) w
    rw [hys, hxs] at hy
    have hS := ssa_block_form F hm hb
    simp only [List.mem_append] at hy
    rcases hy with hy | hy | hy
    · refine Or.inr ⟨_, hS, ?_⟩
      rw [defNames_renamed]
      exact List.mem_append_right _ (hsy hy)
    · refine Or.inr ⟨_, hS, ?_⟩
      rw [defNames_renamed]
      exact List.mem_append_left _ (hsx hy)
    · exact Or.inl hy
  induction hc generalizing y with
  | start =>
    have hr : Reach sub pseudoStart := by
      show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
      rw [connected_start]
      exact start_mem_reachable (by rw [connected_nodes]; simp)
    rcases hentry _ hr _ (phi_block_start hwf) y hy with h | ⟨sb, hS, hm⟩
    · rw [F.entry] at h
      have : stackOf (initialState (Cfg.connected sub).blocks) w = [] := rfl
      rw [this] at h
      simp at h
    · exact ⟨_, sb, Bap.Proofs.Graph.Dom.refl _, hS, hm⟩
  | @step k u q hq _ ih =>
    have hq' : (u, q) ∈ idomOf sub := by
      show _ ∈ Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start
      rw [connected_start]
      exact hq
    obtain ⟨hur, _, _, hdq, _⟩ := idomOf_spec hq'
    obtain ⟨b, hb⟩ := phi_block_exists (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hur)
    rcases hentry u hur b hb y hy with h | ⟨sb, hS, hm⟩
    · rw [F.spec.tree u q hq' hur (dom_reach hur hdq) w] at h
      obtain ⟨a, sb, hd, hS, hm⟩ := ih y h
      exact ⟨a, sb, Bap.Proofs.Graph.Dom.trans hdq hd, hS, hm⟩
    · exact ⟨u, sb, Bap.Proofs.Graph.Dom.refl _, hS, hm⟩

/-- The same for the names visible on entry: they were assigned by a strict dominator. -/
private theorem entry_scope {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {n : Tid} (hn : Reach sub n)
    (w y : Var) (hy : y ∈ stackOf (en n) w) :
    ∃ a sb, DomC sub n a ∧ a ≠ n ∧ (ssaCfg sub).block a = some sb ∧ y ∈ defNames sb := by
  by_cases hs : n = pseudoStart
  · subst hs
    rw [F.entry] at hy
    have : stackOf (initialState (Cfg.connected sub).blocks) w = [] := rfl
    rw [this] at hy
    simp at hy
  · obtain ⟨i, hi⟩ : ∃ i, (n, i) ∈ idomOf sub := by
      have := Bap.Proofs.Graph.immediateDominators_exists (reach_iff.1 hn) hs
      show ∃ i, (n, i) ∈ Bap.Graph.immediateDominators (connG sub) (Cfg.connected sub).start
      rw [connected_start]
      exact this
    obtain ⟨_, _, hin, hd, _⟩ := idomOf_spec hi
    have hir := dom_reach hn hd
    rw [F.spec.tree n i hi hn hir w] at hy
    obtain ⟨k, _, hc⟩ := Bap.Proofs.Graph.idomChain_exists (reach_iff.1 hir)
    obtain ⟨a, sb, hda, hS, hm⟩ := stack_scope hwf F k i hc w y hy
    refine ⟨a, sb, Bap.Proofs.Graph.Dom.trans hd hda, ?_, hS, hm⟩
    rintro rfl
    exact hin (dom_antisymm hir hda hd)

/-- Names of the output are not variables of the input. -/
private theorem output_name_ne {en ex : Tid → RenameState} (_hwf : SubWf sub) (F : SsaTables sub en ex) {n : Tid} (hn : Reach sub n)
    {sb : Blk} (hS : (ssaCfg sub).block n = some sb) {y w : Var} (hy : y ∈ defNames sb) (hw : Tracked (mentionedOf sub) w) :
    y ≠ w := by
  obtain ⟨b, hb⟩ := phi_block_exists (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ hn)
  rw [ssa_block_form F hn hb] at hS
  cases hS
  rw [defNames_renamed] at hy
  exact issued_ne_tracked (F.spec.wf n hn) _ _ hy hw

private theorem walk_exit {g : Bap.Graph.Graph Tid} {s x : Tid} {p : List Tid} (hs : s ≠ pseudoExit)
    (he : ∀ b, (pseudoExit, b) ∉ g.edges) (h : Bap.Proofs.Graph.Walk g s x p) (hm : pseudoExit ∈ p) : x = pseudoExit := by
  induction h with
  | nil _ =>
    exact absurd (List.mem_singleton.1 hm).symm hs
  | @cons a b p hw hedge _ ih =>
    rcases List.mem_cons.1 hm with h | h
    · exact h.symm
    · have := ih h
      subst this
      exact absurd hedge (he _)

/-- A proper dominator of a block of the subroutine is a block of the subroutine. -/
private theorem dom_real (hwf : SubWf sub) {n a : Tid} (hn : n ∈ sub.blks.map Blk.tid) (hd : DomC sub n a) (hne : a ≠ pseudoStart) :
    a ∈ sub.blks.map Blk.tid := by
  have hr := connected_all_reachable sub hn
  have har := dom_reach hr hd
  have hnode := Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ har
  rw [connected_nodes] at hnode
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hnode
  rcases hnode with h | h | h
  · exact absurd h hne
  · exact h
  · subst h
    obtain ⟨w, hw⟩ := (Bap.Proofs.Graph.mem_reachable_iff_walk n).1 (reach_iff.1 hr)
    have := walk_exit pseudoStart_ne_exit (fun b => hwf.no_edge_from_exit) hw (hd w hw)
    subst this
    obtain ⟨b, hb, ht⟩ := List.mem_map.1 hn
    exact absurd ht (hwf.exit_ne hb)

private theorem mem_toSsa_of_block {a : Tid} {sb : Blk} (ha : a ∈ sub.blks.map Blk.tid) (hS : (ssaCfg sub).block a = some sb) :
    sb ∈ (toSsa sub).blks := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
  rw [toSsa_eq]
  exact List.mem_filterMap.2 ⟨o, ho, hS⟩

private theorem toSsa_blocks_cases {blk : Blk} (h : blk ∈ (toSsa sub).blks) :
    ∃ o ∈ sub.blks, o.tid = blk.tid ∧ (ssaCfg sub).block blk.tid = some blk := by
  rw [toSsa_eq] at h
  obtain ⟨o, ho, hS⟩ := List.mem_filterMap.1 h
  have ht := (block_some hS).2
  exact ⟨o, ho, ht.symm, by rw [ht]; exact hS⟩

/-- With tids that can be told apart, a block found by tid is the one listed. -/
private theorem fromSub_block_of_mem (hwf : SubWf sub) {o : Blk} (ho : o ∈ sub.blks) : (Cfg.fromSub sub).block o.tid = some o := by
  have hnd : (sub.blks.map Blk.tid).Nodup := by
    have := hwf.nodup
    simp only [List.cons_append, List.nodup_cons, List.nodup_append] at this
    exact this.2.1
  obtain ⟨x, hx⟩ := block_exists (cfg := Cfg.fromSub sub) (List.mem_map.2 ⟨o, ho, rfl⟩)
  have hm := block_some hx
  rw [hx, eq_of_tid_eq hnd ho hm.1 hm.2.symm]

/-- Walks of the output are walks of the connected CFG, entered through the pseudo start. -/
private theorem toSsa_walk (hwf : SubWf sub) {x : Tid} {p : List Tid}
    (h : Bap.Proofs.Graph.Walk (Cfg.fromSub (toSsa sub)).graph (Cfg.fromSub (toSsa sub)).start x p) :
    Bap.Proofs.Graph.Walk (connG sub) pseudoStart x (p ++ [pseudoStart]) := by
  have htids := toSsa_tids sub
  have hpairs := toSsa_successors sub hwf.nodup
  have hnodes : ∀ {t}, t ∈ (Cfg.fromSub (toSsa sub)).graph.nodes → t ∈ (connG sub).nodes := by
    intro t ht
    have ht' : t ∈ (toSsa sub).blks.map Blk.tid := ht
    rw [htids] at ht'
    rw [connected_nodes]
    simp [ht']
  have hedges : ∀ {a b}, (a, b) ∈ (Cfg.fromSub (toSsa sub)).graph.edges → (a, b) ∈ (connG sub).edges := by
    intro a b he
    obtain ⟨blk, hblk, hta, hs⟩ := (fromSub_mem_edges _ a b).1 he
    have hp : (blk.tid, blk.successors) ∈ (toSsa sub).blks.map (fun b => (b.tid, b.successors)) :=
      List.mem_map.2 ⟨blk, hblk, rfl⟩
    rw [hpairs] at hp
    obtain ⟨o, ho, heq⟩ := List.mem_map.1 hp
    simp only [Prod.mk.injEq] at heq
    exact connected_edges_superset sub ((fromSub_mem_edges sub a b).2 ⟨o, ho, heq.1.trans hta, heq.2 ▸ hs⟩)
  induction h with
  | nil hs =>
    have hne : sub.blks ≠ [] := by
      intro he
      have ht : (Cfg.fromSub (toSsa sub)).start ∈ (toSsa sub).blks.map Blk.tid := hs
      rw [htids, he] at ht
      simp at ht
    have hstart : (Cfg.fromSub (toSsa sub)).start = (Cfg.fromSub sub).start := by
      show ((toSsa sub).blks.head?.map Blk.tid).getD 0 = (sub.blks.head?.map Blk.tid).getD 0
      have : (toSsa sub).blks.head?.map Blk.tid = sub.blks.head?.map Blk.tid := by
        rw [← List.head?_map, ← List.head?_map, htids]
      rw [this]
    have he := connected_entry_edge hne
    rw [← hstart] at he
    exact .cons (.nil (by rw [connected_nodes]; simp)) he (hnodes hs)
  | cons _ he hn ih => exact .cons ih (hedges he) (hnodes hn)

/-- Transfer of dominance to the output. -/
private theorem dom_transfer (hwf : SubWf sub) {n a : Tid} (hd : DomC sub n a) (hne : a ≠ pseudoStart) :
    Bap.Proofs.Graph.Dom (Cfg.fromSub (toSsa sub)).graph (Cfg.fromSub (toSsa sub)).start n a := by
  intro p hp
  rcases List.mem_append.1 (hd _ (toSsa_walk hwf hp)) with h | h
  · exact h
  · exact absurd (List.mem_singleton.1 h) hne

/-- A read in `blk`, after the definitions `earlier`, has its reaching definition available: its variable
is assigned nowhere, so it reads the entry value, or by a phi of `blk`, or by a definition before the
read, or in a block strictly dominating `blk`. -/
def DefReaches (out : Sub) (blk : Blk) (earlier : List Def) (x : Var) : Prop :=
  (∀ b ∈ out.blks, x ∉ defNames b) ∨ x ∈ blk.phis.map Phi.var ∨ x ∈ earlier.map Def.var ∨
    ∃ a ∈ out.blks, a.tid ≠ blk.tid ∧ x ∈ defNames a ∧
      Bap.Proofs.Graph.Dom (Cfg.fromSub out).graph (Cfg.fromSub out).start blk.tid a.tid

private theorem real_name_cases {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {w x : Var}
    (hw : Tracked (mentionedOf sub) w) (hx : x = w) : ∀ b ∈ (toSsa sub).blks, x ∉ defNames b := by
  intro b hb hm
  obtain ⟨o, ho, ht, hS⟩ := toSsa_blocks_cases hb
  exact output_name_ne hwf F (connected_all_reachable sub (List.mem_map.2 ⟨o, ho, ht⟩)) hS hm hw hx

private theorem no_names_at_start {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {sb : Blk} {y : Var}
    (hS : (ssaCfg sub).block pseudoStart = some sb) (hm : y ∈ defNames sb) : False := by
  have hr : Reach sub pseudoStart := by
    show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact start_mem_reachable (by rw [connected_nodes]; simp)
  rw [ssa_block_form F hr (phi_block_start hwf)] at hS
  cases hS
  rw [defNames_renamed] at hm
  simp [renamePhis_nil, renameDefs_nil] at hm

private theorem ancestor_reaches {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {blk : Blk}
    (hblk : blk ∈ (toSsa sub).blks) {y w : Var} (hy : y ∈ stackOf (en blk.tid) w) (earlier : List Def) :
    DefReaches (toSsa sub) blk earlier y := by
  obtain ⟨o, ho, ht, _⟩ := toSsa_blocks_cases hblk
  have hmem : blk.tid ∈ sub.blks.map Blk.tid := List.mem_map.2 ⟨o, ho, ht⟩
  obtain ⟨a, sb, hd, hne, hS, hm⟩ := entry_scope hwf F (connected_all_reachable sub hmem) w y hy
  have hastart : a ≠ pseudoStart := by
    rintro rfl
    exact no_names_at_start hwf F hS hm
  have hreal := dom_real hwf hmem hd hastart
  have hsbt := (block_some hS).2
  refine Or.inr (Or.inr (Or.inr ⟨sb, mem_toSsa_of_block hreal hS, by rw [hsbt]; exact hne, hm, ?_⟩))
  rw [hsbt]
  exact dom_transfer hwf hd hastart

/-- The output block and its input, for a block of the output. -/
private theorem toSsa_block_form {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {blk : Blk}
    (hblk : blk ∈ (toSsa sub).blks) :
    ∃ o ∈ sub.blks, ∃ ins, o.tid = blk.tid ∧ (phiCfg sub).block blk.tid = some { o with phis := o.phis ++ ins } ∧
      (∀ φ ∈ ins, φ.var ∈ phiVars sub ∧ φ.var ∉ o.phis.map Phi.var ∧
        φ.values = ((Cfg.connected sub).predecessors blk.tid).map fun pred => (pred, Exp.var φ.var)) ∧
      blk = withInputs (doneInput (Canon (phiCfg sub) (Reach sub) · blk.tid) ex)
        (renamedStmts { o with phis := o.phis ++ ins } (en blk.tid) (ex blk.tid)) ∧ Reach sub blk.tid := by
  obtain ⟨o, ho, ht, hS⟩ := toSsa_blocks_cases hblk
  have hfb := fromSub_block_of_mem hwf ho
  rw [ht] at hfb
  obtain ⟨ins, hb, hall⟩ := phi_block_real hwf hfb
  have hr := real_reach hfb
  refine ⟨o, ho, ins, ht, hb, hall, ?_, hr⟩
  have := ssa_block_form F hr hb
  rw [hS] at this
  exact Option.some.inj this

private theorem exit_reaches {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {blk : Blk}
    (hblk : blk ∈ (toSsa sub).blks) {w x : Var} (hw : Tracked (mentionedOf sub) w) (hx : x = topName w (ex blk.tid)) :
    DefReaches (toSsa sub) blk blk.defs x := by
  obtain ⟨o, _, ins, _, hb, _, hform, hr⟩ := toSsa_block_form hwf F hblk
  rcases topName_cases w (ex blk.tid) with h | h
  · exact Or.inl (real_name_cases hwf F hw (hx.trans h))
  · rw [← hx] at h
    rw [F.spec.exits _ _ hb hr] at h
    obtain ⟨ys, hys, _, hsy⟩ := stackOf_renameDefs { o with phis := o.phis ++ ins }.defs
      (renamePhis { o with phis := o.phis ++ ins }.phis (en blk.tid)).2 w
    obtain ⟨xs, hxs, _, hsx⟩ := stackOf_renamePhis { o with phis := o.phis ++ ins }.phis (en blk.tid) w
    rw [exitOf, hys, hxs] at h
    simp only [List.mem_append] at h
    rcases h with h | h | h
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [congrArg Blk.defs hform]
      exact hsy h
    · refine Or.inr (Or.inl ?_)
      rw [congrArg Blk.phis hform]
      simpa [withInputs, renamedStmts, setVals, Function.comp_def] using hsx h
    · exact ancestor_reaches hwf F hblk h _

/-- Position of a read inside renamed definitions. -/
private theorem renameDefs_read {U : List Var} (defs : List Def) {st : RenameState} (hst : RenameWf U st) {pre post : List Def} {d : Def}
    (h : (renameDefs defs st).1 = pre ++ d :: post) :
    ∃ c ∈ defs, ∃ st', d.rhs = renameExp st' c.rhs ∧ RenameWf U st' ∧
      ∀ k y, y ∈ stackOf st' k → y ∈ stackOf st k ∨ y ∈ pre.map Def.var := by
  induction defs generalizing st pre with
  | nil =>
    rw [renameDefs_nil] at h
    cases pre <;> simp at h
  | cons e es ih =>
    rw [renameDefs_cons] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      refine ⟨e, by simp, st, ?_, hst, fun _ _ hy => Or.inl hy⟩
      rw [← h.1]
    | cons a as =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨c, hc, st', hrhs, hwf', hstack⟩ := ih (hst.push e.var) h.2
      refine ⟨c, List.mem_cons_of_mem _ hc, st', hrhs, hwf', ?_⟩
      intro k y hy
      rcases hstack k y hy with hy | hy
      · rw [stackOf_newName] at hy
        split at hy
        · rcases List.mem_cons.1 hy with hy | hy
          · refine Or.inr ?_
            rw [hy, ← h.1]
            simp
          · exact Or.inl hy
        · exact Or.inl hy
      · exact Or.inr (List.mem_cons_of_mem _ hy)

private theorem renamePhis_values (phis : List Phi) (st : RenameState) {φ : Phi} (h : φ ∈ (renamePhis phis st).1) :
    ∃ ψ ∈ phis, φ.values = ψ.values := by
  induction phis generalizing st with
  | nil => simp [renamePhis_nil] at h
  | cons p ps ih =>
    rw [renamePhis_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨p, by simp, rfl⟩
    · obtain ⟨ψ, hψ, he⟩ := ih _ h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, he⟩

private theorem toSsa_edge (hwf : SubWf sub) {a b : Tid} (he : (a, b) ∈ (Cfg.fromSub (toSsa sub)).graph.edges) :
    (a, b) ∈ (connG sub).edges := by
  obtain ⟨blk, hblk, hta, hs⟩ := (fromSub_mem_edges _ a b).1 he
  have hp : (blk.tid, blk.successors) ∈ (toSsa sub).blks.map (fun b => (b.tid, b.successors)) :=
    List.mem_map.2 ⟨blk, hblk, rfl⟩
  rw [toSsa_successors sub hwf.nodup] at hp
  obtain ⟨o, ho, heq⟩ := List.mem_map.1 hp
  simp only [Prod.mk.injEq] at heq
  exact connected_edges_superset sub ((fromSub_mem_edges sub a b).2 ⟨o, ho, heq.1.trans hta, heq.2 ▸ hs⟩)

/-- The SSA property. In the output of `toSsa`, the reaching definition of every read is available:
a definition's read sees a phi of its block, an earlier definition of its block or a strict dominator;
a jump's read sees all of its block too; and the input a phi takes from a predecessor sees the same in
that predecessor. Reads of a variable assigned nowhere read the entry value. Together with
`toSsa_single_assignment` each read has exactly one definition, and it dominates the read. -/
theorem toSsa_uses_dominated (sub : Sub) (hwf : SubWf sub) (blk : Blk) (hblk : blk ∈ (toSsa sub).blks) :
    (∀ pre d post, blk.defs = pre ++ d :: post → ∀ x ∈ Bil.freeVars d.rhs, DefReaches (toSsa sub) blk pre x) ∧
    (∀ j ∈ blk.jmps, ∀ x ∈ j.freeVars, DefReaches (toSsa sub) blk blk.defs x) ∧
    ∀ phi ∈ blk.phis, ∀ pb ∈ (toSsa sub).blks, blk.tid ∈ pb.successors → ∀ e,
      Assoc.get pb.tid phi.values = some e → ∀ x ∈ Bil.freeVars e, DefReaches (toSsa sub) pb pb.defs x := by
  obtain ⟨en, ex, F⟩ := ssa_tables hwf
  obtain ⟨o, ho, ins, ht, hb, hins, hform, hr⟩ := toSsa_block_form hwf F hblk
  have hom : o ∈ (Cfg.connected sub).blocks := real_mem_connected ho
  have hwft := F.spec.wf _ hr
  refine ⟨?_, ?_, ?_⟩
  · intro pre d post hdefs x hx
    have hd : (renameDefs { o with phis := o.phis ++ ins }.defs
        (renamePhis { o with phis := o.phis ++ ins }.phis (en blk.tid)).2).1 = pre ++ d :: post := by
      rw [← hdefs]
      exact (congrArg Blk.defs hform).symm
    obtain ⟨c, hc, st', hrhs, hwf', hstack⟩ := renameDefs_read _ (hwft.renamePhis _) hd
    rw [hrhs] at hx
    obtain ⟨w, hw, hxw⟩ := freeVars_renameExp hwf'.keys hx
    have htrack : Tracked (mentionedOf sub) w := Or.inr (def_read_mentioned hom hc hw)
    rcases topName_cases w st' with h | h
    · exact Or.inl (real_name_cases hwf F htrack (hxw.trans h))
    · rw [← hxw] at h
      rcases hstack w x h with h | h
      · obtain ⟨xs, hxs, _, hsx⟩ := stackOf_renamePhis { o with phis := o.phis ++ ins }.phis (en blk.tid) w
        rw [hxs] at h
        rcases List.mem_append.1 h with h | h
        · refine Or.inr (Or.inl ?_)
          rw [congrArg Blk.phis hform]
          simpa [withInputs, renamedStmts, setVals, Function.comp_def] using hsx h
        · exact ancestor_reaches hwf F hblk h _
      · exact Or.inr (Or.inr (Or.inl h))
  · intro j hj x hx
    obtain ⟨e', he', hxe⟩ := mem_jmp_freeVars hx
    have hjm : j ∈ o.jmps.map (Jmp.mapExp (renameExp (ex blk.tid))) := by
      rw [congrArg Blk.jmps hform] at hj
      exact hj
    obtain ⟨j₀, hj₀, rfl⟩ := List.mem_map.1 hjm
    rw [jmpExps_mapExp] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have hwfex := exit_wf F hr
    obtain ⟨w, hw, hxw⟩ := freeVars_renameExp hwfex.keys hxe
    exact exit_reaches hwf F hblk (Or.inr (jump_read_mentioned hom hj₀ (freeVars_of_jmpExps he hw))) hxw
  · intro phi hphi pb hpb hs e hget x hx
    obtain ⟨op, hop, opt, hpr⟩ : ∃ op ∈ sub.blks, ∃ h : op.tid = pb.tid, Reach sub pb.tid := by
      obtain ⟨op, hop, ht', _⟩ := toSsa_blocks_cases hpb
      exact ⟨op, hop, ht', connected_all_reachable sub (List.mem_map.2 ⟨op, hop, ht'⟩)⟩
    have hedge : (pb.tid, blk.tid) ∈ (connG sub).edges :=
      toSsa_edge hwf ((fromSub_mem_edges _ _ _).2 ⟨pb, hpb, rfl, hs⟩)
    have hcanon : Canon (phiCfg sub) (Reach sub) pb.tid blk.tid :=
      ⟨hpr, (Bap.Graph.successors_mem _ _ _).2 (by
        rw [(phiCfg_spec sub).1.graph]
        exact hedge)⟩
    have hphim : phi ∈ ((renamePhis { o with phis := o.phis ++ ins }.phis (en blk.tid)).1).map
        (setVals (doneInput (Canon (phiCfg sub) (Reach sub) · blk.tid) ex)) := by
      rw [congrArg Blk.phis hform] at hphi
      exact hphi
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hphim
    obtain ⟨ψ, hψ, hvals⟩ := renamePhis_values _ _ hφ
    have hg := get_doneInput (D := (Canon (phiCfg sub) (Reach sub) · blk.tid)) ex hcanon φ.values
    simp only at hget
    rw [hg, hvals] at hget
    cases hg₀ : Assoc.get pb.tid ψ.values with
    | none =>
      rw [hg₀] at hget
      simp at hget
    | some e₀ =>
      rw [hg₀] at hget
      simp only [Option.map_some, Option.some.injEq] at hget
      subst hget
      have hwfex := exit_wf F hpr
      obtain ⟨w, hw, hxw⟩ := freeVars_renameExp hwfex.keys hx
      refine exit_reaches hwf F hpb (Or.inr ?_) hxw
      rcases List.mem_append.1 hψ with h | h
      · exact phi_read_mentioned hom h (get_mem_env' hg₀) hw
      · have hv := (hins ψ h)
        rw [hv.2.2] at hg₀
        have hpm : pb.tid ∈ (Cfg.connected sub).predecessors blk.tid := (mem_predecessors' _ _ _).2 hedge
        rw [get_trivial_values _ _ hpm] at hg₀
        cases hg₀
        have hx' : w = ψ.var := by
          have := (Bap.Proofs.Bil.mem_freeVars_iff w (.var ψ.var)).1 hw
          simp only [Bil.occursFree, beq_iff_eq] at this
          exact this.symm
        exact hx' ▸ mem_phiVars_mentioned hv.1

/-- Phi placement is exactly the iterated dominance frontier. Apart from phis the input already has, a
block gets a phi for a variable just when it lies in the iterated dominance frontier of the blocks
assigning that variable: minimal SSA in the sense of Cytron et al. -/
theorem phi_placement_exact (sub : Sub) (hwf : SubWf sub) (var : Var) (hvar : var ∈ phiVars sub) {n : Tid} {x c : Blk}
    (hx : (Cfg.connected sub).block n = some x) (hc : (phiCfg sub).block n = some c) :
    (∃ φ ∈ c.phis, φ.var = var) ↔
      (∃ φ ∈ x.phis, φ.var = var) ∨
        IteratedFrontier (Cfg.connected sub).dominanceFrontier (DefSites (Cfg.connected sub) var) n := by
  constructor
  · exact (phiCfg_spec sub).2.2 var hvar n x c hx hc
  · rintro (⟨φ, hφ, he⟩ | hi)
    · obtain ⟨ins, hb, _⟩ := (phiCfg_spec sub).1.blocks n x hx
      rw [hb] at hc
      cases hc
      exact ⟨φ, List.mem_append_left _ hφ, he⟩
    · have hgen : ∀ m, IteratedFrontier (Cfg.connected sub).dominanceFrontier (DefSites (Cfg.connected sub) var) m →
          HasPhi (phiCfg sub) var m := by
        intro m hm
        have hdef : ∀ u, DefSites (Cfg.connected sub) var u → ∃ y, (phiCfg sub).block u = some y ∧ var ∈ y.definedVars := by
          rintro u ⟨y, hy, ht, hd⟩
          have hnd : (tidsOf (Cfg.connected sub).blocks).Nodup := by
            show ((Cfg.connected sub).blocks.map Blk.tid).Nodup
            rw [connected_tids_eq_nodes]
            exact connected_nodes_nodup hwf
          obtain ⟨z, hz⟩ := block_exists (cfg := Cfg.connected sub) (List.mem_map.2 ⟨y, hy, ht⟩)
          have hzm := block_some hz
          have hzy : z = y := eq_of_tid_eq hnd hzm.1 hy (hzm.2.trans ht.symm)
          subst hzy
          obtain ⟨ins, hb, _⟩ := (phiCfg_spec sub).1.blocks u z hz
          refine ⟨_, hb, ?_⟩
          rw [mem_definedVars] at hd ⊢
          rcases hd with ⟨φ, hφ, he⟩ | hd
          · exact Or.inl ⟨φ, List.mem_append_left _ hφ, he⟩
          · exact Or.inr hd
        induction hm with
        | base hd hj =>
          obtain ⟨y, hy, hdv⟩ := hdef _ hd
          exact (phiCfg_spec sub).2.1 var hvar _ y hy hdv _ hj
        | @step u j hu hj ih =>
          cases hb : (phiCfg sub).block u with
          | none =>
            exfalso
            have hany : ∃ s, u ∈ (Assoc.get s (Cfg.connected sub).dominanceFrontier).getD [] := by
              cases hu with
              | base _ hj' => exact ⟨_, hj'⟩
              | step _ hj' => exact ⟨_, hj'⟩
            obtain ⟨s, hs⟩ := hany
            cases hg : Assoc.get s (Cfg.connected sub).dominanceFrontier with
            | none =>
              rw [hg] at hs
              simp at hs
            | some f =>
              rw [hg] at hs
              obtain ⟨y, hy⟩ := phi_block_exists (sub := sub) (n := u) (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _
                (Bap.Proofs.Graph.dominanceFrontier_target (get_mem_env' hg) hs).1)
              rw [hb] at hy
              cases hy
          | some y =>
            obtain ⟨φ, hφ, he⟩ := ih y hb
            exact (phiCfg_spec sub).2.1 var hvar _ y hb ((mem_definedVars _ _).2 (Or.inl ⟨φ, hφ, he⟩)) _ hj
      exact hgen n hi c hc

private theorem block_mem_real {t : Tid} {f : Blk} (h : (Cfg.fromSub sub).block t = some f) : ∃ o, o ∈ sub.blks ∧ o.tid = t :=
  ⟨f, (block_some h).1, (block_some h).2⟩

private theorem toSsa_start (sub : Sub) : (Cfg.fromSub sub).start = (Cfg.fromSub (toSsa sub)).start := by
  show (sub.blks.head?.map Blk.tid).getD 0 = ((toSsa sub).blks.head?.map Blk.tid).getD 0
  have : (toSsa sub).blks.head?.map Blk.tid = sub.blks.head?.map Blk.tid := by
    rw [← List.head?_map, ← List.head?_map, toSsa_tids]
  rw [this]

/-- The last block of a run from a reachable block is reachable. -/
private theorem Run.last_reachable {cfg : Cfg} {p t : Tid} {E F : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    (h : Run cfg p t E path tr F f) (hnodes : ∀ b ∈ cfg.blocks, b.tid ∈ cfg.graph.nodes) (ht : t ∈ cfg.reachable) :
    f.tid ∈ cfg.reachable := by
  induction h with
  | last hb _ _ => rwa [(block_some hb).2]
  | next hb _ _ _ _ hsucc hrest ih =>
    obtain ⟨b', hb'⟩ := hrest.block
    refine ih (Bap.Proofs.Graph.reachableFrom_closed _ _ ht ((Bap.Graph.successors_mem _ _ _).1 hsucc) ?_)
    exact (block_some hb').2 ▸ hnodes b' (block_some hb').1

/-- `toSsa` preserves semantics. Every run of a subroutine from its entry corresponds to a run of the SSA
form from the same environment along the same path, ending in the block with the same tid, with the
same stored values, and selecting the rewrite of the same jump. At the end of the run each variable the
subroutine mentions, and each unversioned one, is readable under a version of itself, the name reads of
it see at that block, with its original value. Unbound variables stay unbound in both runs. -/
theorem toSsa_preserves_runs (sub : Sub) (hwf : SubWf sub) {env final : Env} {path : List Tid}
    {tr : List (Var × Value)} {f : Blk}
    (h : Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f) :
    ∃ tr' final' f', ∃ names : Var → Var, Run (Cfg.fromSub (toSsa sub)) pseudoStart (Cfg.fromSub sub).start env path tr' final' f' ∧
      tr'.map (fun e => (e.1.base, e.2)) = tr.map (fun e => (e.1.base, e.2)) ∧ f'.tid = f.tid ∧
      (∀ w : Var, (w.index = 0 ∨ w ∈ (Cfg.connected sub).blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars) →
        (names w).base = w.base ∧ Bil.lookup final' (names w) = Bil.lookup final w ∧
          (names w = w ∨ ∃ b ∈ (Cfg.fromSub (toSsa sub)).prune.blocks, names w ∈ b.definedVars)) ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        (∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, evalExp final' (g e) = evalExp final e) ∧
        ∀ o, selectJmp final f.jmps = .ok o → selectJmp final' f'.jmps = .ok (o.map (Jmp.mapExp g)) := by
  obtain ⟨en, ex, F⟩ := ssa_tables hwf
  obtain ⟨b, hb⟩ := h.block
  have hne : sub.blks ≠ [] := fromSub_start_block hb
  have hentry : (pseudoStart, (Cfg.fromSub sub).start) ∈ (connG sub).edges := connected_entry_edge hne
  have hreach₀ : Reach sub pseudoStart := by
    show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact start_mem_reachable (by rw [connected_nodes]; simp)
  obtain ⟨tr', F', f', hrun, hs, ht, hfb, hl, hj⟩ := ssa_run_sim hwf F h hentry hreach₀ (E' := env)
    (fun w _ => by rw [start_names hwf F])
  have hfr := real_reach hfb
  have hexp : ∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, evalExp F' (renameExp (ex f.tid) e) = evalExp final e :=
    fun j hj e he => jump_rename F hfb hfr hl hj he
  refine ⟨tr', F', f', fun w => topName w (ex f.tid), hrun, hs, ht, ?_, renameExp (ex f.tid), hj, hexp, ?_⟩
  · intro w hw
    refine ⟨exit_name_base F hfr hw, hl w hw, ?_⟩
    rcases topName_cases w (ex f.tid) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      obtain ⟨o, ho⟩ := block_mem_real hfb
      obtain ⟨k, _, hc⟩ := Bap.Proofs.Graph.idomChain_exists (reach_iff.1 hfr)
      obtain ⟨a, sb, hd, hS, hm⟩ := stack_scope hwf F k f.tid hc w _ h
      have hastart : a ≠ pseudoStart := by
        rintro rfl
        exact no_names_at_start hwf F hS hm
      have hreal := dom_real hwf (List.mem_map.2 ⟨o, ho.1, ho.2⟩) hd hastart
      have hsb := mem_toSsa_of_block hreal hS
      have hrun' : f'.tid ∈ (Cfg.fromSub (toSsa sub)).reachable := by
        have hst : (Cfg.fromSub (toSsa sub)).start ∈ (Cfg.fromSub (toSsa sub)).reachable := by
          apply start_mem_reachable
          have hb' : (Cfg.fromSub (toSsa sub)).block (Cfg.fromSub sub).start = _ := toSsa_block hb
          obtain ⟨x, hx⟩ := hrun.block
          have hm' := block_some hx
          have hst' : (Cfg.fromSub sub).start = (Cfg.fromSub (toSsa sub)).start := toSsa_start sub
          rw [← hst']
          exact hm'.2 ▸ List.mem_map.2 ⟨x, hm'.1, rfl⟩
        rw [toSsa_start sub] at hrun
        exact hrun.last_reachable (fun b hb => List.mem_map.2 ⟨b, hb, rfl⟩) hst
      rw [ht] at hrun'
      obtain ⟨w', hw'⟩ := (Bap.Proofs.Graph.mem_reachable_iff_walk _).1 hrun'
      have hareach := hw'.subset_reachable (dom_transfer hwf hd hastart w' hw')
      have hsbt := (block_some hS).2
      refine ⟨sb, ?_, ?_⟩
      · refine List.mem_filter.2 ⟨hsb, decide_eq_true ?_⟩
        rw [hsbt]
        exact prune_mem_nodes.2 hareach
      · rw [mem_definedVars]
        rcases List.mem_append.1 hm with hm | hm
        · obtain ⟨φ, hφ, he⟩ := List.mem_map.1 hm
          exact Or.inl ⟨φ, hφ, he⟩
        · obtain ⟨d, hd', he⟩ := List.mem_map.1 hm
          exact Or.inr ⟨d, hd', he⟩
  · intro o ho
    rw [hj]
    exact selectJmp_mapExp (fun a ha e he v hv => by rw [hexp a ha e he]; exact hv) ho

/-- What runs in a block of the output runs in the input: the renaming fails where the input fails. -/
private theorem ssa_block_back {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {p t : Tid}
    (he : (p, t) ∈ (connG sub).edges) (hp : Reach sub p) {o : Blk} (ho : (Cfg.fromSub sub).block t = some o) {E E' E₁' : Env}
    {sb : Blk} {r' : Env × List (Var × Value)}
    (hI : ∀ w, Tracked (mentionedOf sub) w → Bil.lookup E' (topName w (ex p)) = Bil.lookup E w)
    (hS : (ssaCfg sub).block t = some sb) (hphis : execPhis p E' sb.phis E' = .ok E₁') (hdefs : execDefs E₁' sb.defs = .ok r') :
    ∃ E₁ r, execPhis p E o.phis E = .ok E₁ ∧ execDefs E₁ o.defs = .ok r := by
  obtain ⟨ins, hb, hins⟩ := phi_block_real hwf ho
  have htreach := real_reach ho
  have hom : o ∈ (Cfg.connected sub).blocks := real_mem_connected (block_some ho).1
  have hpredmem : p ∈ (Cfg.connected sub).predecessors t := (mem_predecessors' _ _ _).2 he
  let b : Blk := { o with phis := o.phis ++ ins }
  have hwfp := exit_wf F hp
  have hstart : RenameWf (mentionedOf sub) (en t) := F.spec.wf t htreach
  let f := doneInput (Canon (phiCfg sub) (Reach sub) · t) ex
  have hval : ∀ phi ∈ b.phis, ∀ e, Assoc.get p phi.values = some e →
      phiValue E' (renameExp (ex p) e) = phiValue E e := by
    intro phi hphi e hget
    refine phiValue_renameExp hwfp e hI ?_
    intro x hx
    refine Or.inr ?_
    rcases List.mem_append.1 hphi with hphi | hphi
    · exact phi_read_mentioned hom hphi (get_mem_env' hget) hx
    · obtain ⟨hv, _, hvals⟩ := hins phi hphi
      rw [hvals, get_trivial_values _ _ hpredmem] at hget
      cases hget
      have hx' : x = phi.var := by
        have := (Bap.Proofs.Bil.mem_freeVars_iff x (.var phi.var)).1 hx
        simp only [Bil.occursFree, beq_iff_eq] at this
        exact this.symm
      exact hx' ▸ mem_phiVars_mentioned hv
  have hhf : ∀ phi : Phi, Assoc.get p (phi.values.map f) = (Assoc.get p phi.values).map (renameExp (ex p)) :=
    fun phi => get_doneInput ex ⟨hp, (Bap.Graph.successors_mem _ _ _).2 (by
      rw [(phiCfg_spec sub).1.graph]
      exact he)⟩ phi.values
  have hform : stmtForm (Reach sub) en ex t b = renamedStmts b (en t) (ex t) := by
    unfold stmtForm
    rw [ite_eq_left htreach]
  have hS' := F.spec.block t b hb
  rw [hform, hS] at hS'
  cases hS'
  cases hpo : execPhis p E o.phis E with
  | error m =>
    have := renamePhis_error p (renameExp (ex p)) f hhf (read' := E') b.phis hval (en t) (acc' := E')
      (execPhis_error_append ins hpo)
    exact absurd (hphis.symm.trans this) (by simp)
  | ok E₁ =>
    cases hdo : execDefs E₁ o.defs with
    | ok r => exact ⟨E₁, r, rfl, hdo⟩
    | error m =>
      exfalso
      obtain ⟨r₂, hr₂, hsame⟩ : ∃ r₂, execPhis p E b.phis E = .ok r₂ ∧ ∀ w, Bil.lookup r₂ w = Bil.lookup E₁ w := by
        obtain ⟨r₂, hr₂, hsame⟩ := execPhis_insert p E ins (acc := E₁) (by
          intro φ hφ
          obtain ⟨_, hnot, hval⟩ := hins φ hφ
          refine ⟨by rw [hval]; exact get_trivial_values _ _ hpredmem _, ?_⟩
          exact lookup_execPhis_other hpo fun phi hphi heq => hnot (List.mem_map.2 ⟨phi, hphi, heq⟩))
        exact ⟨r₂, execPhis_append hpo hr₂, hsame⟩
      have hphi₀ : ∀ w, Tracked (mentionedOf sub) w → (∀ phi ∈ b.phis, phi.var ≠ w) →
          Bil.lookup E' (topName w (en t)) = Bil.lookup E w := by
        intro w hw hn
        have hst : stackOf (ex p) w = stackOf (en t) w :=
          edge_names hwf F he hp (Bap.Proofs.Graph.reachableFrom_subset_nodes _ _ htreach) w (by
            intro c hc φ hφ
            rw [hb] at hc
            cases hc
            exact hn φ hφ)
        rw [← top_of_stack w hst]
        exact hI w hw
      obtain ⟨E₁'', hE₁'', hI₁⟩ := renamePhis_sim (U := mentionedOf sub) p (renameExp (ex p)) f hhf b.phis hval hstart hphi₀ hr₂
      have hE : E₁'' = E₁' := Except.ok.inj (hE₁''.symm.trans hphis)
      subst hE
      have hI₁' : ∀ w, Tracked (mentionedOf sub) w →
          Bil.lookup E₁'' (topName w (renamePhis b.phis (en t)).2) = Bil.lookup E₁ w :=
        fun w hw => by rw [hI₁ w hw, hsame]
      have := renameDefs_error (U := mentionedOf sub) b.defs
        (fun d hd x hx => Or.inr (def_read_mentioned hom hd hx)) (hstart.renamePhis b.phis) hI₁' hdo
      exact absurd (hdefs.symm.trans this) (by simp)

/-- The simulation back along a path: a run of the output from a block is a run of the input along the
same path, from environments that agree through the names at the exit of the predecessor. -/
private theorem ssa_run_back {en ex : Tid → RenameState} (hwf : SubWf sub) (F : SsaTables sub en ex) {p t : Tid} {E' F' : Env}
    {path : List Tid} {tr' : List (Var × Value)} {f' : Blk} (h : Run (Cfg.fromSub (toSsa sub)) p t E' path tr' F' f')
    (he : (p, t) ∈ (connG sub).edges) (hp : Reach sub p) {E : Env}
    (hI : ∀ w, Tracked (mentionedOf sub) w → Bil.lookup E' (topName w (ex p)) = Bil.lookup E w) :
    ∃ tr F₀ f, Run (Cfg.fromSub sub) p t E path tr F₀ f := by
  have hinput : ∀ {t : Tid} {sb : Blk}, (Cfg.fromSub (toSsa sub)).block t = some sb →
      ∃ o, (Cfg.fromSub sub).block t = some o ∧ (ssaCfg sub).block t = some sb := by
    intro t sb hsb
    have hm := block_some hsb
    have ht : t ∈ (toSsa sub).blks.map Blk.tid := List.mem_map.2 ⟨sb, hm.1, hm.2⟩
    rw [toSsa_tids] at ht
    obtain ⟨o, ho⟩ := block_exists (cfg := Cfg.fromSub sub) ht
    exact ⟨o, ho, by rw [← toSsa_block ho]; exact hsb⟩
  induction h generalizing E with
  | @last p t E' E₁' r' sb hsb hphis hdefs =>
    obtain ⟨o, ho, hS⟩ := hinput hsb
    obtain ⟨E₁, r, hpo, hdo⟩ := ssa_block_back hwf F he hp ho hI hS hphis hdefs
    exact ⟨_, _, _, .last ho hpo hdo⟩
  | @next p t t' E' E₁' r' sb j path stores final lastBlk hsb hphis hdefs hsel htarget hsucc hrest ih =>
    obtain ⟨o, ho, hS⟩ := hinput hsb
    obtain ⟨E₁, r, hpo, hdo⟩ := ssa_block_back hwf F he hp ho hI hS hphis hdefs
    obtain ⟨sb₂, E₁₂, r₂, hS₂, hp₂, hd₂, _, hl, hj⟩ := ssa_block_sim hwf F he hp ho hI hpo hdo
    have hsb₂ : sb₂ = sb := Option.some.inj (hS₂.symm.trans hS)
    subst hsb₂
    have hE : E₁₂ = E₁' := Except.ok.inj (hp₂.symm.trans hphis)
    subst hE
    have hr : r₂ = r' := Except.ok.inj (hd₂.symm.trans hdefs)
    subst hr
    have htr := real_reach ho
    have hexp : ∀ a ∈ o.jmps, ∀ e ∈ jmpExps a, evalExp r₂.1 (renameExp (ex t) e) = evalExp r.1 e :=
      fun a ha e he => jump_rename F ho htr hl ha he
    rw [hj] at hsel
    cases hs : selectJmp r.1 o.jmps with
    | error m =>
      have := selectJmp_mapExp_error hexp hs
      exact absurd (hsel.symm.trans this) (by simp)
    | ok so =>
      have hmapped := selectJmp_mapExp (env := r.1) (env' := r₂.1) (g := renameExp (ex t)) (jmps := o.jmps) (o := so)
        (fun a ha e he v hv => by rw [hexp a ha e he]; exact hv) hs
      rw [hsel] at hmapped
      cases so with
      | none => simp at hmapped
      | some j₀ =>
        have hjj : j = j₀.mapExp (renameExp (ex t)) := by simpa using hmapped
        have ht₀ : t' ∈ j₀.successors := by
          rw [hjj, Jmp.successors_mapExp] at htarget
          exact htarget
        have hsucc₀ : t' ∈ (Cfg.fromSub sub).successors t := fromSub_jump_edge ho (selectJmp_mem hs) ht₀
        have hedge : (t, t') ∈ (connG sub).edges :=
          connected_edges_superset sub ((Bap.Graph.successors_mem _ _ _).1 hsucc₀)
        obtain ⟨tr, F₀, f, hrun⟩ := ih hedge htr hl
        exact ⟨_, _, _, .next ho hpo hdo hs ht₀ hsucc₀ hrun⟩

/-- The converse of `toSsa_preserves_runs`: every run of the SSA form from its entry is a run of the
subroutine from the same environment along the same path, related as that theorem says. Nothing is
lost either way: the renaming fails exactly where the input fails. -/
theorem toSsa_reflects_runs (sub : Sub) (hwf : SubWf sub) {env final' : Env} {path : List Tid}
    {tr' : List (Var × Value)} {f' : Blk}
    (h : Run (Cfg.fromSub (toSsa sub)) pseudoStart (Cfg.fromSub sub).start env path tr' final' f') :
    ∃ tr final f, ∃ names : Var → Var, Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f ∧
      tr'.map (fun e => (e.1.base, e.2)) = tr.map (fun e => (e.1.base, e.2)) ∧ f'.tid = f.tid ∧
      (∀ w : Var, (w.index = 0 ∨ w ∈ (Cfg.connected sub).blocks.flatMap fun blk => blk.definedVars ++ blk.freeVars) →
        (names w).base = w.base ∧ Bil.lookup final' (names w) = Bil.lookup final w ∧
          (names w = w ∨ ∃ b ∈ (Cfg.fromSub (toSsa sub)).prune.blocks, names w ∈ b.definedVars)) ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        (∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, evalExp final' (g e) = evalExp final e) ∧
        ∀ o, selectJmp final f.jmps = .ok o → selectJmp final' f'.jmps = .ok (o.map (Jmp.mapExp g)) := by
  obtain ⟨en, ex, F⟩ := ssa_tables hwf
  obtain ⟨b, hb⟩ := h.block
  have hne : sub.blks ≠ [] := by
    intro hnil
    have ht := fromSub_start_block hb
    have htids := toSsa_tids sub
    rw [hnil] at htids
    simp only [List.map_nil, List.map_eq_nil_iff] at htids
    exact ht htids
  have hentry : (pseudoStart, (Cfg.fromSub sub).start) ∈ (connG sub).edges := connected_entry_edge hne
  have hreach₀ : Reach sub pseudoStart := by
    show pseudoStart ∈ Bap.Graph.reachable (connG sub) (Cfg.connected sub).start
    rw [connected_start]
    exact start_mem_reachable (by rw [connected_nodes]; simp)
  obtain ⟨tr, final, f, hrun⟩ := ssa_run_back hwf F h hentry hreach₀ (E := env) (fun w _ => by rw [start_names hwf F])
  obtain ⟨tr₁, F₁, f₁, names, hrun₁, hs, ht, hn, g, hj⟩ := toSsa_preserves_runs sub hwf hrun
  obtain ⟨_, hdet⟩ := Run.deterministic hrun₁ h
  obtain ⟨rfl, rfl, rfl⟩ := hdet rfl
  exact ⟨tr, final, f, names, hrun, hs, ht, hn, g, hj⟩

/-- `toSsa` has exactly the runs of the input. -/
theorem toSsa_runs_iff (sub : Sub) (hwf : SubWf sub) {env : Env} {path : List Tid} :
    (∃ tr final f, Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f) ↔
      ∃ tr final f, Run (Cfg.fromSub (toSsa sub)) pseudoStart (Cfg.fromSub sub).start env path tr final f := by
  constructor
  · rintro ⟨tr, final, f, h⟩
    obtain ⟨tr', final', f', _, h', _⟩ := toSsa_preserves_runs sub hwf h
    exact ⟨tr', final', f', h'⟩
  · rintro ⟨tr, final, f, h⟩
    obtain ⟨tr', final', f', _, h', _⟩ := toSsa_reflects_runs sub hwf h
    exact ⟨tr', final', f', h'⟩

/-- A run with its arguments: `sub.args` are definitions that run on entry, before the first block. `toSsa`
leaves them as they are (`toSsa_args`), which is the renaming at the entry, where every variable reads
itself and the first block has yet to assign any version: so a subroutine and its SSA form enter
the first block with the same environment, and have the same runs. -/
theorem toSsa_runs_with_args (sub : Sub) (hwf : SubWf sub) {env : Env} {path : List Tid} :
    (∃ entered tr final f, execDefs env sub.args = .ok entered ∧
        Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start entered.1 path tr final f) ↔
      ∃ entered tr final f, execDefs env (toSsa sub).args = .ok entered ∧
        Run (Cfg.fromSub (toSsa sub)) pseudoStart (Cfg.fromSub sub).start entered.1 path tr final f := by
  simp only [toSsa_args]
  constructor
  · rintro ⟨entered, tr, final, f, ha, h⟩
    obtain ⟨tr', final', f', h'⟩ := (toSsa_runs_iff sub hwf).1 ⟨tr, final, f, h⟩
    exact ⟨entered, tr', final', f', ha, h'⟩
  · rintro ⟨entered, tr, final, f, ha, h⟩
    obtain ⟨tr', final', f', h'⟩ := (toSsa_runs_iff sub hwf).2 ⟨tr, final, f, h⟩
    exact ⟨entered, tr', final', f', ha, h'⟩

private theorem storeShape_sublist {a b : List (Var × Value)} (h : a.Sublist b) : (storeShape a).Sublist (storeShape b) :=
  h.map _

/-- `optimize` on SSA form. The optimized SSA form of a subroutine follows the same path as the subroutine,
keeps its stored values in order, and at the end of the run holds the value of every protected
unversioned output under the name that output has at that point. Such an output protects all its SSA
versions, whichever exit is taken. -/
theorem optimize_toSsa_preserves_runs (sub : Sub) (hwf : SubWf sub) (ps : List Var) (hps : ∀ p ∈ ps, p.index = 0)
    {env final : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    (h : Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f) :
    ∃ tr' final' f', ∃ names : Var → Var,
      Run (Cfg.fromSub (optimize (toSsa sub) ps)) pseudoStart (Cfg.fromSub sub).start env path tr' final' f' ∧
      (tr.map fun e => (e.1.base, e.2)).Sublist (tr'.map fun e => (e.1.base, e.2)) ∧ f'.tid = f.tid ∧
      (∀ w ∈ ps, (names w).base = w ∧ Bil.lookup final' (names w) = Bil.lookup final w) ∧
      ∃ g, f'.jmps = f.jmps.map (Jmp.mapExp g) ∧
        (∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp final' (g e) = .ok v) ∧
        ∀ o, selectJmp final f.jmps = .ok o → selectJmp final' f'.jmps = .ok (o.map (Jmp.mapExp g)) := by
  obtain ⟨tr₁, F₁, f₁, names, hrun, hshape, ht₁, hnames, g₁, hg₁, hexp₁, -⟩ := toSsa_preserves_runs sub hwf h
  rw [toSsa_start sub] at hrun
  obtain ⟨tr₂, F₂, f₂, hrun₂, hsub, ht₂, hprot, g₂, hg₂, hexp₂, -⟩ := optimize_preserves_runs (toSsa sub) ps hrun
  rw [← toSsa_start sub] at hrun₂
  have hexp : ∀ j ∈ f.jmps, ∀ e ∈ jmpExps j, ∀ v, evalExp final e = .ok v → evalExp F₂ (g₂ (g₁ e)) = .ok v := by
    intro j hj e he v hv
    have h₁ : evalExp F₁ (g₁ e) = .ok v := by rw [hexp₁ j hj e he]; exact hv
    refine hexp₂ (j.mapExp g₁) ?_ (g₁ e) ?_ v h₁
    · rw [hg₁]
      exact List.mem_map.2 ⟨j, hj, rfl⟩
    · rw [jmpExps_mapExp]
      exact List.mem_map.2 ⟨e, he, rfl⟩
  refine ⟨tr₂, F₂, f₂, names, hrun₂, ?_, ht₂.trans ht₁, ?_, g₂ ∘ g₁, ?_, hexp, ?_⟩
  · have := storeShape_sublist hsub
    simp only [storeShape] at this
    rw [← hshape]
    exact this
  · intro w hw
    have hbase : w.base = w := by
      obtain ⟨n, t, i, v⟩ := w
      have := hps _ hw
      simp only at this
      subst this
      rfl
    obtain ⟨hb, hl, hcase⟩ := hnames w (Or.inl (hps w hw))
    refine ⟨hb.trans hbase, ?_⟩
    rw [← hl]
    refine (hprot (names w) ?_).symm
    rcases hcase with h | hd
    · exact Or.inl (by rw [h]; exact hw)
    · exact Or.inr ⟨by rw [hb, hbase]; exact hw, hd⟩
  · rw [hg₂, hg₁, List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    rw [Jmp.mapExp_comp]
  · intro o ho
    rw [hg₂, hg₁]
    have := selectJmp_mapExp (env := final) (env' := F₂) (g := g₂ ∘ g₁) (jmps := f.jmps) (o := o) hexp ho
    have hm : (f.jmps.map (Jmp.mapExp g₁)).map (Jmp.mapExp g₂) = f.jmps.map (Jmp.mapExp (g₂ ∘ g₁)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp]
      rw [Jmp.mapExp_comp]
    rw [hm]
    exact this

/-- The converse of `optimize_toSsa_preserves_runs`: a run of the optimized SSA form is a run of the subroutine
along the same path, unless the SSA form fails on the way, which removing code hides. -/
theorem optimize_toSsa_reflects_runs (sub : Sub) (hwf : SubWf sub) (ps : List Var) {env final' : Env} {path : List Tid}
    {tr' : List (Var × Value)} {f' : Blk}
    (h : Run (Cfg.fromSub (optimize (toSsa sub) ps)) pseudoStart (Cfg.fromSub sub).start env path tr' final' f') :
    (∃ tr final f, Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f) ∨
      ∃ failed, failed <+: path ∧ RunFails (Cfg.fromSub (toSsa sub)) pseudoStart (Cfg.fromSub sub).start env failed := by
  rw [toSsa_start sub] at h ⊢
  rcases optimize_run_back (toSsa sub) ps pseudoStart env path h with ⟨tr, final, f, hr⟩ | hf
  · rw [← toSsa_start sub] at hr
    obtain ⟨tr₁, F₁, f₁, _, hrun, _⟩ := toSsa_reflects_runs sub hwf hr
    exact .inl ⟨tr₁, F₁, f₁, by rw [← toSsa_start sub]; exact hrun⟩
  · exact .inr hf

/-- Pruned SSA has no dead phi: what `toSsaPruned` keeps is live where it stands. -/
theorem toSsaPruned_phis_live (sub : Sub) (ps : List Var) {blk : Blk} {phi : Phi} (hb : blk ∈ (toSsaPruned sub ps).blks)
    (hphi : phi ∈ blk.phis) :
    let names := (Cfg.fromSub (toSsa sub)).protectedNames ps
    phi.var ∈ (dceDefs blk.defs (dceLive names (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names) blk)).2 := by
  intro names
  have hfix := dcePass_eliminateDeadCode names (Cfg.fromSub (toSsa sub))
  have hblocks : (dcePass names (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names)).blocks =
      (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names).blocks := by rw [hfix]
  have hb' : blk ∈ (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names).blocks := hb
  have hmap : ∀ (l : List Blk) (f : Blk → Blk), l.map f = l → ∀ x ∈ l, f x = x := by
    intro l f
    induction l with
    | nil => simp
    | cons a as ih =>
      intro h x hx
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1
      · exact ih h.2 x hx
  have hsame := hmap _ (dceBlk names (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names)) hblocks blk hb'
  have hmem : phi ∈ (dceBlk names (eliminateDeadCode (Cfg.fromSub (toSsa sub)) names) blk).phis := by
    rw [hsame]
    exact hphi
  simpa using (List.mem_filter.1 hmem).2

/-- `toSsaPruned` preserves runs, as `optimize_toSsa_preserves_runs` for `optimize`: the same path, the
same stored values, and at the end the value of every protected unversioned output under the name that
output has there. Only phis and definitions no one reads have gone. -/
theorem toSsaPruned_preserves_runs (sub : Sub) (hwf : SubWf sub) (ps : List Var) (hps : ∀ p ∈ ps, p.index = 0)
    {env final : Env} {path : List Tid} {tr : List (Var × Value)} {f : Blk}
    (h : Run (Cfg.fromSub sub) pseudoStart (Cfg.fromSub sub).start env path tr final f) :
    ∃ tr' final' f', ∃ names : Var → Var,
      Run (Cfg.fromSub (toSsaPruned sub ps)) pseudoStart (Cfg.fromSub sub).start env path tr' final' f' ∧
      tr'.map (fun e => (e.1.base, e.2)) = tr.map (fun e => (e.1.base, e.2)) ∧ f'.tid = f.tid ∧
      ∀ w ∈ ps, (names w).base = w ∧ Bil.lookup final' (names w) = Bil.lookup final w := by
  obtain ⟨tr₁, F₁, f₁, names, hrun, hshape, ht₁, hnames, _⟩ := toSsa_preserves_runs sub hwf h
  have hstart₀ := toSsa_start sub
  rw [hstart₀] at hrun
  have hreach : (Cfg.fromSub (toSsa sub)).start ∈ (Cfg.fromSub (toSsa sub)).reachable := by
    obtain ⟨x, hx⟩ := hrun.block
    have hm := block_some hx
    exact start_mem_reachable (hm.2 ▸ List.mem_map.2 ⟨x, hm.1, rfl⟩)
  generalize hnamesDef : (Cfg.fromSub (toSsa sub)).protectedNames ps = kept
  obtain ⟨F₂, f₂, hrun₂, ht₂, _, ha₂⟩ := dceAux_run (ps := kept)
    (weight (Cfg.fromSub (toSsa sub)).blocks + 1) (fun b hb => List.mem_map.2 ⟨b, hb, rfl⟩) hrun hreach
  rw [← eliminateDeadCode_eq] at hrun₂
  refine ⟨tr₁, F₂, f₂, names, ?_, hshape, ht₂.trans ht₁, fun w hw => ?_⟩
  · rw [hstart₀]
    subst hnamesDef
    exact run_fromSub_of_blocks rfl hrun₂
  · have hbase : w.base = w := by
      obtain ⟨n, t, i, v⟩ := w
      have := hps _ hw
      simp only at this
      subst this
      rfl
    obtain ⟨hb, hl, hcase⟩ := hnames w (Or.inl (hps w hw))
    refine ⟨hb.trans hbase, ?_⟩
    rw [← hl]
    refine (ha₂ (names w) (List.mem_append_right _ ?_)).symm
    rw [← hnamesDef, mem_protectedNames]
    rcases hcase with h' | ⟨b, hbm, hd⟩
    · exact .inl (by rw [h']; exact hw)
    · refine .inr ⟨by rw [hb, hbase]; exact hw, b, (prune_blocks_sublist _).subset hbm, hd⟩

end ConnectedFacts
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
    simp [parseTyp, printTyp, Sexp.tagged, nat_repr_roundtrip, Bind.bind, Except.bind]

private theorem parseVar_printVar' (var : Var) : parseVar
    (.list [.atom "var", .atom var.name, .atom var.index.repr, printTyp var.typ,
      .atom (if var.isVirtual = true then "1" else "0")]) = .ok var := by
  obtain ⟨name, typ, index, virt⟩ := var
  cases virt <;>
    simp [parseVar, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, nat_repr_roundtrip,
      parseTyp_printTyp, Bind.bind, Except.bind]

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
  simp [Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, 
    nat_repr_roundtrip, parseVar_printVar, parseExp_printExp]

private theorem mapM_ok {α : Type} {g : α → Except String α} (l : List α) (h : ∀ a, g a = .ok a) :
    l.mapM g = .ok l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [List.mapM_cons, h, ih, Bind.bind, Except.bind, pure, Except.pure]

theorem parsePhi_printPhi (phi : Phi) : parsePhi (printPhi phi) = .ok phi := by
  obtain ⟨tid, var, values⟩ := phi
  simp only [printPhi, parsePhi, Sexp.tagged]
  simp [Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, nat_repr_roundtrip,
    parseVar_printVar]
  rw [mapM_ok]
  rintro ⟨t, v⟩
  simp [nat_repr_roundtrip, parseExp_printExp]

theorem parseJmp_printJmp (jmp : Jmp) : parseJmp (printJmp jmp) = .ok jmp := by
  obtain ⟨tid, condition, kind⟩ := jmp
  cases condition <;> cases kind <;>
    simp [printJmp, parseJmp, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, nat_repr_roundtrip, parseLabel_printLabel, parseOptionalLabel_printOptionalLabel, parseExp_printExp]

theorem parseBlk_printBlk (blk : Blk) : parseBlk (printBlk blk) = .ok blk := by
  obtain ⟨tid, phis, defs, jmps⟩ := blk
  simp [printBlk, parseBlk, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Bind.bind, Except.bind, 
    nat_repr_roundtrip, mapM_roundtrip parsePhi_printPhi, mapM_roundtrip parseJmp_printJmp,
    mapM_roundtrip (parseDef_printDef "def")]

/-- Printing then parsing a whole subroutine returns it unchanged. -/
theorem parseSub_printSub (sub : Sub) : parseSub (printSub sub) = .ok sub := by
  obtain ⟨tid, name, args, blks⟩ := sub
  simp [printSub, parseSub, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, Bind.bind, Except.bind,
    nat_repr_roundtrip, mapM_roundtrip parseBlk_printBlk,
    mapM_roundtrip (parseDef_printDef "arg")]

end Bap.Proofs.IR
