import Bap.IR.Liveness

/-! The dataflow equations `Cfg.liveness` solves, and that it finds their least solution.
They are apart from the rest of the IR proofs for `Bap.IR.Optimize` to use them. -/

namespace Bap.Proofs.IR

open Bap Bap.Bil Bap.IR

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

theorem block_some {cfg : Cfg} {t : Tid} {blk : Blk} (h : cfg.block t = some blk) :
    blk ∈ cfg.blocks ∧ blk.tid = t := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

/-- Variables read by a definition list before they are overwritten inside it. -/
def Exposed : List Def → Var → Prop
  | [], _ => False
  | defn :: rest, x => x ∈ Bil.freeVars defn.rhs ∨ (x ≠ defn.var ∧ Exposed rest x)

abbrev defsStep (state : List Var × List Var) (defn : Def) : List Var × List Var :=
  (state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2, defn.var :: state.2)

theorem defsFold_killed (defs : List Def) (input killed : List Var) (x : Var) :
    x ∈ (defs.foldl defsStep (input, killed)).2 ↔ x ∈ killed ∨ ∃ defn ∈ defs, defn.var = x := by
  induction defs generalizing input killed with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    grind

theorem defsFold_input (defs : List Def) (input killed : List Var) (x : Var) :
    x ∈ (defs.foldl defsStep (input, killed)).1 ↔ x ∈ input ∨ (x ∉ killed ∧ Exposed defs x) := by
  induction defs generalizing input killed with
  | nil => simp [Exposed]
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, List.mem_append, List.mem_filter, decide_eq_true_eq, Exposed,
      List.mem_cons, not_or]
    grind

/-- Exact characterization of a block's free variables: what its definitions and jumps read before
the block assigns it, and the inputs of its phis. -/
theorem mem_blk_freeVars (blk : Blk) (x : Var) :
    x ∈ blk.freeVars ↔ ((∀ phi ∈ blk.phis, phi.var ≠ x) ∧
        (Exposed blk.defs x ∨ ((∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars) ∧ ∀ defn ∈ blk.defs, defn.var ≠ x))) ∨
      ∃ phi ∈ blk.phis, ∃ input ∈ phi.values, x ∈ Bil.freeVars input.2 := by
  have h : blk.freeVars = ((blk.defs.foldl defsStep ([], blk.phis.map Phi.var)).1 ++
      blk.phis.flatMap (fun phi => phi.values.flatMap (Bil.freeVars ∘ Prod.snd)) ++
      (blk.jmps.flatMap Jmp.freeVars).filter fun var => var ∉ (blk.defs.foldl defsStep ([], blk.phis.map Phi.var)).2).eraseDups := rfl
  rw [h]
  simp only [List.mem_eraseDups, List.mem_append, defsFold_input, defsFold_killed, List.mem_flatMap,
    List.mem_filter, Function.comp, decide_eq_true_eq, List.mem_map]
  simp only [List.not_mem_nil, false_or, not_or, not_exists, not_and]
  grind

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
          simp [List.lookup, hb, ih]
        · have hb : (a != t) = true := by simpa using ha
          simp [List.lookup, hb, ih]
    have hb : (z == t) = false := by simpa using hz
    simp [Assoc.get, Assoc.put, List.lookup, hb, key]

@[simp] theorem mem_liveUnion (l r : List Var) (x : Var) :
    x ∈ liveUnion l r ↔ x ∈ l ∨ x ∈ r := by
  show x ∈ (l ++ r).eraseDups ↔ _
  simp [List.mem_eraseDups]

@[simp] theorem mem_liveSubtract (l r : List Var) (x : Var) :
    x ∈ liveSubtract l r ↔ x ∈ l ∧ x ∉ r := by
  show x ∈ l.filter _ ↔ _
  simp

theorem get_mem_env' {κ β : Type} [DecidableEq κ] {k : κ} {v : β} {T : List (κ × β)}
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

theorem mem_phiFold (t : Tid) (phis : List Phi) (out : List Var) (x : Var) :
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
        simp only [LiveEdge]
        grind
      | some blk =>
        simp only [mem_phiFold, mem_liveUnion, mem_liveSubtract, LiveEdge]
        simp only [List.mem_map, not_exists, not_and]
        grind
  refine Iff.trans (key (cfg.successors t) []) ?_
  simp

/-- Exact gen/kill characterization of `blockIn`. A variable is live before the phis if the block
reads it, or it is live out, before anything in the block assigns it. -/
theorem mem_blockIn (blk : Blk) (out : List Var) (x : Var) :
    x ∈ blockIn blk out ↔ (∀ phi ∈ blk.phis, phi.var ≠ x) ∧ (Exposed blk.defs x ∨
      (((∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars) ∨ x ∈ out) ∧ ∀ defn ∈ blk.defs, defn.var ≠ x)) := by
  have hjmp : ∀ (js : List Jmp) (input killed : List Var),
      x ∈ js.foldl (fun input jmp => liveUnion input (liveSubtract jmp.freeVars killed)) input ↔
        x ∈ input ∨ ∃ jmp ∈ js, x ∈ jmp.freeVars ∧ x ∉ killed := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      intro input killed
      simp only [List.foldl_cons, ih, mem_liveUnion, mem_liveSubtract]
      grind
  have heq : blockIn blk out = liveUnion
      (blk.jmps.foldl (fun input jmp => liveUnion input
        (liveSubtract jmp.freeVars (blk.defs.foldl defsStep ([], blk.phis.map Phi.var)).2))
        (blk.defs.foldl defsStep ([], blk.phis.map Phi.var)).1)
      (liveSubtract out (blk.defs.foldl defsStep ([], blk.phis.map Phi.var)).2) := rfl
  rw [heq]
  simp only [mem_liveUnion, mem_liveSubtract, hjmp, defsFold_input, defsFold_killed, List.mem_map]
  simp only [List.not_mem_nil, false_or, not_or, not_exists, not_and]
  grind

theorem blockIn_mono (blk : Blk) {o₁ o₂ : List Var} (h : o₁ ⊆ o₂) : blockIn blk o₁ ⊆ blockIn blk o₂ := by
  intro x hx
  rw [mem_blockIn] at hx ⊢
  obtain ⟨hp, hx⟩ := hx
  refine ⟨hp, ?_⟩
  rcases hx with hx | ⟨hx, hd⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hx.imp_right fun hx => h hx, hd⟩

/-- The live-in set distributes over unions of the live-out set. -/
theorem blockIn_union (blk : Blk) (o₁ o₂ : List Var) (x : Var) :
    x ∈ blockIn blk (o₁ ++ o₂) ↔ x ∈ blockIn blk o₁ ∨ x ∈ blockIn blk o₂ := by
  simp only [mem_blockIn, List.mem_append]
  grind

/-- A variable a block defines and does not read before that is not live on entry, whatever is live
out and even if the block's jumps read it: they see the block's own write. -/
theorem blockIn_kill {blk : Blk} {out : List Var} {x : Var} (hdef : ∃ defn ∈ blk.defs, defn.var = x)
    (hexp : ¬ Exposed blk.defs x) : x ∉ blockIn blk out := by
  rw [mem_blockIn]
  obtain ⟨defn, hd, hv⟩ := hdef
  rintro ⟨_, h | ⟨_, h⟩⟩
  · exact hexp h
  · exact h defn hd hv

/-- A phi assigns its variable on entry, so that variable is not live before the block. -/
theorem blockIn_phi_kill {blk : Blk} {out : List Var} {phi : Phi} (hphi : phi ∈ blk.phis) :
    phi.var ∉ blockIn blk out := by
  rw [mem_blockIn]
  exact fun h => h.1 phi hphi rfl

/-- What a jump reads and the block has not assigned is live on entry. -/
theorem blockIn_jump_read {blk : Blk} {out : List Var} {x : Var} {jmp : Jmp} (hj : jmp ∈ blk.jmps)
    (hx : x ∈ jmp.freeVars) (hphi : ∀ phi ∈ blk.phis, phi.var ≠ x) (hdef : ∀ defn ∈ blk.defs, defn.var ≠ x) :
    x ∈ blockIn blk out :=
  (mem_blockIn _ _ _).2 ⟨hphi, Or.inr ⟨Or.inl ⟨jmp, hj, hx⟩, hdef⟩⟩

/-- Block-local liveness never exceeds the free variables of the block when nothing is live out. -/
theorem blockIn_nil_subset_freeVars (blk : Blk) : blockIn blk [] ⊆ blk.freeVars := by
  intro x hx
  rw [mem_blockIn] at hx
  rw [mem_blk_freeVars]
  obtain ⟨hp, hx⟩ := hx
  rcases hx with hx | ⟨hj | hn, hd⟩
  · exact Or.inl ⟨hp, Or.inl hx⟩
  · exact Or.inl ⟨hp, Or.inr ⟨hj, hd⟩⟩
  · simp at hn

/-! ### Liveness fixpoint -/

abbrev getL (t : Tid) (S : List (Tid × List Var)) : List Var := (Assoc.get t S).getD []

abbrev Seed := Option (Tid × List Var)

/-- The transfer function's live-out, including a seed at the seeded exit. -/
abbrev liveOut (cfg : Cfg) (initial : Seed) (S : List (Tid × List Var)) (t : Tid) : List Var :=
  seedOut initial t (blockOut cfg S t)

theorem mem_seedOut (initial : Seed) (t : Tid) (out : List Var) (x : Var) :
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

def Le (S S' : List (Tid × List Var)) : Prop := ∀ t x, x ∈ getL t S → x ∈ getL t S'

theorem Le.refl (S : List (Tid × List Var)) : Le S S := fun _ _ h => h

theorem Le.trans {a b c : List (Tid × List Var)} (h : Le a b) (h' : Le b c) : Le a c :=
  fun t x hx => h' t x (h t x hx)

theorem blockOut_mono (cfg : Cfg) {S S' : List (Tid × List Var)} (h : Le S S') (t : Tid) :
    blockOut cfg S t ⊆ blockOut cfg S' t := by
  intro x hx
  rw [mem_blockOut] at hx ⊢
  obtain ⟨succ, hs, blk, hb, hc⟩ := hx
  refine ⟨succ, hs, blk, hb, ?_⟩
  rcases hc with ⟨hin, hp⟩ | hc
  · exact Or.inl ⟨h _ _ hin, hp⟩
  · exact Or.inr hc

theorem liveOut_mono (cfg : Cfg) (initial : Seed) {S S' : List (Tid × List Var)} (h : Le S S')
    (t : Tid) : liveOut cfg initial S t ⊆ liveOut cfg initial S' t := by
  intro x hx
  rw [mem_seedOut] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (blockOut_mono cfg h t hx)
  · exact Or.inr hx

theorem transfer_mono (cfg : Cfg) (initial : Seed) {S S' : List (Tid × List Var)} (h : Le S S')
    (t : Tid) (blk : Blk) :
    blockIn blk (liveOut cfg initial S t) ⊆ blockIn blk (liveOut cfg initial S' t) :=
  blockIn_mono blk (liveOut_mono cfg initial h t)

theorem getL_put_same (t : Tid) (v : List Var) (S : List (Tid × List Var)) :
    getL t (Assoc.put t v S) = v := by
  simp [getL]

theorem getL_put_ne {z t : Tid} (h : z ≠ t) (v : List Var) (S : List (Tid × List Var)) :
    getL z (Assoc.put t v S) = getL z S := by
  simp [getL, get_put, h]

/-- Invariant of the solver: rows are justified by the transfer function and stay in the universe. -/
structure LiveInv (cfg : Cfg) (initial : Seed) (U : List Var) (I O : List (Tid × List Var)) : Prop where
  post : ∀ t x, x ∈ getL t I → ∃ blk, cfg.block t = some blk ∧ x ∈ blockIn blk (liveOut cfg initial I t)
  outs : ∀ t x, x ∈ getL t O → x ∈ liveOut cfg initial I t
  univ : ∀ t x, x ∈ getL t I → x ∈ U

structure Universe (cfg : Cfg) (initial : Seed) (U : List Var) : Prop where
  blocks : ∀ blk ∈ cfg.blocks, blk.freeVars ⊆ U
  seeds : ∀ t vars, initial = some (t, vars) → vars ⊆ U

theorem liveOut_univ {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {I : List (Tid × List Var)} (hI : ∀ t x, x ∈ getL t I → x ∈ U) (t : Tid) :
    liveOut cfg initial I t ⊆ U := by
  intro x hx
  rcases (mem_seedOut _ _ _ _).1 hx with hx | ⟨vars, hi, hv⟩
  · obtain ⟨succ, _, blk, hb, hc⟩ := (mem_blockOut _ _ _ _).1 hx
    rcases hc with ⟨hin, _⟩ | ⟨phi, hphi, value, hget, hfv⟩
    · exact hI _ _ hin
    · refine hU.blocks blk (block_some hb).1 ((mem_blk_freeVars _ _).2 (Or.inr ?_))
      exact ⟨phi, hphi, (t, value), get_mem_env' hget, hfv⟩
  · exact hU.seeds _ _ hi hv

theorem blockIn_univ {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
    {blk : Blk} (hb : blk ∈ cfg.blocks) {out : List Var} (hout : out ⊆ U) : blockIn blk out ⊆ U := by
  intro x hx
  obtain ⟨hp, h⟩ := (mem_blockIn _ _ _).1 hx
  rcases h with h | ⟨h | h, hd⟩
  · exact hU.blocks blk hb ((mem_blk_freeVars _ _).2 (Or.inl ⟨hp, Or.inl h⟩))
  · exact hU.blocks blk hb ((mem_blk_freeVars _ _).2 (Or.inl ⟨hp, Or.inr ⟨h, hd⟩⟩))
  · exact hout h

abbrev stepFold (cfg : Cfg) (initial : Seed) (state : List (Tid × List Var) × List (Tid × List Var))
    (tid : Tid) : List (Tid × List Var) × List (Tid × List Var) :=
  match cfg.block tid with
  | none => state
  | some blk =>
    (Assoc.put tid (blockIn blk (liveOut cfg initial state.1 tid)) state.1,
      Assoc.put tid (liveOut cfg initial state.1 tid) state.2)

theorem livenessStep_eq (cfg : Cfg) (initial : Seed) (ins outs : List (Tid × List Var)) :
    livenessStep cfg initial ins outs = cfg.reachable.reverse.foldl (stepFold cfg initial) (ins, outs) := rfl

theorem step_preserves {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
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
structure FoldSpec (cfg : Cfg) (initial : Seed) (U : List Var) (l : List Tid)
    (I O I' O' : List (Tid × List Var)) : Prop where
  inv : LiveInv cfg initial U I' O'
  le : Le I I'
  leO : Le O O'
  inLower : ∀ t ∈ l, ∀ blk, cfg.block t = some blk → blockIn blk (liveOut cfg initial I t) ⊆ getL t I'
  outLower : ∀ t ∈ l, (∃ blk, cfg.block t = some blk) → liveOut cfg initial I t ⊆ getL t O'

theorem foldSpec (cfg : Cfg) (initial : Seed) {U : List Var} (hU : Universe cfg initial U)
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

theorem sameSets_iff (keys : List Tid) (a b : List (Tid × List Var)) :
    sameSets keys a b = true ↔ ∀ t ∈ keys, ∀ x, x ∈ getL t a ↔ x ∈ getL t b := by
  show (keys.all fun tid => Bap.Graph.setEq (getL tid a) (getL tid b)) = true ↔ _
  simp only [List.all_eq_true, Bap.Proofs.Graph.setEq_iff]

/-- Sum over the keys of the number of distinct variables in each row. -/
def card (keys : List Tid) (S : List (Tid × List Var)) : Nat :=
  (keys.map fun t => (getL t S).eraseDups.length).sum

theorem card_mono (keys : List Tid) {S S' : List (Tid × List Var)} (h : Le S S') :
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

theorem card_lt (keys : List Tid) {S S' : List (Tid × List Var)} (h : Le S S')
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

theorem card_le (keys : List Tid) {U : List Var} {S : List (Tid × List Var)}
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

theorem livenessAux_succ (cfg : Cfg) (initial : Seed) (fuel : Nat) (ins outs : List (Tid × List Var)) :
    livenessAux cfg initial (fuel + 1) ins outs =
      if sameSets cfg.reachable (livenessStep cfg initial ins outs).1 ins &&
          sameSets cfg.reachable (livenessStep cfg initial ins outs).2 outs then (ins, outs)
      else livenessAux cfg initial fuel (livenessStep cfg initial ins outs).1
        (livenessStep cfg initial ins outs).2 := rfl

/-- The solver result: an invariant-respecting table on which one more pass changes no row. -/
structure Converged (cfg : Cfg) (initial : Seed) (U : List Var) (r : List (Tid × List Var) × List (Tid × List Var)) : Prop where
  inv : LiveInv cfg initial U r.1 r.2
  ins : sameSets cfg.reachable (livenessStep cfg initial r.1 r.2).1 r.1 = true
  outs : sameSets cfg.reachable (livenessStep cfg initial r.1 r.2).2 r.2 = true

/-- Each pass that changes a table grows a row, and rows are bounded, so the fuel is sufficient. -/
theorem livenessAux_converged (cfg : Cfg) (initial : Seed) {U : List Var} (hU : Universe cfg initial U)
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

theorem getL_empty (l : List Tid) (t : Tid) : getL t (l.map fun tid => (tid, ([] : List Var))) = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hta : t = a
    · subst hta
      simp [getL, Assoc.get]
    · have hb : (t == a) = false := by simpa using hta
      have ih' : (List.lookup t (as.map fun tid => (tid, ([] : List Var)))).getD [] = [] := ih
      simpa [getL, Assoc.get, List.lookup, hb] using ih'

def universeOf (cfg : Cfg) (vars : List Var) : List Var :=
  (cfg.blocks.flatMap (fun blk => blk.definedVars ++ blk.freeVars) ++ vars).eraseDups

theorem universeOf_spec (cfg : Cfg) (vars : List Var) (initial : Seed)
    (h : ∀ t vs, initial = some (t, vs) → vs ⊆ vars) : Universe cfg initial (universeOf cfg vars) := by
  constructor
  · intro blk hb x hx
    simp only [universeOf, List.mem_eraseDups, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨blk, hb, Or.inr hx⟩
  · intro t vs hi x hx
    simp only [universeOf, List.mem_eraseDups, List.mem_append]
    exact Or.inr (h t vs hi hx)

theorem fuel_eq (cfg : Cfg) (vars : List Var) :
    livenessFuel cfg vars = 2 * (universeOf cfg vars).length * cfg.reachable.length + 1 := rfl

theorem liveness_converged (cfg : Cfg) : Converged cfg none (universeOf cfg []) (livenessRaw cfg) := by
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

theorem livenessFrom_converged (cfg : Cfg) (exit : Tid) (vars : List Var) :
    Converged cfg (some (exit, vars)) (universeOf cfg vars) (livenessFromRaw cfg exit vars) := by
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

theorem converged_equations {cfg : Cfg} {initial : Seed} {U : List Var} (hU : Universe cfg initial U)
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

theorem getL_rowsOf (keys : List Tid) (table : List (Tid × List Var)) (t : Tid) :
    getL t (keys.map fun tid => (tid, (Assoc.get tid table).getD [])) = if t ∈ keys then getL t table else [] := by
  induction keys with
  | nil => simp [getL, Assoc.get]
  | cons a as ih =>
    by_cases hta : t = a
    · subst hta
      simp [getL, Assoc.get]
    · have hb : (t == a) = false := by simpa using hta
      have hih := ih
      simp only [getL, Assoc.get] at hih ⊢
      simp [List.lookup, hb, hih, hta]

/-- The solver leaves a block it doesn't visit with nothing live in. -/
theorem fold_outside (cfg : Cfg) (initial : Seed) (keys : List Tid) {t : Tid} (ht : t ∉ keys)
    (I O : List (Tid × List Var)) (h : getL t I = []) : getL t (keys.foldl (stepFold cfg initial) (I, O)).1 = [] := by
  induction keys generalizing I O with
  | nil => exact h
  | cons a as ih =>
    simp only [List.mem_cons, not_or] at ht
    simp only [List.foldl_cons]
    cases hb : cfg.block a with
    | none =>
      have hstep : stepFold cfg initial (I, O) a = (I, O) := by simp only [stepFold, hb]
      rw [hstep]
      exact ih ht.2 I O h
    | some blk =>
      have hstep : stepFold cfg initial (I, O) a =
          (Assoc.put a (blockIn blk (liveOut cfg initial I a)) I, Assoc.put a (liveOut cfg initial I a) O) := by
        simp only [stepFold, hb]
      rw [hstep]
      exact ih ht.2 _ _ (by rw [getL_put_ne ht.1]; exact h)

theorem aux_outside (cfg : Cfg) (initial : Seed) {t : Tid} (ht : t ∉ cfg.reachable) (fuel : Nat)
    (I O : List (Tid × List Var)) (h : getL t I = []) : getL t (livenessAux cfg initial fuel I O).1 = [] := by
  induction fuel generalizing I O with
  | zero => exact h
  | succ fuel ih =>
    rw [livenessAux_succ]
    split
    · exact h
    · apply ih
      rw [livenessStep_eq]
      exact fold_outside cfg initial _ (by simpa using ht) I O h

theorem blockOut_congr (cfg : Cfg) {A B : List (Tid × List Var)} (h : ∀ s, getL s A = getL s B) (t : Tid) :
    blockOut cfg A t = blockOut cfg B t := by
  have h' : ∀ s, (Assoc.get s A).getD [] = (Assoc.get s B).getD [] := h
  unfold_blockOut_with h'

/-- The rows of `Cfg.liveness` are those of the solver. -/
theorem liveness_rows (cfg : Cfg) :
    (∀ s, getL s cfg.liveness.1 = getL s (livenessRaw cfg).1) ∧
      ∀ s ∈ cfg.reachable, getL s cfg.liveness.2 = getL s (livenessRaw cfg).2 := by
  refine ⟨fun s => ?_, fun s hs => ?_⟩
  · show getL s (cfg.reachable.map fun tid => (tid, (Assoc.get tid (livenessRaw cfg).1).getD [])) = _
    rw [getL_rowsOf]
    split
    · rfl
    · rename_i hs
      exact (aux_outside cfg none hs _ _ _ (getL_empty _ _)).symm
  · show getL s (cfg.reachable.map fun tid => (tid, (Assoc.get tid (livenessRaw cfg).2).getD [])) = _
    rw [getL_rowsOf, ite_eq_left hs]

/-- The rows of `Cfg.livenessFrom` are those of the solver. -/
theorem livenessFrom_rows (cfg : Cfg) (exit : Tid) (vars : List Var) :
    (∀ s, getL s (cfg.livenessFrom exit vars).1 = getL s (livenessFromRaw cfg exit vars).1) ∧
      ∀ s ∈ cfg.reachable, getL s (cfg.livenessFrom exit vars).2 = getL s (livenessFromRaw cfg exit vars).2 := by
  refine ⟨fun s => ?_, fun s hs => ?_⟩
  · show getL s (cfg.reachable.map fun tid => (tid, (Assoc.get tid (livenessFromRaw cfg exit vars).1).getD [])) = _
    rw [getL_rowsOf]
    split
    · rfl
    · rename_i hs
      exact (aux_outside cfg _ hs _ _ _ (getL_empty _ _)).symm
  · show getL s (cfg.reachable.map fun tid => (tid, (Assoc.get tid (livenessFromRaw cfg exit vars).2).getD [])) = _
    rw [getL_rowsOf, ite_eq_left hs]

/-- Every variable reported live-in at a block is justified by the transfer function. -/
theorem liveness_justified (cfg : Cfg) (t : Tid) (x : Var) (hx : x ∈ (Assoc.get t cfg.liveness.1).getD []) :
    ∃ blk, cfg.block t = some blk ∧ x ∈ blockIn blk (blockOut cfg cfg.liveness.1 t) := by
  have hx' : x ∈ getL t (livenessRaw cfg).1 := by
    rw [← (liveness_rows cfg).1 t]
    exact hx
  obtain ⟨blk, hb, hm⟩ := (liveness_converged cfg).inv.post t x hx'
  refine ⟨blk, hb, ?_⟩
  rw [blockOut_congr cfg (liveness_rows cfg).1 t]
  exact hm

/-- The solver always converges within its fuel, and its tables satisfy the backward dataflow
equations at every reachable block. -/
theorem liveness_equations (cfg : Cfg) {t : Tid} (ht : t ∈ cfg.reachable) {blk : Blk}
    (hb : cfg.block t = some blk) (x : Var) :
    (x ∈ (Assoc.get t cfg.liveness.1).getD [] ↔ x ∈ blockIn blk (blockOut cfg cfg.liveness.1 t)) ∧
      (x ∈ (Assoc.get t cfg.liveness.2).getD [] ↔ x ∈ blockOut cfg cfg.liveness.1 t) := by
  have heq := converged_equations (universeOf_spec cfg [] none (by simp)) (liveness_converged cfg) ht hb x
  have h1 : (Assoc.get t cfg.liveness.1).getD [] = getL t (livenessRaw cfg).1 := (liveness_rows cfg).1 t
  have h2 : (Assoc.get t cfg.liveness.2).getD [] = getL t (livenessRaw cfg).2 := (liveness_rows cfg).2 t ht
  rw [h1, h2, blockOut_congr cfg (liveness_rows cfg).1 t]
  exact heq

/-- `livenessFrom` satisfies the same equations with the seed added to the exit's live-out. -/
theorem livenessFrom_equations (cfg : Cfg) (exit : Tid) (vars : List Var) {t : Tid} (ht : t ∈ cfg.reachable)
    {blk : Blk} (hb : cfg.block t = some blk) (x : Var) :
    let r := cfg.livenessFrom exit vars
    (x ∈ (Assoc.get t r.1).getD [] ↔ (∀ phi ∈ blk.phis, phi.var ≠ x) ∧ (Exposed blk.defs x ∨
        (((∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars) ∨ x ∈ blockOut cfg r.1 t ∨ (t = exit ∧ x ∈ vars)) ∧
          ∀ defn ∈ blk.defs, defn.var ≠ x))) ∧
      (x ∈ (Assoc.get t r.2).getD [] ↔ x ∈ blockOut cfg r.1 t ∨ (t = exit ∧ x ∈ vars)) := by
  intro r
  have hU := universeOf_spec cfg vars (some (exit, vars)) (by
    intro t vs h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ List.Subset.refl _)
  have heq := converged_equations hU (livenessFrom_converged cfg exit vars) ht hb x
  have h1 : (Assoc.get t r.1).getD [] = getL t (livenessFromRaw cfg exit vars).1 := (livenessFrom_rows cfg exit vars).1 t
  have h2 : (Assoc.get t r.2).getD [] = getL t (livenessFromRaw cfg exit vars).2 := (livenessFrom_rows cfg exit vars).2 t ht
  have hout : blockOut cfg r.1 t = blockOut cfg (livenessFromRaw cfg exit vars).1 t :=
    blockOut_congr cfg (livenessFrom_rows cfg exit vars).1 t
  rw [h1, h2, hout]
  generalize (livenessFromRaw cfg exit vars) = raw at heq
  have hseed : ∀ y, y ∈ liveOut cfg (some (exit, vars)) raw.1 t ↔ y ∈ blockOut cfg raw.1 t ∨ (t = exit ∧ y ∈ vars) := by
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
    (hphi : ∀ phi ∈ eb.phis, phi.var ≠ x) (hpkill : ∀ defn ∈ pb.defs, defn.var ≠ x)
    (hppkill : ∀ phi ∈ pb.phis, phi.var ≠ x) :
    x ∈ (Assoc.get pred (cfg.livenessFrom exit vars).1).getD [] := by
  have hin : x ∈ (Assoc.get exit (cfg.livenessFrom exit vars).1).getD [] :=
    (livenessFrom_equations cfg exit vars hexit he x).1.2
      ⟨hphi, Or.inr ⟨Or.inr (Or.inr ⟨rfl, hx⟩), hkill⟩⟩
  refine (livenessFrom_equations cfg exit vars hpred hp x).1.2 ⟨hppkill, Or.inr ⟨Or.inr (Or.inl ?_), hpkill⟩⟩
  exact (mem_blockOut _ _ _ _).2 ⟨exit, hedge, eb, he, Or.inl ⟨hin, hphi⟩⟩

theorem fold_below (cfg : Cfg) (initial : Seed) (X : List (Tid × List Var)) (l : List Tid)
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

theorem aux_below (cfg : Cfg) (initial : Seed) (X : List (Tid × List Var))
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
    x ∈ (Assoc.get t X).getD [] := by
  have hx' : x ∈ getL t (livenessRaw cfg).1 := by
    rw [← (liveness_rows cfg).1 t]
    exact hx
  exact aux_below cfg none X hX _ _ _ (by intro z y hy; rw [getL_empty] at hy; simp at hy) t x hx'

end Bap.Proofs.IR
