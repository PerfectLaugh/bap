import Bap.IR.LiveFacts

/-! What `Cfg.liveness` finds, one variable at a time, for those who only ask whether a variable is live in a block.

Its rows are lists in the order the solver left them, so `Cfg.liveness` has to run its own solver to have them; but whether
a variable is live depends only on the blocks that mention it, and on the graph. That makes for two things: the blocks
where a variable is live can be found going back from where it is read, for what the rows have in them instead of the blocks
times the passes; and a variable no change mentions stays as it was, so it need not be looked at again. -/

namespace Bap.IR.LiveSets

open Bap Bap.Bil Bap.Proofs.IR

local macro "blockIn" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockIn)
local macro "blockOut" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockOut)
local macro "rowsOf" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.rowsOf)
local macro "livenessRaw" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.livenessRaw)

/-- The row of a block: what is live into it. -/
def liveIn (cfg : Cfg) (t : Tid) : List Bap.Var := (Assoc.get t cfg.liveness.1).getD []

/-- What the phis of a block read on the edge from `source`. -/
def phiReads (source : Tid) (blk : Blk) : List Bap.Var :=
  blk.phis.flatMap fun phi =>
    match Assoc.get source phi.values with
    | some value => Bil.freeVars value
    | none => []

def Killed (blk : Blk) (x : Bap.Var) : Prop :=
  (∃ phi ∈ blk.phis, phi.var = x) ∨ ∃ defn ∈ blk.defs, defn.var = x

/-- `x` is live out of `t` on the edge to `s`, given where it is live in. -/
def EdgeNeed (cfg : Cfg) (Row : Tid → Prop) (x : Bap.Var) (t s : Tid) : Prop :=
  ∃ blk, cfg.block s = some blk ∧ ((Row s ∧ ∀ phi ∈ blk.phis, phi.var ≠ x) ∨ x ∈ phiReads t blk)

theorem mem_phiReads (source : Tid) (blk : Blk) (x : Bap.Var) :
    x ∈ phiReads source blk ↔ ∃ phi ∈ blk.phis, ∃ value, Assoc.get source phi.values = some value ∧ x ∈ Bil.freeVars value := by
  simp only [phiReads, List.mem_flatMap]
  constructor
  · rintro ⟨phi, hp, hx⟩
    split at hx
    · exact ⟨phi, hp, _, by assumption, hx⟩
    · simp at hx
  · rintro ⟨phi, hp, value, hg, hx⟩
    exact ⟨phi, hp, by rw [hg]; exact hx⟩

theorem mem_blockIn_split (blk : Blk) (out : List Bap.Var) (x : Bap.Var) :
    x ∈ blockIn blk out ↔ x ∈ blockIn blk [] ∨ (x ∈ out ∧ ¬ Killed blk x) := by
  simp only [mem_blockIn, Killed, List.not_mem_nil, or_false]
  grind

theorem mem_blockOut_edge (cfg : Cfg) (S : List (Tid × List Bap.Var)) (t : Tid) (x : Bap.Var) :
    x ∈ blockOut cfg S t ↔ ∃ s ∈ cfg.successors t, EdgeNeed cfg (fun s => x ∈ (Assoc.get s S).getD []) x t s := by
  simp only [mem_blockOut, EdgeNeed, LiveEdge, mem_phiReads]

theorem reachable_of_live {cfg : Cfg} {t : Tid} {x : Bap.Var} (h : x ∈ liveIn cfg t) : t ∈ cfg.reachable := by
  have hl : liveIn cfg t = if t ∈ cfg.reachable then getL t (livenessRaw cfg).1 else [] := getL_rowsOf _ _ _
  rw [hl] at h
  split at h
  · assumption
  · simp at h

/-- A variable live into a block is one the block's own transfer justifies. -/
theorem live_of_gen {cfg : Cfg} {t : Tid} {blk : Blk} {x : Bap.Var} (ht : t ∈ cfg.reachable)
    (hb : cfg.block t = some blk) (h : x ∈ blockIn blk []) : x ∈ liveIn cfg t := by
  refine (liveness_equations cfg ht hb x).1.2 ?_
  exact (mem_blockIn_split _ _ _).2 (Or.inl h)

theorem live_of_edge {cfg : Cfg} {t s : Tid} {blk : Blk} {x : Bap.Var} (ht : t ∈ cfg.reachable)
    (hb : cfg.block t = some blk) (hk : ¬ Killed blk x) (hs : s ∈ cfg.successors t)
    (he : EdgeNeed cfg (fun s => x ∈ liveIn cfg s) x t s) : x ∈ liveIn cfg t := by
  refine (liveness_equations cfg ht hb x).1.2 ?_
  exact (mem_blockIn_split _ _ _).2 (Or.inr ⟨(mem_blockOut_edge _ _ _ _).2 ⟨s, hs, he⟩, hk⟩)

private theorem getD_map_keys (f : Tid → List Bap.Var) (keys : List Tid) (t : Tid) :
    (Assoc.get t (keys.map fun t => (t, f t))).getD [] = if t ∈ keys then f t else [] := by
  induction keys with
  | nil => simp [Assoc.get]
  | cons a as ih =>
    by_cases hta : t = a
    · subst hta
      simp [Assoc.get]
    · have hq : (t == a) = false := by simpa using hta
      simp only [Assoc.get] at ih ⊢
      simp [List.lookup, hq, ih, hta]

/-- Where a variable is live is the least set closed under the transfer of that variable alone: the other variables
can be taken to be live everywhere, as they don't affect it. -/
theorem live_least (cfg : Cfg) (x : Bap.Var) (Row : Tid → Prop)
    (hgen : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk → x ∈ blockIn blk [] → Row t)
    (hedge : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk → ¬ Killed blk x →
      ∀ s ∈ cfg.successors t, EdgeNeed cfg Row x t s → Row t)
    {t : Tid} (h : x ∈ liveIn cfg t) : Row t := by
  classical
  let U := universeOf cfg []
  let X : List (Tid × List Bap.Var) := cfg.reachable.map fun t => (t, U.filter fun y => y ≠ x ∨ Row t)
  have hrow : ∀ t, (Assoc.get t X).getD [] = if t ∈ cfg.reachable then U.filter (fun y => y ≠ x ∨ Row t) else [] :=
    fun t => getD_map_keys _ _ t
  have hU : Universe cfg none U := universeOf_spec cfg [] none (by simp)
  have hXU : ∀ t y, y ∈ getL t X → y ∈ U := by
    intro t y hy
    have : y ∈ (Assoc.get t X).getD [] := hy
    rw [hrow] at this
    split at this
    · exact (List.mem_filter.1 this).1
    · simp at this
  have hx := liveness_least cfg X (by
    intro t ht blk hb y hy
    rw [hrow, ite_eq_left ht, List.mem_filter]
    refine ⟨blockIn_univ hU (block_some hb).1 (liveOut_univ hU hXU t) hy, ?_⟩
    by_cases hyx : y = x
    · subst hyx
      simp only [ne_eq, not_true_eq_false, false_or, decide_eq_true_eq]
      rcases (mem_blockIn_split _ _ _).1 hy with hg | ⟨hout, hk⟩
      · exact hgen t ht blk hb hg
      · obtain ⟨s, hs, b, hbs, he⟩ := (mem_blockOut_edge _ _ _ _).1 hout
        refine hedge t ht blk hb hk s hs ⟨b, hbs, ?_⟩
        rcases he with ⟨hin, hp⟩ | hr
        · refine Or.inl ⟨?_, hp⟩
          rw [hrow] at hin
          split at hin
          · simpa using (List.mem_filter.1 hin).2
          · simp at hin
        · exact Or.inr hr
    · simp [hyx]) t x h
  rw [hrow] at hx
  split at hx
  · simpa using (List.mem_filter.1 hx).2
  · simp at hx

/-- A block as far as a variable goes. -/
structure Agree (x : Bap.Var) (blk other : Blk) : Prop where
  gen : x ∈ blockIn blk [] ↔ x ∈ blockIn other []
  kill : Killed blk x ↔ Killed other x
  phi : (∀ phi ∈ blk.phis, phi.var ≠ x) ↔ ∀ phi ∈ other.phis, phi.var ≠ x
  reads : ∀ source, x ∈ phiReads source blk ↔ x ∈ phiReads source other

theorem Agree.symm {x : Bap.Var} {blk other : Blk} (h : Agree x blk other) : Agree x other blk :=
  ⟨h.gen.symm, h.kill.symm, h.phi.symm, fun source => (h.reads source).symm⟩

private theorem live_sub (cfg other : Cfg) (x : Bap.Var) (hgraph : other.reachable = cfg.reachable)
    (hsucc : ∀ t, other.successors t = cfg.successors t)
    (hagree : ∀ t blk, cfg.block t = some blk → ∃ b, other.block t = some b ∧ Agree x blk b) {t : Tid}
    (h : x ∈ liveIn cfg t) : x ∈ liveIn other t := by
  refine live_least cfg x (fun t => x ∈ liveIn other t) ?_ ?_ h
  · intro t ht blk hb hg
    obtain ⟨b, hb', ha⟩ := hagree t blk hb
    exact live_of_gen (hgraph ▸ ht) hb' (ha.gen.1 hg)
  · intro t ht blk hb hk s hs he
    obtain ⟨b, hb', ha⟩ := hagree t blk hb
    refine live_of_edge (hgraph ▸ ht) hb' (fun hk' => hk (ha.kill.2 hk')) (by rw [hsucc]; exact hs) ?_
    obtain ⟨bs, hbs, hc⟩ := he
    obtain ⟨bs', hbs', ha'⟩ := hagree s bs hbs
    refine ⟨bs', hbs', ?_⟩
    rcases hc with ⟨hr, hp⟩ | hr
    · exact Or.inl ⟨hr, ha'.phi.1 hp⟩
    · exact Or.inr ((ha'.reads t).1 hr)

/-- A variable all blocks of two CFGs of the same graph agree on is live in the same places. -/
theorem live_iff_of_agree (cfg other : Cfg) (x : Bap.Var) (hgraph : other.reachable = cfg.reachable)
    (hsucc : ∀ t, other.successors t = cfg.successors t)
    (hagree : ∀ t blk, cfg.block t = some blk → ∃ b, other.block t = some b ∧ Agree x blk b)
    (hagree' : ∀ t blk, other.block t = some blk → ∃ b, cfg.block t = some b ∧ Agree x b blk) (t : Tid) :
    x ∈ liveIn cfg t ↔ x ∈ liveIn other t :=
  ⟨live_sub cfg other x hgraph hsucc hagree,
    live_sub other cfg x hgraph.symm (fun t => (hsucc t).symm)
      (fun t blk hb => (hagree' t blk hb).imp fun _ h => ⟨h.1, h.2.symm⟩)⟩

/-! ### Going back from where a variable is read -/

abbrev Blocks := Std.HashMap Tid Blk
abbrev Preds := Std.HashMap Tid (List Tid)
abbrev Row := Std.HashSet Tid

def killed (blk : Blk) (x : Bap.Var) : Bool :=
  blk.phis.any (·.var == x) || blk.defs.any (·.var == x)

theorem killed_iff (blk : Blk) (x : Bap.Var) : killed blk x = true ↔ Killed blk x := by
  simp [killed, Killed]

def hasPhi (blk : Blk) (x : Bap.Var) : Bool := blk.phis.any (·.var == x)

theorem hasPhi_false_iff (blk : Blk) (x : Bap.Var) : hasPhi blk x = false ↔ ∀ phi ∈ blk.phis, phi.var ≠ x := by
  simp [hasPhi]

/-- The blocks and the reachable edges of a CFG, by where they go. -/
structure Tables (cfg : Cfg) (blocks : Blocks) (preds : Preds) : Prop where
  block : ∀ t, blocks.get? t = cfg.block t
  pred : ∀ t p, p ∈ preds.getD t [] ↔ p ∈ cfg.reachable ∧ t ∈ cfg.successors p

def visitPreds (blocks : Blocks) (x : Bap.Var) (preds : List Tid) (state : Row × List Tid) : Row × List Tid :=
  preds.foldl (init := state) fun state p =>
    if state.1.contains p then state
    else
      match blocks.get? p with
      | none => state
      | some blk => if killed blk x then state else (state.1.insert p, p :: state.2)

def floodAux (blocks : Blocks) (preds : Preds) (x : Bap.Var) : Nat → Row → List Tid → Option Row
  | 0, _, _ => none
  | _ + 1, row, [] => some row
  | fuel + 1, row, t :: work =>
    match blocks.get? t with
    | none => floodAux blocks preds x fuel row work
    | some blk =>
      if hasPhi blk x then
        floodAux blocks preds x fuel row work
      else
        let next := visitPreds blocks x (preds.getD t []) (row, work)
        floodAux blocks preds x fuel next.1 next.2

/-- Where a variable is live is known, given what starts it. -/
structure Seeds (cfg : Cfg) (x : Bap.Var) (seeds : List Tid) : Prop where
  sound : ∀ t ∈ seeds, x ∈ liveIn cfg t
  gen : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk → x ∈ blockIn blk [] → t ∈ seeds
  read : ∀ t ∈ cfg.reachable, ∀ blk, cfg.block t = some blk → ¬ Killed blk x → ∀ s ∈ cfg.successors t,
    ∀ b, cfg.block s = some b → x ∈ phiReads t b → t ∈ seeds

private structure FloodInv (cfg : Cfg) (x : Bap.Var) (row : Row) (work : List Tid) : Prop where
  sound : ∀ t, row.contains t = true → x ∈ liveIn cfg t
  closed : ∀ t b, row.contains t = true → t ∉ work → cfg.block t = some b → (∀ phi ∈ b.phis, phi.var ≠ x) →
    ∀ p ∈ cfg.reachable, t ∈ cfg.successors p → ∀ bp, cfg.block p = some bp → ¬ Killed bp x → row.contains p = true

private theorem visitPreds_spec {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) (x : Bap.Var)
    {t : Tid} (hlive : x ∈ liveIn cfg t)
    (ps : List Tid) (hps : ∀ p ∈ ps, p ∈ preds.getD t [])
    (hb : ∃ b, cfg.block t = some b ∧ ∀ phi ∈ b.phis, phi.var ≠ x) (state : Row × List Tid)
    (hs : ∀ q, state.1.contains q = true → x ∈ liveIn cfg q) :
    let next := visitPreds blocks x ps state
    (∀ q, next.1.contains q = true → x ∈ liveIn cfg q) ∧
    (∀ q, state.1.contains q = true → next.1.contains q = true) ∧
    (∀ q ∈ state.2, q ∈ next.2) ∧
    (∀ q, next.1.contains q = true → state.1.contains q = false → q ∈ next.2) ∧
    (∀ p ∈ ps, ∀ bp, cfg.block p = some bp → ¬ Killed bp x → next.1.contains p = true) ∧
    (∀ q ∈ next.2, q ∈ state.2 ∨ next.1.contains q = true) := by
  induction ps generalizing state with
  | nil =>
    refine ⟨hs, fun _ h => h, fun _ h => h, fun q h1 h2 => ?_, by simp, fun _ h => Or.inl h⟩
    have : state.1.contains q = true := h1
    rw [this] at h2
    cases h2
  | cons p rest ih =>
    have hrest : ∀ p ∈ rest, p ∈ preds.getD t [] := fun p hp => hps p (List.mem_cons_of_mem _ hp)
    simp only [visitPreds, List.foldl_cons]
    by_cases hc : state.1.contains p = true
    · simp only [hc, ↓reduceIte]
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hrest state hs
      refine ⟨h1, h2, h3, h4, ?_, h6⟩
      intro q hq bp hbp hk
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h2 _ hc
      · exact h5 q hq bp hbp hk
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
      cases hg : blocks.get? p with
      | none =>
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hrest state hs
        refine ⟨h1, h2, h3, h4, ?_, h6⟩
        intro q hq bp hbp hk
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [h.block, hbp] at hg
          cases hg
        · exact h5 q hq bp hbp hk
      | some blk =>
        have hblk : cfg.block p = some blk := by rw [← h.block, hg]
        dsimp only
        by_cases hk : killed blk x = true
        · simp only [hk, ↓reduceIte]
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hrest state hs
          refine ⟨h1, h2, h3, h4, ?_, h6⟩
          intro q hq bp hbp hk'
          rcases List.mem_cons.1 hq with rfl | hq
          · rw [hblk] at hbp
            cases hbp
            exact absurd ((killed_iff _ _).1 hk) hk'
          · exact h5 q hq bp hbp hk'
        · simp only [hk, ↓reduceIte, Bool.false_eq_true]
          have hpm := (h.pred t p).1 (hps p List.mem_cons_self)
          have hnew : x ∈ liveIn cfg p := by
            obtain ⟨b, hb1, hb2⟩ := hb
            refine live_of_edge hpm.1 hblk (fun hk' => hk ((killed_iff _ _).2 hk')) hpm.2 ⟨b, hb1, Or.inl ⟨hlive, hb2⟩⟩
          have hs' : ∀ q, ((state.1.insert p, p :: state.2) : Row × List Tid).1.contains q = true → x ∈ liveIn cfg q := by
            intro q hq
            simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hq
            rcases hq with rfl | hq
            · exact hnew
            · exact hs q hq
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hrest (state.1.insert p, p :: state.2) hs'
          refine ⟨h1, ?_, ?_, ?_, ?_, ?_⟩
          · intro q hq
            apply h2
            simp [hq]
          · intro q hq
            exact h3 q (List.mem_cons_of_mem _ hq)
          · intro q hq hnq
            by_cases hqp : q = p
            · subst hqp
              exact h3 q List.mem_cons_self
            · apply h4 q hq
              simp only [Std.HashSet.contains_insert]
              have : (p == q) = false := by simpa using fun e : p = q => hqp e.symm
              simp [this, hnq]
          · intro q hq bp hbp hk'
            rcases List.mem_cons.1 hq with rfl | hq
            · apply h2
              simp
            · exact h5 q hq bp hbp hk'
          · intro q hq
            rcases h6 q hq with hq | hq
            · rcases List.mem_cons.1 hq with rfl | hq
              · exact Or.inr (h2 _ (by simp))
              · exact Or.inl hq
            · exact Or.inr hq

private theorem floodAux_inv {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) (x : Bap.Var)
    (fuel : Nat) (row : Row) (work : List Tid) (result : Row) (hinv : FloodInv cfg x row work)
    (hwork : ∀ t ∈ work, row.contains t = true) (hr : floodAux blocks preds x fuel row work = some result) :
    FloodInv cfg x result [] ∧ ∀ t, row.contains t = true → result.contains t = true := by
  induction fuel generalizing row work with
  | zero => simp [floodAux] at hr
  | succ fuel ih =>
    cases work with
    | nil =>
      simp only [floodAux, Option.some.injEq] at hr
      subst hr
      exact ⟨hinv, fun _ h => h⟩
    | cons t work =>
      simp only [floodAux] at hr
      have hrow : row.contains t = true := hwork t List.mem_cons_self
      have hskip : floodAux blocks preds x fuel row work = some result →
          (∀ b, cfg.block t = some b → (∀ phi ∈ b.phis, phi.var ≠ x) → False) →
          FloodInv cfg x result [] ∧ ∀ t, row.contains t = true → result.contains t = true := by
        intro hr hno
        refine ih row work ⟨hinv.sound, ?_⟩ (fun q hq => hwork q (List.mem_cons_of_mem _ hq)) hr
        intro q b hq hnq hbq hp
        by_cases hqt : q = t
        · subst hqt
          exact (hno b hbq hp).elim
        · exact hinv.closed q b hq (by simp [hqt, hnq]) hbq hp
      cases hg : blocks.get? t with
      | none =>
        rw [hg] at hr
        refine hskip hr fun b hb _ => ?_
        rw [h.block, hb] at hg
        cases hg
      | some blk =>
        rw [hg] at hr
        have hblk : cfg.block t = some blk := by rw [← h.block, hg]
        dsimp only at hr
        by_cases hp : hasPhi blk x = true
        · rw [ite_eq_left hp] at hr
          refine hskip hr fun b hb hno => ?_
          rw [hblk] at hb
          cases hb
          have := (hasPhi_false_iff _ _).2 hno
          rw [hp] at this
          cases this
        · rw [ite_eq_right hp] at hr
          have hnp : ∀ phi ∈ blk.phis, phi.var ≠ x := (hasPhi_false_iff _ _).1 (by simpa using hp)
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := visitPreds_spec h x (hinv.sound t hrow) (preds.getD t [])
            (fun _ h => h) ⟨blk, hblk, hnp⟩ (row, work) hinv.sound
          have hstep := ih _ _ ⟨h1, ?_⟩ ?_ hr
          · exact ⟨hstep.1, fun q hq => hstep.2 q (h2 q hq)⟩
          · intro q b hq hnq hbq hpq p hpr hps bp hbp hk
            by_cases hnew : row.contains q = true
            · by_cases hqt : q = t
              · subst hqt
                rw [hblk] at hbq
                cases hbq
                exact h5 p ((h.pred q p).2 ⟨hpr, hps⟩) bp hbp hk
              · have hnw : q ∉ t :: work := by
                  intro hm
                  rcases List.mem_cons.1 hm with rfl | hm
                  · exact hqt rfl
                  · exact hnq (h3 q hm)
                exact h2 _ (hinv.closed q b hnew hnw hbq hpq p hpr hps bp hbp hk)
            · exact (hnq (h4 q hq (by simpa using hnew))).elim
          · intro q hq
            rcases h6 q hq with hq | hq
            · exact h2 q (hwork q (List.mem_cons_of_mem _ hq))
            · exact hq

def seedRow (seeds : List Tid) : Row := seeds.foldl (fun row t => row.insert t) {}

private theorem seedRow_contains (seeds : List Tid) (t : Tid) : (seedRow seeds).contains t = true ↔ t ∈ seeds := by
  have key : ∀ (l : List Tid) (row : Row), (l.foldl (fun row t => row.insert t) row).contains t = true ↔
      row.contains t = true ∨ t ∈ l := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro row
      simp only [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
      grind
  simpa [seedRow] using key seeds {}

/-- Where `x` is live, from what starts it, if the fuel lasts. -/
def flood (blocks : Blocks) (preds : Preds) (x : Bap.Var) (fuel : Nat) (seeds : List Tid) : Option Row :=
  floodAux blocks preds x fuel (seedRow seeds) seeds

theorem flood_spec {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {x : Bap.Var} {fuel : Nat}
    {seeds : List Tid} (hs : Seeds cfg x seeds) {row : Row} (hr : flood blocks preds x fuel seeds = some row) (t : Tid) :
    row.contains t = true ↔ x ∈ liveIn cfg t := by
  have hstart : FloodInv cfg x (seedRow seeds) seeds :=
    ⟨fun t ht => hs.sound t ((seedRow_contains _ _).1 ht), fun _ _ ht hnw => (hnw ((seedRow_contains _ _).1 ht)).elim⟩
  obtain ⟨hinv, hmono⟩ := floodAux_inv h x fuel _ _ row hstart (fun t ht => (seedRow_contains _ _).2 ht) hr
  refine ⟨hinv.sound t, fun hl => ?_⟩
  refine live_least cfg x (fun t => row.contains t = true) ?_ ?_ hl
  · intro t ht blk hb hg
    exact hmono t ((seedRow_contains _ _).2 (hs.gen t ht blk hb hg))
  · intro t ht blk hb hk s hss he
    obtain ⟨bs, hbs, hc⟩ := he
    rcases hc with ⟨hrow, hp⟩ | hread
    · exact hinv.closed s bs hrow (by simp) hbs hp t ht hss blk hb hk
    · exact hmono t ((seedRow_contains _ _).2 (hs.read t ht blk hb hk s hss bs hbs hread))

/-! ### What starts a variable, and which variables to look at -/

/-- Everything a block mentions. -/
def vocabulary (blk : Blk) : List Bap.Var :=
  blk.phis.map Phi.var ++ blk.phis.flatMap (fun phi => phi.values.flatMap fun input => Bil.freeVars input.2) ++
    blk.defs.flatMap (fun defn => defn.var :: Bil.freeVars defn.rhs) ++ blk.jmps.flatMap Jmp.freeVars

private theorem get_mem {k : Tid} {v : Bil.Exp} {T : List (Tid × Bil.Exp)} (h : Assoc.get k T = some v) : (k, v) ∈ T :=
  get_mem_env' h

theorem vocabulary_of_read {source : Tid} {blk : Blk} {x : Bap.Var} (h : x ∈ phiReads source blk) : x ∈ vocabulary blk := by
  obtain ⟨phi, hp, value, hg, hx⟩ := (mem_phiReads _ _ _).1 h
  simp only [vocabulary, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inl (Or.inr ⟨phi, hp, (source, value), get_mem hg, hx⟩))

private theorem exposed_read {defs : List Def} {x : Bap.Var} (h : Exposed defs x) : ∃ d ∈ defs, x ∈ Bil.freeVars d.rhs := by
  induction defs with
  | nil => exact h.elim
  | cons d ds ih =>
    rcases h with h | ⟨_, h⟩
    · exact ⟨d, List.mem_cons_self, h⟩
    · obtain ⟨e, he, hx⟩ := ih h
      exact ⟨e, List.mem_cons_of_mem _ he, hx⟩

theorem vocabulary_of_gen {blk : Blk} {x : Bap.Var} (h : x ∈ blockIn blk []) : x ∈ vocabulary blk := by
  obtain ⟨_, h⟩ := (mem_blockIn _ _ _).1 h
  simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
  rcases h with h | ⟨h | h, _⟩
  · obtain ⟨d, hd, hx⟩ := exposed_read h
    exact Or.inl (Or.inr ⟨d, hd, Or.inr hx⟩)
  · obtain ⟨j, hj, hx⟩ := h
    exact Or.inr ⟨j, hj, hx⟩
  · simp at h

abbrev VarTable := Std.HashMap Bap.Var (List Tid)

def addTo (table : VarTable) (y : Bap.Var) (t : Tid) : VarTable := table.insert y (t :: table.getD y [])

theorem mem_addTo (table : VarTable) (y z : Bap.Var) (t u : Tid) :
    u ∈ (addTo table y t).getD z [] ↔ u ∈ table.getD z [] ∨ (z = y ∧ u = t) := by
  simp only [addTo, Std.HashMap.getD_insert]
  by_cases h : y = z
  · subst h
    simp [or_comm]
  · have hq : (y == z) = false := by simpa using h
    have hne : z ≠ y := fun e => h e.symm
    simp [hq, hne]

/-- The blocks each variable is listed for by `vars`. -/
def tableOf (vars : Blk → List Bap.Var) (blocks : List Blk) : VarTable :=
  blocks.foldl (init := {}) fun table blk => (vars blk).foldl (fun table y => addTo table y blk.tid) table

theorem mem_tableOf (vars : Blk → List Bap.Var) (blocks : List Blk) :
    ∀ blk ∈ blocks, ∀ y ∈ vars blk, blk.tid ∈ (tableOf vars blocks).getD y [] := by
  have inner : ∀ (l : List Bap.Var) (t : Tid) (table : VarTable) (z : Bap.Var) (u : Tid),
      u ∈ (l.foldl (fun table y => addTo table y t) table).getD z [] ↔ u ∈ table.getD z [] ∨ (z ∈ l ∧ u = t) := by
    intro l t
    induction l with
    | nil => simp
    | cons a as ih =>
      intro table z u
      simp only [List.foldl_cons, ih, mem_addTo, List.mem_cons]
      grind
  have outer : ∀ (l : List Blk) (table : VarTable), (∀ blk ∈ l, ∀ y ∈ vars blk, blk.tid ∈
      (l.foldl (fun table blk => (vars blk).foldl (fun table y => addTo table y blk.tid) table) table).getD y []) ∧
      ∀ z u, u ∈ table.getD z [] →
        u ∈ (l.foldl (fun table blk => (vars blk).foldl (fun table y => addTo table y blk.tid) table) table).getD z [] := by
    intro l
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro table
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih ((vars b).foldl (fun table y => addTo table y b.tid) table)
      refine ⟨?_, fun z u hu => h2 z u ((inner _ _ _ _ _).2 (Or.inl hu))⟩
      intro blk hblk y hy
      rcases List.mem_cons.1 hblk with rfl | hblk
      · exact h2 y _ ((inner _ _ _ _ _).2 (Or.inr ⟨hy, rfl⟩))
      · exact h1 blk hblk y hy
  exact fun blk hb y hy => (outer blocks {}).1 blk hb y hy

/-- What a block assigns. -/
def assigned (blk : Blk) : List Bap.Var := blk.defs.map Def.var ++ blk.phis.map Phi.var

def SitesOf (cfg : Cfg) (sites : VarTable) : Prop :=
  ∀ blk ∈ cfg.blocks, ∀ y ∈ vocabulary blk, blk.tid ∈ sites.getD y []

def DefinersOf (cfg : Cfg) (definers : VarTable) : Prop :=
  ∀ blk ∈ cfg.blocks, ∀ y ∈ assigned blk, blk.tid ∈ definers.getD y []

private theorem foldAdd (l : List Bap.Var) (c : Bap.Var → Bool) (t : Tid) (table : VarTable) (z : Bap.Var) (u : Tid) :
    u ∈ (l.foldl (fun table y => if c y then addTo table y t else table) table).getD z [] ↔
      u ∈ table.getD z [] ∨ (u = t ∧ z ∈ l ∧ c z = true) := by
  induction l generalizing table with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih]
    split
    · simp only [mem_addTo, List.mem_cons]
      grind
    · simp only [List.mem_cons]
      grind

/-- What starts the variables of `affected` that the block `s` starts: in itself and in the blocks before it. -/
def seedsAt (blocks : Blocks) (preds : Preds) (affected : Std.HashSet Bap.Var) (reach : Row) (table : VarTable) (s : Tid) : VarTable :=
  match blocks.get? s with
  | none => table
  | some blk =>
    let table := if reach.contains s then
        (blockIn blk []).foldl (fun table y => if affected.contains y then addTo table y s else table) table
      else table
    (preds.getD s []).foldl (init := table) fun table p =>
      match blocks.get? p with
      | none => table
      | some bp =>
        (phiReads p blk).foldl (fun table y => if affected.contains y && !killed bp y then addTo table y p else table) table

private theorem seedsAt_preds (blocks : Blocks) (affected : Std.HashSet Bap.Var) (blk : Blk) (ps : List Tid) (table : VarTable)
    (z : Bap.Var) (u : Tid) :
    u ∈ (ps.foldl (init := table) fun table p =>
      match blocks.get? p with
      | none => table
      | some bp =>
        (phiReads p blk).foldl (fun table y => if affected.contains y && !killed bp y then addTo table y p else table) table).getD z [] ↔
      u ∈ table.getD z [] ∨ (u ∈ ps ∧ ∃ bp, blocks.get? u = some bp ∧ z ∈ phiReads u blk ∧ affected.contains z = true ∧ killed bp z = false) := by
  induction ps generalizing table with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    cases hg : blocks.get? p with
    | none =>
      constructor
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, h'⟩
      · rintro (h | ⟨rfl | h, bp, hb, h'⟩)
        · exact Or.inl h
        · rw [hg] at hb
          cases hb
        · exact Or.inr ⟨h, bp, hb, h'⟩
    | some bp =>
      dsimp only
      rw [foldAdd]
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ((h | ⟨rfl, h1, h2, h3⟩) | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, bp, hg, h1, h2, h3⟩
        · exact Or.inr ⟨Or.inr h, h'⟩
      · rintro (h | ⟨rfl | h, b, hb, h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rw [hg] at hb
          cases hb
          exact Or.inl (Or.inr ⟨rfl, h1, h2, h3⟩)
        · exact Or.inr ⟨h, b, hb, h1, h2, h3⟩

theorem mem_seedsAt {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {reach : Row}
    (hreach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable) (affected : Std.HashSet Bap.Var) (table : VarTable)
    (s : Tid) (z : Bap.Var) (u : Tid) :
    u ∈ (seedsAt blocks preds affected reach table s).getD z [] ↔ u ∈ table.getD z [] ∨
      (∃ blk, cfg.block s = some blk ∧ affected.contains z = true ∧
        ((u = s ∧ s ∈ cfg.reachable ∧ z ∈ blockIn blk []) ∨
          (u ∈ cfg.reachable ∧ s ∈ cfg.successors u ∧ ∃ bp, cfg.block u = some bp ∧ z ∈ phiReads u blk ∧ ¬ Killed bp z))) := by
  simp only [seedsAt]
  cases hg : blocks.get? s with
  | none =>
    have hb : cfg.block s = none := by rw [← h.block, hg]
    simp [hb]
  | some blk =>
    have hb : cfg.block s = some blk := by rw [← h.block, hg]
    dsimp only
    rw [seedsAt_preds]
    have hkill : ∀ bp y, killed bp y = false ↔ ¬ Killed bp y := by
      intro bp y
      rw [← killed_iff]
      simp
    have hfirst : u ∈ (if reach.contains s = true then
          (blockIn blk []).foldl (fun table y => if affected.contains y then addTo table y s else table) table
        else table).getD z [] ↔
        u ∈ table.getD z [] ∨ (s ∈ cfg.reachable ∧ u = s ∧ z ∈ blockIn blk [] ∧ affected.contains z = true) := by
      by_cases hr : reach.contains s = true
      · rw [ite_eq_left hr, foldAdd, hreach s |>.symm]
        simp [hr]
      · have hns : s ∉ cfg.reachable := fun hm => hr ((hreach s).2 hm)
        rw [ite_eq_right hr]
        simp [hns]
    rw [hfirst, or_assoc]
    apply or_congr_right
    simp only [h.pred, h.block, hkill, hb, Option.some.injEq, exists_eq_left']
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨⟨h1, h2⟩, bp, hbp, h3, h4, h5⟩)
      · exact ⟨h4, Or.inl ⟨h2, h1, h3⟩⟩
      · exact ⟨h4, Or.inr ⟨h1, h2, bp, hbp, h3, h5⟩⟩
    · rintro ⟨h4, ⟨h1, h2, h3⟩ | ⟨h1, h2, bp, hbp, h3, h5⟩⟩
      · exact Or.inl ⟨h2, h1, h3, h4⟩
      · exact Or.inr ⟨⟨h1, h2⟩, bp, hbp, h3, h4, h5⟩

/-- `seedsAt` over the blocks that mention the variables of `affected`. -/
def seedTable (blocks : Blocks) (preds : Preds) (affected : Std.HashSet Bap.Var) (reach : Row) (sites : List Tid) : VarTable :=
  sites.foldl (seedsAt blocks preds affected reach) {}

private theorem mem_seedTable {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {reach : Row}
    (hreach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable) (affected : Std.HashSet Bap.Var) (sites : List Tid) (z : Bap.Var) (u : Tid) :
    u ∈ (seedTable blocks preds affected reach sites).getD z [] ↔
      ∃ s ∈ sites, ∃ blk, cfg.block s = some blk ∧ affected.contains z = true ∧
        ((u = s ∧ s ∈ cfg.reachable ∧ z ∈ blockIn blk []) ∨
          (u ∈ cfg.reachable ∧ s ∈ cfg.successors u ∧ ∃ bp, cfg.block u = some bp ∧ z ∈ phiReads u blk ∧ ¬ Killed bp z)) := by
  have key : ∀ (l : List Tid) (table : VarTable), u ∈ (l.foldl (seedsAt blocks preds affected reach) table).getD z [] ↔
      u ∈ table.getD z [] ∨ ∃ s ∈ l, ∃ blk, cfg.block s = some blk ∧ affected.contains z = true ∧
        ((u = s ∧ s ∈ cfg.reachable ∧ z ∈ blockIn blk []) ∨
          (u ∈ cfg.reachable ∧ s ∈ cfg.successors u ∧ ∃ bp, cfg.block u = some bp ∧ z ∈ phiReads u blk ∧ ¬ Killed bp z)) := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro table
      simp only [List.foldl_cons, ih, mem_seedsAt h hreach, List.mem_cons, exists_eq_or_imp, or_assoc]
  simpa [seedTable] using key sites {}

theorem seedTable_seeds {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {reach : Row}
    (hreach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable) {affected : Std.HashSet Bap.Var} {sites : List Tid} {x : Bap.Var}
    (hx : affected.contains x = true)
    (hsites : ∀ s blk, cfg.block s = some blk → x ∈ vocabulary blk → s ∈ sites) :
    Seeds cfg x ((seedTable blocks preds affected reach sites).getD x []) := by
  constructor
  · intro t ht
    obtain ⟨s, _, blk, hb, _, hc⟩ := (mem_seedTable h hreach _ _ _ _).1 ht
    rcases hc with ⟨rfl, hr, hg⟩ | ⟨hr, hsucc, bp, hbp, hread, hk⟩
    · exact live_of_gen hr hb hg
    · exact live_of_edge hr hbp hk hsucc ⟨blk, hb, Or.inr hread⟩
  · intro t ht blk hb hg
    exact (mem_seedTable h hreach _ _ _ _).2 ⟨t, hsites t blk hb (vocabulary_of_gen hg), blk, hb, hx, Or.inl ⟨rfl, ht, hg⟩⟩
  · intro t ht blk hb hk s hs b hbs hread
    exact (mem_seedTable h hreach _ _ _ _).2
      ⟨s, hsites s b hbs (vocabulary_of_read hread), b, hbs, hx, Or.inr ⟨ht, hs, blk, hb, hread, hk⟩⟩

/-! ### Rows by variable -/

abbrev Live := Std.HashMap Bap.Var Row

def isLive (live : Live) (x : Bap.Var) (t : Tid) : Bool := (live.getD x {}).contains t

/-- What the table has for a variable is its row. -/
def RowOf (cfg : Cfg) (live : Live) (x : Bap.Var) : Prop := ∀ t, isLive live x t = true ↔ x ∈ liveIn cfg t

def refreshAux (blocks : Blocks) (preds : Preds) (seeds : VarTable) (blockCount : Nat) (live : Live) : List Bap.Var → Option Live
  | [] => some live
  | x :: rest =>
    let start := seeds.getD x []
    match start with
    | [] => refreshAux blocks preds seeds blockCount (live.erase x) rest
    | _ =>
      match flood blocks preds x (start.length + blockCount + 1) start with
      | none => none
      | some row => refreshAux blocks preds seeds blockCount (live.insert x row) rest

private theorem refreshAux_spec {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {seeds : VarTable} {count : Nat}
    (vars : List Bap.Var) (hseeds : ∀ x ∈ vars, Seeds cfg x (seeds.getD x [])) (live : Live) (result : Live)
    (hr : refreshAux blocks preds seeds count live vars = some result) :
    (∀ x, x ∉ vars → RowOf cfg live x → RowOf cfg result x) ∧ ∀ x ∈ vars, RowOf cfg result x := by
  induction vars generalizing live with
  | nil =>
    simp only [refreshAux, Option.some.injEq] at hr
    subst hr
    exact ⟨fun _ _ h => h, by simp⟩
  | cons a as ih =>
    have hnext : ∀ live' : Live, RowOf cfg live' a → (∀ x, a ≠ x → ∀ t, isLive live' x t = isLive live x t) →
        refreshAux blocks preds seeds count live' as = some result →
        (∀ x, x ∉ a :: as → RowOf cfg live x → RowOf cfg result x) ∧ ∀ x ∈ a :: as, RowOf cfg result x := by
      intro live' hrow hsame hr
      obtain ⟨h1, h2⟩ := ih (fun x hx => hseeds x (List.mem_cons_of_mem _ hx)) _ hr
      refine ⟨fun x hx hl => h1 x (fun hm => hx (List.mem_cons_of_mem _ hm)) ?_, ?_⟩
      · intro t
        rw [← hl t, hsame x (fun e => hx (e ▸ List.mem_cons_self)) t]
      · intro x hx
        by_cases hax : x = a
        · subst hax
          by_cases hmem : x ∈ as
          · exact h2 x hmem
          · exact h1 x hmem hrow
        · exact h2 x (by simpa [hax] using hx)
    simp only [refreshAux] at hr
    cases hstart : seeds.getD a [] with
    | nil =>
      rw [hstart] at hr
      dsimp only at hr
      have hf : flood blocks preds a (0 + count + 1) [] = some {} := by
        simp [flood, floodAux, seedRow]
      refine hnext _ ?_ ?_ hr
      · intro t
        have hseed := hseeds a List.mem_cons_self
        rw [hstart] at hseed
        rw [← flood_spec h hseed hf t]
        simp [isLive]
      · intro x hx t
        simp only [isLive, Std.HashMap.getD_erase]
        simp [hx]
    | cons first others =>
      rw [hstart] at hr
      dsimp only at hr
      rw [← hstart] at hr
      cases hf : flood blocks preds a ((seeds.getD a []).length + count + 1) (seeds.getD a []) with
      | none =>
        rw [hf] at hr
        cases hr
      | some row =>
        rw [hf] at hr
        dsimp only at hr
        refine hnext _ ?_ ?_ hr
        · intro t
          rw [← flood_spec h (hseeds a List.mem_cons_self) hf t]
          simp [isLive]
        · intro x hx t
          have hq : (a == x) = false := by simpa using hx
          simp [isLive, Std.HashMap.getD_insert, hq]

/-- Rows for `affected`, from the blocks in the table. -/
def refresh (blocks : Blocks) (preds : Preds) (reach : Row) (sites : VarTable) (blockCount : Nat) (live : Live)
    (affected : List Bap.Var) : Option Live :=
  let affectedSet : Std.HashSet Bap.Var := Std.HashSet.ofList affected
  let seeds := seedTable blocks preds affectedSet reach (Bap.Graph.Fast.dedup (affected.flatMap fun x => sites.getD x []))
  refreshAux blocks preds seeds blockCount live affected

theorem refresh_spec {cfg : Cfg} {blocks : Blocks} {preds : Preds} (h : Tables cfg blocks preds) {reach : Row}
    (hreach : ∀ t, reach.contains t = true ↔ t ∈ cfg.reachable) {sites : VarTable} (hsites : SitesOf cfg sites)
    {count : Nat} {live result : Live} {affected : List Bap.Var} (hold : ∀ x, x ∉ affected → RowOf cfg live x)
    (hr : refresh blocks preds reach sites count live affected = some result) (x : Bap.Var) : RowOf cfg result x := by
  have hseeds : ∀ x ∈ affected, Seeds cfg x ((seedTable blocks preds (Std.HashSet.ofList affected) reach
      (Bap.Graph.Fast.dedup (affected.flatMap fun x => sites.getD x []))).getD x []) := by
    intro x hx
    refine seedTable_seeds h hreach (by simp [Std.HashSet.contains_ofList, hx]) ?_
    intro s blk hb hv
    rw [Bap.Graph.Fast.dedup_eq, List.mem_eraseDups, List.mem_flatMap]
    have hm := block_some hb
    have := hsites blk hm.1 x hv
    rw [hm.2] at this
    exact ⟨x, hx, this⟩
  obtain ⟨h1, h2⟩ := refreshAux_spec h affected hseeds live result hr
  by_cases hx : x ∈ affected
  · exact h2 x hx
  · exact h1 x hx (hold x hx)

/-! ### Live out -/

/-- An edge out of a block, as far as what is live out of it goes. -/
structure Edge where
  target : Tid
  phis : Std.HashSet Bap.Var
  reads : Std.HashSet Bap.Var

def edgesOf (blocks : Blocks) (successors : Std.HashMap Tid (List Tid)) (t : Tid) : List Edge :=
  (Bap.Graph.Fast.dedup (successors.getD t [])).filterMap fun s =>
    (blocks.get? s).map fun blk =>
      { target := s, phis := Std.HashSet.ofList (blk.phis.map Phi.var), reads := Std.HashSet.ofList (phiReads t blk) }

/-- Whether `x` is live out of a block. -/
def liveOver (live : Live) (edges : List Edge) (x : Bap.Var) : Bool :=
  edges.any fun edge => (isLive live x edge.target && !edge.phis.contains x) || edge.reads.contains x

/-- The other row of a block: what is live out of it. -/
def liveOut (cfg : Cfg) (t : Tid) : List Bap.Var := (Assoc.get t cfg.liveness.2).getD []

theorem mem_liveOut {cfg : Cfg} {t : Tid} {blk : Blk} (ht : t ∈ cfg.reachable) (hb : cfg.block t = some blk) (x : Bap.Var) :
    x ∈ liveOut cfg t ↔ ∃ s ∈ cfg.successors t, EdgeNeed cfg (fun s => x ∈ liveIn cfg s) x t s := by
  exact (liveness_equations cfg ht hb x).2.trans (mem_blockOut_edge _ _ _ _)

theorem liveOut_unreachable {cfg : Cfg} {t : Tid} (ht : t ∉ cfg.reachable) : liveOut cfg t = [] := by
  have hl : liveOut cfg t = if t ∈ cfg.reachable then getL t (livenessRaw cfg).2 else [] := getL_rowsOf _ _ _
  rw [hl, ite_eq_right ht]

theorem liveOver_iff {cfg : Cfg} {blocks : Blocks} {live : Live} {successors : Std.HashMap Tid (List Tid)}
    (hblocks : ∀ t, blocks.get? t = cfg.block t) (hsucc : ∀ t, Bap.Graph.Fast.dedup (successors.getD t []) = cfg.successors t)
    {x : Bap.Var} (hrow : RowOf cfg live x) (t : Tid) :
    liveOver live (edgesOf blocks successors t) x = true ↔
      ∃ s ∈ cfg.successors t, EdgeNeed cfg (fun s => x ∈ liveIn cfg s) x t s := by
  simp only [liveOver, edgesOf, hsucc, List.any_eq_true, List.mem_filterMap, Option.map_eq_some_iff, hblocks]
  constructor
  · rintro ⟨e, ⟨s, hs, blk, hb, rfl⟩, he⟩
    refine ⟨s, hs, blk, hb, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.contains_ofList] at he
    rcases he with ⟨h1, h2⟩ | h1
    · refine Or.inl ⟨(hrow s).1 h1, fun phi hp hv => ?_⟩
      have : (blk.phis.map Phi.var).contains x = true := by
        simpa using ⟨phi, hp, hv⟩
      rw [this] at h2
      cases h2
    · exact Or.inr (by simpa using h1)
  · rintro ⟨s, hs, blk, hb, hc⟩
    refine ⟨_, ⟨s, hs, blk, hb, rfl⟩, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Std.HashSet.contains_ofList]
    rcases hc with ⟨h1, h2⟩ | h1
    · refine Or.inl ⟨(hrow s).2 h1, ?_⟩
      simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map, not_exists, not_and]
      exact fun phi hp => h2 phi hp
    · exact Or.inr (by simpa using h1)

/-- A variable that isn't mentioned is live nowhere. -/
theorem not_live_of_unmentioned {cfg : Cfg} {x : Bap.Var} (hx : ∀ blk ∈ cfg.blocks, x ∉ vocabulary blk) (t : Tid) : x ∉ liveIn cfg t := by
  intro h
  exact live_least cfg x (fun _ => False) (fun _ _ blk hb hg => hx blk (block_some hb).1 (vocabulary_of_gen hg))
    (fun _ _ _ _ _ s _ he => by
      obtain ⟨b, hb, hc⟩ := he
      rcases hc with ⟨hr, _⟩ | hr
      · exact hr
      · exact hx b (block_some hb).1 (vocabulary_of_read hr)) h

/-- The tables of a CFG that its passes don't change. -/
def predsOf (cfg : Cfg) (successors : Std.HashMap Tid (List Tid)) : Preds :=
  cfg.reachable.foldl (init := {}) fun table p =>
    (Bap.Graph.Fast.dedup (successors.getD p [])).foldl (fun table s => table.insert s (p :: table.getD s [])) table

theorem mem_predsOf (cfg : Cfg) {successors : Std.HashMap Tid (List Tid)}
    (hsucc : ∀ t, Bap.Graph.Fast.dedup (successors.getD t []) = cfg.successors t) (t p : Tid) :
    p ∈ (predsOf cfg successors).getD t [] ↔ p ∈ cfg.reachable ∧ t ∈ cfg.successors p := by
  have inner : ∀ (l : List Tid) (q : Tid) (table : Preds),
      p ∈ (l.foldl (fun table s => table.insert s (q :: table.getD s [])) table).getD t [] ↔
        p ∈ table.getD t [] ∨ (p = q ∧ t ∈ l) := by
    intro l q
    induction l with
    | nil => simp
    | cons a as ih =>
      intro table
      simp only [List.foldl_cons, ih, Std.HashMap.getD_insert, List.mem_cons]
      by_cases hat : a = t
      · subst hat
        simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, true_or, and_true]
        grind
      · have hq : (a == t) = false := by simpa using hat
        have hne : t ≠ a := fun e => hat e.symm
        simp [hq, hne]
  have outer : ∀ (l : List Tid) (table : Preds), p ∈ (l.foldl (fun table p =>
      (Bap.Graph.Fast.dedup (successors.getD p [])).foldl (fun table s => table.insert s (p :: table.getD s [])) table) table).getD t [] ↔
        p ∈ table.getD t [] ∨ (p ∈ l ∧ t ∈ cfg.successors p) := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      intro table
      rw [List.foldl_cons, ih, inner, hsucc a]
      simp only [List.mem_cons]
      grind
  simpa [predsOf] using outer cfg.reachable {}

end Bap.IR.LiveSets
