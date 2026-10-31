import Bap.Graph.Facts

namespace Bap.Proofs.Graph

open Bap.Graph


variable {α : Type} [DecidableEq α]

local macro "closureStep" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closureStep)
local macro "closure" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.closure)
local macro "initialDominators" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.initialDominators)
local macro "dominatorStep" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.dominatorStep)
local macro "dominatorsAux" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.dominatorsAux)
local macro "frontierWalk" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.frontierWalk)

local macro "unfold_dominatorStep" h:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.dominatorStep)):ident] $(h)?)
local macro "unfold_dominatorsAux" h:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.dominatorsAux)):ident] $(h)?)
local macro "unfold_frontierWalk" h:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [$(Lean.mkIdent (.num (`_private ++ `Bap.Graph.Basic) 0 ++ `Bap.Graph.frontierWalk)):ident] $(h)?)

/-! ### List-as-set helpers -/
variable {g : Graph α} {s : α}

/-! ### Immediate dominators -/

/-- Size of the dominator set recorded for a node. -/
private abbrev domSize (g : Graph α) (s c : α) : Nat :=
  ((Assoc.get c (dominators g s)).getD []).length

private abbrev pick (g : Graph α) (s n : α) (best : Option (α × α)) (candidate : α) : Option (α × α) :=
  match best with
  | none => some (n, candidate)
  | some (_, current) =>
    let candidateSize := (Assoc.get candidate (dominators g s)).getD []
    let currentSize := (Assoc.get current (dominators g s)).getD []
    if candidateSize.length > currentSize.length then some (n, candidate) else best

private theorem foldl_pick_some (n b₀ : α) (l : List α) :
    ∃ b, l.foldl (pick g s n) (some (n, b₀)) = some (n, b) ∧ (b = b₀ ∨ b ∈ l) ∧
      domSize g s b₀ ≤ domSize g s b ∧ ∀ c ∈ l, domSize g s c ≤ domSize g s b := by
  induction l generalizing b₀ with
  | nil => exact ⟨b₀, rfl, Or.inl rfl, Nat.le_refl _, by simp⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    by_cases hgt : domSize g s c > domSize g s b₀
    · have hstep : pick g s n (some (n, b₀)) c = some (n, c) := by
        simp only [pick]
        split
        · rfl
        · exact absurd hgt ‹_›
      rw [hstep]
      obtain ⟨b, hb, hmem, hle, hall⟩ := ih c
      refine ⟨b, hb, ?_, by omega, ?_⟩
      · rcases hmem with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | h
        · exact hle
        · exact hall d h
    · have hstep : pick g s n (some (n, b₀)) c = some (n, b₀) := by
        simp only [pick]
        split
        · exact absurd ‹_› hgt
        · rfl
      rw [hstep]
      obtain ⟨b, hb, hmem, hle, hall⟩ := ih b₀
      refine ⟨b, hb, ?_, hle, ?_⟩
      · rcases hmem with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro d hd
        rcases List.mem_cons.1 hd with rfl | h
        · omega
        · exact hall d h

private theorem foldl_pick_none (n : α) (l : List α) (hne : l ≠ []) :
    ∃ b ∈ l, l.foldl (pick g s n) none = some (n, b) ∧ ∀ c ∈ l, domSize g s c ≤ domSize g s b := by
  match l, hne with
  | c :: cs, _ =>
    obtain ⟨b, hb, hmem, hle, hall⟩ := foldl_pick_some (g := g) (s := s) n c cs
    refine ⟨b, ?_, hb, ?_⟩
    · rcases hmem with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ h
    · intro d hd
      rcases List.mem_cons.1 hd with rfl | h
      · exact hle
      · exact hall d h

private theorem foldl_pick_eq {n i : α} {l : List α} {r : Option (α × α)} (hr : ∀ a b, r = some (a, b) → a = n)
    (h : l.foldl (pick g s n) r = some (i', i)) : i' = n := by
  induction l generalizing r with
  | nil => exact hr _ _ h
  | cons c cs ih =>
    refine ih ?_ h
    intro a b hab
    simp only [pick] at hab
    split at hab
    · simp only [Option.some.injEq, Prod.mk.injEq] at hab
      exact hab.1.symm
    · split at hab
      · simp only [Option.some.injEq, Prod.mk.injEq] at hab
        exact hab.1.symm
      · rename_i best _ current _
        exact hr _ _ hab

private theorem immediateDominators_eq :
    immediateDominators g s = (dominators g s).filterMap fun entry =>
      if entry.1 = s then none
      else (entry.2.filter fun c => c != entry.1).foldl (pick g s entry.1) none := by
  rfl

private theorem domSize_eq {c : α} {ds : List α} (h : Assoc.get c (dominators g s) = some ds) :
    domSize g s c = ds.length := by
  simp [domSize, h]

/-- If `b` strictly dominates `a` then `b`'s dominator set is strictly smaller. -/
private theorem domSize_lt {a b : α} (ha : a ∈ reachable g s) (hab : Dom g s a b) (hne : a ≠ b) :
    domSize g s b < domSize g s a := by
  obtain ⟨p, hp⟩ := (mem_reachable_iff_walk a).1 ha
  have hb : b ∈ reachable g s := hp.subset_reachable (hab p hp)
  obtain ⟨da, hda⟩ := get_exists (T := dominators g s) (k := a) (by rw [dominators_keys]; exact ha)
  obtain ⟨db, hdb⟩ := get_exists (T := dominators g s) (k := b) (by rw [dominators_keys]; exact hb)
  rw [domSize_eq hda, domSize_eq hdb]
  have hamem : a ∈ da := (mem_dominators_iff (get_mem hda)).2 (Dom.refl _)
  have hnd : db.Nodup := dominators_nodup _ (get_mem hdb)
  have hsub : db ⊆ da.erase a := by
    intro x hx
    have hbx := (mem_dominators_iff (get_mem hdb)).1 hx
    have hxa : x ≠ a := by
      rintro rfl
      exact hne (Dom.antisymm ha hab hbx)
    exact (List.mem_erase_of_ne hxa).2 ((mem_dominators_iff (get_mem hda)).2 (hab.trans hbx))
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem hamem] at this
  have := List.length_pos_of_mem hamem
  omega

/-- Immediate dominators are the unique closest strict dominators. -/
theorem immediateDominators_spec {n i : α} (h : (n, i) ∈ immediateDominators g s) :
    n ∈ reachable g s ∧ n ≠ s ∧ i ≠ n ∧ Dom g s n i ∧ ∀ c, c ≠ n → Dom g s n c → Dom g s i c := by
  rw [immediateDominators_eq] at h
  obtain ⟨⟨m, ds⟩, hmem, hval⟩ := List.mem_filterMap.1 h
  simp only at hval
  have hm : m ∈ reachable g s := by
    rw [← dominators_keys]
    exact List.mem_map.2 ⟨_, hmem, rfl⟩
  by_cases hms : m = s
  · simp [hms] at hval
  simp only [hms, ite_false] at hval
  have hnm : n = m := foldl_pick_eq (g := g) (s := s) (n := m) (r := none) (by simp) hval
  subst hnm
  have hne : ds.filter (fun c => c != n) ≠ [] := by
    apply List.ne_nil_of_mem (a := s)
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    exact ⟨(mem_dominators_iff hmem).2 (Dom.start _), Ne.symm hms⟩
  obtain ⟨b, hb, hfold, hall⟩ := foldl_pick_none (g := g) (s := s) n _ hne
  rw [hfold] at hval
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hval
  subst hval
  simp only [List.mem_filter, bne_iff_ne, ne_eq] at hb
  have hdom : Dom g s n b := (mem_dominators_iff hmem).1 hb.1
  refine ⟨hm, hms, hb.2, hdom, ?_⟩
  intro c hcn hc
  rcases Dom.chain hm hc hdom with hcb | hbc
  · by_cases hcbe : c = b
    · subst hcbe
      exact Dom.refl _
    · exfalso
      obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hm
      have hcr : c ∈ reachable g s := hp.subset_reachable (hc p hp)
      have hlt := domSize_lt hcr hcb hcbe
      have hle := hall c (by simp [(mem_dominators_iff hmem).2 hc, hcn])
      omega
  · exact hbc

theorem immediateDominators_unique {n i j : α} (hi : (n, i) ∈ immediateDominators g s)
    (hj : (n, j) ∈ immediateDominators g s) : i = j := by
  obtain ⟨hn, _, hin, hdi, hmi⟩ := immediateDominators_spec hi
  obtain ⟨_, _, hjn, hdj, hmj⟩ := immediateDominators_spec hj
  obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hn
  exact Dom.antisymm (hp.subset_reachable (hdi p hp)) (hmi j hjn hdj) (hmj i hin hdi)

/-- Every reachable node other than the start has an immediate dominator. -/
theorem immediateDominators_exists {n : α} (hn : n ∈ reachable g s) (hne : n ≠ s) :
    ∃ i, (n, i) ∈ immediateDominators g s := by
  obtain ⟨ds, hds⟩ := get_exists (T := dominators g s) (k := n) (by rw [dominators_keys]; exact hn)
  have hmem := get_mem hds
  have hf : ds.filter (fun c => c != n) ≠ [] := by
    apply List.ne_nil_of_mem (a := s)
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    exact ⟨(mem_dominators_iff hmem).2 (Dom.start _), Ne.symm hne⟩
  obtain ⟨b, _, hfold, _⟩ := foldl_pick_none (g := g) (s := s) n _ hf
  refine ⟨b, ?_⟩
  rw [immediateDominators_eq]
  refine List.mem_filterMap.2 ⟨(n, ds), hmem, ?_⟩
  simp only [hne, ite_false]
  exact hfold

theorem immediateDominators_keys_get {n : α} (hn : n ∈ reachable g s) (hne : n ≠ s) :
    ∃ i, Assoc.get n (immediateDominators g s) = some i := by
  obtain ⟨i, hi⟩ := immediateDominators_exists hn hne
  exact get_exists (List.mem_map.2 ⟨_, hi, rfl⟩)

/-! ### Dominance frontier -/

private abbrev frontierPairs (g : Graph α) (s : α) : List (α × α) :=
  (reachable g s).foldl (init := []) fun result tid =>
    (predecessors g tid).foldl (fun result pred =>
      frontierWalk g (immediateDominators g s) (Assoc.get tid (immediateDominators g s)) tid
        (g.nodes.length + 1) pred result) result

private theorem mem_frontier {x y : α} {f : List α} (h : (x, f) ∈ dominanceFrontier g s) :
    y ∈ f ↔ (x, y) ∈ frontierPairs g s := by
  have h' : (x, f) ∈ g.nodes.map fun node =>
      (node, ((frontierPairs g s).filter fun pair => pair.1 = node).map Prod.snd |>.eraseDups) := h
  obtain ⟨m, _, heq⟩ := List.mem_map.1 h'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  simp [List.mem_eraseDups]

/-- The frontier table has exactly one row per graph node. -/
theorem dominanceFrontier_keys : (dominanceFrontier g s).map Prod.fst = g.nodes := by
  show (g.nodes.map _).map Prod.fst = _
  simp [Function.comp_def]

private theorem frontierWalk_succ (idom : List (α × α)) (stop : Option α) (tid : α) (fuel : Nat) (r : α)
    (res : List (α × α)) :
    frontierWalk g idom stop tid (fuel + 1) r res =
      if some r = stop then res
      else match Assoc.get r idom with
        | some next => frontierWalk g idom stop tid fuel next ((r, tid) :: res)
        | none => (r, tid) :: res := by
  unfold_frontierWalk
  rfl

private theorem frontierWalk_mono (idom : List (α × α)) (stop : Option α) (tid : α) (fuel : Nat) (r : α)
    (res : List (α × α)) : res ⊆ frontierWalk g idom stop tid fuel r res := by
  induction fuel generalizing r res with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    rw [frontierWalk_succ]
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.trans (List.subset_cons_self _ _) (ih _ _)
      · exact List.subset_cons_self _ _

/-- Vertices collected by the walk dominate the first runner and lie strictly below any stop. -/
private theorem frontierWalk_sound {pred tid : α} {stop : Option α} {fuel : Nat} {r : α} {res : List (α × α)}
    (hr : r ∈ reachable g s) (hpr : Dom g s pred r) (hrs : ∀ st, stop = some st → Dom g s r st) {x y : α}
    (h : (x, y) ∈ frontierWalk g (immediateDominators g s) stop tid fuel r res) :
    (x, y) ∈ res ∨ (y = tid ∧ Dom g s pred x ∧ x ∈ reachable g s ∧
      ∀ st, stop = some st → Dom g s x st ∧ x ≠ st) := by
  induction fuel generalizing r res with
  | zero => exact Or.inl h
  | succ fuel ih =>
    rw [frontierWalk_succ] at h
    split at h
    · exact Or.inl h
    · rename_i hne
      have hhead : (x, y) ∈ (r, tid) :: res → (x, y) ∈ res ∨
          (y = tid ∧ Dom g s pred x ∧ x ∈ reachable g s ∧
            ∀ st, stop = some st → Dom g s x st ∧ x ≠ st) := by
        intro hm
        rcases List.mem_cons.1 hm with heq | hm
        · simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine Or.inr ⟨rfl, hpr, hr, fun st hst => ⟨hrs st hst, ?_⟩⟩
          rintro rfl
          exact hne hst.symm
        · exact Or.inl hm
      split at h
      · rename_i next hnext
        obtain ⟨_, _, hnr, hdn, hmin⟩ := immediateDominators_spec (get_mem hnext)
        obtain ⟨p, hp⟩ := (mem_reachable_iff_walk r).1 hr
        have hnreach := hp.subset_reachable (hdn p hp)
        have hstopn : ∀ st, stop = some st → Dom g s next st := by
          intro st hst
          refine hmin st ?_ (hrs st hst)
          rintro rfl
          exact hne hst.symm
        rcases ih hnreach (hpr.trans hdn) hstopn h with hm | hgood
        · exact hhead hm
        · exact Or.inr hgood
      · exact hhead h

private theorem frontierWalk_unreachable {tid : α} {stop : Option α} {fuel : Nat} {r : α} {res : List (α × α)}
    (hr : r ∉ reachable g s) {x y : α}
    (h : (x, y) ∈ frontierWalk g (immediateDominators g s) stop tid fuel r res) :
    (x, y) ∈ res ∨ x = r := by
  cases fuel with
  | zero => exact Or.inl h
  | succ fuel =>
    rw [frontierWalk_succ] at h
    split at h
    · exact Or.inl h
    · split at h
      · rename_i next hnext
        exact absurd (immediateDominators_spec (get_mem hnext)).1 hr
      · rcases List.mem_cons.1 h with heq | hm
        · simp only [Prod.mk.injEq] at heq
          exact Or.inr heq.1
        · exact Or.inl hm

private theorem frontierPairs_sound {x y : α} (hx : x ∈ reachable g s) (h : (x, y) ∈ frontierPairs g s) :
    ∃ pred, (pred, y) ∈ g.edges ∧ pred ∈ reachable g s ∧ y ∈ g.nodes ∧ Dom g s pred x ∧
      (x ≠ y → ¬ Dom g s y x) := by
  let Q : α × α → Prop := fun e => e.1 ∈ reachable g s → ∃ pred, (pred, e.2) ∈ g.edges ∧
    pred ∈ reachable g s ∧ e.2 ∈ g.nodes ∧ Dom g s pred e.1 ∧ (e.1 ≠ e.2 → ¬ Dom g s e.2 e.1)
  have outer : ∀ (l : List α) (init : List (α × α)), (∀ e ∈ init, Q e) → (∀ t ∈ l, t ∈ reachable g s) →
      ∀ e ∈ l.foldl (fun result tid =>
        (predecessors g tid).foldl (fun result pred =>
          frontierWalk g (immediateDominators g s) (Assoc.get tid (immediateDominators g s)) tid
            (g.nodes.length + 1) pred result) result)
        init, Q e := by
    intro l
    induction l with
    | nil => intro init hi _; simpa using hi
    | cons t ts ih =>
      intro init hi hl
      apply ih
      · have htr := hl t (by simp)
        obtain ⟨wt, hwt⟩ := (mem_reachable_iff_walk t).1 htr
        have inner : ∀ (ps : List α) (acc : List (α × α)), (∀ e ∈ acc, Q e) →
            (∀ p ∈ ps, (p, t) ∈ g.edges) →
            ∀ e ∈ ps.foldl (fun result pred =>
              frontierWalk g (immediateDominators g s) (Assoc.get t (immediateDominators g s)) t
                (g.nodes.length + 1) pred result) acc,
              Q e := by
          intro ps
          induction ps with
          | nil => intro acc ha _; simpa using ha
          | cons q qs ihq =>
            intro acc ha hq
            apply ihq _ _ (fun p hp => hq p (List.mem_cons_of_mem _ hp))
            rintro ⟨a, b⟩ he
            by_cases hqr : q ∈ reachable g s
            · have hstopq : ∀ st, Assoc.get t (immediateDominators g s) = some st → Dom g s q st := by
                intro st hst
                obtain ⟨_, _, hsn, hds, _⟩ := immediateDominators_spec (get_mem hst)
                intro w hw
                rcases List.mem_cons.1 (hds _ (Walk.cons hw (hq q (by simp)) hwt.mem_nodes)) with h' | h'
                · exact absurd h' hsn
                · exact h'
              rcases frontierWalk_sound hqr (Dom.refl q) hstopq he with hm | ⟨rfl, hqa, ha', hst⟩
              · exact ha _ hm
              · intro _
                refine ⟨q, hq q (by simp), hqr, hwt.mem_nodes, hqa, ?_⟩
                intro hab hdom
                -- `a` strictly dominates `b`, so `b` is not the start and has an immediate dominator
                have hbs : b ≠ s := by
                  rintro rfl
                  exact hab (List.mem_singleton.1 (hdom _ (.nil hwt.mem_nodes)))
                obtain ⟨st, hstget⟩ := immediateDominators_keys_get htr hbs
                obtain ⟨has, hne⟩ := hst st hstget
                obtain ⟨_, _, _, _, hmin⟩ := immediateDominators_spec (get_mem hstget)
                exact hne (Dom.antisymm ha' has (hmin a hab hdom))
            · rcases frontierWalk_unreachable hqr he with hm | rfl
              · exact ha _ hm
              · intro habs
                exact absurd habs hqr
        exact inner _ _ hi (fun p hp => (mem_predecessors g p t).1 hp)
      · exact fun z hz => hl z (List.mem_cons_of_mem _ hz)
  exact outer _ [] (by simp) (fun _ h => h) _ h hx

private theorem foldl_mem_of {β γ : Type} (f : List γ → β → List γ) (e : γ) (a : β) (l : List β)
    (init : List γ) (hmono : ∀ r b, e ∈ r → e ∈ f r b) (hadd : ∀ r, e ∈ f r a) (ha : a ∈ l) :
    e ∈ l.foldl f init := by
  have hkeep : ∀ (l : List β) (r : List γ), e ∈ r → e ∈ l.foldl f r := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons b bs ih => exact fun r h => ih _ (hmono r b h)
  induction l generalizing init with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.1 ha with rfl | h
    · exact hkeep bs _ (hadd init)
    · exact ih _ h

private theorem domSize_le_nodes {r : α} : domSize g s r ≤ g.nodes.length := by
  by_cases hr : r ∈ reachable g s
  · obtain ⟨ds, h⟩ := get_exists (T := dominators g s) (k := r) (by rw [dominators_keys]; exact hr)
    rw [domSize_eq h]
    apply (dominators_nodup _ (get_mem h)).length_le_of_subset
    intro x hx
    obtain ⟨p, hp⟩ := (mem_reachable_iff_walk r).1 hr
    exact reachableFrom_subset_nodes _ _
      (hp.subset_reachable (((mem_dominators_iff (get_mem h)).1 hx) p hp))
  · have : Assoc.get r (dominators g s) = none := by
      apply List.lookup_eq_none_iff.2
      intro e he
      simp only [bne_iff_ne, ne_eq]
      rintro rfl
      exact hr (by rw [← dominators_keys]; exact List.mem_map.2 ⟨_, he, rfl⟩)
    simp [domSize, this]

private theorem frontierWalk_complete {stop : Option α} {tid x : α} {fuel : Nat} {r : α} {res : List (α × α)}
    (hr : r ∈ reachable g s) (hrx : Dom g s r x) (htr : tid ∈ reachable g s)
    (hstop : ∀ st, stop = some st → tid ≠ st ∧ Dom g s tid st) (hnot : x ≠ tid → ¬ Dom g s tid x)
    (hfuel : domSize g s r < fuel) :
    (x, tid) ∈ frontierWalk g (immediateDominators g s) stop tid fuel r res := by
  induction fuel generalizing r res with
  | zero => omega
  | succ fuel ih =>
    rw [frontierWalk_succ]
    by_cases hrs : some r = stop
    · exfalso
      obtain ⟨hts, hd⟩ := hstop r hrs.symm
      have hxt : x = tid := by
        refine Classical.byContradiction fun hne => hnot hne (hd.trans hrx)
      subst hxt
      exact hts (Dom.antisymm htr hd hrx)
    · simp only [hrs, ite_false]
      by_cases hrxe : r = x
      · subst hrxe
        split
        · exact frontierWalk_mono _ _ _ _ _ _ (by simp)
        · simp
      · have hrns : r ≠ s := by
          rintro rfl
          obtain ⟨p, hp⟩ := (mem_reachable_iff_walk r).1 hr
          exact hrxe (List.mem_singleton.1 (hrx _ (.nil hp.mem_nodes))).symm
        obtain ⟨next, hnext⟩ := immediateDominators_keys_get hr hrns
        rw [hnext]
        obtain ⟨_, _, hnr, hdn, hmin⟩ := immediateDominators_spec (get_mem hnext)
        obtain ⟨p, hp⟩ := (mem_reachable_iff_walk r).1 hr
        have hlt := domSize_lt hr hdn (Ne.symm hnr)
        exact ih (hp.subset_reachable (hdn p hp)) (hmin x (Ne.symm hrxe) hrx) (by omega)

/-- Correctness of the dominance frontier, including back edges to the start. `y` is in the frontier
of a reachable `x` exactly when `x` dominates a reachable predecessor of `y` but not strictly `y`. -/
theorem mem_dominanceFrontier_iff {x y : α} {f : List α} (hf : (x, f) ∈ dominanceFrontier g s)
    (hx : x ∈ reachable g s) :
    y ∈ f ↔ ∃ pred, (pred, y) ∈ g.edges ∧ pred ∈ reachable g s ∧ y ∈ g.nodes ∧ Dom g s pred x ∧
      (x ≠ y → ¬ Dom g s y x) := by
  rw [mem_frontier hf]
  constructor
  · exact fun h => frontierPairs_sound hx h
  · rintro ⟨pred, he, hpr, hyn, hdom, hnot⟩
    have hyr : y ∈ reachable g s := reachableFrom_closed g _ hpr he hyn
    refine foldl_mem_of _ (x, y) y _ [] ?_ ?_ hyr
    · intro r b hm
      have hkeep : ∀ (ps : List α) (acc : List (α × α)), (x, y) ∈ acc → (x, y) ∈ ps.foldl
          (fun result pred => frontierWalk g (immediateDominators g s)
            (Assoc.get b (immediateDominators g s)) b (g.nodes.length + 1) pred result) acc := by
        intro ps
        induction ps with
        | nil => exact fun _ h => h
        | cons q qs ih => exact fun acc h => ih _ (frontierWalk_mono _ _ _ _ _ _ h)
      exact hkeep _ _ hm
    · intro r
      refine foldl_mem_of _ (x, y) pred _ r ?_ ?_ ((mem_predecessors g pred y).2 he)
      · exact fun acc q hm => frontierWalk_mono _ _ _ _ _ _ hm
      · intro acc
        refine frontierWalk_complete hpr hdom hyr ?_ hnot (Nat.lt_succ_of_le domSize_le_nodes)
        intro st hst
        obtain ⟨_, _, hsn, hds, _⟩ := immediateDominators_spec (get_mem hst)
        exact ⟨Ne.symm hsn, hds⟩

/-- A back edge to the start puts the start in the frontier of every dominator of the source. -/
theorem start_mem_dominanceFrontier {x pred : α} {f : List α} (hf : (x, f) ∈ dominanceFrontier g s)
    (hx : x ∈ reachable g s) (hpred : pred ∈ reachable g s) (he : (pred, s) ∈ g.edges)
    (hdom : Dom g s pred x) : s ∈ f := by
  have hsn : s ∈ g.nodes := by
    obtain ⟨p, hp⟩ := (mem_reachable_iff_walk pred).1 hpred
    exact reachableFrom_subset_nodes _ _ (hp.subset_reachable hp.start_mem)
  refine (mem_dominanceFrontier_iff hf hx).2 ⟨pred, he, hpred, hsn, hdom, ?_⟩
  intro hne hd
  exact hne (List.mem_singleton.1 (hd _ (.nil hsn)))

/-- Chains of immediate dominators from a reachable node to the start. -/
inductive IdomChain (g : Graph α) (s : α) : Nat → α → Prop where
  | start : IdomChain g s 0 s
  | step {k n p} : (n, p) ∈ immediateDominators g s → IdomChain g s k p → IdomChain g s (k + 1) n

/-- The dominator tree spans the reachable nodes and is no deeper than the node count. -/
theorem idomChain_exists {n : α} (hn : n ∈ reachable g s) :
    ∃ k, k < g.nodes.length ∧ IdomChain g s k n := by
  have key : ∀ m n, domSize g s n = m → n ∈ reachable g s → ∃ k, k < m ∧ IdomChain g s k n := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro n hm hn
      obtain ⟨ds, hds⟩ := get_exists (T := dominators g s) (k := n) (by rw [dominators_keys]; exact hn)
      have hnm : n ∈ ds := (mem_dominators_iff (get_mem hds)).2 (Dom.refl _)
      have hpos : 0 < m := by
        rw [← hm, domSize_eq hds]
        exact List.length_pos_of_mem hnm
      by_cases hns : n = s
      · subst hns
        exact ⟨0, hpos, .start⟩
      · obtain ⟨p, hp⟩ := immediateDominators_exists hn hns
        obtain ⟨_, _, hpn, hd, _⟩ := immediateDominators_spec hp
        have hlt := domSize_lt hn hd (Ne.symm hpn)
        obtain ⟨w, hw⟩ := (mem_reachable_iff_walk n).1 hn
        obtain ⟨k, hk, hc⟩ := ih (domSize g s p) (by omega) p rfl (hw.subset_reachable (hd w hw))
        exact ⟨k + 1, by omega, .step hp hc⟩
  obtain ⟨k, hk, hc⟩ := key _ n rfl hn
  exact ⟨k, Nat.lt_of_lt_of_le hk domSize_le_nodes, hc⟩

/-! ### Shape of the computed tables -/

private theorem closure_nodup (hn : g.nodes.Nodup) (fuel : Nat) (seen : List α) (hs : seen.Nodup) :
    (closure g fuel seen).Nodup := by
  induction fuel generalizing seen with
  | zero => exact hs
  | succ fuel ih =>
    rw [closure_succ]
    split
    · exact hs
    · apply ih
      rw [closureStep_eq]
      refine List.nodup_append.2 ⟨hs, hn.filter _, ?_⟩
      rintro a ha b hb rfl
      exact (of_decide_eq_true (List.mem_filter.1 hb).2).1 ha

/-- With distinct nodes each reachable node is listed once. -/
theorem reachable_nodup (hn : g.nodes.Nodup) : (reachable g s).Nodup :=
  closure_nodup hn _ _ (nodup_eraseDups _)

/-- Each node has at most one row in the immediate dominator table. -/
theorem immediateDominators_keys_nodup (hn : g.nodes.Nodup) : ((immediateDominators g s).map Prod.fst).Nodup := by
  have key : ∀ l : List (α × List α), (l.map Prod.fst).Nodup → ((l.filterMap fun entry =>
      if entry.1 = s then none else
        (entry.2.filter fun candidate => candidate != entry.1).foldl (pick g s entry.1) none).map Prod.fst).Nodup := by
    have hsub : ∀ l : List (α × List α), ((l.filterMap fun entry =>
        if entry.1 = s then none else
          (entry.2.filter fun candidate => candidate != entry.1).foldl (pick g s entry.1) none).map Prod.fst).Sublist
        (l.map Prod.fst) := by
      intro l
      induction l with
      | nil => exact List.Sublist.refl _
      | cons e es ih =>
        simp only [List.filterMap_cons, List.map_cons]
        split
        · exact ih.cons _
        · rename_i x hx
          obtain ⟨a, b⟩ := x
          have hk : a = e.1 := by
            split at hx
            · cases hx
            · exact foldl_pick_eq (g := g) (s := s) (n := e.1) (r := none) (by simp) hx
          simp only [hk]
          exact ih.cons_cons _
    exact fun l hl => (hsub l).nodup hl
  rw [immediateDominators_eq]
  apply key
  rw [dominators_keys]
  exact reachable_nodup hn

private theorem frontierWalk_target (idom : List (α × α)) (stop : Option α) (tid : α) (fuel : Nat) (r : α)
    (res : List (α × α)) {x y : α} (h : (x, y) ∈ frontierWalk g idom stop tid fuel r res) :
    (x, y) ∈ res ∨ y = tid := by
  induction fuel generalizing r res with
  | zero => exact Or.inl h
  | succ fuel ih =>
    rw [frontierWalk_succ] at h
    split at h
    · exact Or.inl h
    · split at h
      · rcases ih _ _ h with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr (Prod.mk.inj h).2
          · exact Or.inl h
        · exact Or.inr h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr (Prod.mk.inj h).2
        · exact Or.inl h

/-- Everything in a dominance frontier is a reachable node that has a predecessor. -/
theorem dominanceFrontier_target {x y : α} {f : List α} (hf : (x, f) ∈ dominanceFrontier g s)
    (hy : y ∈ f) : y ∈ reachable g s ∧ ∃ pred, (pred, y) ∈ g.edges := by
  have hp : (x, y) ∈ frontierPairs g s := (mem_frontier hf).1 hy
  have hinner : ∀ (b : α) (qs : List α) (acc : List (α × α)), (x, y) ∈ qs.foldl (fun result pred =>
      frontierWalk g (immediateDominators g s) (Assoc.get b (immediateDominators g s)) b
        (g.nodes.length + 1) pred result) acc → (x, y) ∈ acc ∨ (y = b ∧ ∃ q, q ∈ qs) := by
    intro b qs
    induction qs with
    | nil => exact fun _ h => Or.inl h
    | cons q qs ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with h | ⟨h, r, hr⟩
      · rcases frontierWalk_target _ _ _ _ _ _ h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, q, by simp⟩
      · exact Or.inr ⟨h, r, List.mem_cons_of_mem _ hr⟩
  have houter : ∀ (l : List α) (acc : List (α × α)), (∀ b ∈ l, b ∈ reachable g s) →
      (x, y) ∈ l.foldl (fun result tid => (predecessors g tid).foldl (fun result pred =>
        frontierWalk g (immediateDominators g s) (Assoc.get tid (immediateDominators g s)) tid
          (g.nodes.length + 1) pred result) result) acc →
      (x, y) ∈ acc ∨ (y ∈ reachable g s ∧ ∃ pred, (pred, y) ∈ g.edges) := by
    intro l
    induction l with
    | nil => exact fun _ _ h => Or.inl h
    | cons b bs ih =>
      intro acc hl h
      simp only [List.foldl_cons] at h
      rcases ih _ (fun c hc => hl c (List.mem_cons_of_mem _ hc)) h with h | h
      · rcases hinner _ _ _ h with h | ⟨rfl, q, hq⟩
        · exact Or.inl h
        · exact Or.inr ⟨hl y (by simp), q, (mem_predecessors g q y).1 hq⟩
      · exact Or.inr h
  rcases houter _ [] (fun _ h => h) hp with h | h
  · simp at h
  · exact h

end Bap.Proofs.Graph
