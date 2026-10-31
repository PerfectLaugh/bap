import Bap.Graph.Basic

/-! What walks and dominators are, and that the graph algorithms of `Bap.Graph.Basic` find them. `Bap.Graph.Fast` is proved against these. -/

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

@[simp] theorem mem_predecessors (g : Graph α) (source target : α) :
    source ∈ predecessors g target ↔ (source, target) ∈ g.edges := by
  simp [predecessors]

theorem successor_iff_predecessor (g : Graph α) (source target : α) :
    target ∈ successors g source ↔ source ∈ predecessors g target := by
  simp

@[simp] theorem mem_intersect (left right : List α) (x : α) :
    x ∈ intersect left right ↔ x ∈ left ∧ x ∈ right := by
  simp [intersect]

theorem subset_iff (left right : List α) : subset left right = true ↔ left ⊆ right := by
  simp [subset, List.subset_def]

theorem subset_trans {a b c : List α} (hab : subset a b = true) (hbc : subset b c = true) :
    subset a c = true := by
  rw [subset_iff] at *
  exact List.Subset.trans hab hbc

theorem setEq_iff (left right : List α) :
    setEq left right = true ↔ ∀ x, x ∈ left ↔ x ∈ right := by
  simp only [setEq, Bool.and_eq_true, subset_iff, List.subset_def]
  exact ⟨fun ⟨l, r⟩ x => ⟨@l x, @r x⟩, fun h => ⟨fun {x} => (h x).1, fun {x} => (h x).2⟩⟩

theorem setEq_refl (values : List α) : setEq values values = true := by
  simp [setEq_iff]

theorem setEq_symm {a b : List α} (h : setEq a b = true) : setEq b a = true := by
  rw [setEq_iff] at *
  exact fun x => (h x).symm

theorem setEq_trans {a b c : List α} (hab : setEq a b = true) (hbc : setEq b c = true) :
    setEq a c = true := by
  rw [setEq_iff] at *
  exact fun x => (hab x).trans (hbc x)

theorem intersect_comm_setEq (a b : List α) : setEq (intersect a b) (intersect b a) = true := by
  rw [setEq_iff]
  simp [and_comm]

theorem intersect_subset_left (a b : List α) : subset (intersect a b) a = true := by
  rw [subset_iff, List.subset_def]
  simp +contextual

theorem nodup_eraseDups (l : List α) : l.eraseDups.Nodup := by
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    match l with
    | [] => simp
    | a :: as =>
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, ih _ ?_ _ rfl⟩
      · simp [List.mem_eraseDups]
      · have := List.length_filter_le (fun b => !b == a) as
        simp only [List.length_cons] at h
        omega

theorem successors_nodup (g : Graph α) (node : α) : (successors g node).Nodup :=
  nodup_eraseDups _

theorem predecessors_nodup (g : Graph α) (node : α) : (predecessors g node).Nodup :=
  nodup_eraseDups _

/-! ### Reachability -/

/-- Inductive reachability from a list of seeds, staying inside `g.nodes`. -/
inductive Reaches (g : Graph α) (seeds : List α) : α → Prop where
  | seed {a} : a ∈ seeds → a ∈ g.nodes → Reaches g seeds a
  | step {a b} : Reaches g seeds a → (a, b) ∈ g.edges → b ∈ g.nodes → Reaches g seeds b

omit [DecidableEq α] in
theorem Reaches.mem_nodes {g : Graph α} {seeds : List α} {x : α} (h : Reaches g seeds x) :
    x ∈ g.nodes := by
  cases h <;> assumption

theorem closureStep_eq (g : Graph α) (seen : List α) :
    closureStep g seen = seen ++ g.nodes.filter fun node =>
      node ∉ seen ∧ (predecessors g node).any fun pred => pred ∈ seen := rfl

theorem closure_succ (g : Graph α) (fuel : Nat) (seen : List α) :
    closure g (fuel + 1) seen =
      if closureStep g seen = seen then seen else closure g fuel (closureStep g seen) := rfl

theorem mem_closureStep (g : Graph α) (seen : List α) (x : α) :
    x ∈ closureStep g seen ↔ x ∈ seen ∨ (x ∈ g.nodes ∧ ∃ p ∈ seen, (p, x) ∈ g.edges) := by
  simp only [closureStep_eq, List.mem_append, List.mem_filter, decide_eq_true_eq, List.any_eq_true,
    mem_predecessors]
  by_cases hx : x ∈ seen <;> simp [hx, and_comm]

private theorem countP_lt {β : Type} (P Q : β → Bool) (xs : List β) (hle : ∀ x ∈ xs, P x = true → Q x = true)
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

theorem subset_closure (g : Graph α) (fuel : Nat) (seen : List α) : seen ⊆ closure g fuel seen := by
  induction fuel generalizing seen with
  | zero => exact List.Subset.refl _
  | succ fuel ih =>
    rw [closure_succ]
    split
    · exact List.Subset.refl _
    · refine List.Subset.trans ?_ (ih _)
      intro x hx
      exact (mem_closureStep g seen x).2 (Or.inl hx)

theorem closure_sound (g : Graph α) (seeds : List α) (fuel : Nat) (seen : List α)
    (hseen : ∀ x ∈ seen, Reaches g seeds x) : ∀ x ∈ closure g fuel seen, Reaches g seeds x := by
  induction fuel generalizing seen with
  | zero => exact hseen
  | succ fuel ih =>
    rw [closure_succ]
    split
    · exact hseen
    · apply ih
      intro x hx
      rcases (mem_closureStep g seen x).1 hx with h | ⟨hn, p, hp, he⟩
      · exact hseen x h
      · exact .step (hseen p hp) he hn

/-- With enough fuel the closure is closed under every edge whose target is a node. -/
theorem closure_closed (g : Graph α) (fuel : Nat) (seen : List α)
    (hfuel : g.nodes.countP (fun x => decide (x ∉ seen)) < fuel) {a b : α}
    (ha : a ∈ closure g fuel seen) (he : (a, b) ∈ g.edges) (hb : b ∈ g.nodes) :
    b ∈ closure g fuel seen := by
  induction fuel generalizing seen with
  | zero => omega
  | succ fuel ih =>
    rw [closure_succ] at ha ⊢
    split at ha
    · rename_i hfix
      simp only [hfix, ↓reduceIte]
      rw [← hfix]
      exact (mem_closureStep g seen b).2 (Or.inr ⟨hb, a, ha, he⟩)
    · rename_i hne
      simp only [hne, ↓reduceIte]
      refine ih _ ?_ ha
      have hex : ∃ x ∈ g.nodes, x ∉ seen ∧ x ∈ closureStep g seen := by
        refine Classical.byContradiction fun hno => hne ?_
        have : (g.nodes.filter fun node => node ∉ seen ∧
            (predecessors g node).any fun pred => pred ∈ seen) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx hc
          simp only [decide_eq_true_eq] at hc
          exact hno ⟨x, hx, hc.1, by
            have ⟨p, hp, hq⟩ := List.any_eq_true.1 hc.2
            exact (mem_closureStep g seen x).2 (Or.inr ⟨hx, p, by simpa using hq, by simpa using hp⟩)⟩
        rw [closureStep_eq, this, List.append_nil]
      obtain ⟨x, hx, hxs, hxn⟩ := hex
      have hlt := countP_lt (fun x => decide (x ∉ closureStep g seen))
        (fun x => decide (x ∉ seen)) g.nodes
        (by
          intro y _ hy
          simp only [decide_eq_true_eq] at *
          exact fun h => hy ((mem_closureStep g seen y).2 (Or.inl h)))
        ⟨x, hx, by simpa using hxs, by simpa using hxn⟩
      omega

private theorem countP_le_length (g : Graph α) (seen : List α) :
    g.nodes.countP (fun x => decide (x ∉ seen)) < g.nodes.length + 1 :=
  Nat.lt_succ_of_le (List.countP_le_length)

/-- `reachableFrom` computes exactly the inductive reachability relation. -/
theorem mem_reachableFrom_iff (g : Graph α) (seeds : List α) (x : α) :
    x ∈ reachableFrom g seeds ↔ Reaches g seeds x := by
  unfold reachableFrom
  constructor
  · apply closure_sound
    intro y hy
    have hy' : y ∈ seeds ∧ y ∈ g.nodes := by simpa [List.mem_eraseDups] using hy
    exact .seed hy'.1 hy'.2
  · intro h
    induction h with
    | seed hs hn =>
      apply subset_closure
      simp [List.mem_eraseDups, hs, hn]
    | step _ he hn ih => exact closure_closed g _ _ (countP_le_length g _) ih he hn

theorem mem_reachableFrom_of_seed {g : Graph α} {seeds : List α} {x : α}
    (hs : x ∈ seeds) (hn : x ∈ g.nodes) : x ∈ reachableFrom g seeds :=
  (mem_reachableFrom_iff ..).2 (.seed hs hn)

theorem reachableFrom_subset_nodes (g : Graph α) (seeds : List α) :
    reachableFrom g seeds ⊆ g.nodes := fun _ h => ((mem_reachableFrom_iff ..).1 h).mem_nodes

theorem reachableFrom_closed (g : Graph α) (seeds : List α) {a b : α}
    (ha : a ∈ reachableFrom g seeds) (he : (a, b) ∈ g.edges) (hb : b ∈ g.nodes) :
    b ∈ reachableFrom g seeds :=
  (mem_reachableFrom_iff ..).2 (.step ((mem_reachableFrom_iff ..).1 ha) he hb)

/-- Reachability is the least edge-closed set containing the seeds. -/
theorem reachableFrom_least (g : Graph α) (seeds : List α) (s : α → Prop)
    (hseed : ∀ x ∈ seeds, x ∈ g.nodes → s x)
    (hstep : ∀ a b, s a → (a, b) ∈ g.edges → b ∈ g.nodes → s b) :
    ∀ x ∈ reachableFrom g seeds, s x := by
  intro x hx
  have h := (mem_reachableFrom_iff ..).1 hx
  induction h with
  | seed hs hn => exact hseed _ hs hn
  | step _ he hn ih =>
    exact hstep _ _ (ih ((mem_reachableFrom_iff ..).2 ‹_›)) he hn

theorem reachableFrom_mono_seeds (g : Graph α) {s₁ s₂ : List α} (h : s₁ ⊆ s₂) :
    reachableFrom g s₁ ⊆ reachableFrom g s₂ := by
  intro x hx
  have hr := (mem_reachableFrom_iff ..).1 hx
  rw [mem_reachableFrom_iff]
  induction hr with
  | seed hs hn => exact .seed (h hs) hn
  | step _ he hn ih => exact .step (ih ((mem_reachableFrom_iff ..).2 ‹_›)) he hn

/-- Adding nodes and edges can only grow the reachable set. -/
theorem reachableFrom_mono_graph {g₁ g₂ : Graph α} (hn : g₁.nodes ⊆ g₂.nodes)
    (he : g₁.edges ⊆ g₂.edges) (seeds : List α) :
    reachableFrom g₁ seeds ⊆ reachableFrom g₂ seeds := by
  intro x hx
  have hr := (mem_reachableFrom_iff ..).1 hx
  rw [mem_reachableFrom_iff]
  induction hr with
  | seed hs hx' => exact .seed hs (hn hx')
  | step hr h hx' ih => exact .step (ih ((mem_reachableFrom_iff ..).2 hr)) (he h) (hn hx')

theorem reachableFrom_nil (g : Graph α) : reachableFrom g [] = [] := by
  have : ∀ x, x ∉ reachableFrom g [] := by
    intro x hx
    have h := (mem_reachableFrom_iff ..).1 hx
    induction h with
    | seed hs _ => simp at hs
    | step _ _ _ ih => exact ih ((mem_reachableFrom_iff ..).2 ‹_›)
  exact List.eq_nil_iff_forall_not_mem.2 this

theorem reachable_eq_nil_of_not_mem {g : Graph α} {start : α} (h : start ∉ g.nodes) :
    reachable g start = [] := by
  simp [reachable, reachableFrom, h, closure_nil]
where
  closure_nil {g : Graph α} : (fuel : Nat) → closure g fuel [] = []
    | 0 => rfl
    | fuel + 1 => by
      rw [closure_succ]
      split
      · rfl
      · rename_i hne
        exfalso
        apply hne
        rw [closureStep_eq]
        simp

/-- Walks from `s`, stored as the reversed list of visited vertices. -/
inductive Walk (g : Graph α) (s : α) : α → List α → Prop where
  | nil : s ∈ g.nodes → Walk g s s [s]
  | cons {a b p} : Walk g s a p → (a, b) ∈ g.edges → b ∈ g.nodes → Walk g s b (b :: p)

variable {g : Graph α} {s : α}

omit [DecidableEq α] in
theorem Walk.head_mem {x : α} {p : List α} (h : Walk g s x p) : x ∈ p := by
  cases h <;> simp

omit [DecidableEq α] in
theorem Walk.start_mem {x : α} {p : List α} (h : Walk g s x p) : s ∈ p := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => exact List.mem_cons_of_mem _ ih

omit [DecidableEq α] in
theorem Walk.ne_nil {x : α} {p : List α} (h : Walk g s x p) : p ≠ [] := by
  cases h <;> simp

omit [DecidableEq α] in
theorem Walk.length_pos {x : α} {p : List α} (h : Walk g s x p) : 0 < p.length :=
  List.length_pos_of_mem h.head_mem

omit [DecidableEq α] in
theorem Walk.mem_nodes {x : α} {p : List α} (h : Walk g s x p) : x ∈ g.nodes := by
  cases h <;> assumption

theorem Walk.subset_reachable {x : α} {p : List α} (h : Walk g s x p) :
    p ⊆ reachable g s := by
  induction h with
  | nil hs =>
    intro y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact mem_reachableFrom_of_seed (by simp) hs
  | @cons a b p w he hb ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact reachableFrom_closed g _ (ih w.head_mem) he hb
    · exact ih hy

theorem mem_reachable_iff_walk (x : α) : x ∈ reachable g s ↔ ∃ p, Walk g s x p := by
  constructor
  · intro hx
    have h := (mem_reachableFrom_iff ..).1 hx
    induction h with
    | seed hs hn =>
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨_, .nil hn⟩
    | step _ he hn ih =>
      obtain ⟨p, hp⟩ := ih ((mem_reachableFrom_iff ..).2 ‹_›)
      exact ⟨_, .cons hp he hn⟩
  · rintro ⟨p, hp⟩
    exact hp.subset_reachable hp.head_mem

omit [DecidableEq α] in
/-- Every vertex on a walk splits it, with a walk ending at that vertex as the tail. -/
theorem Walk.split {x d : α} {p : List α} (h : Walk g s x p) (hd : d ∈ p) :
    ∃ u q, p = u ++ q ∧ Walk g s d q := by
  induction h with
  | nil hs =>
    simp only [List.mem_singleton] at hd
    subst hd
    exact ⟨[], _, rfl, .nil hs⟩
  | @cons a b p w he hb ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨[], _, rfl, .cons w he hb⟩
    · obtain ⟨u, q, rfl, hq⟩ := ih hd
      exact ⟨b :: u, q, rfl, hq⟩

omit [DecidableEq α] in
/-- Replacing the tail of a walk at `d` by any other walk to `d` gives a walk. -/
theorem Walk.graft {x d : α} {p r q : List α} (h : Walk g s x p) (u : List α)
    (hp : p = u ++ d :: q) (hr : Walk g s d r) : Walk g s x (u ++ r) := by
  induction h generalizing u with
  | nil hs =>
    match u, hp with
    | [], hp =>
      simp only [List.nil_append, List.cons.injEq] at hp
      obtain ⟨rfl, _⟩ := hp
      exact hr
    | _ :: u, hp =>
      simp only [List.cons_append, List.cons.injEq] at hp
      simpa using hp.2
  | @cons a b p w he hb ih =>
    match u, hp with
    | [], hp =>
      simp only [List.nil_append, List.cons.injEq] at hp
      obtain ⟨rfl, _⟩ := hp
      exact hr
    | v :: u, hp =>
      simp only [List.cons_append, List.cons.injEq] at hp
      obtain ⟨rfl, hp⟩ := hp
      exact .cons (ih u hp) he hb

/-- Every walk contains a simple walk over a subset of its vertices. -/
theorem Walk.simple {x : α} {p : List α} (h : Walk g s x p) :
    ∃ q, Walk g s x q ∧ q.Nodup ∧ q ⊆ p := by
  induction h with
  | nil hs => exact ⟨[s], .nil hs, by simp, List.Subset.refl _⟩
  | @cons a b p w he hb ih =>
    obtain ⟨q, hq, hnd, hsub⟩ := ih
    by_cases hbq : b ∈ q
    · obtain ⟨u, r, rfl, hr⟩ := hq.split hbq
      exact ⟨r, hr, (List.nodup_append.1 hnd).2.1,
        fun y hy => List.mem_cons_of_mem _ (hsub (by simp [hy]))⟩
    · exact ⟨b :: q, .cons hq he hb, List.nodup_cons.2 ⟨hbq, hnd⟩, List.cons_subset_cons _ hsub⟩

theorem reachable_trans {a b c : α} (hb : b ∈ reachable g a) (hc : c ∈ reachable g b) :
    c ∈ reachable g a := by
  have hr := (mem_reachableFrom_iff ..).1 hc
  induction hr with
  | seed hs _ =>
    simp only [List.mem_singleton] at hs
    subst hs
    exact hb
  | step _ he hn ih => exact reachableFrom_closed g _ (ih ((mem_reachableFrom_iff ..).2 ‹_›)) he hn

/-! ### Pruning -/

@[simp] theorem mem_prune_nodes (x : α) : x ∈ (prune g s).nodes ↔ x ∈ reachable g s := by
  simp only [prune, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨reachableFrom_subset_nodes _ _ h, h⟩⟩

@[simp] theorem mem_prune_edges (a b : α) :
    (a, b) ∈ (prune g s).edges ↔ (a, b) ∈ g.edges ∧ a ∈ reachable g s ∧ b ∈ reachable g s := by
  simp [prune]

theorem prune_no_dangling {a b : α} (h : (a, b) ∈ (prune g s).edges) :
    a ∈ (prune g s).nodes ∧ b ∈ (prune g s).nodes := by
  simp only [mem_prune_edges, mem_prune_nodes] at *
  exact h.2

/-- Pruning preserves every outgoing edge of a surviving node that lands on a node. -/
theorem prune_keeps_successors {a b : α} (ha : a ∈ reachable g s) (he : (a, b) ∈ g.edges)
    (hb : b ∈ g.nodes) : (a, b) ∈ (prune g s).edges :=
  (mem_prune_edges a b).2 ⟨he, ha, reachableFrom_closed g _ ha he hb⟩

theorem reachable_prune (x : α) : x ∈ reachable (prune g s) s ↔ x ∈ reachable g s := by
  constructor
  · intro h
    exact (mem_prune_nodes x).1 (reachableFrom_subset_nodes _ _ h)
  · rw [mem_reachable_iff_walk]
    rintro ⟨p, hp⟩
    rw [mem_reachable_iff_walk]
    refine ⟨p, ?_⟩
    induction hp with
    | nil hs => exact .nil ((mem_prune_nodes _).2 (mem_reachableFrom_of_seed (by simp) hs))
    | @cons a b p w he hb ih =>
      have ha : a ∈ reachable g s := (mem_reachable_iff_walk a).2 ⟨_, w⟩
      have hb' := reachableFrom_closed g _ ha he hb
      exact .cons ih ((mem_prune_edges a b).2 ⟨he, ha, hb'⟩) ((mem_prune_nodes b).2 hb')

/-- Pruning twice from the same start changes nothing. -/
theorem prune_idempotent : prune (prune g s) s = prune g s := by
  have hn : (prune g s).nodes.filter (fun n => n ∈ reachable (prune g s) s) = (prune g s).nodes := by
    apply List.filter_eq_self.2
    intro x hx
    simpa [reachable_prune] using hx
  have he : (prune g s).edges.filter
      (fun e => e.1 ∈ reachable (prune g s) s ∧ e.2 ∈ reachable (prune g s) s) = (prune g s).edges := by
    apply List.filter_eq_self.2
    rintro ⟨a, b⟩ hx
    have := (mem_prune_edges a b).1 hx
    simpa [reachable_prune] using this.2
  have hprune : prune (prune g s) s = ⟨(prune g s).nodes.filter (fun n => n ∈ reachable (prune g s) s),
      (prune g s).edges.filter
        (fun e => e.1 ∈ reachable (prune g s) s ∧ e.2 ∈ reachable (prune g s) s)⟩ := rfl
  rw [hprune, hn, he]

theorem prune_all_reachable {x : α} (hx : x ∈ (prune g s).nodes) : x ∈ reachable (prune g s) s := by
  rw [reachable_prune]
  exact (mem_prune_nodes x).1 hx

/-! ### Dominators -/

/-- `d` dominates `n`: every walk from `s` to `n` visits `d`. -/
def Dom (g : Graph α) (s n d : α) : Prop := ∀ p, Walk g s n p → d ∈ p

omit [DecidableEq α] in
theorem Dom.refl (n : α) : Dom g s n n := fun _ h => h.head_mem

omit [DecidableEq α] in
theorem Dom.start (n : α) : Dom g s n s := fun _ h => h.start_mem

omit [DecidableEq α] in
theorem Dom.trans {a b c : α} (hab : Dom g s a b) (hbc : Dom g s b c) : Dom g s a c := by
  intro p hp
  obtain ⟨u, q, rfl, hq⟩ := hp.split (hab p hp)
  exact List.mem_append_right _ (hbc q hq)

omit [DecidableEq α] in
/-- On a simple walk to `n`, a dominator of `n` lying before `x` also dominates `x`. -/
private theorem dom_of_simple {n x y : α} {a b : List α} (hw : Walk g s n (a ++ x :: b))
    (hnd : (a ++ x :: b).Nodup) (hy : y ∈ b) (hdom : Dom g s n y) : Dom g s x y := by
  intro r hr
  have := hdom _ (hw.graft a rfl hr)
  rcases List.mem_append.1 this with h | h
  · exact absurd (List.mem_cons_of_mem _ hy)
      ((List.nodup_append.1 hnd).2.2 y h y · rfl)
  · exact h

theorem Dom.antisymm {a b : α} (ha : a ∈ reachable g s) (hab : Dom g s a b) (hba : Dom g s b a) :
    a = b := by
  obtain ⟨p, hp⟩ := (mem_reachable_iff_walk a).1 ha
  obtain ⟨q, hq, hnd, -⟩ := hp.simple
  cases hq with
  | nil _ =>
    exact (List.mem_singleton.1 (hab _ (.nil ‹_›))).symm
  | @cons c _ q' w he hb =>
    rcases List.mem_cons.1 (hab _ (.cons w he hb)) with h | h
    · exact h.symm
    · exfalso
      obtain ⟨u, r, rfl, hr⟩ := w.split h
      exact (List.nodup_cons.1 hnd).1 (List.mem_append_right _ (hba r hr))

/-- The dominators of a reachable node are totally ordered by dominance. -/
theorem Dom.chain {n a b : α} (hn : n ∈ reachable g s) (ha : Dom g s n a) (hb : Dom g s n b) :
    Dom g s a b ∨ Dom g s b a := by
  obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hn
  obtain ⟨q, hq, hnd, -⟩ := hp.simple
  obtain ⟨u, v, rfl⟩ := List.append_of_mem (hb q hq)
  rcases List.mem_append.1 (ha _ hq) with h | h
  · obtain ⟨u₁, u₂, rfl⟩ := List.append_of_mem h
    left
    have heq : u₁ ++ a :: u₂ ++ b :: v = u₁ ++ a :: (u₂ ++ b :: v) := by simp
    rw [heq] at hq hnd
    exact dom_of_simple hq hnd (by simp) hb
  · rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (Dom.refl _)
    · exact Or.inr (dom_of_simple hq hnd h ha)

theorem get_mem {β : Type} {k : α} {v : β} {T : List (α × β)}
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

theorem get_exists {β : Type} {k : α} {T : List (α × β)} (h : k ∈ T.map Prod.fst) :
    ∃ v, Assoc.get k T = some v := by
  induction T with
  | nil => simp at h
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk
      exact ⟨b, by simp [Assoc.get]⟩
    · have h' : k ∈ es.map Prod.fst := by simpa [hk] using h
      obtain ⟨v, hv⟩ := ih h'
      have hb : (k == a) = false := by simpa using hk
      exact ⟨v, by simpa [Assoc.get, List.lookup, hb] using hv⟩

private theorem mem_foldl_intersect (sets : List (List α)) (init : List α) (x : α) :
    x ∈ sets.foldl (fun result values => intersect result values) init ↔
      x ∈ init ∧ ∀ v ∈ sets, x ∈ v := by
  induction sets generalizing init with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, ih, mem_intersect, List.forall_mem_cons]
    exact and_assoc

private abbrev reachPreds (g : Graph α) (s n : α) : List α :=
  (predecessors g n).filter fun pred => pred ∈ reachable g s

private abbrev common (g : Graph α) (s n : α) (T : List (α × List α)) : List α :=
  ((reachPreds g s n).filterMap fun pred => Assoc.get pred T).foldl
    (fun result values => intersect result values) (reachable g s)

private theorem reachPreds_ne_nil {n : α} (hn : n ∈ reachable g s) (hne : n ≠ s) :
    reachPreds g s n ≠ [] := by
  obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hn
  cases hp with
  | nil => exact absurd rfl hne
  | @cons a _ _ w he _ =>
    apply List.ne_nil_of_mem (a := a)
    simp only [reachPreds, List.mem_filter, mem_predecessors, decide_eq_true_eq]
    exact ⟨he, (mem_reachable_iff_walk a).2 ⟨_, w⟩⟩

private theorem mem_step {T : List (α × List α)} {n : α} {ds : List α}
    (h : (n, ds) ∈ dominatorStep g s T) :
    ∃ old, (n, old) ∈ T ∧
      ((n = s ∧ ds = [s]) ∨ (n ≠ s ∧ reachPreds g s n = [] ∧ ds = old) ∨
        (n ≠ s ∧ reachPreds g s n ≠ [] ∧ ds = (n :: common g s n T).eraseDups)) := by
  unfold_dominatorStep at h
  obtain ⟨⟨m, old⟩, he, heq⟩ := List.mem_map.1 h
  refine ⟨old, ?_⟩
  by_cases hms : m = s
  · simp only [hms, ite_true, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    subst hms
    exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [hms, ite_false] at heq
    split at heq
    · rename_i hnil
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨he, Or.inr (Or.inl ⟨hms, hnil, rfl⟩)⟩
    · rename_i hne
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact ⟨he, Or.inr (Or.inr ⟨hms, by simpa using hne, rfl⟩)⟩

private abbrev Keys (g : Graph α) (s : α) (T : List (α × List α)) : Prop :=
  T.map Prod.fst = reachable g s

private def SoundUpTo (g : Graph α) (s : α) (T : List (α × List α)) (m : Nat) : Prop :=
  ∀ n ds, (n, ds) ∈ T → ∀ d ∈ ds, ∀ p, Walk g s n p → p.length ≤ m → d ∈ p

private def Complete (g : Graph α) (s : α) (T : List (α × List α)) : Prop :=
  ∀ n ds, (n, ds) ∈ T → ∀ d, Dom g s n d → d ∈ ds

private theorem keys_step {T : List (α × List α)} : (dominatorStep g s T).map Prod.fst = T.map Prod.fst := by
  unfold_dominatorStep
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨m, old⟩ -
  simp only [Function.comp]
  by_cases hms : m = s
  · simp [hms]
  · simp only [hms, ite_false]
    split <;> rfl

private theorem mem_keys {T : List (α × List α)} (hk : Keys g s T) {n : α} {ds : List α}
    (h : (n, ds) ∈ T) : n ∈ reachable g s := by
  rw [← hk]
  exact List.mem_map.2 ⟨_, h, rfl⟩

private theorem sets_of_common {T : List (α × List α)} (hk : Keys g s T) {n a d : α}
    (ha : a ∈ reachable g s) (he : (a, n) ∈ g.edges) (hd : d ∈ common g s n T) :
    ∃ v, (a, v) ∈ T ∧ d ∈ v := by
  obtain ⟨v, hv⟩ := get_exists (T := T) (k := a) (by rw [hk]; exact ha)
  refine ⟨v, get_mem hv, ((mem_foldl_intersect _ _ _).1 hd).2 v ?_⟩
  refine List.mem_filterMap.2 ⟨a, ?_, hv⟩
  simp [he, ha]

private theorem step_sound {T : List (α × List α)} {m : Nat} (hk : Keys g s T)
    (hs : SoundUpTo g s T m) : SoundUpTo g s (dominatorStep g s T) (m + 1) := by
  intro n ds hmem d hd p hw hlen
  obtain ⟨old, hold, hc⟩ := mem_step hmem
  rcases hc with ⟨_, rfl⟩ | ⟨hne, hnil, _⟩ | ⟨hne, _, rfl⟩
  · rw [List.mem_singleton.1 hd]
    exact hw.start_mem
  · exact absurd hnil (reachPreds_ne_nil (mem_keys hk hold) hne)
  · rw [List.mem_eraseDups, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hw.head_mem
    · cases hw with
      | nil _ => exact absurd rfl hne
      | @cons a _ q w he hb =>
        have ha : a ∈ reachable g s := (mem_reachable_iff_walk a).2 ⟨_, w⟩
        obtain ⟨v, hv, hdv⟩ := sets_of_common hk ha he hd
        have hlen' : q.length ≤ m := by simpa using hlen
        exact List.mem_cons_of_mem _ (hs a v hv d hdv q w hlen')

private theorem step_complete {T : List (α × List α)} (hk : Keys g s T) (hc : Complete g s T) :
    Complete g s (dominatorStep g s T) := by
  intro n ds hmem d hd
  obtain ⟨old, hold, hcase⟩ := mem_step hmem
  have hn := mem_keys hk hold
  obtain ⟨p₀, hp₀⟩ := (mem_reachable_iff_walk n).1 hn
  rcases hcase with ⟨rfl, rfl⟩ | ⟨hne, hnil, _⟩ | ⟨hne, _, rfl⟩
  · exact hd _ (.nil hp₀.mem_nodes)
  · exact absurd hnil (reachPreds_ne_nil hn hne)
  · rw [List.mem_eraseDups, List.mem_cons]
    by_cases hdn : d = n
    · exact Or.inl hdn
    · refine Or.inr ((mem_foldl_intersect _ _ _).2 ⟨hp₀.subset_reachable (hd _ hp₀), ?_⟩)
      intro v hv
      obtain ⟨a, ha, hget⟩ := List.mem_filterMap.1 hv
      simp only [List.mem_filter, mem_predecessors, decide_eq_true_eq] at ha
      refine hc a v (get_mem hget) d ?_
      intro q hq
      rcases List.mem_cons.1 (hd _ (.cons hq ha.1 hp₀.mem_nodes)) with h | h
      · exact absurd h hdn
      · exact h

private theorem step_nodup {T : List (α × List α)} (hk : Keys g s T) :
    ∀ e ∈ dominatorStep g s T, e.2.Nodup := by
  rintro ⟨n, ds⟩ hmem
  obtain ⟨old, hold, hc⟩ := mem_step hmem
  rcases hc with ⟨_, rfl⟩ | ⟨hne, hnil, _⟩ | ⟨_, _, rfl⟩
  · simp
  · exact absurd hnil (reachPreds_ne_nil (mem_keys hk hold) hne)
  · exact nodup_eraseDups _

private theorem sound_of_fix {T : List (α × List α)} (hk : Keys g s T) (hfix : dominatorStep g s T = T)
    {m : Nat} (hs : SoundUpTo g s T m) (k : Nat) : SoundUpTo g s T (m + k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    have := step_sound hk ih
    rw [hfix] at this
    exact this

private structure AuxInv (g : Graph α) (s : α) (T : List (α × List α)) (m : Nat) : Prop where
  keys : Keys g s T
  sound : SoundUpTo g s T m
  complete : Complete g s T

private theorem aux_inv {T : List (α × List α)} {m : Nat} (fuel : Nat) (h : AuxInv g s T m) :
    AuxInv g s (dominatorsAux g s fuel T) (m + fuel) := by
  induction fuel generalizing T m with
  | zero => exact h
  | succ fuel ih =>
    unfold_dominatorsAux
    split
    · rename_i hfix
      exact ⟨h.keys, sound_of_fix h.keys hfix h.sound _, h.complete⟩
    · have := ih (T := dominatorStep g s T) (m := m + 1)
        ⟨by rw [Keys, keys_step]; exact h.keys, step_sound h.keys h.sound, step_complete h.keys h.complete⟩
      rw [show m + (fuel + 1) = m + 1 + fuel by omega]
      exact this

private theorem aux_nodup {T : List (α × List α)} (fuel : Nat) (hk : Keys g s T) :
    ∀ e ∈ dominatorsAux g s (fuel + 1) T, e.2.Nodup := by
  induction fuel generalizing T with
  | zero =>
    unfold_dominatorsAux
    split
    · rename_i hfix
      have := step_nodup hk
      rwa [hfix] at this
    · exact step_nodup hk
  | succ fuel ih =>
    rw [show dominatorsAux g s (fuel + 1 + 1) T =
      if dominatorStep g s T = T then T else dominatorsAux g s (fuel + 1) (dominatorStep g s T) from by
        unfold_dominatorsAux]
    split
    · rename_i hfix
      have := step_nodup hk
      rwa [hfix] at this
    · exact ih (by rw [Keys, keys_step]; exact hk)

private theorem initial_inv : AuxInv g s (initialDominators g s) 1 := by
  have hmem : ∀ n ds, (n, ds) ∈ initialDominators g s →
      n ∈ reachable g s ∧ ds = if n = s then [n] else reachable g s := by
    intro n ds h
    obtain ⟨m, hm, heq⟩ := List.mem_map.1 h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨hm, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · show ((reachable g s).map fun node => (node, if node = s then [node] else reachable g s)).map
      Prod.fst = reachable g s
    simp [Function.comp_def]
  · intro n ds hn d hd p hw hlen
    obtain ⟨_, rfl⟩ := hmem n ds hn
    cases hw with
    | nil _ =>
      simp only [ite_true, List.mem_singleton] at hd
      simp [hd]
    | cons w _ _ =>
      have := w.length_pos
      simp only [List.length_cons] at hlen
      omega
  · intro n ds hn d hd
    obtain ⟨hr, rfl⟩ := hmem n ds hn
    obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hr
    by_cases hns : n = s
    · subst hns
      simpa using hd _ (.nil hp.mem_nodes)
    · simpa [hns] using hp.subset_reachable (hd p hp)

private theorem dominators_eq :
    dominators g s = dominatorsAux g s ((initialDominators g s).length + 1) (initialDominators g s) := rfl

private theorem initial_length : (initialDominators g s).length = (reachable g s).length := by
  show ((reachable g s).map _).length = _
  simp

private theorem dominators_inv :
    AuxInv g s (dominators g s) ((reachable g s).length + 2) := by
  have := aux_inv (g := g) (s := s) ((initialDominators g s).length + 1) initial_inv
  rw [← dominators_eq, initial_length] at this
  rwa [show 1 + ((reachable g s).length + 1) = (reachable g s).length + 2 by omega] at this

/-- The dominator table has exactly one row per entry of the reachable list, in order. -/
theorem dominators_keys : (dominators g s).map Prod.fst = reachable g s :=
  dominators_inv.keys

/-- The dominator table is correct: its rows hold exactly the vertices on all walks to the node. -/
theorem mem_dominators_iff {n d : α} {ds : List α} (h : (n, ds) ∈ dominators g s) :
    d ∈ ds ↔ Dom g s n d := by
  constructor
  · intro hd p hp
    obtain ⟨q, hq, hnd, hsub⟩ := hp.simple
    refine hsub (dominators_inv.sound n ds h d hd q hq ?_)
    have := hnd.length_le_of_subset hq.subset_reachable
    omega
  · exact dominators_inv.complete n ds h d

theorem dominators_nodup : ∀ e ∈ dominators g s, e.2.Nodup := by
  rw [dominators_eq]
  exact aux_nodup _ initial_inv.keys

theorem get_dominators_iff {n d : α} (hn : n ∈ reachable g s) :
    ∃ ds, Assoc.get n (dominators g s) = some ds ∧ (d ∈ ds ↔ Dom g s n d) := by
  obtain ⟨ds, h⟩ := get_exists (T := dominators g s) (k := n) (by rw [dominators_keys]; exact hn)
  exact ⟨ds, h, mem_dominators_iff (get_mem h)⟩

/-- The start node is dominated only by itself. -/
theorem dominators_start {ds : List α} {d : α} (h : (s, ds) ∈ dominators g s) : d ∈ ds ↔ d = s := by
  rw [mem_dominators_iff h]
  constructor
  · intro hd
    have hs : s ∈ reachable g s := by
      rw [← dominators_keys]
      exact List.mem_map.2 ⟨_, h, rfl⟩
    obtain ⟨p, hp⟩ := (mem_reachable_iff_walk s).1 hs
    exact List.mem_singleton.1 (hd _ (.nil hp.mem_nodes))
  · rintro rfl
    exact Dom.start _

theorem dominators_eq_nil_of_not_mem (h : s ∉ g.nodes) : dominators g s = [] := by
  have := dominators_keys (g := g) (s := s)
  rw [reachable_eq_nil_of_not_mem h] at this
  simpa using this

/-! ### The dominator table, row by row -/

private theorem foldl_intersect_eq (sets : List (List α)) (init : List α) :
    sets.foldl (fun result values => intersect result values) init =
      init.filter fun x => sets.all fun v => decide (x ∈ v) := by
  induction sets generalizing init with
  | nil => exact (List.filter_eq_self.2 (by simp)).symm
  | cons v vs ih =>
    rw [List.foldl_cons, ih, intersect, List.filter_filter]
    apply List.filter_congr
    intro x _
    simp only [List.all_cons]
    rw [Bool.and_comm]

/-- `eraseDups` does nothing to a list without repeats. -/
theorem eraseDups_of_nodup {l : List α} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.1 h
    rw [List.eraseDups_cons]
    congr 1
    have : xs.filter (fun b => !b == x) = xs := by
      apply List.filter_eq_self.2
      intro y hy
      have : y ≠ x := fun e => hx (e ▸ hy)
      simpa using this
    rw [this]
    exact ih hxs

/-- `eraseDups` keeps the first of each, so it doesn't matter whether a filter goes first. -/
theorem eraseDups_filter (P : α → Bool) (l : List α) : (l.filter P).eraseDups = l.eraseDups.filter P := by
  induction l generalizing P with
  | nil => simp
  | cons x xs ih =>
    rw [List.eraseDups_cons, List.filter_cons]
    split
    · rename_i hx
      rw [List.eraseDups_cons, List.filter_cons, ite_eq_left hx]
      congr 1
      rw [List.filter_filter, ih, ih, List.filter_filter]
      apply List.filter_congr
      intro y _
      simp [Bool.and_comm]
    · rename_i hx
      rw [ih, List.filter_cons, ite_eq_right hx, ih, List.filter_filter]
      apply List.filter_congr
      intro y _
      by_cases hy : y = x
      · subst hy
        simp [hx]
      · simp [hy]

/-- A table that is exact, whichever way it was reached. -/
private structure Exact (g : Graph α) (s : α) (T : List (α × List α)) : Prop where
  keys : T.map Prod.fst = reachable g s
  mem : ∀ n ds, (n, ds) ∈ T → ∀ d, d ∈ ds ↔ Dom g s n d

private theorem aux_prior {T : List (α × List α)} {m : Nat} (fuel : Nat) (h : AuxInv g s T m)
    (hm : (reachable g s).length ≤ m + fuel) :
    ∃ T', Exact g s T' ∧ dominatorsAux g s (fuel + 1) T = dominatorStep g s T' := by
  have hexact : ∀ {T : List (α × List α)} {m : Nat}, AuxInv g s T m → (reachable g s).length ≤ m → Exact g s T := by
    intro T m h hm
    refine ⟨h.keys, fun n ds hmem d => ⟨fun hd p hp => ?_, h.complete n ds hmem d⟩⟩
    obtain ⟨q, hq, hnd, hsub⟩ := hp.simple
    refine hsub (h.sound n ds hmem d hd q hq ?_)
    have := hnd.length_le_of_subset hq.subset_reachable
    omega
  induction fuel generalizing T m with
  | zero =>
    refine ⟨T, hexact h (by omega), ?_⟩
    unfold_dominatorsAux
    split
    · rename_i hfix
      exact hfix.symm
    · unfold_dominatorsAux
  | succ fuel ih =>
    have hfuel : dominatorsAux g s (fuel + 1 + 1) T =
        if dominatorStep g s T = T then T else dominatorsAux g s (fuel + 1) (dominatorStep g s T) := by
      unfold_dominatorsAux
    rw [hfuel]
    split
    · rename_i hfix
      refine ⟨T, ?_, hfix.symm⟩
      have hs := sound_of_fix h.keys hfix h.sound (reachable g s).length
      exact hexact ⟨h.keys, hs, h.complete⟩ (by omega)
    · exact ih ⟨by rw [Keys, keys_step]; exact h.keys, step_sound h.keys h.sound, step_complete h.keys h.complete⟩
        (by omega)

open Classical in
/-- What a row of the dominator table is, in terms of `Dom`: the node, then its other dominators in the
order of `reachable`. -/
theorem dominators_rows :
    dominators g s = (reachable g s).map fun n =>
      (n, if n = s then [s] else n :: ((reachable g s).eraseDups.filter fun d => decide (Dom g s n d ∧ d ≠ n))) := by
  have hlen : (reachable g s).length ≤ 1 + (initialDominators g s).length := by
    rw [initial_length]
    omega
  obtain ⟨T, hT, heq⟩ := aux_prior (g := g) (s := s) (initialDominators g s).length initial_inv hlen
  have hd : dominators g s = dominatorStep g s T := dominators_eq.trans heq
  rw [hd]
  conv => rhs; rw [← hT.keys]
  unfold_dominatorStep
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨n, old⟩ hold
  simp only [Function.comp]
  have hn : n ∈ reachable g s := by
    rw [← hT.keys]
    exact List.mem_map.2 ⟨_, hold, rfl⟩
  by_cases hns : n = s
  · simp [hns]
  · simp only [hns, ite_false]
    have hpne := reachPreds_ne_nil hn hns
    split
    · rename_i hnil
      exact absurd hnil hpne
    · rename_i hne
      rw [List.eraseDups_cons]
      congr 1
      rw [foldl_intersect_eq]
      have hkey : ∀ d, ((((predecessors g n).filter fun pred => pred ∈ reachable g s).filterMap fun pred =>
          Assoc.get pred T).all fun v => decide (d ∈ v)) = true ↔ ∀ a, (a, n) ∈ g.edges → a ∈ reachable g s → Dom g s a d := by
        intro d
        simp only [List.all_eq_true, decide_eq_true_eq, List.mem_filterMap, List.mem_filter, mem_predecessors]
        constructor
        · intro h a he ha
          obtain ⟨v, hv⟩ := get_exists (T := T) (k := a) (by rw [hT.keys]; exact ha)
          exact (hT.mem a v (get_mem hv) d).1 (h v ⟨a, ⟨he, by simpa using ha⟩, hv⟩)
        · rintro h v ⟨a, ⟨he, ha⟩, hv⟩
          exact (hT.mem a v (get_mem hv) d).2 (h a he (by simpa using ha))
      have hdom : ∀ d, d ≠ n → (Dom g s n d ↔ ∀ a, (a, n) ∈ g.edges → a ∈ reachable g s → Dom g s a d) := by
        intro d hdn
        constructor
        · intro h a he ha q hq
          rcases List.mem_cons.1 (h _ (.cons hq he ((mem_reachable_iff_walk n).1 hn).choose_spec.mem_nodes)) with h' | h'
          · exact absurd h' hdn
          · exact h'
        · intro h p hp
          cases hp with
          | nil _ => exact absurd rfl hns
          | @cons a _ q w he _ =>
            exact List.mem_cons_of_mem _ (h a he ((mem_reachable_iff_walk a).2 ⟨_, w⟩) q w)
      rw [List.filter_filter, eraseDups_filter, hT.keys]
      refine congrArg (n :: ·) (List.filter_congr ?_)
      intro d _
      by_cases hdn : d = n
      · subst hdn
        simp
      · have h1 := hkey d
        have h2 := hdom d hdn
        rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨_, h⟩
          exact ⟨h2.2 (h1.1 h), hdn⟩
        · rintro ⟨h, _⟩
          exact ⟨by simpa using hdn, h1.2 (h2.1 h)⟩

/-! ### Immediate dominators -/

/-- Size of the dominator set recorded for a node. -/
abbrev domSize (g : Graph α) (s c : α) : Nat :=
  ((Assoc.get c (dominators g s)).getD []).length

abbrev pick (g : Graph α) (s n : α) (best : Option (α × α)) (candidate : α) : Option (α × α) :=
  match best with
  | none => some (n, candidate)
  | some (_, current) =>
    let candidateSize := (Assoc.get candidate (dominators g s)).getD []
    let currentSize := (Assoc.get current (dominators g s)).getD []
    if candidateSize.length > currentSize.length then some (n, candidate) else best

theorem foldl_pick_some (n b₀ : α) (l : List α) :
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

theorem foldl_pick_none (n : α) (l : List α) (hne : l ≠ []) :
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

theorem foldl_pick_eq {n i : α} {l : List α} {r : Option (α × α)} (hr : ∀ a b, r = some (a, b) → a = n)
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

theorem immediateDominators_eq :
    immediateDominators g s = (dominators g s).filterMap fun entry =>
      if entry.1 = s then none
      else (entry.2.filter fun c => c != entry.1).foldl (pick g s entry.1) none := by
  rfl

theorem domSize_eq {c : α} {ds : List α} (h : Assoc.get c (dominators g s) = some ds) :
    domSize g s c = ds.length := by
  simp [domSize, h]

/-- If `b` strictly dominates `a` then `b`'s dominator set is strictly smaller. -/
theorem domSize_lt {a b : α} (ha : a ∈ reachable g s) (hab : Dom g s a b) (hne : a ≠ b) :
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

private theorem filterMap_congr_of_mem {β γ : Type} {f h : β → Option γ} {l : List β} (H : ∀ x ∈ l, f x = h x) :
    l.filterMap f = l.filterMap h := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := H x List.mem_cons_self
    have hr := ih fun y hy => H y (List.mem_cons_of_mem _ hy)
    simp only [List.filterMap_cons, hx, hr]

/-- **The list of immediate dominators, of any function that has them**: a node's immediate dominator is a strict dominator that all its strict dominators dominate, so that
what has that property for each reachable node gives the very list. -/
theorem immediateDominators_of (idom : α → α)
    (hi : ∀ n ∈ reachable g s, n ≠ s → idom n ≠ n ∧ Dom g s n (idom n) ∧ ∀ c, c ≠ n → Dom g s n c → Dom g s (idom n) c) :
    immediateDominators g s = (reachable g s).filterMap fun n => if n = s then none else some (n, idom n) := by
  rw [immediateDominators_eq]
  conv => rhs; rw [← dominators_keys (g := g) (s := s), List.filterMap_map]
  apply filterMap_congr_of_mem
  rintro ⟨n, ds⟩ hmem
  by_cases hns : n = s
  · simp [hns]
  · have hn : n ∈ reachable g s := by
      rw [← dominators_keys (g := g) (s := s)]
      exact List.mem_map.2 ⟨_, hmem, rfl⟩
    simp only [hns, ↓reduceIte, Function.comp_apply]
    obtain ⟨hne, hdom, hall⟩ := hi n hn hns
    have hf : ds.filter (fun c => c != n) ≠ [] := by
      apply List.ne_nil_of_mem (a := s)
      simp only [List.mem_filter, bne_iff_ne, ne_eq]
      exact ⟨(mem_dominators_iff hmem).2 (Dom.start _), Ne.symm hns⟩
    obtain ⟨b, _, hfold, _⟩ := foldl_pick_none (g := g) (s := s) n _ hf
    have hmemB : (n, b) ∈ immediateDominators g s := by
      rw [immediateDominators_eq]
      refine List.mem_filterMap.2 ⟨(n, ds), hmem, ?_⟩
      simp only [hns, ite_false]
      exact hfold
    obtain ⟨_, _, hbn, hdb, hmin⟩ := immediateDominators_spec hmemB
    have hreach : b ∈ reachable g s := by
      obtain ⟨p, hp⟩ := (mem_reachable_iff_walk n).1 hn
      exact hp.subset_reachable (hdb p hp)
    have heq : b = idom n := Dom.antisymm hreach (hmin (idom n) hne hdom) (hall b hbn hdb)
    rw [hfold, heq]

end Bap.Proofs.Graph
