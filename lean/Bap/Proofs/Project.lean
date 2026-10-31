import Lean.Elab.Command
import Bap.Project.Pass
import Bap.Project.Persist
import Bap.Proofs.Bil
import Bap.Proofs.Binary
import Bap.Proofs.Knowledge
import Bap.Proofs.Disasm
import Bap.Proofs.Image

namespace Bap.Proofs.Project

open Lean Elab Command in
/-- `open_private Mod in Ns : a b` names private declarations `Ns.a`, `Ns.b` of module `Mod`
as `a`, `b` for the rest of the current scope. -/
local elab "open_private " mod:ident " in " ns:ident " : " names:ident* : command => do
  for name in names do
    let target := (Name.mkNum (`_private ++ mod.getId) 0) ++ (ns.getId ++ name.getId)
    unless (← getEnv).contains target do
      throwErrorAt name "no private declaration {target}"
    modifyScope fun scope =>
      { scope with openDecls := .explicit name.getId target :: scope.openDecls }

open Bap.Project

section Storage

private theorem lookup_filter_other {k j : String} (hne : j ≠ k) (entries : List (String × String)) :
    List.lookup j (entries.filter fun entry => entry.1 != k) = List.lookup j entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨a, b⟩ := head
    by_cases hak : a = k
    · subst hak
      have : (j == a) = false := by simpa using hne
      simp [List.lookup, this, ih]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hak, not_false_eq_true, ite_true, List.lookup, ih]

theorem get_set_same (project : Project) (name value : String) :
    (project.set name value).get name = some value := by
  simp [Project.get, Project.set]

theorem get_set_other (project : Project) {name other : String} (value : String) (h : other ≠ name) :
    (project.set name value).get other = project.get other := by
  have : (other == name) = false := by simpa using h
  simp [Project.get, Project.set, Bap.Assoc.get, Bap.Assoc.put, List.lookup, this, lookup_filter_other h]

theorem set_set_same (project : Project) (name a b : String) :
    (project.set name a).set name b = project.set name b := by
  simp [Project.set, Bap.Assoc.put, List.filter_filter]

theorem set_frame (project : Project) (name value : String) :
    (project.set name value).image = project.image ∧ (project.set name value).disasm = project.disasm ∧
      (project.set name value).passed = project.passed := ⟨rfl, rfl, rfl⟩

theorem set_no_duplicate_keys (project : Project) (name value : String)
    (h : (project.storage.map Prod.fst).Nodup) :
    ((project.set name value).storage.map Prod.fst).Nodup := by
  have hsub : ((project.storage.filter fun entry => entry.1 != name).map Prod.fst).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup h
  simp only [Project.set, Bap.Assoc.put, List.map_cons, List.nodup_cons]
  refine ⟨?_, hsub⟩
  simp

theorem markPassed_frame (project : Project) (name : String) :
    (project.markPassed name).storage = project.storage ∧ (project.markPassed name).image = project.image ∧
      (project.markPassed name).passed = name :: project.passed := ⟨rfl, rfl, rfl⟩

theorem get_markPassed (project : Project) (pass key : String) :
    (project.markPassed pass).get key = project.get key := rfl

end Storage

section RunPass

open_private Bap.Project.Pass in Bap.Project : runPass sortPassesAux sortPasses

theorem runPass_skip (pass : Pass) (project : Project) (ho : pass.runonce = true)
    (hp : pass.name ∈ project.passed) : runPass pass project = .ok project := by
  simp [runPass, ho, hp]

theorem runPass_fresh (pass : Pass) (project out : Project) (hrun : pass.run project = .ok out)
    (hp : pass.runonce = false ∨ pass.name ∉ project.passed) :
    runPass pass project = .ok (out.markPassed pass.name) := by
  have : ¬ (pass.runonce = true ∧ pass.name ∈ project.passed) := by
    rcases hp with hp | hp <;> simp [hp]
  simp only [runPass, Bool.and_eq_true, List.contains_iff_mem, this, ite_false, hrun]

theorem runPass_error (pass : Pass) (project : Project) (message : String)
    (hrun : pass.run project = .error message)
    (hp : pass.runonce = false ∨ pass.name ∉ project.passed) :
    runPass pass project = .error (.runtime pass.name message) := by
  have : ¬ (pass.runonce = true ∧ pass.name ∈ project.passed) := by
    rcases hp with hp | hp <;> simp [hp]
  simp only [runPass, Bool.and_eq_true, List.contains_iff_mem, this, ite_false, hrun]

/-- A successful `runPass` always leaves the pass marked as passed, when it ran or was skipped. -/
theorem runPass_marks {pass : Pass} {project out : Project} (h : runPass pass project = .ok out) :
    pass.runonce = true ∧ pass.name ∈ project.passed ∧ out = project ∨
      ∃ inner, pass.run project = .ok inner ∧ out = inner.markPassed pass.name := by
  by_cases hc : pass.runonce = true ∧ pass.name ∈ project.passed
  · have hskip := runPass_skip pass project hc.1 hc.2
    rw [hskip] at h
    cases h
    exact .inl ⟨hc.1, hc.2, rfl⟩
  · simp only [runPass, Bool.and_eq_true, List.contains_iff_mem, hc, ite_false] at h
    split at h
    · rename_i inner hinner
      cases h
      exact .inr ⟨inner, hinner, rfl⟩
    · cases h

/-- A second run of a `runonce` pass is a no-op. -/
theorem runPass_runonce_idempotent {pass : Pass} {project out : Project} (ho : pass.runonce = true)
    (h : runPass pass project = .ok out) : runPass pass out = .ok out := by
  rcases runPass_marks h with ⟨_, hp, rfl⟩ | ⟨inner, _, rfl⟩
  · exact runPass_skip _ _ ho hp
  · exact runPass_skip _ _ ho (by simp [Project.markPassed])

/-- The sequential pass driver used by `runPasses` once the schedule is fixed. -/
def runAll (passes : List Pass) (project : Project) : Except PassError Project :=
  passes.foldlM (fun project pass => runPass pass project) project

theorem runAll_append (left right : List Pass) (project : Project) :
    runAll (left ++ right) project = (runAll left project).bind (runAll right) := by
  simp only [runAll, List.foldlM_append]
  rfl

theorem runAll_short_circuit {before after : List Pass} {bad : Pass} {project mid : Project}
    {error : PassError} (hb : runAll before project = .ok mid) (he : runPass bad mid = .error error) :
    runAll (before ++ bad :: after) project = .error error := by
  rw [runAll_append, hb]
  simp [Except.bind, runAll, List.foldlM_cons, bind, he]

/-- Success of a sequence means every prefix succeeded. -/
theorem runAll_prefix_ok {left right : List Pass} {project out : Project}
    (h : runAll (left ++ right) project = .ok out) : ∃ mid, runAll left project = .ok mid ∧
      runAll right mid = .ok out := by
  rw [runAll_append] at h
  cases hl : runAll left project with
  | error e => simp [hl, Except.bind] at h
  | ok mid => exact ⟨mid, rfl, by simpa [hl, Except.bind] using h⟩

/-- When no pass drops earlier `passed` marks, every pass of a successful sequence ends up marked. -/
theorem runAll_marks_all (passes : List Pass)
    (hkeep : ∀ pass ∈ passes, ∀ p q, pass.run p = .ok q → ∀ n ∈ p.passed, n ∈ q.passed) :
    ∀ (project out : Project), runAll passes project = .ok out →
      (∀ n ∈ project.passed, n ∈ out.passed) ∧ ∀ pass ∈ passes, pass.name ∈ out.passed := by
  induction passes with
  | nil =>
    intro project out h
    cases h
    exact ⟨fun _ hn => hn, by simp⟩
  | cons head tail ih =>
    intro project out h
    simp only [runAll, List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i mid hmid
      obtain ⟨hk, hall⟩ := ih (fun p hp => hkeep p (List.mem_cons_of_mem _ hp)) mid out h
      have hstep : (∀ n ∈ project.passed, n ∈ mid.passed) ∧ head.name ∈ mid.passed := by
        rcases runPass_marks hmid with ⟨_, hp, rfl⟩ | ⟨inner, hr, rfl⟩
        · exact ⟨fun _ hn => hn, hp⟩
        · refine ⟨fun n hn => ?_, by simp [Project.markPassed]⟩
          have := hkeep head List.mem_cons_self _ _ hr n hn
          simp [Project.markPassed, this]
      refine ⟨fun n hn => hk n (hstep.1 n hn), fun pass hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hk _ hstep.2
      · exact hall pass hp

theorem runPasses_unfold (passes : List Pass) (project : Project) :
    runPasses passes project = (sortPasses passes).bind fun sorted => runAll sorted project := rfl

end RunPass

section Scheduler

open_private Bap.Project.Pass in Bap.Project : runPass sortPassesAux sortPasses

/-- The pass a name schedules: the first one in the list with that name. -/
abbrev lookupPass (passes : List Pass) (name : String) : Option Pass :=
  passes.find? fun candidate => candidate.name = name

/-- In a permanent list (newest first), the dependencies of each entry occur further down. -/
def Closed (passes : List Pass) : List String → Prop
  | [] => True
  | name :: tail =>
    (∀ pass, lookupPass passes name = some pass → ∀ d ∈ pass.dependencies, d ∈ tail) ∧ Closed passes tail

/-- What one traversal step guarantees about the temporary and permanent lists. -/
structure VisitPost (passes : List Pass) (t p t' p' : List String) : Prop where
  suffix : p <:+ p'
  closed : Closed passes p → Closed passes p'
  nodup : p.Nodup → p'.Nodup
  temp : ∀ n ∈ t, n ∈ t'
  fresh : ∀ n ∈ p', n ∈ p ∨ n ∉ t
  known : ∀ n ∈ p', n ∈ p ∨ ∃ q ∈ passes, q.name = n

private theorem VisitPost.refl (passes : List Pass) (t p : List String) : VisitPost passes t p t p :=
  ⟨List.suffix_refl _, id, id, fun _ h => h, fun _ h => .inl h, fun _ h => .inl h⟩

private theorem VisitPost.trans {passes : List Pass} {t p t1 p1 t2 p2 : List String}
    (a : VisitPost passes t p t1 p1) (b : VisitPost passes t1 p1 t2 p2) :
    VisitPost passes t p t2 p2 where
  suffix := a.suffix.trans b.suffix
  closed := b.closed ∘ a.closed
  nodup := b.nodup ∘ a.nodup
  temp := fun n h => b.temp n (a.temp n h)
  fresh := fun n h => by
    rcases b.fresh n h with h1 | h1
    · exact a.fresh n h1
    · exact .inr fun hn => h1 (a.temp n hn)
  known := fun n h => by
    rcases b.known n h with h1 | h1
    · exact a.known n h1
    · exact .inr h1

private theorem lookupPass_canonical {passes : List Pass} {name : String} {pass : Pass}
    (h : lookupPass passes name = some pass) :
    pass.name = name ∧ pass ∈ passes ∧ lookupPass passes pass.name = some pass := by
  have hn : pass.name = name := by simpa using (List.find?_some h)
  refine ⟨hn, List.mem_of_find?_eq_some h, ?_⟩
  rw [hn]; exact h

/-- One step of the walk over a pass's dependencies. -/
private def depStep (passes : List Pass) (pass : Pass) (fuel : Nat)
    (visited : List String × List String) (dependency : String) :
    Except PassError (List String × List String) :=
  match passes.find? fun candidate => candidate.name = dependency with
  | none => .error (.missingDependency pass.name dependency)
  | some dependencyPass => visit passes dependencyPass fuel visited.1 visited.2

private theorem visit_succ (passes : List Pass) (pass : Pass) (fuel : Nat) (t p : List String) :
    visit passes pass (fuel + 1) t p =
      if pass.name ∈ p then .ok (t, p)
      else if pass.name ∈ t then .error (.cycle pass.name)
      else (pass.dependencies.foldlM (depStep passes pass fuel) (pass.name :: t, p)).bind
        fun res => .ok (res.1, pass.name :: res.2) := by
  rw [visit]
  simp only [bind, Except.bind, List.contains_iff_mem]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- Soundness of the depth-first traversal, for any fuel. -/
theorem traversal_spec (passes : List Pass) (fuel : Nat) :
    ∀ (pass : Pass) (t p t' p' : List String), lookupPass passes pass.name = some pass →
      visit passes pass fuel t p = .ok (t', p') →
      VisitPost passes t p t' p' ∧ pass.name ∈ p' := by
  induction fuel with
  | zero =>
    intro pass t p t' p' _ h
    simp [visit] at h
  | succ fuel ihv =>
    intro pass t p t' p' hcanon h
    have fold : ∀ (deps : List String) (t p t' p' : List String),
        deps.foldlM (depStep passes pass fuel) (t, p) = .ok (t', p') →
        VisitPost passes t p t' p' ∧ ∀ d ∈ deps, d ∈ p' := by
      intro deps
      induction deps with
      | nil =>
        intro t p t' p' h
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨VisitPost.refl _ _ _, by simp⟩
      | cons d rest ihd =>
        intro t p t' p' h
        simp only [List.foldlM_cons, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i res hres
          obtain ⟨t1, p1⟩ := res
          simp only [depStep] at hres
          split at hres
          · cases hres
          · rename_i dp hfind
            obtain ⟨hn, _, hc⟩ := lookupPass_canonical hfind
            obtain ⟨post1, hm⟩ := ihv _ _ _ _ _ hc hres
            obtain ⟨post2, hrest⟩ := ihd _ _ _ _ h
            refine ⟨post1.trans post2, fun e he => ?_⟩
            rcases List.mem_cons.mp he with rfl | he
            · rw [hn] at hm
              exact post2.suffix.subset hm
            · exact hrest e he
    rw [visit_succ] at h
    split at h
    · rename_i hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨VisitPost.refl _ _ _, hp⟩
    · rename_i hp
      split at h
      · cases h
      · rename_i ht
        cases hres : pass.dependencies.foldlM (depStep passes pass fuel) (pass.name :: t, p) with
        | error e => simp [hres, Except.bind] at h
        | ok res =>
          obtain ⟨t2, p2⟩ := res
          simp only [hres, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨post, hdeps⟩ := fold _ _ _ _ _ hres
          have hnot : pass.name ∉ p2 := by
            intro hmem
            rcases post.fresh _ hmem with h1 | h1
            · exact hp h1
            · exact h1 List.mem_cons_self
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, List.mem_cons_self⟩
          · exact post.suffix.trans (List.suffix_cons _ _)
          · intro hc
            refine ⟨fun q hq d hd => ?_, post.closed hc⟩
            rw [hcanon] at hq
            cases hq
            exact hdeps d hd
          · intro hn
            exact List.nodup_cons.mpr ⟨hnot, post.nodup hn⟩
          · intro n hn
            exact post.temp n (List.mem_cons_of_mem _ hn)
          · intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact .inr ht
            · rcases post.fresh n hn with h1 | h1
              · exact .inl h1
              · exact .inr fun hm => h1 (List.mem_cons_of_mem _ hm)
          · intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · exact .inr ⟨pass, List.mem_of_find?_eq_some hcanon, rfl⟩
            · exact post.known n hn

/-- How many pass names the traversal has yet to put on `temporary`. -/
def unvisited (passes : List Pass) (t : List String) : Nat :=
  ((passes.map Pass.name).filter (· ∉ t)).length

private theorem filter_length_le (names : List String) {f g : String → Bool} (h : ∀ x, f x = true → g x = true) :
    (names.filter f).length ≤ (names.filter g).length := by
  induction names with
  | nil => exact Nat.le_refl _
  | cons n rest ih =>
    simp only [List.filter_cons]
    cases hf : f n with
    | false => cases g n <;> simp <;> omega
    | true => simp [h n hf]; omega

private theorem filter_length_lt {names : List String} {name : String} (hmem : name ∈ names)
    {f g : String → Bool} (h : ∀ x, f x = true → g x = true) (hf : f name = false) (hg : g name = true) :
    (names.filter f).length < (names.filter g).length := by
  induction names with
  | nil => cases hmem
  | cons n rest ih =>
    simp only [List.filter_cons]
    by_cases hn : n = name
    · subst hn
      have := filter_length_le rest h
      simp [hf, hg]
      omega
    · have hrest : name ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hn
        · exact h
      have := ih hrest
      cases hfn : f n with
      | false => cases g n <;> simp <;> omega
      | true => simp [h n hfn]; omega

private theorem unvisited_le_of_subset (passes : List Pass) {t t' : List String} (h : ∀ n ∈ t, n ∈ t') :
    unvisited passes t' ≤ unvisited passes t := by
  apply filter_length_le
  intro n hn
  simp only [decide_eq_true_eq] at hn ⊢
  exact fun hm => hn (h n hm)

private theorem unvisited_cons_lt {passes : List Pass} {pass : Pass} {t : List String}
    (hp : pass ∈ passes) (ht : pass.name ∉ t) :
    unvisited passes (pass.name :: t) < unvisited passes t := by
  apply filter_length_lt (List.mem_map_of_mem hp)
  · intro n hn
    simp only [List.mem_cons, not_or, decide_eq_true_eq] at hn ⊢
    exact hn.2
  · simp
  · simpa using ht

private theorem visit_temp_mono (passes : List Pass) (fuel : Nat) :
    ∀ (pass : Pass) (t p t' p' : List String), visit passes pass fuel t p = .ok (t', p') →
      ∀ n ∈ t, n ∈ t' := by
  induction fuel with
  | zero =>
    intro pass t p t' p' h
    simp [visit] at h
  | succ fuel ihv =>
    intro pass t p t' p' h n hn
    have fold : ∀ (deps : List String) (t p t' p' : List String),
        deps.foldlM (depStep passes pass fuel) (t, p) = .ok (t', p') → ∀ n ∈ t, n ∈ t' := by
      intro deps
      induction deps with
      | nil =>
        intro t p t' p' h n hn
        simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ hn
      | cons d rest ihd =>
        intro t p t' p' h n hn
        simp only [List.foldlM_cons, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i res hres
          obtain ⟨t1, p1⟩ := res
          simp only [depStep] at hres
          split at hres
          · cases hres
          · exact ihd _ _ _ _ h n (ihv _ _ _ _ _ hres n hn)
    rw [visit_succ] at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ hn
    · split at h
      · cases h
      · cases hres : pass.dependencies.foldlM (depStep passes pass fuel) (pass.name :: t, p) with
        | error e => simp [hres, Except.bind] at h
        | ok res =>
          obtain ⟨t2, p2⟩ := res
          simp only [hres, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
          exact h.1 ▸ fold _ _ _ _ _ hres n (List.mem_cons_of_mem _ hn)

/-- The error `visit` gives when out of fuel. -/
abbrev fuelError : PassError := .runtime "scheduler" "dependency traversal fuel exhausted"

/-- The traversal never runs out of fuel, on any input, cyclic or not, when `fuel` exceeds the
names not yet on `temporary`: each level puts a new name there. -/
theorem visit_never_exhausted (passes : List Pass) (fuel : Nat) :
    ∀ (pass : Pass) (t p : List String), pass ∈ passes → unvisited passes t < fuel →
      visit passes pass fuel t p ≠ .error fuelError := by
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ihv =>
    intro pass t p hmem hfuel
    have fold : ∀ (deps : List String) (t p : List String), unvisited passes t < fuel →
        deps.foldlM (depStep passes pass fuel) (t, p) ≠ .error fuelError := by
      intro deps
      induction deps with
      | nil =>
        intro t p _
        simp [pure, Except.pure]
      | cons d rest ihd =>
        intro t p hlt
        simp only [List.foldlM_cons, bind, Except.bind]
        split
        · rename_i e he
          intro heq
          cases heq
          simp only [depStep] at he
          split at he
          · cases he
          · rename_i dp hfind
            exact ihv dp t p (List.mem_of_find?_eq_some hfind) hlt he
        · rename_i res hres
          obtain ⟨t1, p1⟩ := res
          apply ihd
          simp only [depStep] at hres
          split at hres
          · cases hres
          · exact Nat.lt_of_le_of_lt (unvisited_le_of_subset passes (visit_temp_mono _ _ _ _ _ _ _ hres)) hlt
    rw [visit_succ]
    split
    · simp
    · split
      · simp
      · rename_i ht
        have hlt : unvisited passes (pass.name :: t) < fuel := by
          have := unvisited_cons_lt hmem ht
          omega
        have hf := fold pass.dependencies (pass.name :: t) p hlt
        cases hres : pass.dependencies.foldlM (depStep passes pass fuel) (pass.name :: t, p) with
        | error e =>
          simp only [Except.bind]
          rw [hres] at hf
          exact hf
        | ok res => simp [Except.bind]

/-- The dependency relation has no cycle and names only given passes: some rank strictly falls
along every dependency. -/
def Acyclic (passes : List Pass) : Prop :=
  ∃ rank : String → Nat, ∀ p ∈ passes, ∀ d ∈ p.dependencies,
    (∃ q ∈ passes, q.name = d) ∧ rank d < rank p.name

private theorem find_exists {passes : List Pass} {d : String} (h : ∃ q ∈ passes, q.name = d) :
    ∃ dp, (passes.find? fun candidate => decide (candidate.name = d)) = some dp := by
  obtain ⟨q, hq, hn⟩ := h
  have : (passes.find? fun candidate => decide (candidate.name = d)).isSome := by
    simp only [List.find?_isSome]
    exact ⟨q, hq, by simpa using hn⟩
  exact Option.isSome_iff_exists.mp this

/-- On an acyclic input with enough fuel `visit` succeeds. Names on `temporary` that are not yet
permanent are on the stack and outrank `pass`; everything a visit pushes ends up permanent. -/
private theorem visit_acyclic_ok {passes : List Pass} {rank : String → Nat}
    (hrank : ∀ p ∈ passes, ∀ d ∈ p.dependencies, (∃ q ∈ passes, q.name = d) ∧ rank d < rank p.name)
    (fuel : Nat) :
    ∀ (pass : Pass) (t p : List String), pass ∈ passes → unvisited passes t < fuel →
      (∀ n ∈ t, n ∉ p → rank pass.name < rank n) →
      ∃ t' p', visit passes pass fuel t p = .ok (t', p') ∧ (∀ n ∈ t, n ∈ t') ∧ (∀ n ∈ p, n ∈ p') ∧
        ∀ n ∈ t', n ∈ t ∨ n ∈ p' := by
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ihv =>
    intro pass t p hmem hfuel hstack
    rw [visit_succ]
    split
    · exact ⟨t, p, rfl, fun _ h => h, fun _ h => h, fun _ h => .inl h⟩
    · rename_i hp
      split
      · rename_i ht
        exact absurd (hstack _ ht hp) (Nat.lt_irrefl _)
      · rename_i ht
        have hlt : unvisited passes (pass.name :: t) < fuel := by
          have := unvisited_cons_lt hmem ht
          omega
        have fold : ∀ (deps : List String) (cur perm : List String),
            (∀ d ∈ deps, d ∈ pass.dependencies) → (∀ n ∈ pass.name :: t, n ∈ cur) →
            (∀ n ∈ p, n ∈ perm) → (∀ n ∈ cur, n ∈ pass.name :: t ∨ n ∈ perm) →
            ∃ t' p', deps.foldlM (depStep passes pass fuel) (cur, perm) = .ok (t', p') ∧
              (∀ n ∈ cur, n ∈ t') ∧ (∀ n ∈ perm, n ∈ p') ∧
              ∀ n ∈ t', n ∈ pass.name :: t ∨ n ∈ p' := by
          intro deps
          induction deps with
          | nil =>
            intro cur perm _ _ _ hnew
            exact ⟨cur, perm, rfl, fun _ h => h, fun _ h => h, hnew⟩
          | cons d rest ihd =>
            intro cur perm hsub hcur hperm hnew
            have hd := hsub d List.mem_cons_self
            obtain ⟨hex, hlow⟩ := hrank pass hmem d hd
            obtain ⟨dp, hfind⟩ := find_exists hex
            have hdn : dp.name = d := by simpa using List.find?_some hfind
            have hstep := ihv dp cur perm (List.mem_of_find?_eq_some hfind)
              (Nat.lt_of_le_of_lt (unvisited_le_of_subset passes hcur) hlt) (by
                intro n hn hnp
                rw [hdn]
                rcases hnew n hn with h | h
                · rcases List.mem_cons.mp h with rfl | h
                  · exact hlow
                  · exact Nat.lt_trans hlow (hstack n h fun hm => hnp (hperm n hm))
                · exact absurd h hnp)
            obtain ⟨t1, p1, hv, ht1, hp1, hn1⟩ := hstep
            obtain ⟨t2, p2, hf, ht2, hp2, hn2⟩ := ihd t1 p1
              (fun e he => hsub e (List.mem_cons_of_mem _ he))
              (fun n hn => ht1 n (hcur n hn))
              (fun n hn => hp1 n (hperm n hn))
              (by
                intro n hn
                rcases hn1 n hn with h | h
                · rcases hnew n h with h | h
                  · exact .inl h
                  · exact .inr (hp1 n h)
                · exact .inr h)
            refine ⟨t2, p2, ?_, fun n hn => ht2 n (ht1 n hn), fun n hn => hp2 n (hp1 n hn), hn2⟩
            simp only [List.foldlM_cons, bind, Except.bind, depStep, hfind, hv]
            exact hf
        obtain ⟨t2, p2, hf, h1, h2, h3⟩ := fold pass.dependencies (pass.name :: t) p
          (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => .inl h)
        refine ⟨t2, pass.name :: p2, by simp [hf, Except.bind],
          fun n hn => h1 n (List.mem_cons_of_mem _ hn),
          fun n hn => List.mem_cons_of_mem _ (h2 n hn), fun n hn => ?_⟩
        rcases h3 n hn with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact .inr List.mem_cons_self
          · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

private theorem visit_of_permanent (passes : List Pass) (pass : Pass) (fuel : Nat) (t p : List String)
    (h : pass.name ∈ p) : visit passes pass (fuel + 1) t p = .ok (t, p) := by
  simp [visit, h]

private theorem lookup_or_earlier (done : List Pass) (pass : Pass) (rest : List Pass) :
    lookupPass (done ++ pass :: rest) pass.name = some pass ∨ ∃ c ∈ done, c.name = pass.name := by
  cases hd : lookupPass done pass.name with
  | some c =>
    obtain ⟨hn, hm, _⟩ := lookupPass_canonical hd
    exact .inr ⟨c, hm, hn⟩
  | none =>
    left
    simp only [lookupPass] at hd ⊢
    rw [List.find?_append, hd]
    simp

/-- Facts about the name order produced by the scheduler. -/
structure OrderPost (passes : List Pass) (p p' : List String) : Prop where
  suffix : p <:+ p'
  closed : Closed passes p → Closed passes p'
  nodup : p.Nodup → p'.Nodup
  known : ∀ n ∈ p', n ∈ p ∨ ∃ q ∈ passes, q.name = n

private theorem sortAux_post (passes remaining : List Pass) :
    ∀ (done : List Pass) (ordered out : List String), passes = done ++ remaining →
      (∀ c ∈ done, c.name ∈ ordered) →
      sortPassesAux passes remaining ordered = .ok out →
      OrderPost passes ordered out ∧ ∀ c ∈ passes, c.name ∈ out := by
  induction remaining with
  | nil =>
    intro done ordered out hp hd h
    simp only [sortPassesAux, Except.ok.injEq] at h
    subst h
    refine ⟨⟨List.suffix_refl _, id, id, fun _ h => .inl h⟩, fun c hc => hd c ?_⟩
    simpa [hp] using hc
  | cons pass rest ih =>
    intro done ordered out hp hd h
    simp only [sortPassesAux, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i res hres
      obtain ⟨t1, p1⟩ := res
      -- `pass` either canonical (traversal spec) or its name is already permanent
      have hstep : OrderPost passes ordered p1 ∧ pass.name ∈ p1 := by
        rw [hp] at hres
        have hor := lookup_or_earlier done pass rest
        rcases hor with hc | ⟨c, hc, hn⟩
        · rw [← hp] at hres hc
          obtain ⟨post, hm⟩ := traversal_spec passes _ _ _ _ _ _ hc hres
          exact ⟨⟨post.suffix, post.closed, post.nodup, post.known⟩, hm⟩
        · have hmem : pass.name ∈ ordered := hn ▸ hd c hc
          rw [← hp, visit_of_permanent _ _ _ _ _ hmem] at hres
          simp only [Except.ok.injEq, Prod.mk.injEq] at hres
          obtain ⟨_, rfl⟩ := hres
          exact ⟨⟨List.suffix_refl _, id, id, fun _ h => .inl h⟩, hmem⟩
      obtain ⟨post, hm⟩ := hstep
      obtain ⟨post2, hall⟩ := ih (done ++ [pass]) p1 out (by simpa [List.append_assoc] using hp)
        (by
          intro c hc
          rcases List.mem_append.mp hc with hc | hc
          · exact post.suffix.subset (hd c hc)
          · have : c = pass := by simpa using hc
            rw [this]; exact hm) h
      refine ⟨⟨post.suffix.trans post2.suffix, post2.closed ∘ post.closed, post2.nodup ∘ post.nodup, ?_⟩, hall⟩
      intro n hn
      rcases post2.known n hn with h1 | h1
      · exact post.known n h1
      · exact .inr h1

private theorem sortAux_result {passes : List Pass} {out : List String}
    (h : sortPassesAux passes passes [] = .ok out) :
    Closed passes out ∧ out.Nodup ∧ (∀ n ∈ out, ∃ q ∈ passes, q.name = n) ∧
      ∀ c ∈ passes, c.name ∈ out := by
  obtain ⟨post, hall⟩ := sortAux_post passes passes [] [] out rfl (by simp) h
  refine ⟨post.closed trivial, post.nodup List.nodup_nil, fun n hn => ?_, hall⟩
  rcases post.known n hn with h1 | h1
  · cases h1
  · exact h1

private theorem filterMap_lookup_names (passes : List Pass) (names : List String)
    (hk : ∀ n ∈ names, ∃ q ∈ passes, q.name = n) :
    (names.filterMap fun name => passes.find? fun pass => pass.name = name).map Pass.name = names := by
  induction names with
  | nil => rfl
  | cons n rest ih =>
    obtain ⟨q, hq, hqn⟩ := hk n List.mem_cons_self
    have hsome : (lookupPass passes n).isSome := by
      simp only [lookupPass, List.find?_isSome]
      exact ⟨q, hq, by simpa using hqn⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    have hcn := (lookupPass_canonical hc).1
    have hc' : (passes.find? fun pass => decide (pass.name = n)) = some c := hc
    simp only [List.filterMap_cons, hc', List.map_cons, hcn]
    rw [ih fun m hm => hk m (List.mem_cons_of_mem _ hm)]

private theorem filterMap_topological (passes : List Pass) (names : List String)
    (hk : ∀ n ∈ names, ∃ q ∈ passes, q.name = n) (hc : Closed passes names) :
    ∀ (u v : List Pass) (pass : Pass),
      (names.filterMap fun name => passes.find? fun pass => pass.name = name) = u ++ pass :: v →
      ∀ d ∈ pass.dependencies, ∃ q ∈ v, q.name = d := by
  induction names with
  | nil =>
    intro u v pass h
    simp at h
  | cons n rest ih =>
    intro u v pass h d hd
    have hkrest : ∀ m ∈ rest, ∃ q ∈ passes, q.name = m := fun m hm => hk m (List.mem_cons_of_mem _ hm)
    obtain ⟨q, hq, hqn⟩ := hk n List.mem_cons_self
    have hsome : (lookupPass passes n).isSome := by
      simp only [lookupPass, List.find?_isSome]
      exact ⟨q, hq, by simpa using hqn⟩
    obtain ⟨c, hcfind⟩ := Option.isSome_iff_exists.mp hsome
    have hc' : (passes.find? fun pass => decide (pass.name = n)) = some c := hcfind
    simp only [List.filterMap_cons, hc'] at h
    cases u with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmem := hc.1 _ hcfind d hd
      have hnames := filterMap_lookup_names passes rest hkrest
      rw [← hnames] at hmem
      simp only [List.mem_map] at hmem
      exact hmem
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact ih hkrest hc.2 tail v pass h.2 d hd

/-- Every scheduled pass comes from the input, and is the canonical pass of its name. -/
theorem sortPasses_sound {passes sorted : List Pass} (h : sortPasses passes = .ok sorted)
    {pass : Pass} (hp : pass ∈ sorted) : pass ∈ passes ∧ lookupPass passes pass.name = some pass := by
  simp only [sortPasses, bind, Except.bind] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [List.mem_reverse, List.mem_filterMap] at hp
    obtain ⟨n, _, hn⟩ := hp
    obtain ⟨_, hm, hc⟩ := lookupPass_canonical hn
    exact ⟨hm, hc⟩

/-- Every input pass name gets scheduled. -/
theorem sortPasses_complete {passes sorted : List Pass} (h : sortPasses passes = .ok sorted)
    {pass : Pass} (hp : pass ∈ passes) : ∃ q ∈ sorted, q.name = pass.name := by
  simp only [sortPasses, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i out hout
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨_, _, hk, hall⟩ := sortAux_result hout
    have hmem := hall pass hp
    have hnames := filterMap_lookup_names passes out hk
    rw [← hnames] at hmem
    simpa only [List.mem_map, List.mem_reverse] using hmem

/-- Each name is scheduled exactly once. -/
theorem sortPasses_names_nodup {passes sorted : List Pass} (h : sortPasses passes = .ok sorted) :
    (sorted.map Pass.name).Nodup := by
  simp only [sortPasses, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i out hout
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨_, hn, hk, _⟩ := sortAux_result hout
    rw [List.map_reverse, filterMap_lookup_names passes out hk]
    simpa [List.Nodup, List.pairwise_reverse, ne_comm] using hn

/-- Topological order: dependencies of a scheduled pass are scheduled strictly before it. -/
theorem sortPasses_topological {passes sorted before after : List Pass} {pass : Pass}
    (h : sortPasses passes = .ok sorted) (hs : sorted = before ++ pass :: after) :
    ∀ d ∈ pass.dependencies, ∃ q ∈ before, q.name = d := by
  simp only [sortPasses, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i out hout
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨hc, _, hk, _⟩ := sortAux_result hout
    have hrev : (out.filterMap fun name => passes.find? fun pass => pass.name = name) =
        after.reverse ++ pass :: before.reverse := by
      have := congrArg List.reverse hs
      simpa using this
    intro d hd
    obtain ⟨q, hq, hn⟩ := filterMap_topological passes out hk hc _ _ _ hrev d hd
    exact ⟨q, by simpa using hq, hn⟩

/-- Consequently a successful schedule contains no self-dependent pass. -/
theorem sortPasses_no_self_dependency {passes sorted : List Pass} (h : sortPasses passes = .ok sorted)
    {pass : Pass} (hp : pass ∈ sorted) : pass.name ∉ pass.dependencies := by
  intro hself
  obtain ⟨before, after, hs⟩ := List.append_of_mem hp
  obtain ⟨q, hq, hn⟩ := sortPasses_topological h hs _ hself
  have hnd := sortPasses_names_nodup h
  rw [hs, List.map_append, List.map_cons] at hnd
  exact (List.nodup_append.mp hnd).2.2 _ (List.mem_map.mpr ⟨q, hq, hn⟩) _ List.mem_cons_self rfl

theorem visit_missing_dependency (passes : List Pass) (pass : Pass) (fuel : Nat) (t p : List String)
    (d : String) (rest : List String) (hdeps : pass.dependencies = d :: rest)
    (hp : pass.name ∉ p) (ht : pass.name ∉ t) (hmissing : lookupPass passes d = none) :
    visit passes pass (fuel + 1) t p = .error (.missingDependency pass.name d) := by
  have hm : (passes.find? fun candidate => decide (candidate.name = d)) = none := hmissing
  simp [visit_succ, hp, ht, hdeps, List.foldlM_cons, depStep, hm, bind, Except.bind]

theorem visit_self_cycle (passes : List Pass) (pass : Pass) (fuel : Nat) (t p : List String)
    (rest : List String) (hdeps : pass.dependencies = pass.name :: rest)
    (hc : lookupPass passes pass.name = some pass) (hp : pass.name ∉ p) (ht : pass.name ∉ t) :
    visit passes pass (fuel + 2) t p = .error (.cycle pass.name) := by
  have hc' : (passes.find? fun candidate => decide (candidate.name = pass.name)) = some pass := hc
  simp [visit_succ, hp, ht, hdeps, List.foldlM_cons, depStep, hc', bind, Except.bind]

private theorem sortAux_acyclic_ok {passes : List Pass} {rank : String → Nat}
    (hrank : ∀ p ∈ passes, ∀ d ∈ p.dependencies, (∃ q ∈ passes, q.name = d) ∧ rank d < rank p.name)
    (remaining : List Pass) :
    (∀ pass ∈ remaining, pass ∈ passes) → ∀ ordered : List String,
      ∃ out, sortPassesAux passes remaining ordered = .ok out := by
  induction remaining with
  | nil => exact fun _ ordered => ⟨ordered, by simp [sortPassesAux]⟩
  | cons pass rest ih =>
    intro hsub ordered
    have hlen : unvisited passes [] < passes.length + 1 := by
      simp only [unvisited]
      have := List.length_filter_le (· ∉ ([] : List String)) (passes.map Pass.name)
      simp only [List.length_map] at this
      omega
    obtain ⟨t', p', hv, -, -, -⟩ := visit_acyclic_ok hrank (passes.length + 1) pass [] ordered
      (hsub pass List.mem_cons_self) hlen (by simp)
    obtain ⟨out, hout⟩ := ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) p'
    exact ⟨out, by simp only [sortPassesAux, bind, Except.bind, hv]; exact hout⟩

/-- Every acyclic pass set with its dependencies present schedules, regardless of listing order
or of how many passes share a dependency. -/
theorem sortPasses_acyclic_ok {passes : List Pass} (h : Acyclic passes) :
    (sortPasses passes).isOk = true := by
  obtain ⟨rank, hrank⟩ := h
  obtain ⟨out, hout⟩ := sortAux_acyclic_ok hrank passes (fun _ h => h) []
  simp [sortPasses, hout, bind, Except.bind, Except.isOk, Except.toBool]

/-- The scheduler's fuel error is unreachable: its budget exceeds the names of the input. -/
theorem sortPasses_never_exhausted (passes : List Pass) :
    sortPasses passes ≠ .error fuelError := by
  have aux : ∀ (remaining : List Pass), (∀ pass ∈ remaining, pass ∈ passes) → ∀ ordered,
      sortPassesAux passes remaining ordered ≠ .error fuelError := by
    intro remaining
    induction remaining with
    | nil => intro _ ordered; simp [sortPassesAux]
    | cons pass rest ih =>
      intro hsub ordered
      have hlen : unvisited passes [] < passes.length + 1 := by
        simp only [unvisited]
        have := List.length_filter_le (· ∉ ([] : List String)) (passes.map Pass.name)
        simp only [List.length_map] at this
        omega
      have hv := visit_never_exhausted passes _ pass [] ordered (hsub pass List.mem_cons_self) hlen
      simp only [sortPassesAux, bind, Except.bind]
      split
      · rename_i e he
        intro heq
        cases heq
        exact hv he
      · exact ih (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) _
  simp only [sortPasses, bind, Except.bind]
  split
  · rename_i e he
    intro heq
    cases heq
    exact aux passes (fun _ h => h) [] he
  · simp

/-- Under `runPasses`, a success means every input pass name is marked when no pass drops marks. -/
theorem runPasses_marks_all {passes : List Pass} {project out : Project}
    (hkeep : ∀ pass ∈ passes, ∀ p q, pass.run p = .ok q → ∀ n ∈ p.passed, n ∈ q.passed)
    (h : runPasses passes project = .ok out) :
    ∀ pass ∈ passes, pass.name ∈ out.passed := by
  rw [runPasses_unfold] at h
  cases hs : sortPasses passes with
  | error e => simp [hs, Except.bind] at h
  | ok sorted =>
    have hrun : runAll sorted project = .ok out := by simpa [hs, Except.bind] using h
    have hmarks := (runAll_marks_all sorted
      (fun q hq => hkeep q (sortPasses_sound hs hq).1) project out hrun).2
    intro pass hp
    obtain ⟨q, hq, hn⟩ := sortPasses_complete hs hp
    rw [← hn]
    exact hmarks q hq

/-- `runPasses` applies the fold of the sorted schedule, so a scheduler failure means no pass ran. -/
theorem runPasses_sort_error {passes : List Pass} {error : PassError} (project : Project)
    (h : sortPasses passes = .error error) : runPasses passes project = .error error := by
  rw [runPasses_unfold, h]
  rfl

end Scheduler

section Chains

open_private Bap.Project.Pass in Bap.Project : runPass sortPasses

/-- A sequence that all succeeds when every pass it holds does. -/
private theorem runAll_ok (sorted : List Pass) (hrun : ∀ q ∈ sorted, ∀ project, ∃ out, q.run project = .ok out) :
    ∀ project, ∃ out, runAll sorted project = .ok out := by
  induction sorted with
  | nil => exact fun project => ⟨project, rfl⟩
  | cons q rest ih =>
    intro project
    have hstep : ∃ mid, runPass q project = .ok mid := by
      by_cases hc : q.runonce = true ∧ q.name ∈ project.passed
      · exact ⟨project, runPass_skip q project hc.1 hc.2⟩
      · obtain ⟨inner, hinner⟩ := hrun q List.mem_cons_self project
        refine ⟨inner.markPassed q.name, runPass_fresh q project inner hinner ?_⟩
        cases hq : q.runonce with
        | false => exact .inl rfl
        | true => exact .inr fun hm => hc ⟨hq, hm⟩
    obtain ⟨mid, hmid⟩ := hstep
    obtain ⟨out, hout⟩ := ih (fun x hx => hrun x (List.mem_cons_of_mem _ hx)) mid
    exact ⟨out, by simp only [runAll, List.foldlM_cons, bind, Except.bind, hmid]; exact hout⟩

/-- Acyclic passes that cannot fail always run to completion: scheduling adds no failure. -/
theorem runPasses_acyclic_ok {passes : List Pass} (h : Acyclic passes)
    (hrun : ∀ q ∈ passes, ∀ project, ∃ out, q.run project = .ok out) (project : Project) :
    ∃ out, runPasses passes project = .ok out := by
  have hok := sortPasses_acyclic_ok h
  cases hs : sortPasses passes with
  | error e => simp [hs, Except.isOk, Except.toBool] at hok
  | ok sorted =>
    obtain ⟨out, hout⟩ := runAll_ok sorted (fun q hq => hrun q (sortPasses_sound hs hq).1) project
    refine ⟨out, ?_⟩
    rw [runPasses_unfold, hs]
    exact hout

/-- The chain in which each pass depends on the next, and each also on `base`. -/
def chainPasses (base : List String) : List String → List Pass
  | [] => []
  | [last] => [{ name := last, dependencies := base, run := .ok }]
  | name :: next :: rest =>
    { name, dependencies := base ++ [next], run := .ok } :: chainPasses base (next :: rest)

private theorem chain_mem {base : List String} {names : List String} {p : Pass}
    (h : p ∈ chainPasses base names) :
    p.name ∈ names ∧ p.run = .ok ∧ ∀ d ∈ p.dependencies, d ∈ base ∨ d ∈ names := by
  induction names using chainPasses.induct generalizing p with
  | case1 => simp [chainPasses] at h
  | case2 last =>
    simp only [chainPasses, List.mem_singleton] at h
    subst h
    exact ⟨List.mem_singleton.mpr rfl, rfl, fun d hd => .inl hd⟩
  | case3 name next rest ih =>
    simp only [chainPasses, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨List.mem_cons_self, rfl, fun d hd => ?_⟩
      rcases List.mem_append.mp hd with hd | hd
      · exact .inl hd
      · have : d = next := by simpa using hd
        exact .inr (by simp [this])
    · obtain ⟨hn, hr, hd⟩ := ih (by simpa [List.mem_cons] using h)
      refine ⟨List.mem_cons_of_mem _ hn, hr, fun d hmem => ?_⟩
      rcases hd d hmem with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

private theorem chain_head_mem (base : List String) (name : String) (rest : List String) :
    ∃ q ∈ chainPasses base (name :: rest), q.name = name := by
  cases rest <;> simp [chainPasses]

/-- A chain of any length over distinct names, however many of its passes share the base passes,
schedules. (Base passes come first in the input and depend on nothing.) -/
theorem chain_acyclic (base names : List String) (hn : names.Nodup)
    (hb : ∀ d ∈ base, d ∉ names) :
    Acyclic (base.map (fun name => ({ name, run := .ok } : Pass)) ++ chainPasses base names) := by
  have key : ∀ names : List String, names.Nodup → (∀ d ∈ base, d ∉ names) →
      ∃ rank : String → Nat, (∀ d ∈ base, rank d = 0) ∧
        ∀ p ∈ chainPasses base names, 0 < rank p.name ∧ ∀ d ∈ p.dependencies,
          (d ∈ base ∨ ∃ q ∈ chainPasses base names, q.name = d) ∧ rank d < rank p.name := by
    intro names
    induction names using chainPasses.induct with
    | case1 => exact fun _ _ => ⟨fun _ => 0, fun _ _ => rfl, by simp [chainPasses]⟩
    | case2 last =>
      intro _ hb
      refine ⟨fun x => if x = last then 1 else 0, fun d hd => ?_, ?_⟩
      · have : d ≠ last := fun h => hb d hd (by simp [h])
        simp [this]
      · intro p hp
        simp only [chainPasses, List.mem_singleton] at hp
        subst hp
        refine ⟨by simp, fun d hd => ⟨.inl hd, ?_⟩⟩
        have : d ≠ last := fun h => hb d hd (by simp [h])
        simp [this]
    | case3 name next rest ih =>
      intro hnd hb
      have htail : (next :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have hname : name ∉ next :: rest := (List.nodup_cons.mp hnd).1
      obtain ⟨r, hr0, hr⟩ := ih htail (fun d hd hm => hb d hd (List.mem_cons_of_mem _ hm))
      have hnb : ∀ d ∈ base, d ≠ name := fun d hd h => hb d hd (by simp [h])
      have hnext_pos : 0 < r next := by
        obtain ⟨q, hq, hqn⟩ := chain_head_mem base next rest
        have := (hr q hq).1
        rwa [hqn] at this
      refine ⟨fun x => if x = name then r next + 1 else r x, fun d hd => ?_, ?_⟩
      · simp [hnb d hd, hr0 d hd]
      · have hnotname : ∀ x ∈ next :: rest, x ≠ name := fun x hx h => hname (h ▸ hx)
        intro p hp
        simp only [chainPasses, List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨by simp, fun d hd => ?_⟩
          simp only [ite_true]
          rcases List.mem_append.mp hd with hd | hd
          · refine ⟨.inl hd, ?_⟩
            simp [hnb d hd, hr0 d hd]
          · have hde : d = next := by simpa using hd
            subst hde
            refine ⟨.inr ?_, ?_⟩
            · obtain ⟨q, hq, hqn⟩ := chain_head_mem base d rest
              exact ⟨q, by simp only [chainPasses]; exact List.mem_cons_of_mem _ hq, hqn⟩
            · have : d ≠ name := hnotname d List.mem_cons_self
              simp [this]
        · have hp' : p ∈ chainPasses base (next :: rest) := by simpa [List.mem_cons] using hp
          obtain ⟨hpos, hdeps⟩ := hr p hp'
          have hpn : p.name ≠ name := hnotname _ (chain_mem hp').1
          simp only [hpn, ite_false]
          refine ⟨hpos, fun d hd => ?_⟩
          obtain ⟨hmem, hlt⟩ := hdeps d hd
          have hdn : d ≠ name := by
            rcases (chain_mem hp').2.2 d hd with h | h
            · exact hnb d h
            · exact hnotname d h
          simp only [hdn, ite_false]
          refine ⟨?_, hlt⟩
          rcases hmem with h | ⟨q, hq, hqn⟩
          · exact .inl h
          · exact .inr ⟨q, by simp only [chainPasses]; exact List.mem_cons_of_mem _ hq, hqn⟩
  obtain ⟨rank, hr0, hr⟩ := key names hn hb
  refine ⟨rank, fun p hp d hd => ?_⟩
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hp
    simp at hd
  · obtain ⟨hmem, hlt⟩ := (hr p hp).2 d hd
    refine ⟨?_, hlt⟩
    rcases hmem with h | ⟨q, hq, hqn⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem h), rfl⟩
    · exact ⟨q, List.mem_append_right _ hq, hqn⟩

/-- Regression for the fuel failure: the chain sharing a base dependency runs to completion. -/
theorem runPasses_chain_ok (base names : List String) (hn : names.Nodup)
    (hb : ∀ d ∈ base, d ∉ names) (project : Project) :
    ∃ out, runPasses (base.map (fun name => ({ name, run := .ok } : Pass)) ++ chainPasses base names) project
      = .ok out := by
  refine runPasses_acyclic_ok (chain_acyclic base names hn hb) (fun q hq project => ?_) project
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨project, rfl⟩
  · exact ⟨project, by rw [(chain_mem hq).2.1]⟩

/-- The concrete input that used to report fuel exhaustion, in the order that used to fail. -/
theorem runPasses_six_pass_chain :
    ((runPasses (chainPasses ["a"] ["p0", "p1", "p2", "p3", "p4"] ++ [{ name := "a", run := .ok }]) {}).toOption.map
      Project.passed) = some ["p0", "p1", "p2", "p3", "p4", "a"] := by
  rfl

end Chains


section Persist

open Bap.Binary Bap.Proofs.Binary

open_private Bap.Project.Persist in Bap.Project :
  archCode archOf? putSection getSection putSegment getSegment putSymbol getSymbol putRegion getRegion putImage getImage
  flowCode flowOf? tablesOf putInsn getInsn putInsns putEdge getEdge putDisasm getDisasm disasmFits putBinding getBinding
  magic putProject getProject

private theorem getSection_put (data : ByteArray) (value : Bap.Image.Section) : Reads (getSection data) putSection data value := by
  intro out h
  obtain ⟨name, addr, offset, size, flags, kind⟩ := value
  simp only [putSection] at h ⊢
  obtain ⟨h5, r5⟩ := getNat_putNat h
  obtain ⟨h4, r4⟩ := getNat_putNat h5
  obtain ⟨h3, r3⟩ := getNat_putNat h4
  obtain ⟨h2, r2⟩ := getNat_putNat h3
  obtain ⟨h1, r1⟩ := getNat_putNat h2
  obtain ⟨hp, hr⟩ := getText_putText h1
  exact ⟨hp, by simp only [getSection, hr, r1, r2, r3, r4, r5, bind, Option.bind]⟩

private theorem getSegment_put (data : ByteArray) (value : Bap.Image.Segment) : Reads (getSegment data) putSegment data value := by
  intro out h
  obtain ⟨name, addr, size, readable, writable, executable⟩ := value
  simp only [putSegment] at h ⊢
  obtain ⟨h5, r5⟩ := getBool_putBool h
  obtain ⟨h4, r4⟩ := getBool_putBool h5
  obtain ⟨h3, r3⟩ := getBool_putBool h4
  obtain ⟨h2, r2⟩ := getNat_putNat h3
  obtain ⟨h1, r1⟩ := getNat_putNat h2
  obtain ⟨hp, hr⟩ := getText_putText h1
  exact ⟨hp, by simp only [getSegment, hr, r1, r2, r3, r4, r5, bind, Option.bind]⟩

private theorem getSymbol_put (data : ByteArray) (value : Bap.Image.Symbol) : Reads (getSymbol data) putSymbol data value := by
  intro out h
  obtain ⟨name, addr, size, isFunction, isDebug, thumb⟩ := value
  simp only [putSymbol] at h ⊢
  obtain ⟨h5, r5⟩ := getBool_putBool h
  obtain ⟨h4, r4⟩ := getBool_putBool h5
  obtain ⟨h3, r3⟩ := getBool_putBool h4
  obtain ⟨h2, r2⟩ := getNat_putNat h3
  obtain ⟨h1, r1⟩ := getNat_putNat h2
  obtain ⟨hp, hr⟩ := getText_putText h1
  exact ⟨hp, by simp only [getSymbol, hr, r1, r2, r3, r4, r5, bind, Option.bind]⟩

private theorem getRegion_put (data : ByteArray) (value : Bap.Image.MemRegion) : Reads (getRegion data) putRegion data value := by
  intro out h
  obtain ⟨addr, bytes, readable, writable, executable⟩ := value
  simp only [putRegion] at h ⊢
  obtain ⟨h4, r4⟩ := getBool_putBool h
  obtain ⟨h3, r3⟩ := getBool_putBool h4
  obtain ⟨h2, r2⟩ := getBool_putBool h3
  obtain ⟨h1, r1⟩ := getBytes_putBytes h2
  obtain ⟨hp, hr⟩ := getNat_putNat h1
  exact ⟨hp, by simp only [getRegion, hr, r1, r2, r3, r4, bind, Option.bind]⟩

private theorem archOf_code (arch : Bap.Image.Arch) : archOf? (archCode arch) = some arch := by cases arch <;> rfl
private theorem flowOf_code (flow : Bap.Disasm.Flow) : flowOf? (flowCode flow) = some flow := by cases flow <;> rfl

private theorem entries_regions (entries : List (Bap.Image.MemRegion × Unit)) :
    (entries.map Prod.fst).map (·, ()) = entries := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    simpa only [List.map_cons, List.cons.injEq, true_and] using ih

private theorem getImage_put (data : ByteArray) (value : Bap.Image.Image) : Reads (getImage data) putImage data value := by
  intro out h
  obtain ⟨arch, addrWidth, endian, entryPoint, bytes, sections, segments, symbols, ⟨entries⟩⟩ := value
  simp only [putImage] at h ⊢
  obtain ⟨h8, r8⟩ := getList_putList (fun item _ => getRegion_put data item) h
  obtain ⟨h7, r7⟩ := getList_putList (fun item _ => getSymbol_put data item) h8
  obtain ⟨h6, r6⟩ := getList_putList (fun item _ => getSegment_put data item) h7
  obtain ⟨h5, r5⟩ := getList_putList (fun item _ => getSection_put data item) h6
  obtain ⟨h4, r4⟩ := getBytes_putBytes h5
  obtain ⟨h3, r3⟩ := getNat_putNat h4
  obtain ⟨h2, r2⟩ := getEndian_putEndian h3
  obtain ⟨h1, r1⟩ := getNat_putNat h2
  obtain ⟨hp, hr⟩ := getNat_putNat h1
  exact ⟨hp, by simp only [getImage, hr, r1, r2, r3, r4, r5, r6, r7, r8, archOf_code, entries_regions, bind, Option.bind]⟩

private theorem beq_text (first second : String) (h : (first == second) = true) : first = second := by
  simpa using h

private theorem beq_program (first second : Bap.Bil.Program) (h : (first == second) = true) : first = second :=
  Bap.Bil.Stmt.sameAll_eq first second h

private theorem getProgram_put (vars : Table Bap.Var) (data : ByteArray) {value : Bap.Bil.Program} (hd : stmtsDepth value ≤ maxDepth) :
    Reads (getProgram vars.items data) (putProgram vars) data value := by
  intro out h
  simp only [putProgram, putStmts_list] at h ⊢
  exact getStmts_putStmts vars data value hd h

private theorem getInsn_put (tables : Tables) (number : Nat) (data : ByteArray) {value : Bap.Disasm.Insn} (hd : stmtsDepth value.bil ≤ maxDepth) :
    Reads (getInsn tables.vars.items tables.programs.items tables.texts.items data) (putInsn tables number) data value := by
  intro out h
  obtain ⟨address, size, asm, flow, target, bil⟩ := value
  simp only [putInsn] at h ⊢
  obtain ⟨h5, r5⟩ := getRef_putAt beq_program (getProgram_put tables.vars data hd) h
  obtain ⟨h4, r4⟩ := getOption_putOption (fun item _ out h => getNat_putNat h) h5
  obtain ⟨h3, r3⟩ := getNat_putNat h4
  obtain ⟨h2, r2⟩ := getRef_putAt beq_text (fun _ h => getText_putText h) h3
  obtain ⟨h1, r1⟩ := getNat_putNat h2
  obtain ⟨hp, hr⟩ := getNat_putNat h1
  exact ⟨hp, by simp only [getInsn, hr, r1, r2, r3, r4, r5, flowOf_code, bind, Option.bind]⟩

private theorem getItems_putInsns (tables : Tables) (data : ByteArray) {items : List Bap.Disasm.Insn}
    (hd : ∀ insn ∈ items, stmtsDepth insn.bil ≤ maxDepth) :
    ∀ (out : ByteArray) (number : Nat) (done : Array Bap.Disasm.Insn), Prefix (putInsns tables out items number) data →
      Prefix out data ∧ getItems (getInsn tables.vars.items tables.programs.items tables.texts.items data) items.length out.size done =
        some (done ++ items.toArray, (putInsns tables out items number).size) := by
  induction items with
  | nil =>
    intro out number done h
    exact ⟨h, by simp [putInsns, getItems]⟩
  | cons item rest ih =>
    intro out number done h
    simp only [putInsns] at h ⊢
    obtain ⟨hp, hr⟩ := ih (fun other hm => hd other (List.mem_cons_of_mem _ hm)) _ _ (done.push item) h
    obtain ⟨hq, hg⟩ := getInsn_put tables number data (hd item List.mem_cons_self) _ hp
    refine ⟨hq, ?_⟩
    simp [getItems, hg, hr]

private theorem getEdge_put (data : ByteArray) (value : Nat × Nat) : Reads (getEdge data) putEdge data value := by
  intro out h
  obtain ⟨source, target⟩ := value
  simp only [putEdge] at h ⊢
  obtain ⟨h1, r1⟩ := getNat_putNat h
  obtain ⟨hp, hr⟩ := getNat_putNat h1
  exact ⟨hp, by simp only [getEdge, hr, r1, bind, Option.bind]⟩

private theorem getDisasm_put (tables : Tables) (data : ByteArray) {value : Bap.Disasm.Disasm} (hfit : disasmFits tables value = true) :
    Reads (getDisasm data) (putDisasm tables) data value := by
  intro out h
  obtain ⟨entry, instructions, edges, errors⟩ := value
  simp only [disasmFits, Bool.and_eq_true, Array.all_eq_true, List.all_eq_true, decide_eq_true_eq] at hfit
  obtain ⟨hitems, hinsns⟩ := hfit
  simp only [putDisasm] at h ⊢
  obtain ⟨h6, r6⟩ := getList_putList (fun item _ out h => getText_putText h) h
  obtain ⟨h5, r5⟩ := getList_putList (fun item _ => getEdge_put data item) h6
  obtain ⟨h4', r4⟩ := getItems_putInsns tables data hinsns _ _ #[] h5
  obtain ⟨h4, r4n⟩ := getNat_putNat h4'
  have r4l : getList (getInsn tables.vars.items tables.programs.items tables.texts.items data) data
      (putList putText (putList (putProgram tables.vars) (putList putVar (putNat out entry) tables.vars.items.toList) tables.programs.items.toList) tables.texts.items.toList).size =
      some (instructions, (putInsns tables (putNat (putList putText (putList (putProgram tables.vars) (putList putVar (putNat out entry) tables.vars.items.toList) tables.programs.items.toList) tables.texts.items.toList) instructions.length) instructions 0).size) := by
    simp [getList, getArray, r4n, r4]
  obtain ⟨h3, r3⟩ := getArray_putList (fun item _ out h => getText_putText h) h4
  obtain ⟨h2, r2⟩ := getArray_putList (fun item hm => getProgram_put tables.vars data (by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    simp only [Array.getElem_toList]
    exact hitems i (by simpa using hi))) h3
  obtain ⟨h1, r1⟩ := getArray_putList (fun item _ out h => getVar_putVar h) h2
  obtain ⟨hp, hr⟩ := getNat_putNat h1
  refine ⟨hp, ?_⟩
  simp only [Array.toArray_toList] at r1 r2 r3
  simp only [getDisasm, hr, r1, r2, r3, r4l, r5, r6, bind, Option.bind]

private theorem getBinding_put (data : ByteArray) (value : String × String) : Reads (getBinding data) putBinding data value := by
  intro out h
  obtain ⟨name, text⟩ := value
  simp only [putBinding] at h ⊢
  obtain ⟨h1, r1⟩ := getText_putText h
  obtain ⟨hp, hr⟩ := getText_putText h1
  exact ⟨hp, by simp only [getBinding, hr, r1, bind, Option.bind]⟩

private theorem getProject_put {project : Project} {tables : Tables} {knowledge : String}
    (hfit : (project.disasm.map (disasmFits tables)).getD true = true) :
    getProject (putProject project tables knowledge) = some ({ project with knowledge := {} }, knowledge) := by
  have h := Prefix.refl (putProject project tables knowledge)
  have hsize : (putProject project tables knowledge).size = (putProject project tables knowledge).size := rfl
  generalize hdata : putProject project tables knowledge = data at h
  obtain ⟨image, disasm, kn, storage, passed⟩ := project
  simp only [putProject] at hdata
  subst hdata
  simp only [Option.map] at hfit
  obtain ⟨h4, r4⟩ := getText_putText h
  obtain ⟨h3, r3⟩ := getList_putList (fun item _ out h => getText_putText h) h4
  obtain ⟨h2, r2⟩ := getList_putList (fun item _ => getBinding_put _ item) h3
  obtain ⟨h1, r1⟩ := getOption_putOption (fun item hi => getDisasm_put tables _ (by subst hi; simpa using hfit)) h2
  obtain ⟨h0, r0⟩ := getOption_putOption (fun item _ => getImage_put _ item) h1
  have hmagic : ∀ tail, (magic ++ tail).extract 0 magic.size = magic := fun tail => ByteArray.extract_append_eq_left rfl
  obtain ⟨tail, htail⟩ := h0
  have hm := hmagic tail
  rw [← htail] at hm
  simp [getProject, hm, r0, r1, r2, r3, r4, bind, Option.bind]

/-- **A saved project is read back whole.** Facts and opinions must live in slots of `persistent`, uniquely named: `serialize` can only check a slot's
name, and decoding a value needs the slot's own codec. -/
theorem deserialize_serialize {project : Project} {persistent : List Bap.Knowledge.AnySlot} {data : ByteArray}
    (h : serialize project persistent = .ok data)
    (hnames : (persistent.map fun slot => slot.2.name).Nodup)
    (hfacts : ∀ fact ∈ project.knowledge.facts, fact.slot ∈ persistent)
    (hopinions : ∀ opinion ∈ project.knowledge.opinions, opinion.fact.slot ∈ persistent) :
    deserialize data persistent = .ok project := by
  simp only [serialize, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i knowledge hknowledge
      by_cases hfit : (project.disasm.map (disasmFits (tablesOf ((project.disasm.map (·.instructions)).getD [])))).getD true = true
      · simp only [hfit, ↓reduceIte, Except.ok.injEq] at h
        subst h
        have hkd : Bap.Knowledge.decodeState persistent knowledge = .ok project.knowledge := by
          obtain ⟨decoded, hdec, hf, ho, hv⟩ :=
            Bap.Proofs.Knowledge.decodeState_encodeState_total hnames hfacts hopinions hknowledge
          rw [hdec]
          cases decoded
          cases hk : project.knowledge
          simp_all
        have hparse : Sexp.parse (toString knowledge) = .ok knowledge := Bap.Proofs.Core.SexpLaws.parse_render _
        simp only [deserialize, getProject_put hfit, hparse, hkd, bind, Except.bind]
      · simp only [hfit] at h
        cases h

/-- Encoding refuses a project holding a Knowledge fact whose slot is not registered. -/
theorem serialize_rejects_unregistered (project : Project) (persistent : List Bap.Knowledge.AnySlot)
    (fact : Bap.Knowledge.Fact)
    (hm : fact ∈ project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact)
    (hn : fact.slot.2.name ∉ persistent.map fun slot => slot.2.name) :
    ∃ message, serialize project persistent = .error message := by
  simp only [serialize]
  have hsome : (((project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact).find?
      fun fact => !(persistent.map fun slot => slot.2.name).contains fact.slot.2.name)).isSome := by
    rw [List.find?_isSome]
    exact ⟨fact, hm, by simpa using hn⟩
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  simp only [bind, Except.bind]
  rw [hfound]
  exact ⟨_, rfl⟩

/-- A project is refused only for what can't be read back: without Knowledge, only for code nested deeper than the reader goes. -/
theorem serialize_lossless_or_rejecting (project : Project) (hfacts : project.knowledge.facts = [])
    (hopinions : project.knowledge.opinions = []) :
    ((project.disasm.map (disasmFits (tablesOf ((project.disasm.map (·.instructions)).getD [])))).getD true = false ∧
      ∃ error, serialize project [] = .error error) ∨
      ∃ data, serialize project [] = .ok data ∧ deserialize data [] = .ok project := by
  have hk : Bap.Knowledge.encodeState [] project.knowledge = .ok (.tagged "state" [.atom (toString project.knowledge.version), .list [], .list []]) := by
    simp [Bap.Knowledge.encodeState, hfacts, hopinions, bind, Except.bind, pure, Except.pure]
  have hrun : serialize project [] =
      if (project.disasm.map (disasmFits (tablesOf ((project.disasm.map (·.instructions)).getD [])))).getD true = true then
        .ok (putProject project (tablesOf ((project.disasm.map (·.instructions)).getD []))
          (toString (Sexp.tagged "state" [.atom (toString project.knowledge.version), .list [], .list []])))
      else .error "project code is nested too deep" := by
    simp only [serialize, hfacts, hopinions, bind, Except.bind, hk]
    simp
  cases hfit : (project.disasm.map (disasmFits (tablesOf ((project.disasm.map (·.instructions)).getD [])))).getD true with
  | false => exact Or.inl ⟨rfl, "project code is nested too deep", by simp [hrun, hfit]⟩
  | true =>
    have hs : serialize project [] = .ok (putProject project (tablesOf ((project.disasm.map (·.instructions)).getD []))
        (toString (Sexp.tagged "state" [.atom (toString project.knowledge.version), .list [], .list []]))) := by
      simp only [hrun, hfit, ↓reduceIte]
    exact Or.inr ⟨_, hs, deserialize_serialize hs List.nodup_nil (by simp [hfacts]) (by simp [hopinions])⟩

/-- `save` writes exactly what `serialize` produces, and fails only as it does. -/
theorem save_eq (project : Project) (path : String) (persistent : List Bap.Knowledge.AnySlot) :
    save project path persistent = match serialize project persistent with
      | .error error => throw (IO.userError error)
      | .ok data => IO.FS.writeBinFile path data := rfl

/-- `loadSaved` returns exactly what `deserialize` makes of the file. -/
theorem loadSaved_eq (path : String) (persistent : List Bap.Knowledge.AnySlot) :
    loadSaved path persistent = (IO.FS.readBinFile path >>= fun input =>
      match deserialize input persistent with
      | .error error => throw (IO.userError error)
      | .ok project => pure project) := rfl

end Persist

/-! ## The scan of an image -/

/-- The roots of a scan of an image are the candidates that are in code. -/
theorem mem_scanRoots_iff (image : Bap.Image.Image) (address : Nat) :
    address ∈ Bap.Project.Project.scanRoots image ↔
      address ∈ (image.entryPoint :: ((image.symbols.filter (·.isFunction)).map Bap.Project.Project.symbolStart ++
        Bap.Project.Project.initFunctions image ++
        (if image.sections.isEmpty then Bap.Project.Project.pltEntries image else []) ++
        (if image.sections.any (·.name == ".symtab") then [] else Bap.Project.Project.unwindFunctions image))) ∧
      ((Bap.Project.Project.codeRegions image).map Prod.snd).any (·.contains address) = true := by
  simp only [Bap.Project.Project.scanRoots]
  generalize ((Bap.Project.Project.codeRegions image).map Prod.snd) = regions
  generalize (image.entryPoint :: ((image.symbols.filter (·.isFunction)).map Bap.Project.Project.symbolStart ++
    Bap.Project.Project.initFunctions image ++
    (if image.sections.isEmpty then Bap.Project.Project.pltEntries image else []) ++
    (if image.sections.any (·.name == ".symtab") then [] else Bap.Project.Project.unwindFunctions image))) = candidates
  have key : ∀ (l : List Nat) (seen : Std.HashSet Nat) (found : List Nat),
      (∀ a, seen.contains a = true ↔ a ∈ found) →
      (∀ a, a ∈ (l.foldl (init := (seen, found)) fun state address =>
          if state.1.contains address || !regions.any (·.contains address) then state
          else (state.1.insert address, address :: state.2)).2 ↔
        a ∈ found ∨ (a ∈ l ∧ regions.any (·.contains a) = true)) := by
    intro l
    induction l with
    | nil => intro _ _ _ a; simp
    | cons x xs ih =>
      intro seen found hs a
      simp only [List.foldl_cons]
      split
      · rename_i hc
        rw [ih _ _ hs]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl h
          · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl h
          · rcases List.mem_cons.1 h1 with rfl | h1
            · rcases Bool.or_eq_true _ _ ▸ hc with hc | hc
              · exact .inl ((hs _).1 hc)
              · rw [h2] at hc
                cases hc
            · exact .inr ⟨h1, h2⟩
      · rename_i hc
        have hc' := Bool.or_eq_false_iff.1 (Bool.eq_false_iff.2 hc)
        rw [ih _ _ (fun b => by
          rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs, List.mem_cons]
          simp only [beq_iff_eq]
          exact or_congr eq_comm Iff.rfl)]
        constructor
        · rintro (h | ⟨h1, h2⟩)
          · rcases List.mem_cons.1 h with rfl | h
            · exact .inr ⟨List.mem_cons_self, by simpa using hc'.2⟩
            · exact .inl h
          · exact .inr ⟨List.mem_cons_of_mem _ h1, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact .inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.1 h1 with rfl | h1
            · exact .inl List.mem_cons_self
            · exact .inr ⟨h1, h2⟩
  rw [List.mem_reverse, key _ _ _ (by simp)]
  simp

/-- The recursive scan of an image is sound for the decoder it goes with, and starts from all the roots of the image, and
what its sweep added. That of an ARM image goes over keys of addresses and states, whose instructions come out with addresses,
see `Interwork.unkeyAll_spec`, and the theorems of a scan apply to the keys. -/
theorem scanImage_sound (image : Bap.Image.Image) :
    Bap.Proofs.Disasm.Holds (Bap.Project.Project.scanImage image) fun result => ∀ disasm, result = some disasm →
      disasm.entry = Bap.Project.Project.entryOf image ∧ ∃ d extra keyed,
        Bap.Proofs.Disasm.ScanOk d ByteArray.empty (extra ++ Bap.Project.Project.scanRoots image) keyed.instructions keyed.edges ∧
        disasm = if image.arch = .arm then Bap.Disasm.Interwork.unkey keyed else keyed := by
  unfold Bap.Project.Project.scanImage
  refine Bap.Proofs.Disasm.Holds.bind (Bap.Proofs.Disasm.Holds.true _) fun base _ _ => ?_
  dsimp only
  split
  · exact Bap.Proofs.Disasm.Holds.pure (by simp)
  · exact Bap.Proofs.Disasm.Holds.pure (by simp)
  · refine Bap.Proofs.Disasm.Holds.bind (Bap.Proofs.Disasm.Holds.true _) fun decoders _ _ => ?_
    refine Bap.Proofs.Disasm.Holds.bind (Bap.Proofs.Disasm.scanRegions_sound _ _ _ _ _ _) fun disasm hd _ => ?_
    refine Bap.Proofs.Disasm.Holds.pure ?_
    intro _ h
    cases h
    obtain ⟨extra, hok⟩ := hd.2
    refine ⟨?_, _, extra, disasm, hok, rfl⟩
    split
    · exact hd.1
    · exact hd.1

/-! ## The decoder of an image by the fields of its ELF header -/

open Bap.Target.LLVMLift in
/-- Each word size, byte order and release has its own LLVM target. -/
theorem mips_triples :
    MipsVariant.triple { bits := 32, endian := .big } = "mips" ∧
    MipsVariant.triple { bits := 32, endian := .little } = "mipsel" ∧
    MipsVariant.triple { bits := 64, endian := .big } = "mips64" ∧
    MipsVariant.triple { bits := 64, endian := .little } = "mips64el" ∧
    MipsVariant.triple { bits := 32, endian := .big, release6 := true } = "mipsisa32r6" ∧
    MipsVariant.triple { bits := 32, endian := .little, release6 := true } = "mipsisa32r6el" ∧
    MipsVariant.triple { bits := 64, endian := .big, release6 := true } = "mipsisa64r6" ∧
    MipsVariant.triple { bits := 64, endian := .little, release6 := true } = "mipsisa64r6el" :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open Bap.Target.LLVMLift in
theorem powerpc_triples :
    PowerPCVariant.triple { bits := 32, endian := .big } = "powerpc" ∧
    PowerPCVariant.triple { bits := 32, endian := .little } = "powerpcle" ∧
    PowerPCVariant.triple { bits := 64, endian := .big } = "powerpc64" ∧
    PowerPCVariant.triple { bits := 64, endian := .little } = "powerpc64le" :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The MIPS of a decoded ELF file is what its header says: `EI_CLASS`, `EI_DATA` and the architecture of `e_flags`. -/
theorem mipsVariant_of_elf {data : ByteArray} {image : Bap.Image.Image} (h : Bap.Image.Elf.decode data = .ok image) :
    (Project.mipsVariant image).bits = (if Bap.Proofs.Image.byteAt data 4 = 2 then 64 else 32) ∧
    (Project.mipsVariant image).endian = (if Bap.Proofs.Image.byteAt data 5 = 1 then .little else .big) ∧
    (Project.mipsVariant image).release6 = Bap.Image.Elf.mipsRelease6
      ((IO.Reader.u32 data image.endian (if image.addrWidth = 64 then 48 else 36)).toOption.getD 0) := by
  have ⟨_, hw, he⟩ := Bap.Proofs.Image.ElfParser.decode_class_encoding h
  refine ⟨?_, he, ?_⟩
  · simp only [Project.mipsVariant, hw]
    split <;> simp_all
  · simp only [Project.mipsVariant, Bap.Proofs.Image.ElfParser.decode_machineFlags h]

/-- The PowerPC of a decoded ELF file is what its header says: `EI_CLASS` and `EI_DATA`. -/
theorem powerpcVariant_of_elf {data : ByteArray} {image : Bap.Image.Image} (h : Bap.Image.Elf.decode data = .ok image) :
    (Project.powerpcVariant image).bits = (if Bap.Proofs.Image.byteAt data 4 = 2 then 64 else 32) ∧
    (Project.powerpcVariant image).endian = (if Bap.Proofs.Image.byteAt data 5 = 1 then .little else .big) := by
  have ⟨_, hw, he⟩ := Bap.Proofs.Image.ElfParser.decode_class_encoding h
  refine ⟨?_, he⟩
  simp only [Project.powerpcVariant, hw]
  split <;> simp_all

/-- A MIPS image has the decoder of its variant, whatever its word size. -/
theorem codeDisassembler_mips (image : Bap.Image.Image) (base : Nat) (h : image.arch = .mips) :
    Bap.Proofs.Disasm.Holds (Project.codeDisassembler image base) fun result =>
      ∀ d, result = some d → d.name = s!"{(Project.mipsVariant image).triple}-llvm-primus" := by
  have hn : Bap.Proofs.Disasm.Holds (Bap.Target.MIPS.disassembler base (Project.mipsVariant image))
      fun d => d.name = s!"{(Project.mipsVariant image).triple}-llvm-primus" := by
    unfold Bap.Target.MIPS.disassembler
    exact Bap.Proofs.Disasm.Holds.bind (Bap.Proofs.Disasm.Holds.true _) fun _ _ _ => Bap.Proofs.Disasm.Holds.pure rfl
  unfold Project.codeDisassembler
  simp only [h]
  intro s r s' he d hd
  subst hd
  cases hm : Bap.Target.MIPS.disassembler base (Project.mipsVariant image) s with
  | ok a s1 =>
    have he' : (Bap.Target.MIPS.disassembler base (Project.mipsVariant image) >>= fun d => pure (some d)) s =
        EST.Out.ok (some d) s' := he
    rw [Bap.Proofs.Disasm.bind_ok hm] at he'
    cases he'
    exact hn s _ s' hm
  | error e s1 =>
    have he' : (Bap.Target.MIPS.disassembler base (Project.mipsVariant image) >>= fun d => pure (some d)) s =
        EST.Out.ok (some d) s' := he
    rw [Bap.Proofs.Disasm.bind_error hm] at he'
    cases he'

/-- A PowerPC image has the decoder of its variant, whatever its word size. -/
theorem codeDisassembler_powerpc (image : Bap.Image.Image) (base : Nat) (h : image.arch = .powerpc) :
    Bap.Proofs.Disasm.Holds (Project.codeDisassembler image base) fun result =>
      ∀ d, result = some d → d.name = s!"{(Project.powerpcVariant image).triple}-llvm-primus" := by
  have hn : Bap.Proofs.Disasm.Holds (Bap.Target.PowerPC.disassembler base (Project.powerpcVariant image))
      fun d => d.name = s!"{(Project.powerpcVariant image).triple}-llvm-primus" := by
    unfold Bap.Target.PowerPC.disassembler
    exact Bap.Proofs.Disasm.Holds.bind (Bap.Proofs.Disasm.Holds.true _) fun _ _ _ => Bap.Proofs.Disasm.Holds.pure rfl
  unfold Project.codeDisassembler
  simp only [h]
  intro s r s' he d hd
  subst hd
  cases hm : Bap.Target.PowerPC.disassembler base (Project.powerpcVariant image) s with
  | ok a s1 =>
    have he' : (Bap.Target.PowerPC.disassembler base (Project.powerpcVariant image) >>= fun d => pure (some d)) s =
        EST.Out.ok (some d) s' := he
    rw [Bap.Proofs.Disasm.bind_ok hm] at he'
    cases he'
    exact hn s _ s' hm
  | error e s1 =>
    have he' : (Bap.Target.PowerPC.disassembler base (Project.powerpcVariant image) >>= fun d => pure (some d)) s =
        EST.Out.ok (some d) s' := he
    rw [Bap.Proofs.Disasm.bind_error hm] at he'
    cases he'

end Bap.Proofs.Project
