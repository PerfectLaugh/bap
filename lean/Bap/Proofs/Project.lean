import Lean.Elab.Command
import Bap.Project.Pass
import Bap.Project.Persist
import Bap.Proofs.Bil
import Bap.Proofs.Knowledge

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

open_private Bap.Project.Persist in Bap.Project :
  nat bool boolValue encodeBytes decodeBytes encodeArch decodeArch encodeSection decodeSection
  encodeSegment decodeSegment encodeSymbol decodeSymbol encodeRegion decodeRegion encodeImage
  decodeImage encodeFlow decodeFlow encodeTarget decodeTarget encodeInsn decodeInsn encodeEdge
  decodeEdge encodeDisasm decodeDisasm encodeBinding decodeBinding depth depthOfList

@[local simp] theorem nat_roundtrip (value : Nat) : Sexp.nat (nat value) = .ok value := by
  simp [nat, Sexp.nat, Sexp.asAtom, bind, Except.bind]

@[local simp] theorem boolValue_roundtrip (value : Bool) : boolValue (bool value) = .ok value := by
  cases value <;> rfl

private theorem mapM_roundtrip {α β ε} (f : α → β) (g : β → Except ε α) (xs : List α)
    (h : ∀ x ∈ xs, g (f x) = .ok x) : (xs.map f).mapM g = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.mapM_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

private theorem byteArray_toList_loop (bytes : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop bytes i acc = acc.reverse ++ bytes.data.toList.drop i := by
  induction i, acc using ByteArray.toList.loop.induct bytes with
  | case1 i acc hlt ih =>
    rw [ByteArray.toList.loop, ite_eq_left hlt, ih]
    have hlt' : i < bytes.data.toList.length := by simpa using hlt
    have hget : bytes.get! i = bytes.data.toList[i] := by
      simp [ByteArray.get!, hlt]
    rw [List.drop_eq_getElem_cons hlt', hget]
    simp
  | case2 i acc hge =>
    rw [ByteArray.toList.loop, ite_eq_right hge]
    have : bytes.data.toList.length ≤ i := by simpa using hge
    simp [List.drop_of_length_le this]

theorem byteArray_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  simpa [ByteArray.toList] using byteArray_toList_loop bytes 0 []

theorem decodeBytes_roundtrip (bytes : ByteArray) : decodeBytes (encodeBytes bytes) = .ok bytes := by
  have hmap : (bytes.toList.map fun byte => nat byte.toNat).mapM Sexp.nat =
      .ok (bytes.toList.map UInt8.toNat) := by
    have := mapM_roundtrip nat Sexp.nat (bytes.toList.map UInt8.toNat) (fun x _ => nat_roundtrip x)
    simpa [List.map_map, Function.comp_def] using this
  have hany : ((bytes.toList.map UInt8.toNat).any fun byte => decide (byte ≥ 256)) = false := by
    simp only [List.any_map, List.any_eq_false, Function.comp_apply, decide_eq_true_eq]
    intro byte _
    have := byte.toNat_lt
    omega
  simp only [decodeBytes, encodeBytes, Sexp.asList, bind, Except.bind, hmap, hany]
  simp only [Bool.false_eq_true, ite_false, Except.ok.injEq]
  rw [byteArray_toList]
  obtain ⟨data⟩ := bytes
  simp [List.map_map, Function.comp_def]

/-- Soundness of the range check: any encoded value that does not fit a byte is rejected. -/
theorem decodeBytes_rejects_out_of_range (values : List Nat) (h : ∃ v ∈ values, 256 ≤ v) :
    decodeBytes (.list (values.map nat)) = .error "project byte is out of range" := by
  have hmap : (values.map nat).mapM Sexp.nat = .ok values :=
    mapM_roundtrip nat Sexp.nat values fun x _ => nat_roundtrip x
  have hany : (values.any fun byte => decide (byte ≥ 256)) = true := by
    simpa using h
  simp [decodeBytes, Sexp.asList, bind, Except.bind, hmap, hany]

theorem decodeArch_roundtrip (arch : Bap.Image.Arch) : decodeArch (encodeArch arch) = .ok arch := by
  cases arch <;> rfl

theorem decodeFlow_roundtrip (flow : Bap.Disasm.Flow) : decodeFlow (encodeFlow flow) = .ok flow := by
  cases flow <;> rfl

theorem parseEndian_roundtrip (endian : Bap.Endian) :
    Bap.Bil.Wire.parseEndian (Bap.Bil.Wire.printEndian endian) = .ok endian := by
  cases endian <;> rfl

private theorem toString_ne_none (value : Nat) : toString value ≠ "none" := by
  intro h
  have hlist : (toString value).toList = Nat.toDigits 10 value := Nat.toList_repr
  have hmem : 'n' ∈ Nat.toDigits 10 value := by
    rw [← hlist, h]
    simp
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hmem
  revert this
  decide

theorem decodeTarget_roundtrip (target : Option Nat) :
    decodeTarget (encodeTarget target) = .ok target := by
  cases target with
  | none => rfl
  | some value =>
    have hne := toString_ne_none value
    simp only [decodeTarget, encodeTarget]
    split
    · rename_i heq
      simp only [nat, Sexp.atom.injEq] at heq
      exact absurd heq hne
    · simp [bind, Except.bind]

theorem decodeSection_roundtrip (sec : Bap.Image.Section) :
    decodeSection (encodeSection sec) = .ok sec := by
  simp [decodeSection, encodeSection, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom,
    bind, Except.bind]

theorem decodeSegment_roundtrip (segment : Bap.Image.Segment) :
    decodeSegment (encodeSegment segment) = .ok segment := by
  simp [decodeSegment, encodeSegment, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom,
    bind, Except.bind]

theorem decodeSymbol_roundtrip (symbol : Bap.Image.Symbol) :
    decodeSymbol (encodeSymbol symbol) = .ok symbol := by
  simp [decodeSymbol, encodeSymbol, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom,
    bind, Except.bind]

theorem decodeRegion_roundtrip (region : Bap.Image.MemRegion) :
    decodeRegion (encodeRegion region) = .ok region := by
  simp [decodeRegion, encodeRegion, Sexp.expectTagged, Sexp.tagged, Sexp.asList,
    decodeBytes_roundtrip, bind, Except.bind]

theorem decodeEdge_roundtrip (edge : Nat × Nat) : decodeEdge (encodeEdge edge) = .ok edge := by
  simp [decodeEdge, encodeEdge, Sexp.expectTagged, Sexp.tagged, Sexp.asList, bind, Except.bind]

theorem decodeBinding_roundtrip (binding : String × String) :
    decodeBinding (encodeBinding binding) = .ok binding := by
  simp [decodeBinding, encodeBinding, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom,
    bind, Except.bind]

private theorem le_depthOfList {item : Sexp} {items : List Sexp} (h : item ∈ items) :
    depth item ≤ depthOfList items := by
  induction items with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [depthOfList]
      omega
    · have := ih h
      simp only [depthOfList]
      omega

mutual
  private theorem stmtDepth_le : (stmt : Bap.Bil.Stmt) →
      Bap.Proofs.Bil.WireLaws.stmtDepth stmt ≤ depth (Bap.Bil.Wire.printStmt stmt)
    | .move _ _ | .jmp _ | .special _ | .cpuExn _ => by
      simp [Bap.Proofs.Bil.WireLaws.stmtDepth, Bap.Bil.Wire.printStmt, Sexp.tagged, depth]
    | .while condition body => by
      have hb := programDepth_le body
      simp only [Bap.Proofs.Bil.WireLaws.stmtDepth, Bap.Bil.Wire.printStmt, Sexp.tagged, depth, depthOfList]
      omega
    | .ifElse condition yes no => by
      have hy := programDepth_le yes
      have hn := programDepth_le no
      simp only [Bap.Proofs.Bil.WireLaws.stmtDepth, Bap.Bil.Wire.printStmt, Sexp.tagged, depth, depthOfList]
      omega

  private theorem programDepth_le : (program : List Bap.Bil.Stmt) →
      Bap.Proofs.Bil.WireLaws.programDepth program ≤ depthOfList (program.map Bap.Bil.Wire.printStmt)
    | [] => by simp [Bap.Proofs.Bil.WireLaws.programDepth, depthOfList]
    | stmt :: rest => by
      have hs := stmtDepth_le stmt
      have hr := programDepth_le rest
      simp only [Bap.Proofs.Bil.WireLaws.programDepth, List.map_cons, depthOfList]
      omega
end

/-- Parser fuel from the input's own depth always suffices, so no nesting limit remains. -/
theorem parseStmts_depth (program : Bap.Bil.Program) :
    Bap.Bil.Wire.parseStmts (depth (Bap.Bil.Wire.printProgram program)) (Bap.Bil.Wire.printProgram program) =
      .ok program := by
  have h : Bap.Proofs.Bil.WireLaws.programDepth program ≤ depth (Bap.Bil.Wire.printProgram program) := by
    have := programDepth_le program
    simp only [Bap.Bil.Wire.printProgram, depth]
    omega
  have hl := Bap.Proofs.Bil.WireLaws.parseStmtList_print program _ h
  simp only [Bap.Bil.Wire.printProgram] at hl ⊢
  simp [Bap.Bil.Wire.parseStmts, Sexp.asList, hl, bind, Except.bind]

/-- An instruction roundtrips exactly, whatever its BIL and however deep. -/
theorem decodeInsn_roundtrip (insn : Bap.Disasm.Insn) : decodeInsn (encodeInsn insn) = .ok insn := by
  simp [decodeInsn, encodeInsn, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom,
    decodeFlow_roundtrip, decodeTarget_roundtrip, parseStmts_depth, bind, Except.bind]

private theorem mapM_atom_roundtrip (xs : List String) :
    (xs.map Sexp.atom).mapM Sexp.asAtom = .ok xs :=
  mapM_roundtrip _ _ _ fun _ _ => rfl

theorem decodeDisasm_roundtrip (disasm : Bap.Disasm.Disasm) :
    decodeDisasm (encodeDisasm disasm) = .ok disasm := by
  have hi := mapM_roundtrip encodeInsn decodeInsn disasm.instructions
    fun insn _ => decodeInsn_roundtrip insn
  have he := mapM_roundtrip encodeEdge decodeEdge disasm.edges fun edge _ => decodeEdge_roundtrip edge
  have hs := mapM_atom_roundtrip disasm.errors
  simp only [decodeDisasm, encodeDisasm, Sexp.expectTagged, Sexp.tagged, Sexp.asList]
  simp [bind, Except.bind, hi, he, hs]

/-- An image roundtrips exactly, memory regions in order. The saved format is unchanged, so a file
written by an earlier version loads as what it holds, the regions as they were when it was saved. -/
theorem decodeImage_roundtrip (image : Bap.Image.Image) :
    decodeImage (encodeImage image) = .ok image := by
  have hsec := mapM_roundtrip encodeSection decodeSection image.sections
    fun sec _ => decodeSection_roundtrip sec
  have hseg := mapM_roundtrip encodeSegment decodeSegment image.segments
    fun seg _ => decodeSegment_roundtrip seg
  have hsym := mapM_roundtrip encodeSymbol decodeSymbol image.symbols
    fun sym _ => decodeSymbol_roundtrip sym
  have hreg := mapM_roundtrip encodeRegion decodeRegion (image.memory.entries.map Prod.fst)
    fun region _ => decodeRegion_roundtrip region
  rw [List.map_map] at hreg
  have hmap : (encodeRegion ∘ Prod.fst) = fun entry : Bap.Image.MemRegion × Unit => encodeRegion entry.1 := rfl
  rw [hmap] at hreg
  have hid : (image.memory.entries.map Prod.fst).map (·, ()) = image.memory.entries := by
    simp [List.map_map, Function.comp_def]
  simp only [decodeImage, encodeImage, Sexp.expectTagged, Sexp.tagged, Sexp.asList]
  simp [decodeArch_roundtrip, parseEndian_roundtrip, decodeBytes_roundtrip, hsec, hseg, hsym, hreg,
    hid, bind, Except.bind]

/-- Reads of overlapping memory, where the first matching region wins, survive a save and reload. -/
theorem decodeImage_preserves_reads (image : Bap.Image.Image) (address : Nat) :
    ((decodeImage (encodeImage image)).toOption.map fun image => image.memory.readByte address) =
      some (image.memory.readByte address) := by
  rw [decodeImage_roundtrip]
  rfl

/-- Saving a reloaded image writes the same document. -/
theorem encodeImage_decodeImage (image : Bap.Image.Image) :
    ((decodeImage (encodeImage image)).map encodeImage) = .ok (encodeImage image) := by
  rw [decodeImage_roundtrip]
  rfl

/-- Encoding refuses a project holding a Knowledge fact whose slot is not registered. -/
theorem encode_rejects_unregistered (project : Project) (persistent : List Bap.Knowledge.AnySlot)
    (fact : Bap.Knowledge.Fact)
    (hm : fact ∈ project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact)
    (hn : fact.slot.2.name ∉ persistent.map fun slot => slot.2.name) :
    ∃ message, encode project persistent = .error message := by
  simp only [encode]
  have hsome : (((project.knowledge.facts ++ project.knowledge.opinions.map fun opinion => opinion.fact).find?
      fun fact => !(persistent.map fun slot => slot.2.name).contains fact.slot.2.name)).isSome := by
    rw [List.find?_isSome]
    exact ⟨fact, hm, by simpa using hn⟩
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  simp only [bind, Except.bind]
  rw [hfound]
  exact ⟨_, rfl⟩

private theorem expectTagged_ok {tag : String} {arity : Nat} {input : Sexp} {args : List Sexp}
    (h : Sexp.expectTagged tag arity input = .ok args) :
    input = .tagged tag args ∧ args.length = arity := by
  cases input with
  | atom a => simp [Sexp.expectTagged, Sexp.asList, bind, Except.bind] at h
  | list items =>
    simp only [Sexp.expectTagged, Sexp.asList, bind, Except.bind] at h
    split at h
    · rename_i actual rest
      split at h
      · rename_i hc
        cases h
        simp [Sexp.tagged, hc.1, hc.2]
      · cases h
    · cases h

theorem decode_shape {input : Sexp} {persistent : List Bap.Knowledge.AnySlot} {project : Project}
    (h : decode input persistent = .ok project) :
    ∃ image disasm storage passed knowledge,
      input = .tagged "project" [image, disasm, storage, passed, knowledge] := by
  simp only [decode, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i args hargs
    have hinput := (expectTagged_ok hargs).1
    split at h
    · rename_i image disasm storage passed knowledge
      exact ⟨image, disasm, storage, passed, knowledge, hinput⟩
    · cases h

/-- Exact roundtrip of a project. Facts and opinions must live in slots of `persistent`, uniquely
named: `encode` can only check a slot's name, and decoding a value needs the slot's own codec. -/
theorem decode_encode {project : Project} {persistent : List Bap.Knowledge.AnySlot} {encoded : Sexp}
    (h : encode project persistent = .ok encoded)
    (hnames : (persistent.map fun slot => slot.2.name).Nodup)
    (hfacts : ∀ fact ∈ project.knowledge.facts, fact.slot ∈ persistent)
    (hopinions : ∀ opinion ∈ project.knowledge.opinions, opinion.fact.slot ∈ persistent) :
    decode encoded persistent = .ok project := by
  simp only [encode, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i knowledge hknowledge
      simp only [Except.ok.injEq] at h
      subst h
      have hkd : Bap.Knowledge.decodeState persistent knowledge = .ok project.knowledge := by
        obtain ⟨decoded, hdec, hf, ho, hv⟩ :=
          Bap.Proofs.Knowledge.decodeState_encodeState_total hnames hfacts hopinions hknowledge
        rw [hdec]
        cases decoded
        cases hk : project.knowledge
        simp_all
      have hst := mapM_roundtrip encodeBinding decodeBinding project.storage
        fun binding _ => decodeBinding_roundtrip binding
      have hpa := mapM_atom_roundtrip project.passed
      obtain ⟨image, disasm, kn, storage, passed⟩ := project
      simp only at hkd hst hpa
      cases image with
      | none =>
        cases disasm with
        | none =>
          simp [decode, Sexp.expectTagged, Sexp.tagged, Sexp.asList, bind, Except.bind, hst, hpa, hkd]
        | some d =>
          have hd := decodeDisasm_roundtrip d
          simp [decode, Sexp.expectTagged, Sexp.tagged, Sexp.asList, bind, Except.bind, hst, hpa, hkd, hd]
      | some i =>
        have hi := decodeImage_roundtrip i
        cases disasm with
        | none =>
          simp [decode, Sexp.expectTagged, Sexp.tagged, Sexp.asList, bind, Except.bind, hst, hpa, hkd, hi]
        | some d =>
          have hd := decodeDisasm_roundtrip d
          simp [decode, Sexp.expectTagged, Sexp.tagged, Sexp.asList, bind, Except.bind, hst, hpa, hkd, hi, hd]

/-- The roundtrip through text: parsing the rendered document and decoding it gives the project. -/
theorem decode_parse_encode {project : Project} {persistent : List Bap.Knowledge.AnySlot} {encoded : Sexp}
    (h : encode project persistent = .ok encoded)
    (hnames : (persistent.map fun slot => slot.2.name).Nodup)
    (hfacts : ∀ fact ∈ project.knowledge.facts, fact.slot ∈ persistent)
    (hopinions : ∀ opinion ∈ project.knowledge.opinions, opinion.fact.slot ∈ persistent) :
    (Sexp.parse (toString encoded)).bind (decode · persistent) = .ok project := by
  rw [show Sexp.parse (toString encoded) = .ok encoded from Bap.Proofs.Core.SexpLaws.parse_render _]
  exact decode_encode h hnames hfacts hopinions

/-- What `save` writes, `deserialize` reads back: the whole file format, end to end. -/
theorem deserialize_serialize {project : Project} {persistent : List Bap.Knowledge.AnySlot} {text : String}
    (h : serialize project persistent = .ok text)
    (hnames : (persistent.map fun slot => slot.2.name).Nodup)
    (hfacts : ∀ fact ∈ project.knowledge.facts, fact.slot ∈ persistent)
    (hopinions : ∀ opinion ∈ project.knowledge.opinions, opinion.fact.slot ∈ persistent) :
    deserialize text persistent = .ok project := by
  simp only [serialize, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i encoded hencoded
    simp only [Except.ok.injEq] at h
    subst h
    exact decode_parse_encode hencoded hnames hfacts hopinions

/-- `save` writes exactly what `serialize` produces, and fails only as it does. -/
theorem save_eq (project : Project) (path : String) (persistent : List Bap.Knowledge.AnySlot) :
    save project path persistent = match serialize project persistent with
      | .error error => throw (IO.userError error)
      | .ok text => IO.FS.writeFile path text := rfl

/-- `loadSaved` returns exactly what `deserialize` makes of the file. -/
theorem loadSaved_eq (path : String) (persistent : List Bap.Knowledge.AnySlot) :
    loadSaved path persistent = (IO.FS.readFile path >>= fun input =>
      match deserialize input persistent with
      | .error error => throw (IO.userError error)
      | .ok project => pure project) := rfl

/-- Without Knowledge facts the file format needs no registry at all. -/
theorem deserialize_serialize_no_knowledge {project : Project} {text : String}
    (h : serialize project [] = .ok text) (hfacts : project.knowledge.facts = [])
    (hopinions : project.knowledge.opinions = []) : deserialize text [] = .ok project :=
  deserialize_serialize h List.nodup_nil (by simp [hfacts]) (by simp [hopinions])

end Persist

end Bap.Proofs.Project
