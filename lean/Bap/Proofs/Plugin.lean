import Lean.Elab.Command
import Bap.Plugin.Loader

namespace Bap.Proofs.Plugin

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

open Bap.Plugin

section Register

theorem mem_register_iff (p q : Plugin) (r : Registry) :
    q ∈ (Registry.register p r).plugins ↔ q = p ∨ (q ∈ r.plugins ∧ q.name ≠ p.name) := by
  simp [Registry.register]

theorem register_head (p : Plugin) (r : Registry) :
    (Registry.register p r).plugins.head? = some p := by
  simp [Registry.register]

/-- At most one plugin carries the registered name afterwards. -/
theorem register_name_unique (p q : Plugin) (r : Registry)
    (h : q ∈ (Registry.register p r).plugins) (hn : q.name = p.name) : q = p := by
  rcases (mem_register_iff p q r).mp h with rfl | ⟨_, hne⟩
  · rfl
  · exact absurd hn hne

theorem register_override (p q : Plugin) (r : Registry) (hn : q.name = p.name) :
    Registry.register p (Registry.register q r) = Registry.register p r := by
  simp only [Registry.register, List.filter_cons, List.filter_filter]
  simp only [hn, bne_self_eq_false, Bool.false_eq_true, ite_false]
  congr 2
  apply List.filter_congr
  intro x _
  simp

theorem register_idempotent (p : Plugin) (r : Registry) :
    Registry.register p (Registry.register p r) = Registry.register p r :=
  register_override p p r rfl

theorem register_preserves_distinct_names (p : Plugin) (r : Registry)
    (h : (r.plugins.map Plugin.name).Nodup) :
    ((Registry.register p r).plugins.map Plugin.name).Nodup := by
  have hsub : ((r.plugins.filter fun old => old.name != p.name).map Plugin.name).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup h
  simp only [Registry.register, List.map_cons, List.nodup_cons]
  refine ⟨?_, hsub⟩
  simp

/-- Registration of differently named plugins commutes up to order. -/
theorem register_comm_perm (p q : Plugin) (r : Registry) (hn : p.name ≠ q.name) :
    (Registry.register p (Registry.register q r)).plugins.Perm
      (Registry.register q (Registry.register p r)).plugins := by
  have hq : (q.name != p.name) = true := by simpa using fun h : q.name = p.name => hn h.symm
  have hp : (p.name != q.name) = true := by simpa using hn
  simp only [Registry.register, List.filter_cons, hq, hp, ite_true, List.filter_filter]
  have : (r.plugins.filter fun x => (x.name != p.name) && (x.name != q.name)) =
      r.plugins.filter fun x => (x.name != q.name) && (x.name != p.name) := by
    apply List.filter_congr
    intro x _
    exact Bool.and_comm _ _
  rw [this]
  exact List.Perm.swap _ _ _

end Register

section Find

theorem mem_passes_iff (r : Registry) (pass : Bap.Project.Pass) :
    pass ∈ r.passes ↔ ∃ p ∈ r.plugins, pass ∈ p.passes := by
  simp [Registry.passes]

theorem findPass_sound {r : Registry} {n : String} {pass : Bap.Project.Pass}
    (h : r.findPass n = some pass) : pass ∈ r.passes ∧ pass.name = n := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem findPass_complete {r : Registry} {n : String} {pass : Bap.Project.Pass}
    (hm : pass ∈ r.passes) (hn : pass.name = n) : (r.findPass n).isSome := by
  simp only [Registry.findPass, List.find?_isSome]
  exact ⟨pass, hm, by simpa using hn⟩

theorem findPass_eq_none_iff (r : Registry) (n : String) :
    r.findPass n = none ↔ ∀ pass ∈ r.passes, pass.name ≠ n := by
  simp [Registry.findPass]

/-- The most recently registered plugin shadows every older pass of the same name. -/
theorem findPass_register_shadow {p : Plugin} {r : Registry} {n : String} {pass : Bap.Project.Pass}
    (h : p.passes.find? (fun pass => pass.name = n) = some pass) :
    (Registry.register p r).findPass n = some pass := by
  simp only [Registry.findPass, Registry.passes, Registry.register, List.flatMap_cons,
    List.find?_append, h, Option.some_or]

theorem findPass_register_new {p : Plugin} {r : Registry} {pass : Bap.Project.Pass}
    (hm : pass ∈ p.passes) : ((Registry.register p r).findPass pass.name).isSome :=
  findPass_complete ((mem_passes_iff _ _).mpr ⟨p, by simp [Registry.register], hm⟩) rfl

private theorem find_flatMap_filter (plugins : List Plugin) (keep : Plugin → Bool) (n : String)
    (h : ∀ q ∈ plugins, keep q = false → ∀ pass ∈ q.passes, pass.name ≠ n) :
    ((plugins.filter keep).flatMap Plugin.passes).find? (fun pass => pass.name = n) =
      (plugins.flatMap Plugin.passes).find? (fun pass => pass.name = n) := by
  induction plugins with
  | nil => rfl
  | cons head tail ih =>
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    by_cases hk : keep head = true
    · simp [hk, List.find?_append, ih']
    · have hn := h head List.mem_cons_self (by simpa using hk)
      have : head.passes.find? (fun pass => decide (pass.name = n)) = none := by
        simpa using hn
      simp [hk, List.find?_append, ih', this]

/-- Frame: a lookup is unaffected when neither the new plugin nor the plugin it replaces
offers a pass of that name. -/
theorem findPass_register_frame {p : Plugin} {r : Registry} {n : String}
    (hnew : ∀ pass ∈ p.passes, pass.name ≠ n)
    (hold : ∀ q ∈ r.plugins, q.name = p.name → ∀ pass ∈ q.passes, pass.name ≠ n) :
    (Registry.register p r).findPass n = r.findPass n := by
  have hp : p.passes.find? (fun pass => decide (pass.name = n)) = none := by simpa using hnew
  simp only [Registry.findPass, Registry.passes, Registry.register, List.flatMap_cons,
    List.find?_append, hp, Option.none_or]
  apply find_flatMap_filter
  intro q hq hk
  exact hold q hq (by simpa using hk)

end Find

section Dependencies

open_private Bap.Plugin.Basic in Bap.Plugin : includePass includeDependencies

/-- Every pass in the list has all its dependencies present by name. -/
def DepsClosed (passes : List Bap.Project.Pass) : Prop :=
  ∀ x ∈ passes, ∀ d ∈ x.dependencies, ∃ y ∈ passes, y.name = d

/-- One step of the walk over a pass's dependencies. -/
private def includeStep (r : Registry) (pass : Bap.Project.Pass) (fuel : Nat)
    (included : List Bap.Project.Pass) (dependency : String) :
    Except Bap.Project.PassError (List Bap.Project.Pass) :=
  match r.findPass dependency with
  | none => .error (.missingDependency pass.name dependency)
  | some dependencyPass => includePass r dependencyPass fuel included

private theorem includePass_succ (r : Registry) (pass : Bap.Project.Pass) (fuel : Nat)
    (inc : List Bap.Project.Pass) :
    includePass r pass (fuel + 1) inc =
      if inc.any (fun old => decide (old.name = pass.name)) = true then .ok inc
      else pass.dependencies.foldlM (includeStep r pass fuel) (inc ++ [pass]) := by
  rw [includePass]
  rfl

private theorem includePass_of_included {r : Registry} {pass : Bap.Project.Pass} {fuel : Nat}
    {inc : List Bap.Project.Pass} (h : ∃ y ∈ inc, y.name = pass.name) : includePass r pass fuel inc = .ok inc := by
  have hany : (inc.any fun old => decide (old.name = pass.name)) = true := by simpa using h
  unfold includePass
  simp [hany]

/-- Everything `includePass` holds is kept, each addition comes from the root or the registry,
and each addition has its dependencies in the result. -/
theorem includePass_spec (r : Registry) (fuel : Nat) :
    ∀ (pass : Bap.Project.Pass) (inc out : List Bap.Project.Pass),
      includePass r pass fuel inc = .ok out →
      (∀ x ∈ inc, x ∈ out) ∧ (∃ x ∈ out, x.name = pass.name) ∧
        (∀ x ∈ out, x ∈ inc ∨ x = pass ∨ x ∈ r.passes) ∧
        (∀ x ∈ out, x ∉ inc → ∀ d ∈ x.dependencies, ∃ y ∈ out, y.name = d) := by
  induction fuel with
  | zero =>
    intro pass inc out h
    unfold includePass at h
    split at h
    · cases h
      rename_i hany
      obtain ⟨y, hy, hn⟩ := List.any_eq_true.mp hany
      exact ⟨fun _ hx => hx, ⟨y, hy, by simpa using hn⟩, fun _ hx => .inl hx, fun _ hx hn => absurd hx hn⟩
    · simp at h
  | succ fuel ih =>
    intro pass inc out h
    rw [includePass_succ] at h
    split at h
    · cases h
      rename_i hany
      obtain ⟨y, hy, hn⟩ := List.any_eq_true.mp hany
      exact ⟨fun _ hx => hx, ⟨y, hy, by simpa using hn⟩, fun _ hx => .inl hx, fun _ hx hn => absurd hx hn⟩
    · have fold : ∀ (deps : List String) (cur res : List Bap.Project.Pass),
          deps.foldlM (includeStep r pass fuel) cur = .ok res →
          (∀ x ∈ cur, x ∈ res) ∧ (∀ d ∈ deps, ∃ y ∈ res, y.name = d) ∧
            (∀ x ∈ res, x ∈ cur ∨ x ∈ r.passes) ∧
            (∀ x ∈ res, x ∉ cur → ∀ d ∈ x.dependencies, ∃ y ∈ res, y.name = d) := by
        intro deps
        induction deps with
        | nil =>
          intro cur res hf
          simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
          subst hf
          exact ⟨fun _ hx => hx, by simp, fun _ hx => .inl hx, fun _ hx hn => absurd hx hn⟩
        | cons d rest ihd =>
          intro cur res hf
          simp only [List.foldlM_cons, bind, Except.bind] at hf
          split at hf
          · cases hf
          · rename_i mid hmid
            obtain ⟨hsub, hdeps, hfrom, hclosed⟩ := ihd _ _ hf
            simp only [includeStep] at hmid
            split at hmid
            · cases hmid
            · rename_i dp hfind
              obtain ⟨h1, ⟨y, hy, hyn⟩, h3, h4⟩ := ih _ _ _ hmid
              have hdn := (findPass_sound hfind).2
              refine ⟨fun x hx => hsub x (h1 x hx), ?_, ?_, ?_⟩
              · intro e he
                rcases List.mem_cons.mp he with rfl | he
                · exact ⟨y, hsub y hy, hyn.trans hdn⟩
                · exact hdeps e he
              · intro x hx
                rcases hfrom x hx with hm | hp
                · rcases h3 x hm with hc | rfl | hr
                  · exact .inl hc
                  · exact .inr (findPass_sound hfind).1
                  · exact .inr hr
                · exact .inr hp
              · intro x hx hnc e he
                by_cases hm : x ∈ mid
                · obtain ⟨z, hz, hzn⟩ := h4 x hm hnc e he
                  exact ⟨z, hsub z hz, hzn⟩
                · exact hclosed x hx hm e he
      obtain ⟨h1, h2, h3, h4⟩ := fold _ _ _ h
      refine ⟨fun x hx => h1 x (List.mem_append_left _ hx),
        ⟨pass, h1 _ (by simp), rfl⟩, ?_, ?_⟩
      · intro x hx
        rcases h3 x hx with hc | hr
        · rcases List.mem_append.mp hc with hc | hc
          · exact .inl hc
          · exact .inr (.inl (by simpa using hc))
        · exact .inr (.inr hr)
      · intro x hx hnc d hd
        by_cases hp : x = pass
        · subst hp
          exact h2 d hd
        · exact h4 x hx (by simp [hnc, hp]) d hd

private theorem includeFold_spec (r : Registry) (roots : List Bap.Project.Pass) :
    ∀ (cur out : List Bap.Project.Pass),
      roots.foldlM (m := Except Bap.Project.PassError)
        (fun included pass => includePass r pass (r.passes.length + 1) included) cur = .ok out →
      (∀ x ∈ cur, x ∈ out) ∧ (∀ root ∈ roots, ∃ x ∈ out, x.name = root.name) ∧
        (∀ x ∈ out, x ∈ cur ∨ x ∈ roots ∨ x ∈ r.passes) ∧ (DepsClosed cur → DepsClosed out) := by
  induction roots with
  | nil =>
    intro cur out h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ hx => hx, by simp, fun _ hx => .inl hx, id⟩
  | cons root rest ih =>
    intro cur out h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i mid hmid
      obtain ⟨a1, ⟨y, hy, hyn⟩, a3, a4⟩ := includePass_spec _ _ _ _ _ hmid
      obtain ⟨b1, b2, b3, b4⟩ := ih _ _ h
      refine ⟨fun x hx => b1 x (a1 x hx), ?_, ?_, fun hc => b4 ?_⟩
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨y, b1 y hy, hyn⟩
        · exact b2 e he
      · intro x hx
        rcases b3 x hx with hm | hrest | hr
        · rcases a3 x hm with hc | rfl | hr
          · exact .inl hc
          · exact .inr (.inl List.mem_cons_self)
          · exact .inr (.inr hr)
        · exact .inr (.inl (List.mem_cons_of_mem _ hrest))
        · exact .inr (.inr hr)
      · intro x hx d hd
        by_cases hm : x ∈ cur
        · obtain ⟨z, hz, hzn⟩ := hc x hm d hd
          exact ⟨z, a1 z hz, hzn⟩
        · exact a4 x hx hm d hd

/-- The dependency closure contains every root, adds only registry passes, and is closed. -/
theorem includeDependencies_spec {r : Registry} {roots out : List Bap.Project.Pass}
    (h : includeDependencies r roots = .ok out) :
    (∀ root ∈ roots, ∃ x ∈ out, x.name = root.name) ∧
      (∀ x ∈ out, x ∈ roots ∨ x ∈ r.passes) ∧ DepsClosed out := by
  obtain ⟨_, h2, h3, h4⟩ := includeFold_spec r roots [] out h
  refine ⟨h2, fun x hx => ?_, h4 (by simp [DepsClosed])⟩
  rcases h3 x hx with hc | hm
  · cases hc
  · exact hm

theorem includePass_missing_dependency (r : Registry) (pass : Bap.Project.Pass) (fuel : Nat)
    (inc : List Bap.Project.Pass) (d : String) (rest : List String)
    (hdeps : pass.dependencies = d :: rest) (hfresh : ∀ x ∈ inc, x.name ≠ pass.name)
    (hmissing : r.findPass d = none) :
    includePass r pass (fuel + 1) inc = .error (.missingDependency pass.name d) := by
  have hany : (inc.any fun old => decide (old.name = pass.name)) = false := by
    simpa using hfresh
  rw [includePass_succ]
  simp [hany, hdeps, List.foldlM_cons, includeStep, hmissing, bind, Except.bind]

/-- How many registered pass names are not yet included. -/
def unincluded (r : Registry) (inc : List Bap.Project.Pass) : Nat :=
  ((r.passes.map Bap.Project.Pass.name).filter fun name => !inc.any fun old => decide (old.name = name)).length

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

private theorem unincluded_le (r : Registry) {inc out : List Bap.Project.Pass} (h : ∀ x ∈ inc, x ∈ out) :
    unincluded r out ≤ unincluded r inc := by
  apply filter_length_le
  intro n hn
  simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq] at hn ⊢
  exact fun x hx => hn x (h x hx)

private theorem unincluded_lt {r : Registry} {pass : Bap.Project.Pass} {inc : List Bap.Project.Pass}
    (hp : pass ∈ r.passes) (hfresh : ¬ (inc.any fun old => decide (old.name = pass.name)) = true) :
    unincluded r (inc ++ [pass]) < unincluded r inc := by
  apply filter_length_lt (List.mem_map_of_mem hp)
  · intro n hn
    simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, List.mem_append,
      List.mem_singleton] at hn ⊢
    exact fun x hx => hn x (.inl hx)
  · simp
  · simpa using hfresh

/-- The closure walk always succeeds when every dependency a registered pass names is registered,
with fuel above the names not yet included, even if the dependencies form a cycle: a walk marks each
pass before descending, and leaves the cycle for the scheduler to report. -/
theorem includePass_ok (r : Registry) (hdeps : ∀ p ∈ r.passes, ∀ d ∈ p.dependencies, (r.findPass d).isSome)
    (fuel : Nat) :
    ∀ (pass : Bap.Project.Pass) (inc : List Bap.Project.Pass), pass ∈ r.passes → unincluded r inc < fuel →
      ∃ out, includePass r pass fuel inc = .ok out := by
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ fuel ih =>
    intro pass inc hp hfuel
    rw [includePass_succ]
    split
    · exact ⟨inc, rfl⟩
    · rename_i hfresh
      have hlt : unincluded r (inc ++ [pass]) < fuel := by
        have := unincluded_lt hp hfresh
        omega
      have fold : ∀ (deps : List String) (cur : List Bap.Project.Pass),
          (∀ d ∈ deps, d ∈ pass.dependencies) → unincluded r cur < fuel →
          ∃ out, deps.foldlM (includeStep r pass fuel) cur = .ok out := by
        intro deps
        induction deps with
        | nil => exact fun cur _ _ => ⟨cur, rfl⟩
        | cons d rest ihd =>
          intro cur hsub hcur
          obtain ⟨dp, hfind⟩ := Option.isSome_iff_exists.mp (hdeps pass hp d (hsub d List.mem_cons_self))
          obtain ⟨mid, hmid⟩ := ih dp cur (findPass_sound hfind).1 hcur
          obtain ⟨a1, -⟩ := includePass_spec _ _ _ _ _ hmid
          obtain ⟨out, hout⟩ := ihd mid (fun e he => hsub e (List.mem_cons_of_mem _ he))
            (Nat.lt_of_le_of_lt (unincluded_le r a1) hcur)
          refine ⟨out, ?_⟩
          simp only [List.foldlM_cons, bind, Except.bind, includeStep, hfind, hmid]
          exact hout
      exact fold _ _ (fun _ h => h) hlt

/-- Closure over registered roots succeeds when all dependencies are registered, cycles included. -/
theorem includeDependencies_ok {r : Registry} {roots : List Bap.Project.Pass}
    (hdeps : ∀ p ∈ r.passes, ∀ d ∈ p.dependencies, (r.findPass d).isSome) (hroots : ∀ p ∈ roots, p ∈ r.passes) :
    ∃ out, includeDependencies r roots = .ok out := by
  have hbudget : ∀ inc, unincluded r inc < r.passes.length + 1 := by
    intro inc
    have := List.length_filter_le (fun name => !inc.any fun old => decide (old.name = name))
      (r.passes.map Bap.Project.Pass.name)
    simp only [List.length_map] at this
    simp only [unincluded]
    omega
  have fold : ∀ (roots : List Bap.Project.Pass) (cur : List Bap.Project.Pass), (∀ p ∈ roots, p ∈ r.passes) →
      ∃ out, roots.foldlM (m := Except Bap.Project.PassError)
        (fun included pass => includePass r pass (r.passes.length + 1) included) cur = .ok out := by
    intro roots
    induction roots with
    | nil => exact fun cur _ => ⟨cur, rfl⟩
    | cons root rest ih =>
      intro cur hsub
      obtain ⟨mid, hmid⟩ := includePass_ok r hdeps _ root cur (hsub root List.mem_cons_self) (hbudget cur)
      obtain ⟨out, hout⟩ := ih mid fun p hp => hsub p (List.mem_cons_of_mem _ hp)
      refine ⟨out, ?_⟩
      simp only [List.foldlM_cons, bind, Except.bind, hmid]
      exact hout
  exact fold roots [] hroots

/-- With no names, the autorun passes run with their dependencies. -/
theorem analyze_default (r : Registry) (project : Bap.Project.Project) :
    analyze r project [] =
      (includeDependencies r (r.passes.filter fun pass => pass.autorun)).bind
        fun passes => Bap.Project.runPasses passes project := by
  simp only [analyze, List.isEmpty_nil, ite_true, bind, Except.bind]

private def rootOf (r : Registry) (name : String) : Except Bap.Project.PassError Bap.Project.Pass :=
  match r.findPass name with
  | some pass => .ok pass
  | none => .error (.unknownPass name)

/-- With names, every one must be registered, and they run with their dependencies. -/
theorem analyze_named (r : Registry) (project : Bap.Project.Project) (names : List String)
    (hn : names ≠ []) :
    analyze r project names =
      (names.mapM (rootOf r)).bind fun roots =>
        (includeDependencies r roots).bind fun passes => Bap.Project.runPasses passes project := by
  have : names.isEmpty = false := by simpa using hn
  simp only [analyze, this, bind, Except.bind]
  rfl

private theorem mapM_rootOf_unknown (r : Registry) (known : List String) (name : String) (rest : List String)
    (hk : ∀ n ∈ known, (r.findPass n).isSome) (hu : r.findPass name = none) :
    (known ++ name :: rest).mapM (rootOf r) = .error (.unknownPass name) := by
  induction known with
  | nil =>
    simp [List.mapM_cons, rootOf, hu, bind, Except.bind]
  | cons n tail ih =>
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hk n List.mem_cons_self)
    have := ih fun m hm => hk m (List.mem_cons_of_mem _ hm)
    have hr : rootOf r n = .ok p := by simp [rootOf, hp]
    simp [List.mapM_cons, hr, this, bind, Except.bind]

/-- A requested name that is not registered is an error naming the first such name; no pass runs. -/
theorem analyze_unknown_name (r : Registry) (project : Bap.Project.Project) (known : List String)
    (name : String) (rest : List String) (hk : ∀ n ∈ known, (r.findPass n).isSome)
    (hu : r.findPass name = none) :
    analyze r project (known ++ name :: rest) = .error (.unknownPass name) := by
  rw [analyze_named _ _ _ (by simp), mapM_rootOf_unknown r known name rest hk hu]
  rfl

/-- Any unregistered name among those requested makes `analyze` fail with an unknown pass. -/
theorem analyze_error_of_unknown (r : Registry) (project : Bap.Project.Project) {names : List String}
    {name : String} (hm : name ∈ names) (hu : r.findPass name = none) :
    ∃ first, r.findPass first = none ∧ analyze r project names = .error (.unknownPass first) := by
  induction names generalizing name with
  | nil => cases hm
  | cons n tail ih =>
    cases hn : r.findPass n with
    | none => exact ⟨n, hn, analyze_unknown_name r project [] n tail (by simp) hn⟩
    | some p =>
      have hmem : name ∈ tail := by
        rcases List.mem_cons.mp hm with h | h
        · subst h; rw [hn] at hu; cases hu
        · exact h
      obtain ⟨split, hsplit⟩ : ∃ known first rest, tail = known ++ first :: rest ∧
          (∀ m ∈ known, (r.findPass m).isSome) ∧ r.findPass first = none := by
        clear ih hm hn
        induction tail with
        | nil => cases hmem
        | cons m more ihm =>
          cases hmf : r.findPass m with
          | none => exact ⟨[], m, more, rfl, by simp, hmf⟩
          | some q =>
            have hmore : name ∈ more := by
              rcases List.mem_cons.mp hmem with h | h
              · subst h; rw [hmf] at hu; cases hu
              · exact h
            obtain ⟨known, first, rest, he, hk, hf⟩ := ihm hmore
            refine ⟨m :: known, first, rest, by simp [he], ?_, hf⟩
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simp [hmf]
            · exact hk x hx
      obtain ⟨first, rest, he, hk, hf⟩ := hsplit
      refine ⟨first, hf, ?_⟩
      have := analyze_unknown_name r project (n :: split) first rest (by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [hn]
        · exact hk x hx) hf
      simpa [he] using this

private theorem mapM_rootOf_names (r : Registry) (roots : List Bap.Project.Pass)
    (hc : ∀ p ∈ roots, r.findPass p.name = some p) :
    (roots.map Bap.Project.Pass.name).mapM (rootOf r) = .ok roots := by
  induction roots with
  | nil => rfl
  | cons p tail ih =>
    have := ih fun q hq => hc q (List.mem_cons_of_mem _ hq)
    have hr : rootOf r p.name = .ok p := by simp [rootOf, hc p List.mem_cons_self]
    simp [List.mapM_cons, hr, this, bind, Except.bind, pure, Except.pure]

/-- The default path is the named path applied to the autorun names, so an autorun pass behaves
the same however it was requested. Canonicality says no earlier pass shadows it by name. -/
theorem analyze_default_eq_named (r : Registry) (project : Bap.Project.Project)
    (hne : (r.passes.filter fun pass => pass.autorun) ≠ [])
    (hc : ∀ p ∈ r.passes.filter (fun pass => pass.autorun), r.findPass p.name = some p) :
    analyze r project [] =
      analyze r project ((r.passes.filter fun pass => pass.autorun).map Bap.Project.Pass.name) := by
  rw [analyze_default, analyze_named _ _ _ (by simpa using hne), mapM_rootOf_names r _ hc]
  rfl

/-- Dependencies of an autorun pass are in the schedule, autorun or not. -/
theorem includeDependencies_autorun_dependency {r : Registry} {out : List Bap.Project.Pass}
    (h : includeDependencies r (r.passes.filter fun pass => pass.autorun) = .ok out)
    {pass : Bap.Project.Pass} (hp : pass ∈ out) {d : String} (hd : d ∈ pass.dependencies) :
    ∃ y ∈ out, y.name = d ∧ y ∈ r.passes := by
  obtain ⟨_, hfrom, hclosed⟩ := includeDependencies_spec h
  obtain ⟨y, hy, hn⟩ := hclosed pass hp d hd
  refine ⟨y, hy, hn, ?_⟩
  rcases hfrom y hy with hm | hm
  · exact (List.mem_filter.mp hm).1
  · exact hm

private def autorunWithManualDep : Registry :=
  { plugins := [⟨"p", [{ name := "a", dependencies := ["b"], autorun := true, run := .ok },
      { name := "b", autorun := false, run := .ok }]⟩] }

/-- Regression: a registered non-autorun dependency runs first on the default path too. -/
theorem analyze_default_runs_manual_dependency :
    ((analyze autorunWithManualDep {} []).toOption.map Bap.Project.Project.passed) = some ["a", "b"] ∧
      ((analyze autorunWithManualDep {} ["a"]).toOption.map Bap.Project.Project.passed) = some ["a", "b"] := by
  constructor <;> rfl

private def cyclicRegistry : Registry :=
  { plugins := [⟨"p", [{ name := "a", dependencies := ["b"], autorun := true, run := .ok },
      { name := "b", dependencies := ["a"], run := .ok }]⟩] }

/-- Regression: a dependency cycle is reported as a cycle on both paths. -/
theorem analyze_cycle_reported :
    (analyze cyclicRegistry {} [] matches .error (.cycle _)) = true ∧
      (analyze cyclicRegistry {} ["b"] matches .error (.cycle _)) = true := by
  constructor <;> rfl

end Dependencies

section Builtin

theorem summarize_run (project : Bap.Project.Project) :
    summarize.run project = .ok (project.set "instructions"
      (toString ((project.disasm.map fun disasm => disasm.instructions.length).getD 0))) := rfl

theorem report_run (project : Bap.Project.Project) :
    report.run project = .ok ((project.set "blocks"
      (toString ((project.disasm.map fun disasm => disasm.blocks.length).getD 0))).set "status" "analyzed") := rfl

theorem report_marks_analyzed {project out : Bap.Project.Project} (h : report.run project = .ok out) :
    out.get "status" = some "analyzed" := by
  rw [report_run] at h
  cases h
  simp [Bap.Project.Project.get, Bap.Project.Project.set]

theorem findPass_default_iff (n : String) :
    (defaultRegistry.findPass n).isSome = true ↔ n = "summarize" ∨ n = "report" := by
  have : defaultRegistry.passes = [summarize, report] := by
    simp [defaultRegistry, Registry.register, Registry.passes]
  simp only [Registry.findPass, this]
  have hs : (summarize.name = n) ↔ n = "summarize" := eq_comm
  have hr : (report.name = n) ↔ n = "report" := eq_comm
  simp [List.find?_cons, hs, hr]
  by_cases h : n = "summarize"
  · simp [h]
  · by_cases h' : n = "report" <;> simp [h, h']


/-- Built-in passes never fail and only write project storage. -/
theorem builtin_frame (pass : Bap.Project.Pass) (hp : pass = summarize ∨ pass = report)
    (project : Bap.Project.Project) :
    ∃ out, pass.run project = .ok out ∧ out.image = project.image ∧ out.disasm = project.disasm ∧
      out.passed = project.passed := by
  rcases hp with rfl | rfl
  · exact ⟨_, summarize_run project, rfl, rfl, rfl⟩
  · exact ⟨_, report_run project, rfl, rfl, rfl⟩

end Builtin

section Loader

open_private Bap.Plugin.Loader in Bap.Plugin : decodeSet decodeDependencies makePass decodePass decodePlugin

private theorem mapM_spec {α β ε} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i y hy
      split at h
      · cases h
      · rename_i zs hz
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hm⟩ := ih _ hz
        refine ⟨by simp [hl], fun w hw => ?_⟩
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨x, List.mem_cons_self, hy⟩
        · obtain ⟨u, hu, hf⟩ := hm w hw
          exact ⟨u, List.mem_cons_of_mem _ hu, hf⟩

private theorem mapM_atoms (xs : List String) : (xs.map Sexp.atom).mapM Sexp.asAtom = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, Sexp.asAtom, ih, bind, Except.bind, pure, Except.pure]

theorem decodeSet_roundtrip (key value : String) :
    decodeSet (.tagged "set" [.atom key, .atom value]) = .ok (key, value) := by
  simp [decodeSet, Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom, bind, Except.bind]

private theorem asAtom_ok {input : Sexp} {value : String} (h : Sexp.asAtom input = .ok value) :
    input = .atom value := by
  cases input with
  | atom a => simp only [Sexp.asAtom, Except.ok.injEq] at h; rw [h]
  | list _ => simp [Sexp.asAtom] at h

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

theorem decodeSet_sound {input : Sexp} {key value : String} (h : decodeSet input = .ok (key, value)) :
    input = .tagged "set" [.atom key, .atom value] := by
  simp only [decodeSet, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i args hargs
    have hinput := (expectTagged_ok hargs).1
    split at h
    · rename_i k v
      split at h
      · cases h
      · rename_i a ha
        split at h
        · cases h
        · rename_i b hb
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [hinput, asAtom_ok ha, asAtom_ok hb]
    · cases h

theorem decodeDependencies_roundtrip (deps : List String) :
    decodeDependencies (.list (.atom "deps" :: deps.map Sexp.atom)) = .ok deps := by
  simp only [decodeDependencies, Sexp.asList, bind, Except.bind]
  exact mapM_atoms deps

theorem decodeDependencies_sound {input : Sexp} {deps : List String}
    (h : decodeDependencies input = .ok deps) :
    ∃ items, input = .list (.atom "deps" :: items) ∧ items.length = deps.length ∧
      ∀ dep ∈ deps, Sexp.atom dep ∈ items := by
  cases input with
  | atom a => simp [decodeDependencies, Sexp.asList, bind, Except.bind] at h
  | list items =>
    simp only [decodeDependencies, Sexp.asList, bind, Except.bind] at h
    split at h
    · rename_i rest
      obtain ⟨hl, hm⟩ := mapM_spec _ _ _ h
      refine ⟨rest, rfl, hl.symm, fun dep hd => ?_⟩
      obtain ⟨x, hx, hf⟩ := hm dep hd
      rwa [asAtom_ok hf] at hx
    · cases h

theorem makePass_spec {name : String} {deps : List String} {action : Sexp} {pass : Bap.Project.Pass}
    (h : makePass name deps action = .ok pass) :
    pass.name = name ∧ pass.dependencies = deps ∧ pass.autorun = true ∧ pass.runonce = true ∧
      ∃ key value, action = .tagged "set" [.atom key, .atom value] ∧
        ∀ project, pass.run project = .ok (project.set key value) := by
  simp only [makePass, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i kv hkv
    obtain ⟨key, value⟩ := kv
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl, key, value, decodeSet_sound hkv, fun _ => rfl⟩

theorem makePass_roundtrip (name key value : String) (deps : List String)
    (project : Bap.Project.Project) :
    ((makePass name deps (.tagged "set" [.atom key, .atom value])).toOption.map fun pass =>
      (pass.name, pass.dependencies, pass.run project |>.toOption.map fun out => out.storage)) =
      some (name, deps, some (project.set key value).storage) := by
  simp [makePass, decodeSet_roundtrip, bind, Except.bind, Except.toOption]

/-- Passes decoded from a plugin bundle are autorun, total, and only write one storage key. -/
theorem decodePass_sound {input : Sexp} {pass : Bap.Project.Pass} (h : decodePass input = .ok pass) :
    pass.autorun = true ∧ pass.runonce = true ∧
      ∃ key value, ∀ project, pass.run project = .ok (project.set key value) := by
  have safe : ∀ {name deps action}, makePass name deps action = .ok pass →
      pass.autorun = true ∧ pass.runonce = true ∧
        ∃ key value, ∀ project, pass.run project = .ok (project.set key value) := by
    intro name deps action hm
    obtain ⟨_, _, ha, hr, key, value, _, hrun⟩ := makePass_spec hm
    exact ⟨ha, hr, key, value, hrun⟩
  simp only [decodePass, bind, Except.bind, Sexp.asList] at h
  cases input with
  | atom a => cases h
  | list items =>
    simp only at h
    split at h
    · exact safe h
    · split at h
      · cases h
      · exact safe h
    · cases h

theorem decodePass_roundtrip (name key value : String) (deps : List String)
    (project : Bap.Project.Project) :
    ((decodePass (.list [.atom "pass", .atom name, .list (.atom "deps" :: deps.map Sexp.atom),
        .tagged "set" [.atom key, .atom value]])).toOption.map fun pass =>
      (pass.name, pass.dependencies, pass.run project |>.toOption.map fun out => out.storage)) =
      some (name, deps, some (project.set key value).storage) := by
  simp [decodePass, makePass, Sexp.asList, decodeDependencies_roundtrip, decodeSet_roundtrip, bind,
    Except.bind, Except.toOption]

theorem decodePlugin_shape {input : Sexp} {plugin : Plugin} (h : decodePlugin input = .ok plugin) :
    ∃ items, input = .list (.atom "plugin" :: .atom plugin.name :: items) ∧
      plugin.passes.length = items.length ∧
      ∀ pass ∈ plugin.passes, ∃ item ∈ items, decodePass item = .ok pass := by
  cases input with
  | atom a => simp [decodePlugin, Sexp.asList, bind, Except.bind] at h
  | list items =>
    simp only [decodePlugin, Sexp.asList, bind, Except.bind] at h
    split at h
    · rename_i name passes
      split at h
      · cases h
      · rename_i out hm
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨hl, hs⟩ := mapM_spec _ _ _ hm
        exact ⟨passes, rfl, hl, hs⟩
    · cases h

theorem decodePlugin_passes_safe {input : Sexp} {plugin : Plugin} (h : decodePlugin input = .ok plugin)
    {pass : Bap.Project.Pass} (hm : pass ∈ plugin.passes) :
    pass.autorun = true ∧ pass.runonce = true ∧
      ∃ key value, ∀ project, pass.run project = .ok (project.set key value) := by
  obtain ⟨_, _, _, hs⟩ := decodePlugin_shape h
  obtain ⟨_, _, hd⟩ := hs pass hm
  exact decodePass_sound hd

theorem decodePlugin_empty (name : String) :
    (decodePlugin (.list [.atom "plugin", .atom name])).toOption.map Plugin.name = some name := by
  simp [decodePlugin, Sexp.asList, bind, Except.bind, pure, Except.pure, Except.toOption]

end Loader

end Bap.Proofs.Plugin
