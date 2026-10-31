import Lean
import Bap.Proofs.PrimusRelated

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! Evaluation in two states whose definitions differ in what is compiled.

A state that compiled code runs in (`Compat`) says of each name that it finds its definition, as written or compiled. This file proves that it doesn't matter which:
evaluating a form, a list of forms, or compiled code in two such states with the same code and temporaries, on values the same up to compilation, has the same
successes up to compilation, with the same code and temporaries (`apply_same_outcomes`, `eval_same_outcomes`).

It goes by induction on the fuel of the run on one side. The run it makes on the other has no bound on its fuel: where the two call a function and its compilation, the
run on the other side is of the callee as the first side has it, and `apply_compileFunction`, which holds in the state of the other side, turns it into a run of what the
other side has. That is why the theorem holds in both directions: the crossing happens on the side that is built, not the one the induction is on. -/

namespace Bap.Proofs.Primus

open Bap.Primus.Semantics
open_private Bap.Primus.Semantics Bap.Primus.Semantics compileFunction expectBil truth emit freeze freezeBil bindAssignable resolveSymbol resolveDestination macroCandidates
  macroExpansion resolveFunction lookup lookupState assignsLocal condition eval evalList evalSequence evalConditional
  apply evalCompiled evalCompiledList evalCompiledSequence evalCompiledConditional
open_private Bap.Proofs.Primus Bap.Proofs.Primus bind_ok lookupState_compat

local notation "SV" => Bap.Primus.Semantics.Value

/-! ### Runs with enough fuel -/

/-- A family has a result at all fuels from some on. -/
def Ev {α : Type} (family : Nat → Except String α) (result : α) : Prop :=
  ∃ least, ∀ fuel, least ≤ fuel → family fuel = .ok result

theorem Ev.of_succeeds {α : Type} {family : Nat → Except String α} {result : α} (hm : FuelMono family)
    (h : Succeeds family result) : Ev family result := by
  obtain ⟨least, hl⟩ := h
  refine ⟨least, fun fuel hf => ?_⟩
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hf
  induction extra with
  | zero => exact hl
  | succ extra ih => exact hm (ih (Nat.le_add_right _ _))

theorem Ev.succeeds {α : Type} {family : Nat → Except String α} {result : α} (h : Ev family result) : Succeeds family result := by
  obtain ⟨least, hl⟩ := h
  exact ⟨least, hl least (Nat.le_refl _)⟩

/-- There is a result in a relation at all fuels from some on. -/
def Reach {α : Type} (R : α → Prop) (family : Nat → Except String α) : Prop :=
  ∃ result, Ev family result ∧ R result

theorem Reach.step {α : Type} {R : α → Prop} {family : Nat → Except String α}
    (h : Reach R fun fuel => family (fuel + 1)) : Reach R family := by
  obtain ⟨result, ⟨least, hl⟩, hr⟩ := h
  refine ⟨result, ⟨least + 1, fun fuel hf => ?_⟩, hr⟩
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
  exact hl g (by omega)

theorem Reach.unstep {α : Type} {R : α → Prop} {family : Nat → Except String α}
    (h : Reach R family) : Reach R fun fuel => family (fuel + 1) := by
  obtain ⟨result, ⟨least, hl⟩, hr⟩ := h
  exact ⟨result, ⟨least, fun fuel hf => hl (fuel + 1) (by omega)⟩, hr⟩

theorem Reach.pure {α : Type} {R : α → Prop} {value : Except String α} {result : α} (h : value = .ok result) (hr : R result) :
    Reach R fun _ => value :=
  ⟨result, ⟨0, fun _ _ => h⟩, hr⟩

theorem Reach.bind {α β : Type} {R : β → Prop} {P : α → Prop} {family : Nat → Except String α} {next : Nat → α → Except String β}
    (h : Reach P family) (hn : ∀ x, P x → Reach R fun fuel => next fuel x) :
    Reach R fun fuel => family fuel >>= next fuel := by
  obtain ⟨x, ⟨l1, h1⟩, hx⟩ := h
  obtain ⟨y, ⟨l2, h2⟩, hy⟩ := hn x hx
  refine ⟨y, ⟨max l1 l2, fun fuel hf => ?_⟩, hy⟩
  simp only [h1 fuel (by omega), Bind.bind, Except.bind]
  exact h2 fuel (by omega)

/-- `Reach.bind` for what has no fuel. -/
theorem Reach.bind_pure {α β : Type} {R : β → Prop} {value : Except String α} {next : Nat → α → Except String β} {x : α}
    (h : value = .ok x) (hn : Reach R fun fuel => next fuel x) :
    Reach R fun fuel => value >>= next fuel := by
  simp only [h, Bind.bind, Except.bind]
  exact hn

/-! ### Two states -/

/-- Two states that compiled code runs in, with the same code and temporaries. -/
structure StateRel (globals : Globals) (first second : State) : Prop where
  left : Compat globals first
  right : Compat globals second
  code : first.code = second.code
  nextTemp : first.nextTemp = second.nextTemp

variable {globals : Globals}

theorem StateRel.clear {first second : State} (h : StateRel globals first second) :
    StateRel globals { first with code := [] } { second with code := [] } :=
  ⟨h.left.keep ⟨rfl, rfl, rfl⟩, h.right.keep ⟨rfl, rfl, rfl⟩, rfl, h.nextTemp⟩

theorem StateRel.emit {first second : State} (h : StateRel globals first second) (code : Bil.Program) :
    StateRel globals (emit first code) (emit second code) :=
  ⟨h.left.keep ⟨rfl, rfl, rfl⟩, h.right.keep ⟨rfl, rfl, rfl⟩, by show first.code ++ code = second.code ++ code; rw [h.code], h.nextTemp⟩

/-- A result and a value and state the same up to compilation. -/
def ResultRel (globals : Globals) (first second : SV × State) : Prop :=
  ValueRel (namesOf globals) first.1 second.1 ∧ StateRel globals first.2 second.2

/-- The same for several values. -/
def ListResultRel (globals : Globals) (first second : List SV × State) : Prop :=
  ListRel (namesOf globals) first.1 second.1 ∧ StateRel globals first.2 second.2

theorem envGet_rel {names : String → Option SV} {first second : Locals} (name : String) (h : EnvRel names first second) :
    (Assoc.get name first = none ∧ Assoc.get name second = none) ∨
      ∃ x y, Assoc.get name first = some x ∧ Assoc.get name second = some y ∧ ValueRel names x y := by
  induction first generalizing second with
  | nil =>
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | cons head rest ih =>
    cases h with
    | cons key hv ht =>
      simp only [Assoc.get, List.lookup_cons] at ih ⊢
      by_cases hk : name == key
      · simp only [hk]
        exact Or.inr ⟨_, _, rfl, rfl, hv⟩
      · simp only [hk]
        exact ih ht

theorem stateGet_rel {first second : State} (h : StateRel globals first second) (name : String) :
    (Assoc.get name first.globals = none ∧ Assoc.get name second.globals = none) ∨
      ∃ x y, Assoc.get name first.globals = some x ∧ Assoc.get name second.globals = some y ∧ ValueRel (namesOf globals) x y := by
  obtain ⟨v1, h1⟩ := h.left.definitions name
  obtain ⟨v2, h2⟩ := h.right.definitions name
  rw [h1, h2]
  cases Assoc.get name globals with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some value => exact Or.inr ⟨_, _, rfl, rfl, viewValue_rel v1 v2 value⟩

theorem lookupState_rel {locals locals' : Locals} {first second : State} (hl : EnvRel (namesOf globals) locals locals')
    (hs : StateRel globals first second) (name : String) {value : SV} (h : lookupState name locals first = .ok value) :
    ∃ other, lookupState name locals' second = .ok other ∧ ValueRel (namesOf globals) value other := by
  rw [lookupState_compat hs.left] at h
  rw [lookupState_compat hs.right]
  simp only [lookup] at h ⊢
  generalize (if name.startsWith "core:" = true then (name.drop 5).toString else name) = primitive at h ⊢
  rcases envGet_rel name hl with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hv⟩
  · simp only [h1] at h
    simp only [h2]
    by_cases hr : primitive = "replicate"
    · simp only [hr, ↓reduceIte, Except.ok.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, ValueRel.refl _⟩
    · simp only [hr, ↓reduceIte] at h ⊢
      rcases stateGet_rel hs name with ⟨h3, h4⟩ | ⟨x, y, h3, h4, hv⟩
      · simp only [h3] at h
        simp only [h4]
        by_cases hc : primitiveNames.contains primitive = true
        · simp only [hc, ↓reduceIte, Except.ok.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, ValueRel.refl _⟩
        · simp only [hc] at h
          cases h
      · simp only [h3, Except.ok.injEq] at h
        subst h
        simp only [h4]
        exact ⟨_, rfl, hv⟩
  · simp only [h1, Except.ok.injEq] at h
    subst h
    simp only [h2]
    exact ⟨_, rfl, hv⟩

theorem resolveSymbol_rel {first second : State} (hs : StateRel globals first second) {a b : List SV} (h : ListRel (namesOf globals) a b) :
    ListRel (namesOf globals) (resolveSymbol first a) (resolveSymbol second b) := by
  rcases h with _ | ⟨h1, t⟩
  · exact .nil
  · cases h1
    case symbol name =>
      simp only [resolveSymbol]
      rcases stateGet_rel hs name with ⟨h3, h4⟩ | ⟨x, y, h3, h4, hv⟩
      · simp only [h3, h4]
        exact .cons (.symbol _) t
      · simp only [h3, h4]
        cases hv
        case register => exact .cons (.register _ _ _) t
        all_goals exact .cons (.symbol _) t
    case unit => exact .cons .unit t
    case int v => exact .cons (.int v) t
    case bil w v => exact .cons (.bil w v) t
    case bool v => exact .cons (.bool v) t
    case register n w s => exact .cons (.register n w s) t
    case list hl => exact .cons (.list hl) t
    case callable hl => exact .cons (.callable hl) t

theorem resolveDestination_rel {first second : State} (hs : StateRel globals first second) (name : String) {a b : List SV}
    (h : ListRel (namesOf globals) a b) :
    ListRel (namesOf globals) (resolveDestination first name a) (resolveDestination second name b) := by
  rcases h with _ | ⟨h1, t⟩
  · exact .nil
  · cases h1
    case symbol s =>
      simp only [resolveDestination]
      split
      · exact resolveSymbol_rel hs (.cons (.symbol _) t)
      · exact .cons (.symbol _) t
    case unit => exact .cons .unit t
    case int v => exact .cons (.int v) t
    case bil w v => exact .cons (.bil w v) t
    case bool v => exact .cons (.bool v) t
    case register n w s => exact .cons (.register n w s) t
    case list hl => exact .cons (.list hl) t
    case callable hl => exact .cons (.callable hl) t

/-! ### What a call finds -/

theorem macroCandidates_filter {names : String → Option SV} {a b : List Callable} (h : CandidatesRel names a b) :
    (a.filter fun candidate => match candidate with
      | .macro .. => true
      | _ => false) =
    (b.filter fun candidate => match candidate with
      | .macro .. => true
      | _ => false) := by
  induction a generalizing b with
  | nil => cases h; rfl
  | cons head rest ih =>
    cases h with
    | cons hh ht =>
      cases hh <;> simp only [List.filter_cons, ih ht, Bool.false_eq_true, ↓reduceIte]

theorem macroCandidates_rel {names : String → Option SV} {a b : Callable} (h : CallableRel names a b) :
    macroCandidates a = macroCandidates b := by
  cases h
  case overloads hc => exact macroCandidates_filter hc
  all_goals rfl

theorem macroExpansion_rel {names : String → Option SV} {a b : Callable} (h : CallableRel names a b) (operands : List Sexp) :
    macroExpansion a operands = macroExpansion b operands := by
  simp only [macroExpansion, macroCandidates_rel h]

theorem resolveFunction_rel {names : String → Option SV} (count : Nat) {a b : List Callable} (h : CandidatesRel names a b) :
    (resolveFunction count a = none ∧ resolveFunction count b = none) ∨
      ∃ x y, resolveFunction count a = some x ∧ resolveFunction count b = some y ∧ CallableRel names x y := by
  induction a generalizing b with
  | nil =>
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | cons head rest ih =>
    cases h with
    | cons hh ht =>
      have hrest := ih ht
      cases hh with
      | function p e he =>
        simp only [resolveFunction]
        by_cases hc : p.length = count
        · simp only [hc, ↓reduceIte]
          exact Or.inr ⟨_, _, rfl, rfl, .function p e he⟩
        · simp only [hc, ↓reduceIte]
          exact hrest
      | compiled p e he =>
        simp only [resolveFunction]
        by_cases hc : p.length = count
        · simp only [hc, ↓reduceIte]
          exact Or.inr ⟨_, _, rfl, rfl, .compiled p e he⟩
        · simp only [hc, ↓reduceIte]
          exact hrest
      | @compile p e env c he =>
        simp only [resolveFunction]
        by_cases hc : p.length = count
        · simp only [hc, ↓reduceIte]
          exact Or.inr ⟨_, _, rfl, rfl, .compile he⟩
        · simp only [hc, ↓reduceIte]
          exact hrest
      | @decompile p e env c he =>
        simp only [resolveFunction]
        by_cases hc : p.length = count
        · simp only [hc, ↓reduceIte]
          exact Or.inr ⟨_, _, rfl, rfl, .decompile he⟩
        · simp only [hc, ↓reduceIte]
          exact hrest
      | «macro» p e => exact hrest
      | primitive n => exact hrest
      | overloads hc => exact hrest

theorem EnvRel.zip {names : String → Option SV} (params : List String) {a b : List SV} {e f : Locals} (h : ListRel names a b) (he : EnvRel names e f) :
    EnvRel names (params.zip a ++ e) (params.zip b ++ f) := by
  induction params generalizing a b with
  | nil => exact he
  | cons head rest ih =>
    cases h with
    | nil => exact he
    | cons hh ht => exact .cons head hh (ih ht)

/-! ### Steps with no calls -/

theorem StateRel.setCode {first second : State} (h : StateRel globals first second) (code : Bil.Program) :
    StateRel globals { first with code } { second with code } :=
  ⟨h.left.keep ⟨rfl, rfl, rfl⟩, h.right.keep ⟨rfl, rfl, rfl⟩, rfl, h.nextTemp⟩

theorem StateRel.setTemp {first second : State} (h : StateRel globals first second) (nextTemp : Nat) :
    StateRel globals { first with nextTemp } { second with nextTemp } :=
  ⟨h.left.keep ⟨rfl, rfl, rfl⟩, h.right.keep ⟨rfl, rfl, rfl⟩, h.code, rfl⟩

theorem freezeBil_rel {first second : State} (hs : StateRel globals first second) (width : Nat) (expression : Bil.Exp) :
    ResultRel globals (freezeBil first width expression) (freezeBil second width expression) := by
  simp only [freezeBil]
  cases Bil.evalExp [] expression with
  | ok _ => exact ⟨.bil _ _, hs⟩
  | error _ =>
    simp only [hs.nextTemp]
    exact ⟨.bil _ _, hs.left.keep ⟨rfl, rfl, rfl⟩, hs.right.keep ⟨rfl, rfl, rfl⟩, by simp only [hs.code], rfl⟩

theorem freeze_rel (context : Context) {first second : State} (hs : StateRel globals first second) {a b : SV}
    (hv : ValueRel (namesOf globals) a b) : ResultRel globals (freeze context first a) (freeze context second b) := by
  cases hv
  case bil w e => exact freezeBil_rel hs w e
  case register n w s =>
    simp only [freeze]
    cases expectBil context (.register n w s) with
    | ok x => exact freezeBil_rel hs _ _
    | error _ => exact ⟨.register _ _ _, hs⟩
  case unit => exact ⟨.unit, hs⟩
  case int v => exact ⟨.int v, hs⟩
  case bool v => exact ⟨.bool v, hs⟩
  case symbol v => exact ⟨.symbol v, hs⟩
  case list hl => exact ⟨.list hl, hs⟩
  case callable hl => exact ⟨.callable hl, hs⟩

theorem bindAssignable_rel (context : Context) {first second : State} (hs : StateRel globals first second) {a b : SV}
    (hv : ValueRel (namesOf globals) a b) {r : SV × State} (h : bindAssignable context first a = .ok r) :
    ∃ other, bindAssignable context second b = .ok other ∧ ResultRel globals r other := by
  simp only [bindAssignable, expectBil_rel context hv] at h ⊢
  cases hb : expectBil context b with
  | error => rw [hb] at h; cases h
  | ok x =>
    rw [hb] at h
    simp only [bind, Except.bind, Except.ok.injEq] at h
    subst h
    simp only [bind, Except.bind, hs.nextTemp]
    exact ⟨_, rfl, ValueRel.refl _, hs.left.keep ⟨rfl, rfl, rfl⟩, hs.right.keep ⟨rfl, rfl, rfl⟩, by simp only [hs.code], rfl⟩

theorem conditional_sim {context : Context} {test test' : Nat → Except String (SV × State)}
    {yes yes' no no' : Nat → State → Except String (SV × State)} {fuel : Nat}
    (ht : ∀ r, test fuel = .ok r → Reach (ResultRel globals r) test')
    (hy : ∀ s s', StateRel globals s s' → ∀ r, yes fuel s = .ok r → Reach (ResultRel globals r) fun g => yes' g s')
    (hn : ∀ s s', StateRel globals s s' → ∀ r, no fuel s = .ok r → Reach (ResultRel globals r) fun g => no' g s')
    {r : SV × State} (h : conditionalBody context test yes no fuel = .ok r) :
    Reach (ResultRel globals r) (conditionalBody context test' yes' no') := by
  show Reach _ fun g => conditionalBody context test' yes' no' g
  simp only [conditionalBody] at h ⊢
  obtain ⟨⟨tv, s⟩, h1, h⟩ := bind_ok h
  refine Reach.bind (ht _ h1) fun ⟨tv', s₁⟩ hrel => ?_
  obtain ⟨hvt, hst⟩ := hrel
  simp only at hvt hst
  obtain ⟨tr, h2, h⟩ := bind_ok h
  have h2' : truth tv' = .ok tr := by
    rw [← truth_rel hvt]
    exact h2
  refine Reach.bind_pure h2' ?_
  match tr, h with
  | some true, h => exact hy s s₁ hst _ h
  | some false, h => exact hn s s₁ hst _ h
  | none, h =>
    obtain ⟨c, h3, h⟩ := bind_ok h
    refine Reach.bind_pure (x := c) (by rw [← condition_rel context hvt]; exact h3) ?_
    obtain ⟨⟨yv, ys⟩, h4, h⟩ := bind_ok h
    refine Reach.bind (hy _ _ hst.clear _ h4) fun ⟨yv', ys'⟩ hy' => ?_
    obtain ⟨⟨nv, ns⟩, h5, h⟩ := bind_ok h
    refine Reach.bind (hn _ _ hst.clear _ h5) fun ⟨nv', ns'⟩ hn' => ?_
    obtain ⟨hyv, hys⟩ := hy'
    obtain ⟨hnv, hns⟩ := hn'
    simp only at hyv hys hnv hns
    simp only [expectBil_rel context hyv, expectBil_rel context hnv, hys.code, hns.code, hys.nextTemp, hns.nextTemp] at h
    have hst2 := hst.setTemp (max ys'.nextTemp ns'.nextTemp)
    by_cases e : (ys'.code.isEmpty && ns'.code.isEmpty) = true
    · simp only [e, ↓reduceIte] at h ⊢
      obtain ⟨⟨w1, e1⟩, h6, h⟩ := bind_ok h
      obtain ⟨⟨w2, e2⟩, h7, h⟩ := bind_ok h
      simp only [Except.ok.injEq] at h
      subst h
      refine Reach.bind_pure (x := (w1, e1)) h6 ?_
      refine Reach.bind_pure (x := (w2, e2)) h7 ?_
      exact Reach.pure rfl ⟨.bil _ _, hst2⟩
    · have e' : (ys'.code.isEmpty && ns'.code.isEmpty) = false := by simpa using e
      simp only [e', Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h6 : expectBil context yv' <;> cases h7 : expectBil context nv' <;> simp only [h6, h7, Except.ok.injEq] at h
      all_goals subst h
      · exact Reach.pure rfl ⟨.unit, hst2.emit _⟩
      · exact Reach.pure rfl ⟨.unit, hst2.emit _⟩
      · exact Reach.pure rfl ⟨.unit, hst2.emit _⟩
      · exact Reach.pure rfl ⟨.bil _ _, (hst2.setTemp _).emit _⟩

theorem envSlot_rel {names : String → Option SV} (slot : Nat) {first second : Locals} (h : EnvRel names first second) :
    (first[slot]? = none ∧ second[slot]? = none) ∨
      ∃ x y, first[slot]? = some x ∧ second[slot]? = some y ∧ ValueRel names x.2 y.2 := by
  induction first generalizing second slot with
  | nil =>
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | cons head rest ih =>
    cases h with
    | cons key hv ht =>
      cases slot with
      | zero => exact Or.inr ⟨_, _, rfl, rfl, hv⟩
      | succ slot => simpa using ih slot ht

theorem stateRel_finish {a a' b b' : State} {c c' : Bil.Program} (hs : StateRel globals a a') (hb : StateRel globals b b') (hc : c = c') :
    StateRel globals (emit { b with code := a.code } c) (emit { b' with code := a'.code } c') := by
  rw [← hc, ← hs.code]
  exact (hb.setCode a.code).emit c

/-! ### The simulation -/

/-- The step of `let`. -/
theorem letStep_sim {context : Context} {all body : List Sexp} {fuel : Nat}
    (iEval : ∀ {locals locals' : Locals} {s s' : State} {form : Sexp} {r : SV × State}, EnvRel (namesOf globals) locals locals' →
      StateRel globals s s' → eval fuel locals context s form = .ok r → Reach (ResultRel globals r) fun g => eval g locals' context s' form)
    {current current' : Locals × State} {binding : Sexp} {r : Locals × State}
    (hl : EnvRel (namesOf globals) current.1 current'.1) (hs : StateRel globals current.2 current'.2)
    (h : letStep fuel context all body current binding = .ok r) :
    Reach (fun other => EnvRel (namesOf globals) r.1 other.1 ∧ StateRel globals r.2 other.2)
      fun g => letStep g context all body current' binding := by
  simp only [letStep] at h ⊢
  split at h
  · rename_i name value
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hrel => ?_
    obtain ⟨hv, hst⟩ := hrel
    simp only at hv hst
    have hany : (all ++ body).any (assignsLocal (namesOf s1.globals) name 64) = (all ++ body).any (assignsLocal (namesOf s1'.globals) name 64) := by
      have e1 : assignsLocal (namesOf s1.globals) name 64 = assignsLocal (namesOf globals) name 64 := funext fun form => assignsLocal_compat hst.left name 64 form
      have e2 : assignsLocal (namesOf s1'.globals) name 64 = assignsLocal (namesOf globals) name 64 := funext fun form => assignsLocal_compat hst.right name 64 form
      rw [e1, e2]
    simp only [hany] at h ⊢
    split at h
    · next ha =>
      simp only [ha, ↓reduceIte]
      obtain ⟨⟨v2, s2⟩, h2, h⟩ := bind_ok h
      obtain ⟨other, ho, hr⟩ := bindAssignable_rel context hst hv h2
      refine Reach.bind_pure ho (Reach.pure rfl ?_)
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨.cons _ hr.1 hl, hr.2⟩
    · next ha =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte]
      simp only [Except.ok.injEq] at h
      subst h
      have hr := freeze_rel context hst hv
      exact Reach.pure rfl ⟨.cons _ hr.1 hl, hr.2⟩
  · cases h

theorem foldlM_let_sim {context : Context} {all body : List Sexp} {fuel : Nat}
    (iEval : ∀ {locals locals' : Locals} {s s' : State} {form : Sexp} {r : SV × State}, EnvRel (namesOf globals) locals locals' →
      StateRel globals s s' → eval fuel locals context s form = .ok r → Reach (ResultRel globals r) fun g => eval g locals' context s' form)
    {bindings : List Sexp} {current current' : Locals × State} {r : Locals × State}
    (hl : EnvRel (namesOf globals) current.1 current'.1) (hs : StateRel globals current.2 current'.2)
    (h : bindings.foldlM (letStep fuel context all body) current = .ok r) :
    Reach (fun other => EnvRel (namesOf globals) r.1 other.1 ∧ StateRel globals r.2 other.2)
      fun g => bindings.foldlM (letStep g context all body) current' := by
  induction bindings generalizing current current' with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    exact Reach.pure rfl ⟨hl, hs⟩
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨x, h1, h⟩ := bind_ok h
    exact Reach.bind (letStep_sim iEval hl hs h1) fun y hy => ih hy.1 hy.2 h

/-- A run of a compiled function as a run of it applied, and the other way round. -/
theorem apply_crossing {context : Context} {state : State} (hs : Compat globals state) {params : List String} {body : List Sexp} {env : Locals}
    {compiled : List CExp} (hc : compileFunction (namesOf globals) (.function params body env) = .compiled params compiled env)
    (args : List SV) :
    SameResults (fun f => apply f context state (.callable (.compiled params compiled env)) args)
      (fun f => apply f context state (.callable (.function params body env)) args) := by
  have := apply_compileFunction (context := context) hs (.function params body env) args
  rw [hc] at this
  exact this

theorem Reach.cross {α : Type} {R : α → Prop} {first second : Nat → Except String α} (hf : FuelMono second)
    (hs : ∀ r, Succeeds first r → Succeeds second r) (h : Reach R first) : Reach R second := by
  obtain ⟨x, he, hr⟩ := h
  exact ⟨x, Ev.of_succeeds hf (hs x he.succeeds), hr⟩

/-- That a sequence of forms at a fuel has its results in a second state. -/
abbrev SeqSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {forms : List Sexp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalSequence fuel locals context s forms = .ok r → Reach (ResultRel globals r) fun g => evalSequence g locals' context s' forms

/-- The same of a list of forms. -/
abbrev ListSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {forms : List Sexp} {r : List SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalList fuel locals context s forms = .ok r → Reach (ListResultRel globals r) fun g => evalList g locals' context s' forms

/-- The same of a conditional. -/
abbrev CondSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {test : Sexp} {yes no : List Sexp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalConditional fuel locals context s test yes no = .ok r → Reach (ResultRel globals r) fun g => evalConditional g locals' context s' test yes no

/-- The same of a call. -/
abbrev ApplySim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {s s' : State} {value value' : SV} {args args' : List SV} {r : SV × State}, ValueRel (namesOf globals) value value' → ListRel (namesOf globals) args args' → StateRel globals s s' →
    apply fuel context s value args = .ok r → Reach (ResultRel globals r) fun g => apply g context s' value' args'

/-- The same of a form. -/
abbrev FormSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {form : Sexp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    eval fuel locals context s form = .ok r → Reach (ResultRel globals r) fun g => eval g locals' context s' form

/-- The same of a compiled sequence. -/
abbrev CSeqSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {forms : List CExp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalCompiledSequence fuel locals context s forms = .ok r → Reach (ResultRel globals r) fun g => evalCompiledSequence g locals' context s' forms

/-- The same of a compiled list. -/
abbrev CListSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {forms : List CExp} {r : List SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalCompiledList fuel locals context s forms = .ok r → Reach (ListResultRel globals r) fun g => evalCompiledList g locals' context s' forms

/-- The same of a compiled conditional. -/
abbrev CCondSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {test : CExp} {yes no : List CExp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalCompiledConditional fuel locals context s test yes no = .ok r → Reach (ResultRel globals r) fun g => evalCompiledConditional g locals' context s' test yes no

/-- The same of a compiled form. -/
abbrev CompSim (globals : Globals) (context : Context) (fuel : Nat) : Prop :=
  ∀ {locals locals' : Locals} {s s' : State} {form : CExp} {r : SV × State}, EnvRel (namesOf globals) locals locals' → StateRel globals s s' →
    evalCompiled fuel locals context s form = .ok r → Reach (ResultRel globals r) fun g => evalCompiled g locals' context s' form

/-- All of them at a fuel. -/
structure Sim (globals : Globals) (context : Context) (fuel : Nat) : Prop where
  iSeq : SeqSim globals context fuel
  iList : ListSim globals context fuel
  iCond : CondSim globals context fuel
  iApply : ApplySim globals context fuel
  iEval : FormSim globals context fuel
  iCSeq : CSeqSim globals context fuel
  iCList : CListSim globals context fuel
  iCCond : CCondSim globals context fuel
  iComp : CompSim globals context fuel

theorem Sim.seq_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : SeqSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' forms r hl hs h
  refine Reach.step ?_
  rw [evalSequence.eq_def] at h
  simp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [evalSequence]
    exact Reach.pure rfl ⟨.unit, hs⟩
  · simp only [evalSequence]
    exact iEval hl hs h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalSequence]
    exact Reach.bind (iEval hl hs h1) fun x hx => iSeq hl hx.2 h

theorem Sim.list_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : ListSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' forms r hl hs h
  refine Reach.step ?_
  rw [evalList.eq_def] at h
  simp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [evalList]
    exact Reach.pure rfl ⟨.nil, hs⟩
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [evalList]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iList hl hx.2 h2) fun ⟨vs', s2'⟩ hy => ?_
    exact Reach.pure rfl ⟨.cons hx.1 hy.1, hy.2⟩

theorem Sim.cond_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : CondSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' test yes no r hl hs h
  refine Reach.step ?_
  rw [evalConditional_body] at h
  simp only [evalConditional_body]
  exact conditional_sim (fun r h => iEval hl hs h) (fun _ _ hs r h => iSeq hl hs h) (fun _ _ hs r h => iSeq hl hs h) h

theorem Sim.apply_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : ApplySim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro s s' value value' args args' r hv ha hs h
  refine Reach.step ?_
  rw [apply.eq_def] at h
  simp only at h
  split at h
  · -- a primitive
    rename_i name
    cases hv with
    | callable hc =>
      cases hc
      simp only [apply]
      obtain ⟨⟨v, code⟩, h1, h⟩ := bind_ok h
      obtain ⟨other, h2, hvr⟩ := applyPrimitive_rel context name (resolveDestination_rel hs name ha) v code h1
      refine Reach.bind_pure h2 ?_
      simp only at h ⊢
      split at h
      · next hi =>
        simp only [Except.ok.injEq] at h
        subst h
        simp only [hi, ↓reduceIte]
        exact Reach.pure rfl (freeze_rel context (hs.emit code) hvr)
      · next hi =>
        simp only [Except.ok.injEq] at h
        subst h
        simp only [hi]
        exact Reach.pure rfl ⟨hvr, hs.emit code⟩
  · -- several definitions
    rename_i candidates
    cases hv with
    | callable hc =>
      cases hc with
      | overloads hcand =>
        simp only [apply]
        rcases resolveFunction_rel args.length hcand with ⟨h1, _⟩ | ⟨x, y, h1, h2, hxy⟩
        · simp only [h1] at h
          cases h
        · simp only [h1] at h
          simp only [ha.length_eq] at h2
          simp only [h2]
          exact iApply (.callable hxy) ha hs h
  · -- a function
    rename_i params body env
    have hlen := ha.length_eq
    cases hv with
    | callable hc =>
      split at h
      · cases h
      · rename_i hne
        have hne' : (params.length != args'.length) = false := by
          rw [← hlen]
          simpa using hne
        cases hc with
        | function _ _ he =>
          simp only [apply, hne', Bool.false_eq_true, ↓reduceIte]
          exact iSeq (EnvRel.zip params ha he) hs h
        | @compile _ _ _ compiled hcomp =>
          have hrun : Reach (ResultRel globals r) fun g => apply (g + 1) context s' (.callable (.function params body env)) args' := by
            simp only [apply, hne', Bool.false_eq_true, ↓reduceIte]
            exact iSeq (EnvRel.zip params ha (EnvRel.refl _)) hs h
          exact Reach.unstep (Reach.cross (apply_mono context s' _ args') (fun r h => (apply_crossing hs.right hcomp args' r).2 h) (Reach.step hrun))
  · -- compiled code
    rename_i params body env
    have hlen := ha.length_eq
    cases hv with
    | callable hc =>
      split at h
      · cases h
      · rename_i hne
        have hne' : (params.length != args'.length) = false := by
          rw [← hlen]
          simpa using hne
        cases hc with
        | compiled _ _ he =>
          simp only [apply, hne', Bool.false_eq_true, ↓reduceIte]
          exact iCSeq (EnvRel.zip params ha he) hs h
        | @decompile _ written _ _ hcomp =>
          have hrun : Reach (ResultRel globals r) fun g => apply (g + 1) context s' (.callable (.compiled params body env)) args' := by
            simp only [apply, hne', Bool.false_eq_true, ↓reduceIte]
            exact iCSeq (EnvRel.zip params ha (EnvRel.refl _)) hs h
          exact Reach.unstep (Reach.cross (apply_mono context s' _ args') (fun r h => (apply_crossing hs.right hcomp args' r).1 h) (Reach.step hrun))
  · cases h
  · cases h

theorem Sim.form_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : FormSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' form r hl hs h
  refine Reach.step ?_
  have h0 := h
  rw [eval.eq_def] at h
  simp only at h
  split at h
  · -- an atom
    rename_i atom
    split at h
    · next hc =>
      simp only [Except.ok.injEq] at h
      subst h
      simp only [eval, hc, ↓reduceIte]
      exact Reach.pure rfl ⟨ValueRel.refl _, hs⟩
    · next hc =>
      simp only [eval, hc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨lit, h1, h⟩ := bind_ok h
      refine Reach.bind_pure h1 ?_
      match lit, h with
      | some _, h =>
        simp only [Except.ok.injEq] at h
        subst h
        exact Reach.pure rfl ⟨ValueRel.refl _, hs⟩
      | none, h =>
        obtain ⟨v, h2, h⟩ := bind_ok h
        obtain ⟨other, h3, hv⟩ := lookupState_rel hl hs atom h2
        simp only [Except.ok.injEq] at h
        subst h
        exact Reach.bind_pure h3 (Reach.pure rfl ⟨hv, hs⟩)
  · -- the empty list
    simp only [Except.ok.injEq] at h
    subst h
    simp only [eval]
    exact Reach.pure rfl ⟨.list .nil, hs⟩
  · -- a quotation
    simp only [Except.ok.injEq] at h
    subst h
    simp only [eval]
    exact Reach.pure rfl ⟨ValueRel.refl _, hs⟩
  · -- sizeof
    split at h
    all_goals
      simp only [eval]
      split at h
      · cases h
      · next hb =>
        simp only [Except.ok.injEq] at h
        subst h
        first
          | exact absurd rfl hb
          | (simp only [hb, ↓reduceIte]
             exact Reach.pure rfl ⟨.int _, hs⟩)
  · -- an assertion
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    obtain ⟨tr, h2, h⟩ := bind_ok h
    refine Reach.bind_pure (x := tr) ((truth_rel hx.1).symm.trans h2) ?_
    match tr, h with
    | some true, h =>
      simp only [Except.ok.injEq] at h
      subst h
      exact Reach.pure rfl ⟨.unit, hx.2⟩
    | some false, h => cases h
    | none, h => cases h
  · -- replicate
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨c, s2⟩, h2, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iEval hl hx.2 h2) fun ⟨c', s2'⟩ hy => ?_
    obtain ⟨n, h3, h⟩ := bind_ok h
    refine Reach.bind_pure (x := n) ((expectNat_rel hy.1).symm.trans h3) ?_
    obtain ⟨⟨w, e⟩, h4, h⟩ := bind_ok h
    refine Reach.bind_pure (x := (w, e)) ((expectBil_rel context hx.1).symm.trans h4) ?_
    split at h
    · cases h
    · next hn =>
      simp only [Except.ok.injEq] at h
      subst h
      simp only [hn, ↓reduceIte]
      exact Reach.pure rfl ⟨.bil _ _, hy.2⟩
  · -- replicate by its other name
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨c, s2⟩, h2, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iEval hl hx.2 h2) fun ⟨c', s2'⟩ hy => ?_
    obtain ⟨n, h3, h⟩ := bind_ok h
    refine Reach.bind_pure (x := n) ((expectNat_rel hy.1).symm.trans h3) ?_
    obtain ⟨⟨w, e⟩, h4, h⟩ := bind_ok h
    refine Reach.bind_pure (x := (w, e)) ((expectBil_rel context hx.1).symm.trans h4) ?_
    split at h
    · cases h
    · next hn =>
      simp only [Except.ok.injEq] at h
      subst h
      simp only [hn, ↓reduceIte]
      exact Reach.pure rfl ⟨.bil _ _, hy.2⟩
  · -- clz
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    obtain ⟨y, h2, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    exact Reach.bind_pure ((leadingZeros_rel context (.cons hx.1 .nil)).symm.trans h2) (Reach.pure rfl ⟨ValueRel.refl _, hx.2⟩)
  · simp only [eval]
    exact iCond hl hs h
  · simp only [eval]
    exact iCond hl hs h
  · simp only [eval]
    exact iCond hl hs h
  · simp only [eval]
    exact iSeq hl hs h
  · simp only [eval]
    exact iSeq hl hs h
  · -- a loop
    rename_i test body
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs.clear h1) fun ⟨v', s1'⟩ hx => ?_
    obtain ⟨hv, hst⟩ := hx
    simp only at hv hst
    obtain ⟨tr, h2, h⟩ := bind_ok h
    refine Reach.bind_pure (x := tr) ((truth_rel hv).symm.trans h2) ?_
    have tail :
        (do
          let condition ← condition context v
          let (_, bodyState) ← evalSequence fuel locals context { s1 with code := [] } body
          Except.ok (Value.unit, emit { bodyState with code := s.code } (s1.code ++ [.while condition (bodyState.code ++ s1.code)]))) = Except.ok r →
        Reach (ResultRel globals r) fun g =>
          (do
            let condition ← condition context v'
            let (_, bodyState) ← evalSequence g locals' context { s1' with code := [] } body
            Except.ok (Value.unit, emit { bodyState with code := s'.code } (s1'.code ++ [.while condition (bodyState.code ++ s1'.code)]))) := by
      intro he
      obtain ⟨c, h3, he⟩ := bind_ok he
      refine Reach.bind_pure (x := c) ((condition_rel context hv).symm.trans h3) ?_
      obtain ⟨⟨_, bs⟩, h4, he⟩ := bind_ok he
      simp only [Except.ok.injEq] at he
      subst he
      refine Reach.bind (iSeq hl hst.clear h4) fun ⟨_, bs'⟩ hb => ?_
      have hb2 : StateRel globals bs bs' := hb.2
      refine Reach.pure rfl ⟨.unit, stateRel_finish hs hb2 ?_⟩
      simp only [hb2.code, hst.code]
    match tr, h with
    | some false, h =>
      simp only [Except.ok.injEq] at h
      subst h
      refine Reach.pure rfl ⟨.unit, stateRel_finish hs hst ?_⟩
      simp only [hst.code]
    | some true, h => exact tail h
    | none, h => exact tail h
  · -- an error
    split at h <;> cases h
  · -- a message
    simp only [Except.ok.injEq] at h
    subst h
    simp only [eval]
    exact Reach.pure rfl ⟨.unit, hs⟩
  · -- let
    rename_i bindings body
    obtain ⟨⟨locals2, s2⟩, h1, h⟩ := bind_ok h
    have hE : ∀ f, eval (f + 1) locals' context s' (.list (.atom "let" :: .list bindings :: body)) =
        bindings.foldlM (letStep f context bindings body) (locals', s') >>= fun x =>
          evalSequence f x.1 context x.2 body := by
      intro f
      rw [eval]
      rfl
    simp only [hE]
    refine Reach.bind (foldlM_let_sim iEval hl hs h1) fun x hx => ?_
    exact iSeq hx.1 hx.2 h
  · -- a function
    obtain ⟨params, h1, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [eval]
    exact Reach.bind_pure h1 (Reach.pure rfl ⟨.callable (.function _ _ hl), hs⟩)
  · -- a case
    rename_i key branches
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    obtain ⟨forms, h2, h⟩ := bind_ok h
    refine Reach.bind_pure (x := forms) ((selectForm_rel hx.1 branches).symm.trans h2) ?_
    exact iSeq hl hx.2 h
  · -- a call of a name
    rename_i operator operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have hE : ∀ f, eval (f + 1) locals' context s' (.list (.atom operator :: operands)) = (do
        let expansion ← match ← lookupState operator locals' s' with
          | .callable callable =>
            if (Assoc.get operator locals').isSome then .ok none else macroExpansion callable operands
          | _ => .ok none
        match expansion with
        | some expanded => evalSequence f locals' context s' expanded
        | none =>
          eval f locals' context s' (.atom operator) >>= fun x =>
            evalList f locals' context x.2 operands >>= fun y => apply f context y.2 x.1 y.1) := by
      intro f
      rw [eval]
      · rfl
      all_goals (intros; simp_all)
    simp only [hE]
    obtain ⟨lv, h1, h⟩ := bind_ok h
    obtain ⟨other, h2, hlv⟩ := lookupState_rel hl hs operator h1
    refine Reach.bind_pure h2 ?_
    have tail : ∀ {e : Except String (Option (List Sexp))},
        (do
          let expansion ← e
          match expansion with
          | some body => evalSequence fuel locals context s body
          | none => do
            let x ← eval fuel locals context s (Sexp.atom operator)
            let y ← evalList fuel locals context x.2 operands
            apply fuel context y.2 x.1 y.1) = .ok r →
        Reach (ResultRel globals r) fun g =>
          (do
            let expansion ← e
            match expansion with
            | some body => evalSequence g locals' context s' body
            | none => do
              let x ← eval g locals' context s' (Sexp.atom operator)
              let y ← evalList g locals' context x.2 operands
              apply g context y.2 x.1 y.1) := by
      intro e he
      obtain ⟨exp, h3, he⟩ := bind_ok he
      refine Reach.bind_pure h3 ?_
      match exp, he with
      | some expanded, he => exact iSeq hl hs he
      | none, he =>
        obtain ⟨⟨v, s1⟩, h4, he⟩ := bind_ok he
        obtain ⟨⟨vs, s2⟩, h5, he⟩ := bind_ok he
        refine Reach.bind (iEval hl hs h4) fun ⟨v', s1'⟩ hx => ?_
        refine Reach.bind (iList hl hx.2 h5) fun ⟨vs', s2'⟩ hy => ?_
        exact iApply hx.1 hy.1 hy.2 he
    have hsome : (Assoc.get operator locals).isSome = (Assoc.get operator locals').isSome := by
      rcases envGet_rel operator hl with ⟨e1, e2⟩ | ⟨x, y, e1, e2, _⟩ <;> simp only [e1, e2, Option.isSome]
    cases hlv with
    | callable hc =>
      simp only at h ⊢
      rw [← hsome, ← macroExpansion_rel hc]
      by_cases hb : (Assoc.get operator locals).isSome = true
      · simp only [hb] at h ⊢
        exact tail h
      · simp only [hb] at h ⊢
        exact tail h
    | unit => exact tail h
    | int => exact tail h
    | bil => exact tail h
    | bool => exact tail h
    | register => exact tail h
    | symbol => exact tail h
    | list => exact tail h
  · -- a call of a form
    rename_i operator operands _
    obtain ⟨⟨v, s1⟩, h4, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h5, h⟩ := bind_ok h
    simp only [eval]
    refine Reach.bind (iEval hl hs h4) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iList hl hx.2 h5) fun ⟨vs', s2'⟩ hy => ?_
    exact iApply hx.1 hy.1 hy.2 h

theorem Sim.cseq_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : CSeqSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' forms r hl hs h
  refine Reach.step ?_
  rw [evalCompiledSequence.eq_def] at h
  simp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [evalCompiledSequence]
    exact Reach.pure rfl ⟨.unit, hs⟩
  · simp only [evalCompiledSequence]
    exact iComp hl hs h
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiledSequence]
    exact Reach.bind (iComp hl hs h1) fun x hx => iCSeq hl hx.2 h

theorem Sim.clist_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : CListSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' forms r hl hs h
  refine Reach.step ?_
  rw [evalCompiledList.eq_def] at h
  simp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp only [evalCompiledList]
    exact Reach.pure rfl ⟨.nil, hs⟩
  · obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    simp only [evalCompiledList]
    refine Reach.bind (iComp hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iCList hl hx.2 h2) fun ⟨vs', s2'⟩ hy => ?_
    exact Reach.pure rfl ⟨.cons hx.1 hy.1, hy.2⟩

theorem Sim.ccond_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : CCondSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' test yes no r hl hs h
  refine Reach.step ?_
  rw [evalCompiledConditional_body] at h
  simp only [evalCompiledConditional_body]
  exact conditional_sim (fun r h => iComp hl hs h) (fun _ _ hs r h => iCSeq hl hs h) (fun _ _ hs r h => iCSeq hl hs h) h

theorem Sim.comp_succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : CompSim globals context (fuel + 1) := by
  obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
  intro locals locals' s s' form r hl hs h
  refine Reach.step ?_
  rw [evalCompiled.eq_def] at h
  simp only at h
  split at h
  · -- a value
    simp only [Except.ok.injEq] at h
    subst h
    simp only [evalCompiled]
    exact Reach.pure rfl ⟨ValueRel.refl _, hs⟩
  · -- a local
    rename_i slot
    simp only [evalCompiled]
    rcases envSlot_rel slot hl with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
    · simp only [h1] at h
      cases h
    · simp only [h1, Except.ok.injEq] at h
      subst h
      simp only [h2]
      exact Reach.pure rfl ⟨hxy, hs⟩
  · -- a global
    rename_i name
    simp only [evalCompiled]
    rw [hs.left.index name] at h
    rw [hs.right.index name]
    rcases stateGet_rel hs name with ⟨h3, h4⟩ | ⟨x, y, h3, h4, hv⟩
    · simp only [h3] at h
      cases h
    · simp only [h3] at h
      simp only [h4]
      cases hv
      all_goals
        simp only [Except.ok.injEq] at h
        subst h
        exact Reach.pure rfl ⟨by constructor <;> assumption, hs⟩
  · -- a primitive
    rename_i operation operands
    simp only [evalCompiled]
    obtain ⟨⟨vs, s1⟩, h1, h⟩ := bind_ok h
    refine Reach.bind (iCList hl hs h1) fun ⟨vs', s1'⟩ hx => ?_
    obtain ⟨hvs, hst⟩ := hx
    simp only at hvs hst
    obtain ⟨⟨v, code⟩, h2, h⟩ := bind_ok h
    simp only [Except.ok.injEq] at h
    subst h
    have hargs : ListRel (namesOf globals)
        (if (decide (operation = 38) || decide (operation = 39) || decide (operation = 40)) = true then resolveSymbol s1 vs else vs)
        (if (decide (operation = 38) || decide (operation = 39) || decide (operation = 40)) = true then resolveSymbol s1' vs' else vs') := by
      split
      · exact resolveSymbol_rel hst hvs
      · exact hvs
    obtain ⟨other, h3, hvr⟩ := applyPrimitiveIndex_rel context operation hargs v code h2
    exact Reach.bind_pure h3 (Reach.pure rfl ⟨hvr, hst.emit code⟩)
  · -- a call
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨vs, s2⟩, h2, h⟩ := bind_ok h
    simp only [evalCompiled]
    refine Reach.bind (iComp hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    refine Reach.bind (iCList hl hx.2 h2) fun ⟨vs', s2'⟩ hy => ?_
    exact iApply hx.1 hy.1 hy.2 h
  · simp only [evalCompiled]
    exact iCCond hl hs h
  · -- a binding
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiled]
    refine Reach.bind (iComp hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    have hf := freeze_rel context hx.2 hx.1
    exact iComp (.cons "" hf.1 hl) hf.2 h
  · simp only [evalCompiled]
    exact iCSeq hl hs h
  · -- a case
    rename_i key arms
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_ok h
    simp only [evalCompiled]
    refine Reach.bind (iComp hl hs h1) fun ⟨v', s1'⟩ hx => ?_
    obtain ⟨arm, h2, h⟩ := bind_ok h
    refine Reach.bind_pure (x := arm) (by rw [← selectArm_rel hx.1]; exact h2) ?_
    exact iComp hl hx.2 h

theorem StateRel.symm {first second : State} (h : StateRel globals first second) : StateRel globals second first :=
  ⟨h.right, h.left, h.code.symm, h.nextTemp.symm⟩

theorem Sim.succ {globals : Globals} {context : Context} {fuel : Nat} (ih : Sim globals context fuel) : Sim globals context (fuel + 1) :=
  ⟨ih.seq_succ, ih.list_succ, ih.cond_succ, ih.apply_succ, ih.form_succ, ih.cseq_succ, ih.clist_succ, ih.ccond_succ, ih.comp_succ⟩

theorem Sim.zero (globals : Globals) (context : Context) : Sim globals context 0 := by
  refine ⟨fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_,
    fun _ _ h => ?_, fun _ _ h => ?_⟩ <;> first
    | (rw [evalSequence] at h; simp at h; done)
    | (rw [evalList] at h; simp at h; done)
    | (rw [evalConditional] at h; simp at h; done)
    | (rw [apply] at h; simp at h; done)
    | (rw [eval] at h; simp at h; done)
    | (rw [evalCompiledSequence] at h; simp at h; done)
    | (rw [evalCompiledList] at h; simp at h; done)
    | (rw [evalCompiledConditional] at h; simp at h; done)
    | (rw [evalCompiled] at h; simp at h; done)

/-- **The simulation**, at every fuel. -/
theorem simulation (globals : Globals) (context : Context) (fuel : Nat) : Sim globals context fuel := by
  induction fuel with
  | zero => exact Sim.zero globals context
  | succ fuel ih => exact ih.succ

/-! ### What it says -/

/-- Two results of the same run, in states that differ in what is compiled: the same value up to which functions in it are compiled, the same code and the
same temporaries. A value with no function in it is the same value (`ValueRel.eq_of_firstOrder`). -/
def SameOutcome (globals : Globals) (first second : SV × State) : Prop :=
  ValueRel (namesOf globals) first.1 second.1 ∧ first.2.code = second.2.code ∧ first.2.nextTemp = second.2.nextTemp

/-- Each family's successes are successes of the other, with the same outcome. -/
def SameOutcomes {α : Type} (R : α → α → Prop) (first second : Nat → Except String α) : Prop :=
  (∀ r, Succeeds first r → ∃ other, Succeeds second other ∧ R r other) ∧
    ∀ other, Succeeds second other → ∃ r, Succeeds first r ∧ R r other

/-- **A call has the same outcomes in any two states that compiled code runs in**, whichever definitions each has compiled, as long as they start with the same code and
temporaries and the function and its arguments are the same up to compilation. -/
theorem apply_same_outcomes {first second : State} (hs : StateRel globals first second) (context : Context) {value value' : SV} {args args' : List SV}
    (hv : ValueRel (namesOf globals) value value') (ha : ListRel (namesOf globals) args args') :
    SameOutcomes (SameOutcome globals) (fun fuel => apply fuel context first value args)
      (fun fuel => apply fuel context second value' args') := by
  constructor
  · rintro r ⟨fuel, h⟩
    obtain ⟨other, he, hr⟩ := (simulation globals context fuel).iApply hv ha hs h
    exact ⟨other, he.succeeds, hr.1, hr.2.code, hr.2.nextTemp⟩
  · rintro other ⟨fuel, h⟩
    obtain ⟨r, he, hr⟩ := (simulation globals context fuel).iApply hv.symm ha.symm hs.symm h
    exact ⟨r, he.succeeds, hr.1.symm, hr.2.code.symm, hr.2.nextTemp.symm⟩

/-- So does a form. -/
theorem eval_same_outcomes {first second : State} (hs : StateRel globals first second) (context : Context) {locals locals' : Locals}
    (hl : EnvRel (namesOf globals) locals locals') (form : Sexp) :
    SameOutcomes (SameOutcome globals) (fun fuel => eval fuel locals context first form)
      (fun fuel => eval fuel locals' context second form) := by
  constructor
  · rintro r ⟨fuel, h⟩
    obtain ⟨other, he, hr⟩ := (simulation globals context fuel).iEval hl hs h
    exact ⟨other, he.succeeds, hr.1, hr.2.code, hr.2.nextTemp⟩
  · rintro other ⟨fuel, h⟩
    obtain ⟨r, he, hr⟩ := (simulation globals context fuel).iEval hl.symm hs.symm h
    exact ⟨r, he.succeeds, hr.1.symm, hr.2.code.symm, hr.2.nextTemp.symm⟩

end Bap.Proofs.Primus
