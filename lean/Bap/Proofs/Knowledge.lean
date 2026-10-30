import Lean.Elab.Command
import Std.Data.String.ToNat
import Bap.Knowledge.Core
import Bap.Knowledge.Persist

/-- Brings a private production definition into scope under a local alias. -/
local elab "open_private " mod:ident p:ident " as " a:ident : command => do
  let priv := Lean.mkPrivateNameCore mod.getId p.getId
  unless (← Lean.getEnv).contains priv do Lean.throwError "no private name {priv}"
  Lean.modifyEnv (Lean.addAlias · ((← Lean.getCurrNamespace) ++ a.getId) priv)

namespace Bap.Proofs.Knowledge

open Bap.Knowledge

open_private Bap.Knowledge.Core Bap.Knowledge.putFact as putFact
open_private Bap.Knowledge.Core Bap.Knowledge.putOpinion as putOpinion
open_private Bap.Knowledge.Core Bap.Knowledge.joinOpinions as joinOpinions
open_private Bap.Knowledge.Core Bap.Knowledge.runPromises as runPromises
open_private Bap.Knowledge.Core Bap.Knowledge.normalize as normalize
open_private Bap.Bil.Wire Bap.Bil.Wire.hexDigit as hexDigit
open_private Bap.Bil.Wire Bap.Bil.Wire.parseHexLoop as parseHexLoop

/-! ## Domains -/

/-- The partial join-semilattice laws a knowledge domain should satisfy. -/
structure Lawful (domain : Domain α) : Prop where
  eq_iff (left right : α) : domain.eq left right = true ↔ left = right
  comm (left right : α) : domain.join left right = domain.join right left
  assoc (a b c : α) :
    (domain.join a b).bind (domain.join · c) = (domain.join b c).bind (domain.join a ·)
  idem (value : α) : domain.join value value = some value
  empty_left (value : α) : domain.join domain.empty value = some value

theorem maxDomain_lawful : Lawful maxDomain where
  eq_iff left right := by simp [maxDomain]
  comm left right := by simp [maxDomain, Nat.max_comm]
  assoc a b c := by simp [maxDomain, Nat.max_assoc]
  idem value := by simp [maxDomain]
  empty_left value := by simp [maxDomain]

theorem boolDomain_lawful : Lawful boolDomain where
  eq_iff left right := by simp [boolDomain]
  comm left right := by simp [boolDomain, Bool.or_comm]
  assoc a b c := by simp [boolDomain, Bool.or_assoc]
  idem value := by simp [boolDomain]
  empty_left value := by simp [boolDomain]

theorem unitDomain_lawful : Lawful unitDomain where
  eq_iff _ _ := by simp [unitDomain]
  comm _ _ := rfl
  assoc _ _ _ := rfl
  idem _ := rfl
  empty_left _ := rfl

theorem exactDomain_lawful [DecidableEq α] (empty : α) : Lawful (exactDomain empty) where
  eq_iff left right := by simp [exactDomain]
  comm left right := by
    simp only [exactDomain]
    by_cases h₁ : left = empty <;> by_cases h₂ : right = empty <;> by_cases h₃ : left = right <;>
      simp_all [eq_comm]
  assoc a b c := by
    simp only [exactDomain]
    by_cases h₁ : a = empty <;> by_cases h₂ : b = empty <;> by_cases h₃ : c = empty <;>
      by_cases h₄ : a = b <;> by_cases h₅ : b = c <;> by_cases h₆ : a = c <;> simp_all
  idem value := by
    simp only [exactDomain]
    by_cases h : value = empty <;> simp [h]
  empty_left value := by simp [exactDomain]

/-- `stringDomain` is the exact domain over the empty string. -/
theorem stringDomain_eq_exact : stringDomain = exactDomain "" := by
  simp only [stringDomain, exactDomain, Domain.mk.injEq, true_and]
  funext left right
  by_cases h₁ : left = "" <;> by_cases h₂ : right = "" <;> simp [h₁, h₂, String.isEmpty_iff]

theorem stringDomain_lawful : Lawful stringDomain :=
  stringDomain_eq_exact ▸ exactDomain_lawful ""

theorem optionDomain_lawful [DecidableEq α] : Lawful (optionDomain (α := α)) where
  eq_iff left right := by simp [optionDomain]
  comm left right := by
    cases left <;> cases right <;> simp [optionDomain]
    rename_i a b
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  assoc a b c := by
    rcases a with _ | x <;> rcases b with _ | y <;> rcases c with _ | z
    · simp [optionDomain]
    · simp [optionDomain]
    · simp [optionDomain]
    · by_cases h : y = z <;> simp [optionDomain, h]
    · simp [optionDomain]
    · by_cases h : x = z <;> simp [optionDomain, h]
    · by_cases h : x = y <;> simp [optionDomain, h]
    · by_cases h₁ : x = y <;> by_cases h₂ : y = z <;> simp_all [optionDomain]
  idem value := by cases value <;> simp [optionDomain]
  empty_left value := by cases value <;> simp [optionDomain]

section Order

variable {domain : Domain α}

/-- Information order induced by a domain: `right` already contains `left`. -/
abbrev Refines (domain : Domain α) (left right : α) : Prop := domain.join left right = some right

theorem Lawful.empty_right (h : Lawful domain) (value : α) : domain.join value domain.empty = some value := by
  rw [h.comm, h.empty_left]

theorem Lawful.refines_refl (h : Lawful domain) (value : α) : Refines domain value value := h.idem value

theorem Lawful.empty_refines (h : Lawful domain) (value : α) : Refines domain domain.empty value :=
  h.empty_left value

theorem Lawful.refines_trans (h : Lawful domain) {a b c : α} (hab : Refines domain a b)
    (hbc : Refines domain b c) : Refines domain a c := by
  have := h.assoc a b c
  simp only [Refines] at hab hbc
  simpa [hab, hbc] using this.symm

theorem Lawful.refines_antisymm (h : Lawful domain) {a b : α} (hab : Refines domain a b)
    (hba : Refines domain b a) : a = b := by
  simp only [Refines] at hab hba
  rw [h.comm, hab] at hba
  exact (Option.some.inj hba).symm

/-- The result of a successful join is an upper bound of both arguments. -/
theorem Lawful.join_upper (h : Lawful domain) {a b c : α} (hj : domain.join a b = some c) :
    Refines domain a c ∧ Refines domain b c := by
  constructor
  · have := h.assoc a a b
    rw [h.idem, Option.bind_some, hj, Option.bind_some] at this
    exact this.symm
  · have := h.assoc a b b
    rw [h.idem, Option.bind_some, hj, Option.bind_some] at this
    rw [Refines, h.comm]
    exact this

/-- The result of a successful join is below every other upper bound. -/
theorem Lawful.join_least (h : Lawful domain) {a b c d : α} (hj : domain.join a b = some c)
    (had : Refines domain a d) (hbd : Refines domain b d) : Refines domain c d := by
  have := h.assoc a b d
  simp only [Refines] at had hbd
  simpa [hj, hbd, had] using this

/-- A join fails exactly when the two values have no common refinement. -/
theorem Lawful.join_none_iff (h : Lawful domain) (a b : α) :
    domain.join a b = none ↔ ∀ d, ¬(Refines domain a d ∧ Refines domain b d) := by
  constructor
  · rintro hj d ⟨had, hbd⟩
    have := h.assoc a b d
    simp only [Refines] at had hbd
    simp [hj, hbd, had] at this
  · intro hno
    cases hj : domain.join a b with
    | none => rfl
    | some c => exact absurd (h.join_upper hj) (hno c)

end Order

/-! ## Lookup and the fact table -/

section Facts

variable {kind other : PayloadKind}

/-- The cell key under which `provide` stores a fact. -/
def factKey (fact : Fact) : Object × String := (fact.object, fact.slot.2.name)

private theorem lookup_putFact_self (slot : Slot kind) (reader : Slot kind) (object : Object)
    (value : kind.data) (facts : List Fact) (hname : reader.name = slot.name) :
    lookupFact reader object (putFact ⟨object, ⟨kind, slot⟩, value⟩ facts) = .ok (some value) := by
  simp [lookupFact, putFact, hname]

private theorem find?_filter_of_imp {p q : Fact → Bool} (values : List Fact)
    (h : ∀ value, p value = true → q value = true) :
    (values.filter q).find? p = values.find? p := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.filter_cons]
    cases hq : q head with
    | true => simp [List.find?_cons, ih]
    | false =>
      have hp : p head = false := by
        cases hp : p head with
        | false => rfl
        | true => simpa [hq] using h head hp
      simp [hp, ih]

private theorem lookup_putFact_frame (reader : Slot other) (key : Object) (fact : Fact) (facts : List Fact)
    (hkey : (key, reader.name) ≠ factKey fact) :
    lookupFact reader key (putFact fact facts) = lookupFact reader key facts := by
  have hne : ¬(fact.object = key ∧ fact.slot.2.name = reader.name) := by
    rintro ⟨h₁, h₂⟩
    exact hkey (by simp [factKey, h₁, h₂])
  have hfind : (putFact fact facts).find? (fun f => decide (f.object = key ∧ f.slot.2.name = reader.name)) =
      facts.find? (fun f => decide (f.object = key ∧ f.slot.2.name = reader.name)) := by
    simp only [putFact, List.find?_cons, hne, decide_false]
    apply find?_filter_of_imp
    intro value hp
    simp only [decide_eq_true_eq] at hp
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_cases ho : value.object = fact.object
    · refine Or.inr fun hn => hne ⟨ho.symm.trans hp.1, hn.symm.trans hp.2⟩
    · exact Or.inl ho
  simp only [lookupFact, hfind]

theorem provideInFacts_fresh (slot : Slot kind) (object : Object) (value : kind.data) (facts : List Fact)
    (h : lookupFact slot object facts = .ok none) :
    provideInFacts slot object value facts = .ok (true, putFact ⟨object, ⟨kind, slot⟩, value⟩ facts) := by
  simp only [provideInFacts, bind, Except.bind, h]

theorem provideInFacts_existing (slot : Slot kind) (object : Object) (value existing : kind.data)
    (facts : List Fact) (h : lookupFact slot object facts = .ok (some existing)) :
    provideInFacts slot object value facts =
      match slot.domain.join existing value with
      | none => .error (.incompatible slot.name)
      | some joined =>
        if slot.domain.eq existing joined then .ok (false, facts)
        else .ok (true, putFact ⟨object, ⟨kind, slot⟩, joined⟩ facts) := by
  simp only [provideInFacts, bind, Except.bind, h]
  rfl

/-- A slot name used at another payload kind is reported, never reinterpreted. -/
theorem provideInFacts_mismatch (slot : Slot kind) (object : Object) (value : kind.data)
    (facts : List Fact) {conflict : Conflict} (h : lookupFact slot object facts = .error conflict) :
    provideInFacts slot object value facts = .error conflict := by
  simp only [provideInFacts, bind, Except.bind, h]

theorem provideInFacts_conflict (slot : Slot kind) (object : Object) {value existing : kind.data}
    {facts : List Fact} (h : lookupFact slot object facts = .ok (some existing))
    (hj : slot.domain.join existing value = none) :
    provideInFacts slot object value facts = .error (.incompatible slot.name) := by
  rw [provideInFacts_existing slot object value existing facts h, hj]

/-- A `false` change flag really means the table was left untouched. -/
theorem provideInFacts_unchanged {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} (h : provideInFacts slot object value facts = .ok (false, next)) :
    next = facts := by
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object value facts hl] at h; cases h
  | ok result =>
    cases result with
    | none => rw [provideInFacts_fresh slot object value facts hl] at h; cases h
    | some existing =>
      rw [provideInFacts_existing slot object value existing facts hl] at h
      split at h
      · cases h
      · split at h
        · cases h; rfl
        · cases h

/-- What a successful `provideInFacts` leaves at the cell it wrote. -/
private theorem provideInFacts_read {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (h : provideInFacts slot object value facts = .ok (changed, next))
    (heq : Lawful slot.domain) :
    ∃ result, lookupFact slot object next = .ok (some result) ∧
      ((lookupFact slot object facts = .ok none ∧ result = value ∧ changed = true) ∨
        ∃ existing, lookupFact slot object facts = .ok (some existing) ∧
          slot.domain.join existing value = some result ∧ (changed = true ↔ existing ≠ result)) := by
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object value facts hl] at h; cases h
  | ok found =>
    cases found with
    | none =>
      rw [provideInFacts_fresh slot object value facts hl] at h
      cases h
      exact ⟨value, lookup_putFact_self slot slot object value facts rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    | some existing =>
      rw [provideInFacts_existing slot object value existing facts hl] at h
      split at h
      · cases h
      · rename_i joined hj
        split at h
        · rename_i he
          cases h
          have hsame := (heq.eq_iff _ _).1 he
          subst hsame
          exact ⟨existing, hl, Or.inr ⟨existing, rfl, hj, by simp⟩⟩
        · rename_i he
          cases h
          have hne : existing ≠ joined := fun hs => he ((heq.eq_iff _ _).2 hs)
          exact ⟨joined, lookup_putFact_self slot slot object joined facts rfl,
            Or.inr ⟨existing, rfl, hj, by simp [hne]⟩⟩

/-- A successful provide never loses information: the cell afterwards refines both the old
contents and the provided value. -/
theorem provideInFacts_monotone {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (hd : Lawful slot.domain)
    (h : provideInFacts slot object value facts = .ok (changed, next)) :
    ∃ result, lookupFact slot object next = .ok (some result) ∧ Refines slot.domain value result ∧
      ∀ existing, lookupFact slot object facts = .ok (some existing) →
        Refines slot.domain existing result := by
  obtain ⟨result, hread, hcase⟩ := provideInFacts_read h hd
  refine ⟨result, hread, ?_, ?_⟩
  · rcases hcase with ⟨_, rfl, _⟩ | ⟨existing, _, hj, _⟩
    · exact hd.refines_refl _
    · exact (hd.join_upper hj).2
  · intro existing hex
    rcases hcase with ⟨hnone, _⟩ | ⟨old, hold, hj, _⟩
    · rw [hnone] at hex; cases hex
    · rw [hold] at hex
      cases hex
      exact (hd.join_upper hj).1

/-- Providing a value touches only its own cell. -/
theorem provideInFacts_frame {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (h : provideInFacts slot object value facts = .ok (changed, next))
    (reader : Slot other) (key : Object) (hkey : key ≠ object ∨ reader.name ≠ slot.name) :
    lookupFact reader key next = lookupFact reader key facts := by
  have hfresh (val : kind.data) :
      lookupFact reader key (putFact ⟨object, ⟨kind, slot⟩, val⟩ facts) = lookupFact reader key facts := by
    apply lookup_putFact_frame
    intro he
    simp only [factKey, Prod.mk.injEq] at he
    rcases hkey with hk | hk
    · exact hk he.1
    · exact hk he.2
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object value facts hl] at h; cases h
  | ok found =>
    cases found with
    | none =>
      rw [provideInFacts_fresh slot object value facts hl] at h
      cases h
      exact hfresh value
    | some existing =>
      rw [provideInFacts_existing slot object value existing facts hl] at h
      split at h
      · cases h
      · split at h
        · cases h; rfl
        · cases h; exact hfresh _

/-- The table holds at most one fact per object and slot name. -/
private theorem putFact_keys_nodup (fact : Fact) (facts : List Fact) (h : (facts.map factKey).Nodup) :
    ((putFact fact facts).map factKey).Nodup := by
  have hfilter : ∀ values : List Fact, (values.map factKey).Nodup →
      ((values.filter fun old => old.object != fact.object || old.slot.2.name != fact.slot.2.name).map factKey).Nodup := by
    intro values hv
    exact (hv.sublist (List.Sublist.map _ List.filter_sublist))
  simp only [putFact, List.map_cons, List.nodup_cons]
  refine ⟨?_, hfilter _ h⟩
  simp only [List.mem_map, List.mem_filter, not_exists, not_and]
  rintro x ⟨_, hne⟩ heq
  simp only [factKey, Prod.mk.injEq] at heq
  simp [heq] at hne

theorem provideInFacts_keys_nodup {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (h : provideInFacts slot object value facts = .ok (changed, next))
    (hkeys : (facts.map factKey).Nodup) : (next.map factKey).Nodup := by
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object value facts hl] at h; cases h
  | ok found =>
    cases found with
    | none =>
      rw [provideInFacts_fresh slot object value facts hl] at h
      cases h
      exact putFact_keys_nodup _ _ hkeys
    | some existing =>
      rw [provideInFacts_existing slot object value existing facts hl] at h
      split at h
      · cases h
      · split at h
        · cases h; exact hkeys
        · cases h; exact putFact_keys_nodup _ _ hkeys

end Facts

/-! ## The knowledge state -/

section Provide

variable {kind other : PayloadKind} {slot : Slot kind} {object : Object} {value : kind.data}
  {state next : State}

theorem provide_ok_iff :
    provide slot object value state = .ok next ↔
      ∃ changed facts, provideInFacts slot object value state.facts = .ok (changed, facts) ∧
        next = { state with facts := facts, version := state.version + changed.toNat } := by
  simp only [provide, bind, Except.bind]
  cases hp : provideInFacts slot object value state.facts with
  | error conflict => simp
  | ok result =>
    obtain ⟨changed, facts⟩ := result
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro h
      cases h
      exact ⟨changed, facts, ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h.symm

/-- `provide` bumps the version by at most one and leaves opinions alone. -/
theorem provide_version (h : provide slot object value state = .ok next) :
    (next.version = state.version ∨ next.version = state.version + 1) ∧ next.opinions = state.opinions := by
  obtain ⟨changed, facts, _, rfl⟩ := provide_ok_iff.1 h
  cases changed <;> simp

/-- The version stays put exactly when the table does. -/
theorem provide_facts_of_version_eq (h : provide slot object value state = .ok next)
    (hv : next.version = state.version) : next.facts = state.facts := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  cases changed with
  | false => exact provideInFacts_unchanged hp
  | true => simp at hv

theorem provide_read (hd : Lawful slot.domain) (h : provide slot object value state = .ok next) :
    ∃ result, lookupFact slot object next.facts = .ok (some result) ∧ Refines slot.domain value result ∧
      ∀ existing, lookupFact slot object state.facts = .ok (some existing) →
        Refines slot.domain existing result := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  exact provideInFacts_monotone hd hp

/-- A successful provide on an empty cell reads back the exact value. -/
theorem provide_read_fresh (h : provide slot object value state = .ok next)
    (hnone : lookupFact slot object state.facts = .ok none) :
    lookupFact slot object next.facts = .ok (some value) ∧ next.version = state.version + 1 := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  rw [provideInFacts_fresh slot object value _ hnone] at hp
  cases hp
  exact ⟨lookup_putFact_self slot slot object value _ rfl, rfl⟩

theorem provide_frame (h : provide slot object value state = .ok next) (reader : Slot other) (key : Object)
    (hkey : key ≠ object ∨ reader.name ≠ slot.name) :
    lookupFact reader key next.facts = lookupFact reader key state.facts := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  exact provideInFacts_frame hp reader key hkey

/-- Providing the same value twice changes nothing the second time. -/
theorem provide_idempotent (hd : Lawful slot.domain) (h : provide slot object value state = .ok next) :
    provide slot object value next = .ok next := by
  obtain ⟨result, hread, hval, _⟩ := provide_read hd h
  have hj : slot.domain.join result value = some result := by
    rw [hd.comm]
    exact hval
  have hself : slot.domain.eq result result = true := (hd.eq_iff _ _).2 rfl
  simp only [provide, bind, Except.bind]
  rw [provideInFacts_existing slot object value result _ hread, hj]
  simp [hself]

private theorem provide_read_cases {v : kind.data} {source target : State} (hd : Lawful slot.domain)
    (hs : provide slot object v source = .ok target) :
    ∃ result, lookupFact slot object target.facts = .ok (some result) ∧
      ((lookupFact slot object source.facts = .ok none ∧ result = v) ∨
        ∃ existing, lookupFact slot object source.facts = .ok (some existing) ∧
          slot.domain.join existing v = some result) := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 hs
  obtain ⟨result, hread, hcase⟩ := provideInFacts_read hp hd
  refine ⟨result, hread, ?_⟩
  rcases hcase with ⟨h₁, h₂, _⟩ | ⟨existing, h₁, h₂, _⟩
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨existing, h₁, h₂⟩

/-- Two successful provides read back the same contents in either order. -/
theorem provide_provide_comm (hd : Lawful slot.domain) {first second : kind.data}
    {state₁ state₁₂ state₂ state₂₁ : State} (h₁ : provide slot object first state = .ok state₁)
    (h₁₂ : provide slot object second state₁ = .ok state₁₂)
    (h₂ : provide slot object second state = .ok state₂)
    (h₂₁ : provide slot object first state₂ = .ok state₂₁) :
    lookupFact slot object state₁₂.facts = lookupFact slot object state₂₁.facts := by
  obtain ⟨r₁, hr₁, c₁⟩ := provide_read_cases hd h₁
  obtain ⟨r₁₂, hr₁₂, c₁₂⟩ := provide_read_cases hd h₁₂
  obtain ⟨r₂, hr₂, c₂⟩ := provide_read_cases hd h₂
  obtain ⟨r₂₁, hr₂₁, c₂₁⟩ := provide_read_cases hd h₂₁
  rw [hr₁₂, hr₂₁]
  rcases c₁₂ with ⟨hn, _⟩ | ⟨e₁, he₁, hj₁⟩
  · rw [hr₁] at hn; cases hn
  rcases c₂₁ with ⟨hn, _⟩ | ⟨e₂, he₂, hj₂⟩
  · rw [hr₂] at hn; cases hn
  rw [hr₁] at he₁
  rw [hr₂] at he₂
  cases he₁
  cases he₂
  rcases c₁ with ⟨hn₁, rfl⟩ | ⟨e, he, hje⟩ <;> rcases c₂ with ⟨hn₂, rfl⟩ | ⟨e', he', hje'⟩
  · rw [hd.comm, hj₁] at hj₂
    rw [Option.some.inj hj₂]
  · rw [hn₁] at he'; cases he'
  · rw [hn₂] at he; cases he
  · rw [he] at he'
    cases he'
    have hassoc := hd.assoc e first second
    have hassoc' := hd.assoc e second first
    rw [hje, Option.bind_some, hj₁] at hassoc
    rw [hje', Option.bind_some, hj₂, hd.comm second first] at hassoc'
    rw [← hassoc'] at hassoc
    rw [Option.some.inj hassoc]

/-- Conflicting data is rejected by the state, not silently merged. -/
theorem provide_conflict {existing : kind.data} (hl : lookupFact slot object state.facts = .ok (some existing))
    (hj : slot.domain.join existing value = none) :
    provide slot object value state = .error (.incompatible slot.name) := by
  simp only [provide, bind, Except.bind]
  rw [provideInFacts_conflict slot object hl hj]

theorem mem_objects_iff (key : Object) (source : State) :
    key ∈ objects source ↔ ∃ fact ∈ source.facts, fact.object = key := by
  simp [objects, List.mem_eraseDups]

private theorem mem_objects_put (key : Object) (fact : Fact) (facts : List Fact)
    (hkey : ∃ old ∈ facts, old.object = key) : ∃ old ∈ putFact fact facts, old.object = key := by
  obtain ⟨old, hmem, rfl⟩ := hkey
  by_cases ho : old.object = fact.object
  · exact ⟨fact, by simp [putFact], ho.symm⟩
  · exact ⟨old, by simp [putFact, hmem, ho], rfl⟩

private theorem lookup_some_mem {reader : Slot other} {key : Object} {facts : List Fact} {result : other.data}
    (h : lookupFact reader key facts = .ok (some result)) : ∃ fact ∈ facts, fact.object = key := by
  unfold lookupFact at h
  split at h
  · cases h
  · rename_i fact hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    exact ⟨fact, List.mem_of_find?_eq_some hfind, hp.1⟩

private theorem provideInFacts_shape {facts next : List Fact} {changed : Bool}
    (h : provideInFacts slot object value facts = .ok (changed, next)) :
    next = facts ∨ ∃ result, next = putFact ⟨object, ⟨kind, slot⟩, result⟩ facts := by
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object value facts hl] at h; cases h
  | ok found =>
    cases found with
    | none =>
      rw [provideInFacts_fresh slot object value facts hl] at h
      cases h
      exact Or.inr ⟨value, rfl⟩
    | some existing =>
      rw [provideInFacts_existing slot object value existing facts hl] at h
      split at h
      · cases h
      · split at h
        · cases h; exact Or.inl rfl
        · cases h; exact Or.inr ⟨_, rfl⟩

/-- Every known object stays known, and the provided object becomes known. -/
theorem provide_objects (hd : Lawful slot.domain) (h : provide slot object value state = .ok next) :
    object ∈ objects next ∧ ∀ key ∈ objects state, key ∈ objects next := by
  obtain ⟨result, hread, _⟩ := provide_read hd h
  refine ⟨(mem_objects_iff _ _).2 (lookup_some_mem hread), ?_⟩
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  intro key hkey
  rw [mem_objects_iff] at *
  rcases provideInFacts_shape hp with rfl | ⟨_, rfl⟩
  · exact hkey
  · exact mem_objects_put key _ _ hkey

end Provide

/-! ## Opinions -/

section Opinions

variable {kind other : PayloadKind} {slot : Slot kind} {object : Object} {value : kind.data}

/-- The opinions relevant to one slot of one object, as `resolve` selects them. -/
def relevant (slot : Slot kind) (object : Object) : Opinion → Bool :=
  fun opinion => decide (opinion.fact.object = object ∧ opinion.fact.slot.2.name = slot.name)

/-- `resolve` as a function of the relevant opinions alone. -/
def resolveOf (slot : Slot kind) (opinions : List Opinion) : Except Conflict kind.data :=
  if opinions.isEmpty then
    .ok slot.domain.empty
  else
    let trust := opinions.foldl (fun trust opinion => max trust opinion.agent.trust) 0
    joinOpinions slot slot.domain.empty (opinions.filter fun opinion => opinion.agent.trust = trust)

theorem resolve_eq_resolveOf (state : State) :
    resolve slot object state = resolveOf slot (state.opinions.filter (relevant slot object)) := rfl

/-- Suggesting always bumps the version and never touches the fact table. -/
theorem suggest_frame (agent : Agent) (state : State) :
    (suggest agent slot object value state).facts = state.facts ∧
      state.version < (suggest agent slot object value state).version :=
  ⟨rfl, Nat.lt_succ_self _⟩

theorem mem_suggest_opinions (agent : Agent) (state : State) (opinion : Opinion) :
    opinion ∈ (suggest agent slot object value state).opinions ↔
      opinion = ⟨agent, object, ⟨kind, slot⟩, value⟩ ∨
        (opinion ∈ state.opinions ∧
          (opinion.agent.name ≠ agent.name ∨ opinion.fact.object ≠ object ∨
            opinion.fact.slot.2.name ≠ slot.name)) := by
  simp [suggest, putOpinion, or_assoc]

/-- An agent's later suggestion for a slot replaces its earlier one outright. -/
theorem suggest_suggest_same (agent : Agent) (first second : kind.data) (state : State) :
    (suggest agent slot object second (suggest agent slot object first state)).opinions =
      (suggest agent slot object second state).opinions := by
  simp [suggest, putOpinion, List.filter_filter]

private theorem filter_putOpinion_of_other (opinion : Opinion) (opinions : List Opinion) (reader : Slot other)
    (key : Object) (hkey : opinion.fact.object ≠ key ∨ opinion.fact.slot.2.name ≠ reader.name) :
    (putOpinion opinion opinions).filter (relevant reader key) = opinions.filter (relevant reader key) := by
  have hhead : relevant reader key opinion = false := by
    simp only [relevant, decide_eq_false_iff_not, not_and]
    rcases hkey with h | h
    · exact fun e => absurd e h
    · exact fun _ => h
  simp only [putOpinion, List.filter_cons, hhead, List.filter_filter]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply List.filter_congr
  intro old _
  by_cases hr : relevant reader key old = true
  · simp only [hr, Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq]
    simp only [relevant, decide_eq_true_eq] at hr
    simp only [hr.1, hr.2]
    rcases hkey with h | h
    · simp [Ne.symm h]
    · simp [Ne.symm h]
  · simp [hr]

/-- A suggestion about another object or slot cannot change what `resolve` returns. -/
theorem resolve_suggest_frame (agent : Agent) (state : State) (reader : Slot other) (key : Object)
    (hkey : object ≠ key ∨ slot.name ≠ reader.name) :
    resolve reader key (suggest agent slot object value state) = resolve reader key state := by
  rw [resolve_eq_resolveOf, resolve_eq_resolveOf]
  exact congrArg _ (filter_putOpinion_of_other _ _ reader key hkey)

private theorem foldl_max_le (opinions : List Opinion) (init bound : Nat) (hinit : init ≤ bound)
    (h : ∀ opinion ∈ opinions, opinion.agent.trust ≤ bound) :
    opinions.foldl (fun trust opinion => max trust opinion.agent.trust) init ≤ bound := by
  induction opinions generalizing init with
  | nil => exact hinit
  | cons head tail ih =>
    simp only [List.foldl_cons]
    apply ih
    · have := h head List.mem_cons_self
      omega
    · exact fun opinion hm => h opinion (List.mem_cons_of_mem _ hm)

private theorem le_foldl_max (opinions : List Opinion) (init : Nat) :
    init ≤ opinions.foldl (fun trust opinion => max trust opinion.agent.trust) init ∧
      ∀ opinion ∈ opinions,
        opinion.agent.trust ≤ opinions.foldl (fun trust opinion => max trust opinion.agent.trust) init := by
  induction opinions generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h₁, h₂⟩ := ih (max init head.agent.trust)
    refine ⟨by omega, by omega, h₂⟩

private theorem foldl_max_absorb (opinions : List Opinion) {init : Nat}
    (h : init ≤ opinions.foldl (fun trust opinion => max trust opinion.agent.trust) 0) :
    opinions.foldl (fun trust opinion => max trust opinion.agent.trust) init =
      opinions.foldl (fun trust opinion => max trust opinion.agent.trust) 0 := by
  apply Nat.le_antisymm
  · exact foldl_max_le _ _ _ h (le_foldl_max opinions 0).2
  · apply foldl_max_le
    · exact Nat.zero_le _
    · exact (le_foldl_max opinions init).2

/-- A strictly most trusted agent decides the slot on its own. -/
theorem resolve_suggest_dominant (hd : Lawful slot.domain) (agent : Agent) (state : State)
    (hdom : ∀ old ∈ state.opinions, relevant slot object old = true → old.agent.trust < agent.trust) :
    resolve slot object (suggest agent slot object value state) = .ok value := by
  rw [resolve_eq_resolveOf]
  let opinion : Opinion := ⟨agent, object, ⟨kind, slot⟩, value⟩
  have hhead : relevant slot object opinion = true := by simp [relevant, opinion]
  have hshape : (suggest agent slot object value state).opinions.filter (relevant slot object) =
      opinion :: (state.opinions.filter fun old => old.agent.name != agent.name ||
          old.fact.object != object || old.fact.slot.2.name != slot.name).filter (relevant slot object) := by
    simp only [suggest, putOpinion, List.filter_cons, hhead, ↓reduceIte, opinion]
  rw [hshape]
  generalize hrest : (state.opinions.filter fun old => old.agent.name != agent.name ||
    old.fact.object != object || old.fact.slot.2.name != slot.name).filter (relevant slot object) = rest
  have hlt : ∀ old ∈ rest, old.agent.trust < agent.trust := by
    intro old hold
    rw [← hrest, List.mem_filter, List.mem_filter] at hold
    exact hdom old hold.1.1 hold.2
  have htrust : (opinion :: rest).foldl (fun trust opinion => max trust opinion.agent.trust) 0 =
      agent.trust := by
    simp only [List.foldl_cons, opinion]
    apply Nat.le_antisymm
    · exact foldl_max_le _ _ _ (by omega) (fun old hm => Nat.le_of_lt (hlt old hm))
    · exact Nat.le_trans (by omega) (le_foldl_max rest (max 0 agent.trust)).1
  have hfilter : (rest.filter fun old => decide (old.agent.trust = agent.trust)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro old hold
    have := hlt old hold
    simp only [decide_eq_true_eq]
    omega
  simp only [resolveOf, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, htrust]
  simp only [List.filter_cons, opinion, decide_true, ↓reduceIte, hfilter]
  simp [joinOpinions, hd.empty_left]

/-- An agent outranked by another relevant opinion has no influence on the result. -/
theorem resolve_suggest_outranked (agent : Agent) (state : State) {ranked : Opinion}
    (hmem : ranked ∈ state.opinions) (hrel : relevant slot object ranked = true)
    (hlt : agent.trust < ranked.agent.trust)
    (hfresh : ∀ old ∈ state.opinions, relevant slot object old = true → old.agent.name ≠ agent.name) :
    resolve slot object (suggest agent slot object value state) = resolve slot object state := by
  rw [resolve_eq_resolveOf, resolve_eq_resolveOf]
  let opinion : Opinion := ⟨agent, object, ⟨kind, slot⟩, value⟩
  have hhead : relevant slot object opinion = true := by simp [relevant, opinion]
  have hsame : (state.opinions.filter fun old => old.agent.name != agent.name ||
      old.fact.object != object || old.fact.slot.2.name != slot.name).filter (relevant slot object) =
      state.opinions.filter (relevant slot object) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro old hold
    by_cases hr : relevant slot object old = true
    · have := hfresh old hold hr
      simp [hr, this]
    · simp [hr]
  have hshape : (suggest agent slot object value state).opinions.filter (relevant slot object) =
      opinion :: state.opinions.filter (relevant slot object) := by
    simp only [suggest, putOpinion, List.filter_cons, hhead, ↓reduceIte, opinion]
    rw [hsame]
  rw [hshape]
  generalize hrest : state.opinions.filter (relevant slot object) = rest
  have hranked : ranked ∈ rest := by
    rw [← hrest]
    exact List.mem_filter.2 ⟨hmem, hrel⟩
  have hbound := (le_foldl_max rest 0).2 ranked hranked
  have hne : rest ≠ [] := List.ne_nil_of_mem hranked
  have htrust : (opinion :: rest).foldl (fun trust opinion => max trust opinion.agent.trust) 0 =
      rest.foldl (fun trust opinion => max trust opinion.agent.trust) 0 := by
    simp only [List.foldl_cons, opinion]
    apply foldl_max_absorb
    omega
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  simp only [resolveOf, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, hempty, htrust]
  have hskip : decide (opinion.agent.trust = rest.foldl (fun trust opinion => max trust opinion.agent.trust) 0) = false := by
    simp only [decide_eq_false_iff_not, opinion]
    omega
  simp only [List.filter_cons, hskip, Bool.false_eq_true, ↓reduceIte]

private theorem joinOpinions_refines (hd : Lawful slot.domain) {current result : kind.data} (opinions : List Opinion)
    (h : joinOpinions slot current opinions = .ok result) :
    Refines slot.domain current result ∧
      ∀ opinion ∈ opinions, ∀ hk : opinion.fact.slot.1 = kind,
        Refines slot.domain (hk ▸ opinion.fact.value) result := by
  induction opinions generalizing current with
  | nil =>
    simp only [joinOpinions, Except.ok.injEq] at h
    subst h
    exact ⟨hd.refines_refl _, by simp⟩
  | cons head tail ih =>
    simp only [joinOpinions] at h
    split at h
    · rename_i hk
      split at h
      · rename_i joined hj
        obtain ⟨h₁, h₂⟩ := ih h
        obtain ⟨u₁, u₂⟩ := hd.join_upper hj
        refine ⟨hd.refines_trans u₁ h₁, ?_⟩
        intro opinion hmem hk'
        rcases List.mem_cons.1 hmem with rfl | hmem
        · exact hd.refines_trans u₂ h₁
        · exact h₂ opinion hmem hk'
      · cases h
    · cases h

/-- Whatever `resolve` returns refines the opinion of every most-trusted relevant agent. -/
theorem resolve_refines (hd : Lawful slot.domain) {state : State} {result : kind.data}
    (h : resolve slot object state = .ok result) {opinion : Opinion} (hmem : opinion ∈ state.opinions)
    (hrel : relevant slot object opinion = true)
    (htop : ∀ other ∈ state.opinions, relevant slot object other = true →
      other.agent.trust ≤ opinion.agent.trust)
    (hk : opinion.fact.slot.1 = kind) :
    Refines slot.domain (hk ▸ opinion.fact.value) result := by
  rw [resolve_eq_resolveOf] at h
  have hin : opinion ∈ state.opinions.filter (relevant slot object) := List.mem_filter.2 ⟨hmem, hrel⟩
  generalize hrest : state.opinions.filter (relevant slot object) = rest at h hin
  have hempty : rest.isEmpty = false := by
    cases rest with
    | nil => cases hin
    | cons _ _ => rfl
  simp only [resolveOf, hempty, Bool.false_eq_true, ↓reduceIte] at h
  have htrust : rest.foldl (fun trust opinion => max trust opinion.agent.trust) 0 = opinion.agent.trust := by
    apply Nat.le_antisymm
    · apply foldl_max_le _ _ _ (Nat.zero_le _)
      intro other hother
      rw [← hrest, List.mem_filter] at hother
      exact htop other hother.1 hother.2
    · exact (le_foldl_max rest 0).2 opinion hin
  rw [htrust] at h
  exact (joinOpinions_refines hd _ h).2 opinion (List.mem_filter.2 ⟨hin, by simp⟩) hk

end Opinions

/-! ## Observers -/

section Observers

variable {kind : PayloadKind} {slot : Slot kind} {object : Object} {value : kind.data} {state next : State}

/-- Observers can only veto a provide; they cannot alter its result. -/
theorem provideWith_ok {env : Environment} (h : provideWith env slot object value state = .ok next) :
    provide slot object value state = .ok next := by
  simp only [provideWith, bind, Except.bind] at h
  cases hp : provide slot object value state with
  | error conflict => simp [hp] at h
  | ok result =>
    simp only [hp] at h
    split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h; rfl

/-- Without a change, no observer runs and so none can fail. -/
theorem provideWith_unchanged (env : Environment) (h : provide slot object value state = .ok next)
    (hv : next.version = state.version) : provideWith env slot object value state = .ok next := by
  simp [provideWith, h, bind, Except.bind, hv]

theorem provideWith_no_observers (env : Environment) (hempty : env.observers = []) :
    provideWith env slot object value state = provide slot object value state := by
  simp only [provideWith, bind, Except.bind]
  cases hp : provide slot object value state with
  | error conflict => rfl
  | ok result =>
    simp only [notifyObservers, hempty]
    split <;> rfl

end Observers

/-! ## Promises and fixpoints -/

section Normalize

variable {kind other : PayloadKind}

/-- First-order presentation of the promise loop in `runPromises`. -/
def runList (object : Object) : List Promise → Bool → List Fact → Except Conflict (Bool × List Fact)
  | [], changed, facts => .ok (changed, facts)
  | promise :: rest, changed, facts =>
    match promise.compute object facts with
    | .error conflict => .error conflict
    | .ok none => runList object rest changed facts
    | .ok (some value) =>
      match provideInFacts promise.slot.2 object value facts with
      | .error conflict => .error conflict
      | .ok (refined, next) => runList object rest (changed || refined) next

/-- The body of the loop in `runPromises`. -/
def loopBody (object : Object) (promise : Promise) (s : Bool × List Fact) :
    Except Conflict (ForInStep (Bool × List Fact)) := do
  let value ← promise.compute object s.2
  match value with
  | some value => do
    let x ← provideInFacts promise.slot.2 object value s.2
    match x with
    | (refined, next) => pure (ForInStep.yield (s.1 || refined, next))
  | _ => pure (ForInStep.yield (s.1, s.2))

private theorem forIn_runList (object : Object) (promises : List Promise) (changed : Bool) (facts : List Fact) :
    forIn promises (changed, facts) (loopBody object) = runList object promises changed facts := by
  induction promises generalizing changed facts with
  | nil => rfl
  | cons promise rest ih =>
    simp only [List.forIn_cons, runList, bind, Except.bind, loopBody]
    cases hc : promise.compute object facts with
    | error conflict => rfl
    | ok value =>
      cases value with
      | none => exact ih changed facts
      | some value =>
        cases hp : provideInFacts promise.slot.2 object value facts with
        | error conflict => simp only [hp]
        | ok result =>
          obtain ⟨refined, next⟩ := result
          simp only [hp]
          exact ih _ _

theorem runPromises_eq (promises : List Promise) (object : Object) (facts : List Fact) :
    runPromises promises object facts = runList object promises false facts := by
  have hdef : runPromises promises object facts =
      (do
        let s ← forIn promises (false, facts) (loopBody object)
        .ok (s.1, s.2)) := rfl
  rw [hdef, forIn_runList]
  cases runList object promises false facts with
  | error conflict => rfl
  | ok result => rfl

private theorem runList_changed_mono {object : Object} {promises : List Promise} {changed : Bool}
    {facts next : List Fact} {result : Bool} (h : runList object promises changed facts = .ok (result, next))
    (hfalse : result = false) : changed = false ∧ next = facts := by
  induction promises generalizing changed facts with
  | nil =>
    simp only [runList, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.trans hfalse, h.2.symm⟩
  | cons promise rest ih =>
    simp only [runList] at h
    split at h
    · cases h
    · exact ih h
    · split at h
      · cases h
      · rename_i refined after hp
        obtain ⟨h₁, h₂⟩ := ih h
        simp only [Bool.or_eq_false_iff] at h₁
        obtain ⟨hc, hr⟩ := h₁
        subst hc hr
        have := provideInFacts_unchanged hp
        exact ⟨rfl, h₂.trans this⟩

/-- A round of promises reporting no change has left the table exactly as it was. -/
theorem runPromises_unchanged {promises : List Promise} {object : Object} {facts next : List Fact}
    (h : runPromises promises object facts = .ok (false, next)) : next = facts := by
  rw [runPromises_eq] at h
  exact (runList_changed_mono h rfl).2

private theorem normalize_succ (env : Environment) (object : Object) (fuel : Nat) (facts : List Fact) :
    normalize env object (fuel + 1) facts =
      match runPromises env.promises object facts with
      | .error conflict => .error conflict
      | .ok (changed, next) =>
        if changed then
          match normalize env object fuel next with
          | .error conflict => .error conflict
          | .ok (_, final) => .ok (true, final)
        else
          .ok (false, next) := by
  simp only [normalize, bind, Except.bind]
  cases runPromises env.promises object facts with
  | error conflict => rfl
  | ok result =>
    obtain ⟨changed, next⟩ := result
    cases changed with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      cases normalize env object fuel next with
      | error conflict => rfl
      | ok result => rfl

private theorem normalize_succ_cases {env : Environment} {object : Object} {fuel : Nat} {facts final : List Fact}
    {changed : Bool} (h : normalize env object (fuel + 1) facts = .ok (changed, final)) :
    ∃ flag after, runPromises env.promises object facts = .ok (flag, after) ∧
      ((flag = false ∧ changed = false ∧ final = after) ∨
        (flag = true ∧ changed = true ∧ ∃ inner, normalize env object fuel after = .ok (inner, final))) := by
  rw [normalize_succ] at h
  cases hrun : runPromises env.promises object facts with
  | error conflict =>
    simp only [hrun] at h
    cases h
  | ok step =>
    obtain ⟨flag, after⟩ := step
    simp only [hrun] at h
    refine ⟨flag, after, rfl, ?_⟩
    cases flag with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
    | true =>
      simp only [↓reduceIte] at h
      cases hn : normalize env object fuel after with
      | error conflict =>
        simp only [hn] at h
        cases h
      | ok result =>
        obtain ⟨inner, last⟩ := result
        simp only [hn, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl, inner, rfl⟩

theorem normalize_zero (env : Environment) (object : Object) (facts : List Fact) :
    normalize env object 0 facts = .error .exhausted := by
  simp [normalize]

theorem normalize_no_promises (env : Environment) (hempty : env.promises = []) (object : Object) (fuel : Nat)
    (facts : List Fact) : normalize env object (fuel + 1) facts = .ok (false, facts) := by
  rw [normalize_succ, runPromises_eq, hempty]
  rfl

/-- A `false` flag from `normalize` means the table was left exactly as it was. -/
theorem normalize_false_unchanged {env : Environment} {object : Object} {fuel : Nat} {facts next : List Fact}
    (h : normalize env object fuel facts = .ok (false, next)) : next = facts := by
  cases fuel with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel =>
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rcases hcase with ⟨rfl, _, rfl⟩ | ⟨_, hc, _⟩
    · exact runPromises_unchanged hrun
    · cases hc

/-- A terminating `normalize` has reached a genuine fixpoint of the promises. -/
theorem normalize_fixpoint {env : Environment} {object : Object} {fuel : Nat} {facts next : List Fact}
    {changed : Bool} (h : normalize env object fuel facts = .ok (changed, next)) :
    runPromises env.promises object next = .ok (false, next) := by
  induction fuel generalizing facts changed with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel ih =>
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rcases hcase with ⟨rfl, _, rfl⟩ | ⟨_, _, inner, hinner⟩
    · have hsame := runPromises_unchanged hrun
      rw [hsame] at hrun ⊢
      exact hrun
    · exact ih hinner

/-- More fuel never changes a result that was reached with less. -/
theorem normalize_fuel_mono {env : Environment} {object : Object} {fuel extra : Nat} {facts : List Fact}
    {result : Bool × List Fact} (h : normalize env object fuel facts = .ok result) :
    normalize env object (fuel + extra) facts = .ok result := by
  induction fuel generalizing facts result with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel ih =>
    obtain ⟨changed, final⟩ := result
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, normalize_succ, hrun]
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, inner, hinner⟩
    · rfl
    · simp only [↓reduceIte, ih hinner]

/-- Promises for one object leave every other object's facts untouched. -/
private theorem runList_frame {object key : Object} (hkey : key ≠ object) (reader : Slot other)
    {promises : List Promise} {changed result : Bool} {facts next : List Fact}
    (h : runList object promises changed facts = .ok (result, next)) :
    lookupFact reader key next = lookupFact reader key facts := by
  induction promises generalizing changed facts with
  | nil =>
    simp only [runList, Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.2]
  | cons promise rest ih =>
    simp only [runList] at h
    split at h
    · cases h
    · exact ih h
    · split at h
      · cases h
      · rename_i hp
        rw [ih h]
        exact provideInFacts_frame hp reader key (Or.inl hkey)

theorem normalize_frame {env : Environment} {object key : Object} (hkey : key ≠ object) (reader : Slot other)
    {fuel : Nat} {facts next : List Fact} {changed : Bool}
    (h : normalize env object fuel facts = .ok (changed, next)) :
    lookupFact reader key next = lookupFact reader key facts := by
  induction fuel generalizing facts changed with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel ih =>
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rw [runPromises_eq] at hrun
    rcases hcase with ⟨rfl, _, rfl⟩ | ⟨_, _, inner, hinner⟩
    · exact runList_frame hkey reader hrun
    · rw [ih hinner]
      exact runList_frame hkey reader hrun

/-- Promises for a slot's cell may only be registered through that slot itself. -/
def Coherent (slot : Slot kind) (promises : List Promise) : Prop :=
  ∀ promise ∈ promises, promise.slot.2.name ≠ slot.name ∨ promise.slot = ⟨kind, slot⟩

/-- A cell that holds a value still holds a refinement of it. -/
def CellRefines (slot : Slot kind) (object : Object) (before after : List Fact) : Prop :=
  ∀ existing, lookupFact slot object before = .ok (some existing) →
    ∃ result, lookupFact slot object after = .ok (some result) ∧ Refines slot.domain existing result

private theorem CellRefines.refl {slot : Slot kind} (hd : Lawful slot.domain) (object : Object) (facts : List Fact) :
    CellRefines slot object facts facts :=
  fun existing h => ⟨existing, h, hd.refines_refl _⟩

private theorem CellRefines.trans {slot : Slot kind} (hd : Lawful slot.domain) {object : Object} {a b c : List Fact}
    (hab : CellRefines slot object a b) (hbc : CellRefines slot object b c) : CellRefines slot object a c := by
  intro existing hex
  obtain ⟨middle, hm, hrm⟩ := hab existing hex
  obtain ⟨result, hr, hrr⟩ := hbc middle hm
  exact ⟨result, hr, hd.refines_trans hrm hrr⟩

private theorem runList_refines {slot : Slot kind} (hd : Lawful slot.domain) {object : Object}
    {promises : List Promise} (hc : Coherent slot promises) {changed result : Bool} {facts next : List Fact}
    (h : runList object promises changed facts = .ok (result, next)) :
    CellRefines slot object facts next := by
  induction promises generalizing changed facts with
  | nil =>
    simp only [runList, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact CellRefines.refl hd _ _
  | cons promise rest ih =>
    have hrest : Coherent slot rest := fun p hp => hc p (List.mem_cons_of_mem _ hp)
    simp only [runList] at h
    split at h
    · cases h
    · exact ih hrest h
    · split at h
      · cases h
      · rename_i hp
        refine CellRefines.trans hd ?_ (ih hrest h)
        rcases hc promise List.mem_cons_self with hname | hslot
        · intro existing hex
          exact ⟨existing, by
            rw [provideInFacts_frame hp slot object (Or.inr (Ne.symm hname))]
            exact hex, hd.refines_refl _⟩
        · obtain ⟨pkind, pslot⟩ := promise
          simp only at hslot hp
          cases hslot
          intro existing hex
          obtain ⟨res, hr, _, hre⟩ := provideInFacts_monotone hd hp
          exact ⟨res, hr, hre existing hex⟩

/-- Running coherent promises to a fixpoint never loses what a cell already knew. -/
theorem normalize_refines {slot : Slot kind} (hd : Lawful slot.domain) {env : Environment} {object : Object}
    (hc : Coherent slot env.promises) {fuel : Nat} {changed : Bool} {facts next : List Fact}
    (h : normalize env object fuel facts = .ok (changed, next)) :
    CellRefines slot object facts next := by
  induction fuel generalizing facts changed with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel ih =>
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rw [runPromises_eq] at hrun
    have hstep := runList_refines hd hc hrun
    rcases hcase with ⟨rfl, _, rfl⟩ | ⟨_, _, inner, hinner⟩
    · exact hstep
    · exact CellRefines.trans hd hstep (ih hinner)

/-- A cell gained information outright: it was empty and is now filled, or its contents strictly
grew. -/
def CellGrows (slot : Slot kind) (object : Object) (before after : List Fact) : Prop :=
  (lookupFact slot object before = .ok none ∧ ∃ result, lookupFact slot object after = .ok (some result)) ∨
    ∃ existing result, lookupFact slot object before = .ok (some existing) ∧
      lookupFact slot object after = .ok (some result) ∧ Refines slot.domain existing result ∧ existing ≠ result

private theorem CellGrows.ne {slot : Slot kind} {object : Object} {before after : List Fact}
    (h : CellGrows slot object before after) : after ≠ before := by
  rintro rfl
  rcases h with ⟨hnone, result, hsome⟩ | ⟨existing, result, h₁, h₂, _, hne⟩
  · rw [hnone] at hsome
    cases hsome
  · rw [h₁] at h₂
    cases h₂
    exact hne rfl

private theorem CellGrows.refine {slot : Slot kind} (hd : Lawful slot.domain) {object : Object} {a b c : List Fact}
    (hab : CellGrows slot object a b) (hbc : CellRefines slot object b c) : CellGrows slot object a c := by
  rcases hab with ⟨hnone, result, hsome⟩ | ⟨existing, result, h₁, h₂, hre, hne⟩
  · obtain ⟨final, hfinal, _⟩ := hbc result hsome
    exact Or.inl ⟨hnone, final, hfinal⟩
  · obtain ⟨final, hfinal, hrf⟩ := hbc result h₂
    refine Or.inr ⟨existing, final, h₁, hfinal, hd.refines_trans hre hrf, ?_⟩
    rintro rfl
    exact hne (hd.refines_antisymm hre hrf)

private theorem provideInFacts_grows {slot : Slot kind} (hd : Lawful slot.domain) {object : Object}
    {value : kind.data} {facts next : List Fact}
    (h : provideInFacts slot object value facts = .ok (true, next)) : CellGrows slot object facts next := by
  obtain ⟨result, hread, hcase⟩ := provideInFacts_read h hd
  rcases hcase with ⟨hnone, _, _⟩ | ⟨existing, hex, hj, hchanged⟩
  · exact Or.inl ⟨hnone, result, hread⟩
  · exact Or.inr ⟨existing, result, hex, hread, (hd.join_upper hj).1, hchanged.1 rfl⟩

/-- The promises of an environment have lawful domains and agree on what each slot name means. -/
def Coordinated (promises : List Promise) : Prop :=
  ∀ promise ∈ promises, Lawful promise.slot.2.domain ∧ Coherent promise.slot.2 promises

private theorem runList_grows {object : Object} {promises : List Promise} (hw : Coordinated promises)
    {facts next : List Fact} {changed : Bool} (h : runList object promises changed facts = .ok (true, next))
    (hfalse : changed = false) :
    ∃ promise ∈ promises, CellGrows promise.slot.2 object facts next := by
  induction promises generalizing changed facts with
  | nil =>
    simp only [runList, Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.1] at hfalse
    cases hfalse
  | cons head rest ih =>
    have hrest : Coordinated rest := fun p hp =>
      ⟨(hw p (List.mem_cons_of_mem _ hp)).1,
        fun q hq => (hw p (List.mem_cons_of_mem _ hp)).2 q (List.mem_cons_of_mem _ hq)⟩
    have hweaken : ∀ {facts next : List Fact},
        (∃ promise ∈ rest, CellGrows promise.slot.2 object facts next) →
        ∃ promise ∈ head :: rest, CellGrows promise.slot.2 object facts next := by
      rintro _ _ ⟨promise, hp, hg⟩
      exact ⟨promise, List.mem_cons_of_mem _ hp, hg⟩
    subst hfalse
    simp only [runList] at h
    split at h
    · cases h
    · exact hweaken (ih hrest h rfl)
    · split at h
      · cases h
      · rename_i refined after hp
        cases refined with
        | false =>
          rw [provideInFacts_unchanged hp] at h
          exact hweaken (ih hrest h rfl)
        | true =>
          obtain ⟨hlaw, hcoh⟩ := hw head List.mem_cons_self
          have hcoh' : Coherent head.slot.2 rest := fun q hq => hcoh q (List.mem_cons_of_mem _ hq)
          exact ⟨head, List.mem_cons_self,
            (provideInFacts_grows hlaw hp).refine hlaw (runList_refines hlaw hcoh' h)⟩

/-- A `true` flag from `normalize` is a real change: some promise's cell gained information, which
later rounds cannot undo on coordinated promises. -/
theorem normalize_true_changed {env : Environment} {object : Object} (hw : Coordinated env.promises) {fuel : Nat}
    {facts next : List Fact} (h : normalize env object fuel facts = .ok (true, next)) : next ≠ facts := by
  cases fuel with
  | zero => rw [normalize_zero] at h; cases h
  | succ fuel =>
    obtain ⟨flag, after, hrun, hcase⟩ := normalize_succ_cases h
    rw [runPromises_eq] at hrun
    rcases hcase with ⟨_, hc, _⟩ | ⟨rfl, _, inner, hinner⟩
    · cases hc
    · obtain ⟨promise, hp, hgrows⟩ := runList_grows hw hrun rfl
      obtain ⟨hlaw, hcoh⟩ := hw promise hp
      exact (hgrows.refine hlaw (normalize_refines hlaw hcoh hinner)).ne

private theorem collect_ok {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state fuel = .ok (value, next)) :
    ∃ changed facts found, normalize env object fuel state.facts = .ok (changed, facts) ∧
      lookupFact slot object facts = .ok found ∧ value = found.getD slot.domain.empty ∧
      next = { state with facts := facts, version := state.version + changed.toNat } := by
  simp only [collect, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i result hn
    obtain ⟨flag, facts⟩ := result
    simp only at h
    split at h
    · cases h
    · rename_i found hl
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨flag, facts, found, hn, hl, h.1.symm, h.2.symm⟩

theorem collect_zero_fuel (env : Environment) (slot : Slot kind) (object : Object) (state : State) :
    collect env slot object state 0 = .error .exhausted := by
  simp [collect, normalize_zero, bind, Except.bind]

/-- `collect` raises the version by at most one and keeps the opinions. -/
theorem collect_version {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state fuel = .ok (value, next)) :
    (next.version = state.version ∨ next.version = state.version + 1) ∧ next.opinions = state.opinions := by
  obtain ⟨changed, _, _, _, _, _, rfl⟩ := collect_ok h
  cases changed <;> simp

/-- An unmoved version always means an untouched table, whatever the promises are. -/
theorem collect_facts_of_version_eq {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state fuel = .ok (value, next))
    (hv : next.version = state.version) : next.facts = state.facts := by
  obtain ⟨changed, facts, _, hn, _, _, rfl⟩ := collect_ok h
  cases changed with
  | false => exact normalize_false_unchanged hn
  | true => simp at hv

/-- On coordinated promises, `collect` bumps the version exactly when the facts changed. -/
theorem collect_version_iff {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (hw : Coordinated env.promises)
    (h : collect env slot object state fuel = .ok (value, next)) :
    next.version = state.version + 1 ↔ next.facts ≠ state.facts := by
  obtain ⟨changed, facts, _, hn, _, _, rfl⟩ := collect_ok h
  cases changed with
  | false => simpa using normalize_false_unchanged hn
  | true => simpa using normalize_true_changed hw hn

/-- The value `collect` returns refines anything the cell held beforehand. -/
theorem collect_refines {env : Environment} {slot : Slot kind} (hd : Lawful slot.domain) {object : Object}
    (hc : Coherent slot env.promises) {state next : State} {fuel : Nat} {value existing : kind.data}
    (h : collect env slot object state fuel = .ok (value, next))
    (hex : lookupFact slot object state.facts = .ok (some existing)) :
    Refines slot.domain existing value := by
  obtain ⟨_, facts, found, hn, hl, rfl, rfl⟩ := collect_ok h
  obtain ⟨result, hr, hre⟩ := normalize_refines hd hc hn existing hex
  rw [hr] at hl
  cases hl
  exact hre

/-- `collect` is a read: asking again returns the same value and state. -/
theorem collect_idempotent {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state (fuel + 1) = .ok (value, next)) :
    collect env slot object next 1 = .ok (value, next) := by
  obtain ⟨_, facts, found, hn, hl, rfl, rfl⟩ := collect_ok h
  have hfix := normalize_fixpoint hn
  simp only [collect, bind, Except.bind]
  rw [normalize_succ, hfix]
  simp [hl]

theorem collect_no_promises (env : Environment) (hempty : env.promises = []) (slot : Slot kind)
    (object : Object) (state : State) (fuel : Nat) {found : Option kind.data}
    (hl : lookupFact slot object state.facts = .ok found) :
    collect env slot object state (fuel + 1) = .ok (found.getD slot.domain.empty, state) := by
  simp only [collect, bind, Except.bind]
  rw [normalize_no_promises env hempty]
  simp [hl]

/-- A value that `require` returns is never the domain's empty value. -/
theorem require_nonempty {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : require env slot object state fuel = .ok (value, next)) :
    slot.domain.eq value slot.domain.empty = false ∧ collect env slot object state fuel = .ok (value, next) := by
  simp only [require, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i result hc
    obtain ⟨found, after⟩ := result
    simp only at h
    split at h
    · cases h
    · rename_i he
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using he, hc⟩

end Normalize

/-! ## Persistence -/

section Persist

private theorem digit_list_isDigit (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  intro c hc
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

private theorem filter_underscore_digits (n : Nat) :
    (Nat.toDigits 10 n).filter (· != '_') = Nat.toDigits 10 n := by
  apply List.filter_eq_self.2
  intro c hc
  have : c ≠ '_' := fun h => Nat.underscore_not_in_toDigits (h ▸ hc)
  simpa using this

/-- Decimal printing and parsing of naturals are inverse. -/
theorem toNat?_toString (n : Nat) : (toString n).toNat? = some n := by
  have hne : toString n ≠ "" := by
    rw [Nat.toString_eq_repr]
    exact Nat.repr_ne_empty
  have hnat := String.isNat_of_isDigit hne (digit_list_isDigit n)
  rw [String.toNat?_eq_some_ofDigitChars hnat, Nat.toString_eq_ofList_toDigits, String.toList_ofList,
    filter_underscore_digits, Nat.ofDigitChars_ten_toDigits]

theorem nat_atom_toString (n : Nat) : Sexp.nat (.atom (toString n)) = .ok n := by
  simp only [Sexp.nat, Sexp.asAtom, bind, Except.bind, toNat?_toString]

theorem nat_atom_repr (n : Nat) : Sexp.nat (.atom n.repr) = .ok n := nat_atom_toString n

private theorem hexDigit_digitChar : ∀ digit, digit < 16 → hexDigit digit.digitChar = some digit := by
  decide

private theorem parseHexLoop_append (left right : List Char) (acc result : Nat)
    (h : parseHexLoop left acc = .ok result) :
    parseHexLoop (left ++ right) acc = parseHexLoop right result := by
  induction left generalizing acc with
  | nil =>
    simp only [parseHexLoop, Except.ok.injEq] at h
    subst h
    rfl
  | cons head tail ih =>
    simp only [parseHexLoop] at h
    simp only [List.cons_append, parseHexLoop]
    split at h
    · simp only [*]
    · cases h

private theorem parseHexLoop_toDigits (n : Nat) : parseHexLoop (Nat.toDigits 16 n) 0 = .ok n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · rename_i hlt
      simp [parseHexLoop, hexDigit_digitChar n hlt]
    · rename_i hge
      have hlt : n / 16 < n := Nat.div_lt_self (by omega) (by decide)
      rw [parseHexLoop_append _ _ _ _ (ih _ hlt)]
      have hmod : n % 16 < 16 := Nat.mod_lt _ (by decide)
      simp only [parseHexLoop, hexDigit_digitChar _ hmod]
      have := Nat.div_add_mod n 16
      congr 1
      omega

/-- `Word.toHex` and `parseHex` are inverse on the numeric value. -/
theorem parseHex_toHex {width : Nat} (word : Word width) :
    Bil.Wire.parseHex (Word.toHex word) = .ok word.toNat := by
  have hne : (String.ofList (Nat.toDigits 16 word.toNat)).isEmpty = false := by
    apply Bool.eq_false_iff.2
    intro h
    have := congrArg String.toList (String.isEmpty_iff.1 h)
    simp [Nat.toDigits_ne_nil] at this
  simp only [Bil.Wire.parseHex, Word.toHex, hne, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
  exact parseHexLoop_toDigits _

/-- Kinds that have a persistent codec. -/
def Persistable : PayloadKind → Bool
  | .unit | .bool | .nat | .string | .bitvec _ => true
  | _ => false

theorem encodeValue_ok_iff (kind : PayloadKind) (value : kind.data) :
    (∃ encoded, encodeValue kind value = .ok encoded) ↔ Persistable kind = true := by
  cases kind <;> simp [encodeValue, Persistable]

/-- Value codec roundtrip: everything the encoder accepts decodes to the original. -/
theorem decodeValue_encodeValue {kind : PayloadKind} {value : kind.data} {encoded : Sexp}
    (h : encodeValue kind value = .ok encoded) : decodeValue kind encoded = .ok value := by
  cases kind with
  | unit =>
    simp only [encodeValue, Except.ok.injEq] at h
    subst h
    rfl
  | bool =>
    simp only [encodeValue, Except.ok.injEq] at h
    subst h
    cases value <;> rfl
  | nat =>
    simp only [encodeValue, Except.ok.injEq] at h
    subst h
    exact nat_atom_toString value
  | string =>
    simp only [encodeValue, Except.ok.injEq] at h
    subst h
    rfl
  | bitvec width =>
    simp only [encodeValue, Except.ok.injEq] at h
    subst h
    have hlt : Word.toNat value < 2 ^ width := value.isLt
    simp [decodeValue, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
      nat_atom_repr, parseHex_toHex, hlt]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt value.isLt)
  | var => simp [encodeValue] at h
  | vars => simp [encodeValue] at h
  | target => simp [encodeValue] at h
  | exp => simp [encodeValue] at h
  | program => simp [encodeValue] at h
  | cfg => simp [encodeValue] at h

/-- A hex payload that does not fit the width is rejected, never truncated. -/
theorem decodeValue_bitvec_oversized {width value : Nat} {digits : String}
    (hhex : Bil.Wire.parseHex digits = .ok value) (hbig : 2 ^ width ≤ value) :
    decodeValue (.bitvec width) (.tagged "int" [.atom (toString width), .atom digits]) =
      .error "bitvector value exceeds its width" := by
  have hnot : ¬ value < 2 ^ width := Nat.not_lt.2 hbig
  simp [decodeValue, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
    nat_atom_repr, hhex, hnot]

/-- A hex payload that fits decodes to exactly its value. -/
theorem decodeValue_bitvec_in_range {width value : Nat} {digits : String}
    (hhex : Bil.Wire.parseHex digits = .ok value) (hsmall : value < 2 ^ width) :
    ∃ word, decodeValue (.bitvec width) (.tagged "int" [.atom (toString width), .atom digits]) = .ok word ∧
      word.toNat = value := by
  refine ⟨BitVec.ofNat width value, ?_, by simpa using Nat.mod_eq_of_lt hsmall⟩
  simp [decodeValue, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
    nat_atom_repr, hhex, hsmall]

/-- The registry resolves a slot's name to that very slot. -/
def Resolves (registry : List AnySlot) (slot : AnySlot) : Prop :=
  registry.find? (fun candidate => decide (candidate.2.name = slot.2.name)) = some slot

theorem Resolves.of_nodup {registry : List AnySlot} {slot : AnySlot} (hmem : slot ∈ registry)
    (hnodup : (registry.map fun candidate => candidate.2.name).Nodup) : Resolves registry slot := by
  induction registry with
  | nil => cases hmem
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnodup
    simp only [Resolves, List.find?_cons]
    rcases List.mem_cons.1 hmem with rfl | hmem
    · simp
    · have hne : head.2.name ≠ slot.2.name := fun h => hnodup.1 slot hmem h.symm
      simp only [hne, decide_false]
      exact ih hmem hnodup.2

/-- Fact roundtrip, given a registry that knows the fact's slot. -/
theorem decodeFact_encodeFact {registry : List AnySlot} {fact : Fact} {encoded : Sexp}
    (hr : Resolves registry fact.slot) (h : encodeFact fact = .ok encoded) :
    decodeFact registry encoded = .ok fact := by
  simp only [encodeFact, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i value hv
    simp only [Except.ok.injEq] at h
    subst h
    have hdec := decodeValue_encodeValue hv
    obtain ⟨object, slot, val⟩ := fact
    have hfind : registry.find? (fun candidate => decide (candidate.2.name = slot.2.name)) = some slot := hr
    have hval : decodeValue slot.1 value = .ok val := hdec
    simp [decodeFact, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
      nat_atom_repr, hfind, hval]

/-- Opinion roundtrip, given a registry that knows the opinion's slot. -/
theorem decodeOpinion_encodeOpinion {registry : List AnySlot} {opinion : Opinion} {encoded : Sexp}
    (hr : Resolves registry opinion.fact.slot) (h : encodeOpinion opinion = .ok encoded) :
    decodeOpinion registry encoded = .ok opinion := by
  simp only [encodeOpinion, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i value hv
    simp only [Except.ok.injEq] at h
    subst h
    have hdec := decodeFact_encodeFact hr hv
    simp [decodeOpinion, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
      nat_atom_repr, hdec]

private theorem mapM_roundtrip {α : Type} {encode : α → Except String Sexp} {decode : Sexp → Except String α}
    {values : List α} {encoded : List Sexp} (h : values.mapM encode = .ok encoded)
    (hrt : ∀ value ∈ values, ∀ item, encode value = .ok item → decode item = .ok value) :
    encoded.mapM decode = .ok values := by
  induction values generalizing encoded with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i item hitem
      split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hd := hrt head List.mem_cons_self item hitem
        have ht := ih hrest fun value hv => hrt value (List.mem_cons_of_mem _ hv)
        simp only [List.mapM_cons, bind, Except.bind, hd, ht, pure, Except.pure]

/-- State roundtrip: decoding what `encodeState` wrote recovers the persistent projection, including
the version. Non-persistent slots are dropped by design. -/
theorem decodeState_encodeState {registry persistent : List AnySlot} {state : State} {encoded : Sexp}
    (hfacts : ∀ fact ∈ state.facts, fact.slot.2.name ∈ persistent.map (fun slot => slot.2.name) →
      Resolves registry fact.slot)
    (hopinions : ∀ opinion ∈ state.opinions,
      opinion.fact.slot.2.name ∈ persistent.map (fun slot => slot.2.name) →
      Resolves registry opinion.fact.slot)
    (h : encodeState persistent state = .ok encoded) :
    ∃ facts opinions,
      decodeState registry encoded = .ok { facts, opinions, version := state.version } ∧
      facts = state.facts.filter (fun fact => fact.slot.2.name ∈ persistent.map fun slot => slot.2.name) ∧
      opinions = state.opinions.filter
        (fun opinion => opinion.fact.slot.2.name ∈ persistent.map fun slot => slot.2.name) := by
  simp only [encodeState, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i encodedFacts hef
    split at h
    · cases h
    · rename_i encodedOpinions heo
      simp only [Except.ok.injEq] at h
      subst h
      have hfr := mapM_roundtrip (decode := decodeFact registry) hef (by
        intro fact hmem item hitem
        have hm := List.mem_filter.1 hmem
        exact decodeFact_encodeFact (hfacts fact hm.1 (by simpa using hm.2)) hitem)
      have hor := mapM_roundtrip (decode := decodeOpinion registry) heo (by
        intro opinion hmem item hitem
        have hm := List.mem_filter.1 hmem
        exact decodeOpinion_encodeOpinion (hopinions opinion hm.1 (by simpa using hm.2)) hitem)
      refine ⟨_, _, ?_, rfl, rfl⟩
      simp [decodeState, Sexp.tagged, Sexp.expectTagged, Sexp.asList, bind, Except.bind,
        nat_atom_repr, hfr, hor]

/-- With every fact and opinion in a persistent, uniquely named slot, nothing at all is lost. -/
theorem decodeState_encodeState_total {persistent : List AnySlot} {state : State} {encoded : Sexp}
    (hnodup : (persistent.map fun slot => slot.2.name).Nodup)
    (hfacts : ∀ fact ∈ state.facts, fact.slot ∈ persistent)
    (hopinions : ∀ opinion ∈ state.opinions, opinion.fact.slot ∈ persistent)
    (h : encodeState persistent state = .ok encoded) :
    ∃ decoded, decodeState persistent encoded = .ok decoded ∧ decoded.facts = state.facts ∧
      decoded.opinions = state.opinions ∧ decoded.version = state.version := by
  obtain ⟨facts, opinions, hdec, rfl, rfl⟩ := decodeState_encodeState (registry := persistent)
    (fun fact hmem _ => Resolves.of_nodup (hfacts fact hmem) hnodup)
    (fun opinion hmem _ => Resolves.of_nodup (hopinions opinion hmem) hnodup) h
  refine ⟨_, hdec, ?_, ?_, rfl⟩
  · apply List.filter_eq_self.2
    intro fact hmem
    simpa using ⟨_, hfacts fact hmem, rfl⟩
  · apply List.filter_eq_self.2
    intro opinion hmem
    simpa using ⟨_, hopinions opinion hmem, rfl⟩

end Persist

end Bap.Proofs.Knowledge
