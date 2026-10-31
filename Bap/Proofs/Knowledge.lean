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
open_private Bap.Knowledge.Core Bap.Knowledge.isVote as isVote
open_private Bap.Knowledge.Core Bap.Knowledge.voters as voters
open_private Bap.Knowledge.Core Bap.Knowledge.weight as weight
open_private Bap.Knowledge.Core Bap.Knowledge.outweighs as outweighs
open_private Bap.Knowledge.Core Bap.Knowledge.chooseVote as chooseVote
open_private Bap.Knowledge.Core Bap.Knowledge.promiseValue as promiseValue
open_private Bap.Knowledge.Core Bap.Knowledge.providePromised as providePromised
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

/-- The tribool is a lawful domain with unknown at the bottom. -/
theorem boolDomain_lawful : Lawful boolDomain := optionDomain_lawful

/-- Knowing `false` and knowing `true` have no common refinement. -/
theorem boolDomain_false_true : boolDomain.join (some false) (some true) = none := by decide

/-- A string is only refined by itself: a slot of names never picks one of two different names. -/
theorem stringDomain_flat {left right : String} (hleft : left ≠ "") (hright : right ≠ "") (hne : left ≠ right) :
    stringDomain.join left right = none := by
  simp [stringDomain, hleft, hright, hne]

/-- Upstream's `Domain.string` as coded, not as documented: `make_join` over an order where the empty
string is above everything and other strings are ordered lexicographically. -/
def upstreamStringDomain : Domain String where
  empty := ""
  eq := (· == ·)
  join left right :=
    if left.isEmpty || right.isEmpty then some "" else if right < left then some left else some right

/-- Why this port does not follow upstream's code: the empty value would not be the bottom, since a
join with it forgets the other side. -/
theorem upstreamStringDomain_unlawful : ¬Lawful upstreamStringDomain := fun h => by
  have := h.empty_left "a"
  simp [upstreamStringDomain] at this

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

/-- Providing the empty value is a no-op, as upstream: no fact, no conflict, no version bump. -/
theorem provideInFacts_empty (slot : Slot kind) (object : Object) {value : kind.data} (facts : List Fact)
    (h : slot.domain.eq value slot.domain.empty = true) :
    provideInFacts slot object value facts = .ok (false, facts) := by
  simp only [provideInFacts, h, ↓reduceIte]
  rfl

theorem provideInFacts_fresh (slot : Slot kind) (object : Object) {value : kind.data} (facts : List Fact)
    (hne : slot.domain.eq value slot.domain.empty = false)
    (h : lookupFact slot object facts = .ok none) :
    provideInFacts slot object value facts = .ok (true, putFact ⟨object, ⟨kind, slot⟩, value⟩ facts) := by
  simp only [provideInFacts, hne, bind, Except.bind, h, Bool.false_eq_true, ↓reduceIte]

theorem provideInFacts_existing (slot : Slot kind) (object : Object) {value : kind.data} (existing : kind.data)
    (facts : List Fact) (hne : slot.domain.eq value slot.domain.empty = false)
    (h : lookupFact slot object facts = .ok (some existing)) :
    provideInFacts slot object value facts =
      match slot.domain.join existing value with
      | none => .error (.incompatible slot.name)
      | some joined =>
        if slot.domain.eq existing joined then .ok (false, facts)
        else .ok (true, putFact ⟨object, ⟨kind, slot⟩, joined⟩ facts) := by
  simp only [provideInFacts, hne, bind, Except.bind, h, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- A slot name used at another payload kind is reported, never reinterpreted. -/
theorem provideInFacts_mismatch (slot : Slot kind) (object : Object) {value : kind.data}
    (facts : List Fact) (hne : slot.domain.eq value slot.domain.empty = false) {conflict : Conflict}
    (h : lookupFact slot object facts = .error conflict) :
    provideInFacts slot object value facts = .error conflict := by
  simp only [provideInFacts, hne, bind, Except.bind, h, Bool.false_eq_true, ↓reduceIte]

theorem provideInFacts_conflict (slot : Slot kind) (object : Object) {value existing : kind.data}
    {facts : List Fact} (hne : slot.domain.eq value slot.domain.empty = false)
    (h : lookupFact slot object facts = .ok (some existing))
    (hj : slot.domain.join existing value = none) :
    provideInFacts slot object value facts = .error (.incompatible slot.name) := by
  rw [provideInFacts_existing slot object existing facts hne h, hj]

/-- Every outcome of a successful provide: nothing happened, or the cell was written. -/
private theorem provideInFacts_cases {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (h : provideInFacts slot object value facts = .ok (changed, next)) :
    (changed = false ∧ next = facts) ∨
      (changed = true ∧ ∃ result, next = putFact ⟨object, ⟨kind, slot⟩, result⟩ facts) := by
  cases hempty : slot.domain.eq value slot.domain.empty with
  | true =>
    rw [provideInFacts_empty slot object facts hempty] at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | false =>
    cases hl : lookupFact slot object facts with
    | error conflict => rw [provideInFacts_mismatch slot object facts hempty hl] at h; cases h
    | ok found =>
      cases found with
      | none =>
        rw [provideInFacts_fresh slot object facts hempty hl] at h
        cases h
        exact Or.inr ⟨rfl, value, rfl⟩
      | some existing =>
        rw [provideInFacts_existing slot object existing facts hempty hl] at h
        split at h
        · cases h
        · split at h
          · cases h; exact Or.inl ⟨rfl, rfl⟩
          · cases h; exact Or.inr ⟨rfl, _, rfl⟩

/-- A `false` change flag really means the table was left untouched. -/
theorem provideInFacts_unchanged {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} (h : provideInFacts slot object value facts = .ok (false, next)) :
    next = facts := by
  rcases provideInFacts_cases h with ⟨_, rfl⟩ | ⟨hc, _⟩
  · rfl
  · cases hc

/-- What a successful `provideInFacts` of a non-empty value leaves at the cell it wrote. -/
private theorem provideInFacts_read {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (h : provideInFacts slot object value facts = .ok (changed, next))
    (heq : Lawful slot.domain) (hne : slot.domain.eq value slot.domain.empty = false) :
    ∃ result, lookupFact slot object next = .ok (some result) ∧
      ((lookupFact slot object facts = .ok none ∧ result = value ∧ changed = true) ∨
        ∃ existing, lookupFact slot object facts = .ok (some existing) ∧
          slot.domain.join existing value = some result ∧ (changed = true ↔ existing ≠ result)) := by
  cases hl : lookupFact slot object facts with
  | error conflict => rw [provideInFacts_mismatch slot object facts hne hl] at h; cases h
  | ok found =>
    cases found with
    | none =>
      rw [provideInFacts_fresh slot object facts hne hl] at h
      cases h
      exact ⟨value, lookup_putFact_self slot slot object value facts rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
    | some existing =>
      rw [provideInFacts_existing slot object existing facts hne hl] at h
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
          have hne' : existing ≠ joined := fun hs => he ((heq.eq_iff _ _).2 hs)
          exact ⟨joined, lookup_putFact_self slot slot object joined facts rfl,
            Or.inr ⟨existing, rfl, hj, by simp [hne']⟩⟩

/-- A successful provide never loses information: a non-empty value is stored, and the cell
afterwards refines both the old contents and the provided value. -/
theorem provideInFacts_monotone {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {changed : Bool} (hd : Lawful slot.domain)
    (h : provideInFacts slot object value facts = .ok (changed, next)) :
    (slot.domain.eq value slot.domain.empty = false →
      ∃ result, lookupFact slot object next = .ok (some result) ∧ Refines slot.domain value result) ∧
    ∀ existing, lookupFact slot object facts = .ok (some existing) →
      ∃ result, lookupFact slot object next = .ok (some result) ∧ Refines slot.domain existing result ∧
        Refines slot.domain value result := by
  cases hempty : slot.domain.eq value slot.domain.empty with
  | true =>
    rw [provideInFacts_empty slot object facts hempty] at h
    cases h
    have hvalue := (hd.eq_iff _ _).1 hempty
    refine ⟨fun hf => (by cases hf), fun existing hex => ⟨existing, hex, hd.refines_refl _, ?_⟩⟩
    rw [hvalue]
    exact hd.empty_refines _
  | false =>
    obtain ⟨result, hread, hcase⟩ := provideInFacts_read h hd hempty
    have hval : Refines slot.domain value result := by
      rcases hcase with ⟨_, rfl, _⟩ | ⟨existing, _, hj, _⟩
      · exact hd.refines_refl _
      · exact (hd.join_upper hj).2
    refine ⟨fun _ => ⟨result, hread, hval⟩, fun existing hex => ⟨result, hread, ?_, hval⟩⟩
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
  rcases provideInFacts_cases h with ⟨_, rfl⟩ | ⟨_, result, rfl⟩
  · rfl
  · apply lookup_putFact_frame
    intro he
    simp only [factKey, Prod.mk.injEq] at he
    rcases hkey with hk | hk
    · exact hk he.1
    · exact hk he.2

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
  rcases provideInFacts_cases h with ⟨_, rfl⟩ | ⟨_, result, rfl⟩
  · exact hkeys
  · exact putFact_keys_nodup _ _ hkeys

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

/-- Providing the empty value leaves the state as it is. -/
theorem provide_empty (h : slot.domain.eq value slot.domain.empty = true) (source : State) :
    provide slot object value source = .ok source := by
  simp only [provide, bind, Except.bind, provideInFacts_empty slot object _ h]
  rfl

theorem provide_read (hd : Lawful slot.domain) (hne : slot.domain.eq value slot.domain.empty = false)
    (h : provide slot object value state = .ok next) :
    ∃ result, lookupFact slot object next.facts = .ok (some result) ∧ Refines slot.domain value result ∧
      ∀ existing, lookupFact slot object state.facts = .ok (some existing) →
        Refines slot.domain existing result := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  obtain ⟨hsome, hold⟩ := provideInFacts_monotone hd hp
  obtain ⟨result, hread, hval⟩ := hsome hne
  refine ⟨result, hread, hval, fun existing hex => ?_⟩
  obtain ⟨result', hread', hre, _⟩ := hold existing hex
  rw [hread] at hread'
  cases hread'
  exact hre

/-- A successful provide on an empty cell reads back the exact value. -/
theorem provide_read_fresh (hne : slot.domain.eq value slot.domain.empty = false)
    (h : provide slot object value state = .ok next)
    (hnone : lookupFact slot object state.facts = .ok none) :
    lookupFact slot object next.facts = .ok (some value) ∧ next.version = state.version + 1 := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  rw [provideInFacts_fresh slot object _ hne hnone] at hp
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
  cases hempty : slot.domain.eq value slot.domain.empty with
  | true => exact provide_empty hempty next
  | false =>
    obtain ⟨result, hread, hval, _⟩ := provide_read hd hempty h
    have hj : slot.domain.join result value = some result := by
      rw [hd.comm]
      exact hval
    have hself : slot.domain.eq result result = true := (hd.eq_iff _ _).2 rfl
    simp only [provide, bind, Except.bind]
    rw [provideInFacts_existing slot object result _ hempty hread, hj]
    simp [hself]

private theorem provide_read_cases {v : kind.data} {source target : State} (hd : Lawful slot.domain)
    (hne : slot.domain.eq v slot.domain.empty = false) (hs : provide slot object v source = .ok target) :
    ∃ result, lookupFact slot object target.facts = .ok (some result) ∧
      ((lookupFact slot object source.facts = .ok none ∧ result = v) ∨
        ∃ existing, lookupFact slot object source.facts = .ok (some existing) ∧
          slot.domain.join existing v = some result) := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 hs
  obtain ⟨result, hread, hcase⟩ := provideInFacts_read hp hd hne
  refine ⟨result, hread, ?_⟩
  rcases hcase with ⟨h₁, h₂, _⟩ | ⟨existing, h₁, h₂, _⟩
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨existing, h₁, h₂⟩

/-- Two successful provides read back the same contents in either order. -/
theorem provide_provide_comm (hd : Lawful slot.domain) {first second : kind.data}
    (hfirst : slot.domain.eq first slot.domain.empty = false)
    (hsecond : slot.domain.eq second slot.domain.empty = false) {state₁ state₁₂ state₂ state₂₁ : State} (h₁ : provide slot object first state = .ok state₁)
    (h₁₂ : provide slot object second state₁ = .ok state₁₂)
    (h₂ : provide slot object second state = .ok state₂)
    (h₂₁ : provide slot object first state₂ = .ok state₂₁) :
    lookupFact slot object state₁₂.facts = lookupFact slot object state₂₁.facts := by
  obtain ⟨r₁, hr₁, c₁⟩ := provide_read_cases hd hfirst h₁
  obtain ⟨r₁₂, hr₁₂, c₁₂⟩ := provide_read_cases hd hsecond h₁₂
  obtain ⟨r₂, hr₂, c₂⟩ := provide_read_cases hd hsecond h₂
  obtain ⟨r₂₁, hr₂₁, c₂₁⟩ := provide_read_cases hd hfirst h₂₁
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
theorem provide_conflict {existing : kind.data} (hne : slot.domain.eq value slot.domain.empty = false)
    (hl : lookupFact slot object state.facts = .ok (some existing))
    (hj : slot.domain.join existing value = none) :
    provide slot object value state = .error (.incompatible slot.name) := by
  simp only [provide, bind, Except.bind]
  rw [provideInFacts_conflict slot object hne hl hj]

/-- `false` is a fact like any other: it is stored rather than taken for the absence of knowledge. -/
theorem provide_false_stored {slot : Slot .bool} {source : State} (hd : slot.domain = boolDomain)
    (hnone : lookupFact slot object source.facts = .ok none) :
    ∃ target, provide slot object (some false) source = .ok target ∧
      lookupFact slot object target.facts = .ok (some (some false)) ∧ target.version = source.version + 1 := by
  have hne : slot.domain.eq (some false) slot.domain.empty = false := by rw [hd]; decide
  have hp : provide slot object (some false) source = .ok
      { source with
        facts := putFact ⟨object, ⟨.bool, slot⟩, some false⟩ source.facts, version := source.version + 1 } := by
    simp only [provide, bind, Except.bind, provideInFacts_fresh slot object _ hne hnone]
    rfl
  exact ⟨_, hp, provide_read_fresh hne hp hnone⟩

/-- Knowing `true`, a claim of `false` is a conflict and not a no-op. -/
theorem provide_false_conflicts {slot : Slot .bool} {source : State} (hd : slot.domain = boolDomain)
    (htrue : lookupFact slot object source.facts = .ok (some (some true))) :
    provide slot object (some false) source = .error (.incompatible slot.name) := by
  apply provide_conflict _ htrue
  · rw [hd]; decide
  · rw [hd]; decide

theorem mem_objects_iff (key : Object) (source : State) :
    key ∈ objects source ↔ (∃ fact ∈ source.facts, fact.object = key) ∨ ∃ opinion ∈ source.opinions, opinion.fact.object = key := by
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

/-- Every known object stays known, and the provided object becomes known. -/
theorem provide_objects (hd : Lawful slot.domain) (hne : slot.domain.eq value slot.domain.empty = false)
    (h : provide slot object value state = .ok next) :
    object ∈ objects next ∧ ∀ key ∈ objects state, key ∈ objects next := by
  obtain ⟨result, hread, _⟩ := provide_read hd hne h
  refine ⟨(mem_objects_iff _ _).2 (Or.inl (lookup_some_mem hread)), ?_⟩
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  intro key hkey
  rw [mem_objects_iff] at *
  rcases hkey with hkey | hkey
  · refine Or.inl ?_
    rcases provideInFacts_cases hp with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
    · exact hkey
    · exact mem_objects_put key _ _ hkey
  · exact Or.inr hkey

end Provide

/-! ## Opinions -/

section Opinions

variable {kind other : PayloadKind} {slot : Slot kind} {object : Object} {value : kind.data}

/-- The opinions relevant to one slot of one object, as `resolve` selects them. -/
def relevant (slot : Slot kind) (object : Object) : Opinion → Bool :=
  fun opinion => decide (opinion.fact.object = object ∧ opinion.fact.slot.2.name = slot.name)

/-- An opinion as a vote for a value of the slot's kind. -/
def castVote (slot : Slot kind) (opinion : Opinion) : Except Conflict (Agent × kind.data) :=
  if h : opinion.fact.slot.1 = kind then
    .ok (opinion.agent, h ▸ opinion.fact.value)
  else
    .error (.typeMismatch slot.name)

/-- `resolve` as a function of the relevant opinions alone. -/
def resolveOf (slot : Slot kind) (opinions : List Opinion) : Except Conflict kind.data :=
  match opinions.mapM (castVote slot) with
  | .error conflict => .error conflict
  | .ok [] => .ok slot.domain.empty
  | .ok (vote :: rest) => .ok (chooseVote slot (vote :: rest) vote.2 rest)

theorem resolve_eq_resolveOf (state : State) :
    resolve slot object state = resolveOf slot (state.opinions.filter (relevant slot object)) := by
  simp only [resolve, resolveOf, bind, Except.bind]
  have hcast : (fun opinion : Opinion =>
      if h : opinion.fact.slot.1 = kind then
        (Except.ok (opinion.agent, h ▸ opinion.fact.value) : Except Conflict (Agent × kind.data))
      else .error (.typeMismatch slot.name)) = castVote slot := rfl
  have hrel : (fun opinion : Opinion =>
      decide (opinion.fact.object = object ∧ opinion.fact.slot.2.name = slot.name)) = relevant slot object := rfl
  rw [hcast, hrel]
  cases (state.opinions.filter (relevant slot object)).mapM (castVote slot) with
  | error conflict => rfl
  | ok votes => cases votes <;> rfl

/-- Suggesting nothing, or repeating a vote, changes nothing. -/
theorem suggest_empty (agent : Agent) (state : State) (h : slot.domain.eq value slot.domain.empty = true) :
    suggest agent slot object value state = state := by
  simp [suggest, h]

private theorem suggest_fresh {agent : Agent} {state : State} (hne : slot.domain.eq value slot.domain.empty = false)
    (hfresh : state.opinions.any (isVote agent slot object value) = false) :
    suggest agent slot object value state =
      { state with
        opinions := ⟨agent, object, ⟨kind, slot⟩, value⟩ :: state.opinions
        version := state.version + 1 } := by
  simp [suggest, hne, hfresh]

/-- A suggestion never touches the facts, and bumps the version exactly when it records a vote. -/
theorem suggest_frame (agent : Agent) (state : State) :
    (suggest agent slot object value state).facts = state.facts ∧
      ((suggest agent slot object value state).version = state.version ∧
          (suggest agent slot object value state).opinions = state.opinions ∨
        (suggest agent slot object value state).version = state.version + 1 ∧
          (suggest agent slot object value state).opinions =
            ⟨agent, object, ⟨kind, slot⟩, value⟩ :: state.opinions) := by
  simp only [suggest]
  split <;> simp

/-- Votes are never forgotten: an agent may hold several opinions, unlike a replaced fact. -/
theorem suggest_keeps_votes (agent : Agent) (state : State) {old : Opinion} (hold : old ∈ state.opinions) :
    old ∈ (suggest agent slot object value state).opinions := by
  rcases (suggest_frame (slot := slot) (object := object) (value := value) agent state).2 with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]; exact hold
  · rw [h]; exact List.mem_cons_of_mem _ hold

/-- A repeated suggestion by the same agent has no further effect. -/
theorem suggest_idempotent (hd : Lawful slot.domain) (agent : Agent) (state : State) :
    suggest agent slot object value (suggest agent slot object value state) =
      suggest agent slot object value state := by
  have hself : slot.domain.eq value value = true := (hd.eq_iff _ _).2 rfl
  by_cases hnop : (slot.domain.eq value slot.domain.empty || state.opinions.any (isVote agent slot object value)) = true
  · have hsame : suggest agent slot object value state = state := by simp only [suggest, hnop, ↓reduceIte]
    rw [hsame, hsame]
  · have hhead : isVote agent slot object value ⟨agent, object, ⟨kind, slot⟩, value⟩ = true := by
      simp [isVote, hself]
    have hnew : suggest agent slot object value state =
        { state with
          opinions := ⟨agent, object, ⟨kind, slot⟩, value⟩ :: state.opinions
          version := state.version + 1 } := by simp only [suggest, hnop, Bool.false_eq_true, ↓reduceIte]
    rw [hnew]
    simp only [suggest, List.any_cons, hhead, Bool.true_or, Bool.or_true, ↓reduceIte]

theorem resolve_no_opinions {state : State} (h : state.opinions.filter (relevant slot object) = []) :
    resolve slot object state = .ok slot.domain.empty := by
  rw [resolve_eq_resolveOf, h]
  rfl

/-- A suggestion about another object or slot cannot change what `resolve` returns. -/
theorem resolve_suggest_frame (agent : Agent) (state : State) (reader : Slot other) (key : Object)
    (hkey : object ≠ key ∨ slot.name ≠ reader.name) :
    resolve reader key (suggest agent slot object value state) = resolve reader key state := by
  rw [resolve_eq_resolveOf, resolve_eq_resolveOf]
  have hhead : relevant reader key ⟨agent, object, ⟨kind, slot⟩, value⟩ = false := by
    simp only [relevant, decide_eq_false_iff_not, not_and]
    rcases hkey with h | h
    · exact fun e => absurd e h
    · exact fun _ => h
  rcases (suggest_frame (slot := slot) (object := object) (value := value) agent state).2 with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]
  · rw [h, List.filter_cons, hhead]
    rfl

private theorem mapM_castVote_fst {opinions : List Opinion} {votes : List (Agent × kind.data)}
    (h : opinions.mapM (castVote slot) = .ok votes) : votes.map Prod.fst = opinions.map Opinion.agent := by
  induction opinions generalizing votes with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i vote hvote
      split at h
      · cases h
      · rename_i rest hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [castVote] at hvote
        split at hvote
        · simp only [Except.ok.injEq] at hvote
          subst hvote
          simp [ih hrest]
        · cases hvote

/-- `resolve` fails exactly when a relevant opinion is at another payload kind. -/
theorem mapM_castVote_ok_iff (opinions : List Opinion) :
    (∃ votes, opinions.mapM (castVote slot) = .ok votes) ↔
      ∀ opinion ∈ opinions, opinion.fact.slot.1 = kind := by
  induction opinions with
  | nil => exact ⟨fun _ _ h => (by cases h), fun _ => ⟨[], rfl⟩⟩
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Except.bind, List.mem_cons, forall_eq_or_imp]
    by_cases hk : head.fact.slot.1 = kind
    · have hcast : castVote slot head = .ok (head.agent, hk ▸ head.fact.value) := by
        simp [castVote, hk]
      simp only [hcast, hk, true_and, ← ih]
      constructor
      · rintro ⟨votes, h⟩
        split at h
        · cases h
        · exact ⟨_, ‹_›⟩
      · rintro ⟨votes, h⟩
        simp only [h]
        exact ⟨_, rfl⟩
    · have hcast : castVote slot head = .error (.typeMismatch slot.name) := by
        simp [castVote, hk]
      simp [hcast, hk]

private theorem chooseVote_spec (slot : Slot kind) (votes rest : List (Agent × kind.data)) (best : kind.data) :
    let result := chooseVote slot votes best rest
    (result = best ∨ ∃ vote ∈ rest, result = vote.2) ∧
      weight (voters slot votes best) ≤ weight (voters slot votes result) ∧
      ∀ vote ∈ rest, weight (voters slot votes vote.2) ≤ weight (voters slot votes result) := by
  induction rest generalizing best with
  | nil => exact ⟨Or.inl rfl, Nat.le_refl _, by simp⟩
  | cons head tail ih =>
    simp only [chooseVote, List.foldl_cons]
    generalize hstep : (if outweighs (voters slot votes head.2) (voters slot votes best) then head.2 else best) = step
    obtain ⟨hin, hge, hall⟩ := ih step
    simp only [chooseVote] at hin hge hall
    have hweights : weight (voters slot votes best) ≤ weight (voters slot votes step) ∧
        weight (voters slot votes head.2) ≤ weight (voters slot votes step) := by
      rw [← hstep]
      by_cases hout : outweighs (voters slot votes head.2) (voters slot votes best) = true
      · simp only [hout, ↓reduceIte, Nat.le_refl, and_true]
        simp only [outweighs, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hout
        omega
      · simp only [hout, Bool.false_eq_true, ↓reduceIte, Nat.le_refl, true_and]
        simp only [outweighs, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, not_or, not_and] at hout
        omega
    refine ⟨?_, Nat.le_trans hweights.1 hge, ?_⟩
    · rcases hin with hin | ⟨vote, hv, hin⟩
      · rw [hin, ← hstep]
        split
        · exact Or.inr ⟨head, List.mem_cons_self, rfl⟩
        · exact Or.inl rfl
      · exact Or.inr ⟨vote, List.mem_cons_of_mem _ hv, hin⟩
    · intro vote hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Nat.le_trans hweights.2 hge
      · exact hall vote hv

/-- The result of a vote is one of the candidates, and no candidate has more weight behind it. -/
theorem resolveOf_maximal {opinions : List Opinion} {votes : List (Agent × kind.data)} {result : kind.data}
    (hvotes : opinions.mapM (castVote slot) = .ok votes) (hne : votes ≠ [])
    (h : resolveOf slot opinions = .ok result) :
    (∃ vote ∈ votes, result = vote.2) ∧
      ∀ vote ∈ votes, weight (voters slot votes vote.2) ≤ weight (voters slot votes result) := by
  cases votes with
  | nil => exact absurd rfl hne
  | cons head rest =>
    simp only [resolveOf, hvotes, Except.ok.injEq] at h
    subst h
    obtain ⟨hin, hge, hall⟩ := chooseVote_spec slot (head :: rest) rest head.2
    refine ⟨?_, ?_⟩
    · rcases hin with hin | ⟨vote, hv, hin⟩
      · exact ⟨head, List.mem_cons_self, hin⟩
      · exact ⟨vote, List.mem_cons_of_mem _ hv, hin⟩
    · intro vote hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hge
      · exact hall vote hv

/-- When all votes agree, that is the outcome. -/
theorem resolveOf_unanimous {opinions : List Opinion} {votes : List (Agent × kind.data)}
    {result winner : kind.data} (hvotes : opinions.mapM (castVote slot) = .ok votes) (hne : votes ≠ [])
    (hall : ∀ vote ∈ votes, vote.2 = winner) (h : resolveOf slot opinions = .ok result) : result = winner := by
  obtain ⟨⟨vote, hv, rfl⟩, _⟩ := resolveOf_maximal hvotes hne h
  exact hall vote hv

private theorem sum_filter_le (agents : List Agent) (p : Agent → Bool) :
    ((agents.filter p).map Agent.trust).sum ≤ (agents.map Agent.trust).sum := by
  induction agents with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    simp only [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

private theorem weight_eraseDups_le (agents : List Agent) :
    weight agents.eraseDups ≤ (agents.map Agent.trust).sum := by
  generalize hn : agents.length = n
  induction n using Nat.strongRecOn generalizing agents with
  | _ n ih =>
    cases agents with
    | nil => simp [weight]
    | cons head tail =>
      rw [List.eraseDups_cons]
      have hlen : (tail.filter fun other => !other == head).length < n := by
        have := List.length_filter_le (fun other => !other == head) tail
        simp at hn
        omega
      have h₁ := ih _ hlen _ rfl
      have h₂ := sum_filter_le tail fun other => !other == head
      simp only [weight, List.map_cons, List.sum_cons] at h₁ ⊢
      omega

private theorem trust_le_weight {agents : List Agent} {agent : Agent} (h : agent ∈ agents) :
    agent.trust ≤ (agents.map Agent.trust).sum := by
  induction agents with
  | nil => cases h
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h
      omega

private theorem sum_voters_le (slot : Slot kind) (votes : List (Agent × kind.data)) (value : kind.data) :
    weight (voters slot votes value) ≤ ((votes.map Prod.fst).map Agent.trust).sum := by
  refine Nat.le_trans (weight_eraseDups_le _) ?_
  induction votes with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    simp only [List.filter_cons]
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

/-- An agent whose trust exceeds all other relevant opinions together decides the slot, whatever
they say. -/
theorem resolve_suggest_dominant (hd : Lawful slot.domain) (agent : Agent) (state : State)
    (hne : slot.domain.eq value slot.domain.empty = false)
    (hfresh : state.opinions.any (isVote agent slot object value) = false)
    (hkinds : ∀ old ∈ state.opinions, relevant slot object old = true → old.fact.slot.1 = kind)
    (hdom : ((state.opinions.filter (relevant slot object)).map fun old => old.agent.trust).sum < agent.trust) :
    resolve slot object (suggest agent slot object value state) = .ok value := by
  rw [resolve_eq_resolveOf, suggest_fresh hne hfresh]
  let opinion : Opinion := ⟨agent, object, ⟨kind, slot⟩, value⟩
  have hhead : relevant slot object opinion = true := by simp [relevant, opinion]
  simp only [List.filter_cons]
  rw [show relevant slot object ⟨agent, object, ⟨kind, slot⟩, value⟩ = true from hhead]
  simp only [↓reduceIte]
  generalize hrest : state.opinions.filter (relevant slot object) = others at hdom
  obtain ⟨rest, hmap⟩ := (mapM_castVote_ok_iff (slot := slot) others).2 (by
    intro old hold
    rw [← hrest, List.mem_filter] at hold
    exact hkinds old hold.1 hold.2)
  have hsum : ((rest.map Prod.fst).map Agent.trust).sum = (others.map fun old => old.agent.trust).sum := by
    rw [mapM_castVote_fst hmap, List.map_map]
    rfl
  have hcast : castVote slot opinion = .ok (agent, value) := by simp [castVote, opinion]
  have hvotes : (opinion :: others).mapM (castVote slot) = .ok ((agent, value) :: rest) := by
    simp [List.mapM_cons, bind, Except.bind, hcast, hmap, pure, Except.pure]
  cases hresult : resolveOf slot (opinion :: others) with
  | error conflict =>
    simp [resolveOf, hvotes] at hresult
  | ok winner =>
    obtain ⟨_, hmax⟩ := resolveOf_maximal hvotes (by simp) hresult
    have hself : slot.domain.eq value value = true := (hd.eq_iff _ _).2 rfl
    have hagent : agent.trust ≤ weight (voters slot ((agent, value) :: rest) value) := by
      apply trust_le_weight
      simp [voters, hself, List.mem_eraseDups]
    have hge := hmax (agent, value) List.mem_cons_self
    by_cases heq : slot.domain.eq value winner = true
    · have : value = winner := (hd.eq_iff _ _).1 heq
      rw [← this]
    · have hle : weight (voters slot ((agent, value) :: rest) winner) ≤
          ((rest.map Prod.fst).map Agent.trust).sum := by
        have hskip : voters slot ((agent, value) :: rest) winner = voters slot rest winner := by
          simp [voters, heq]
        rw [hskip]
        exact sum_voters_le slot rest winner
      simp only at hge
      omega

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

/-- A change runs the observers of the slot, and they can veto it. -/
theorem provideWith_changed (env : Environment) (h : provide slot object value state = .ok next)
    (hv : next.version ≠ state.version) :
    provideWith env slot object value state = (notifyObservers env slot object next).bind fun _ => .ok next := by
  simp [provideWith, h, bind, Except.bind, hv]

/-- A vote tells the observers of its slot when it is a new one, and only then: `suggest` is `provide` of opinions upstream. -/
theorem suggestWith_changed (env : Environment) (agent : Agent) (slot : Slot kind) (object : Object) (value : kind.data) (state : State)
    (hv : (suggest agent slot object value state).version ≠ state.version) :
    suggestWith env agent slot object value state =
      (notifyObservers env slot object (suggest agent slot object value state)).bind fun _ => .ok (suggest agent slot object value state) := by
  simp [suggestWith, bind, Except.bind, hv]

theorem suggestWith_unchanged (env : Environment) (agent : Agent) (slot : Slot kind) (object : Object) (value : kind.data) (state : State)
    (hv : (suggest agent slot object value state).version = state.version) :
    suggestWith env agent slot object value state = .ok (suggest agent slot object value state) := by
  simp [suggestWith, hv]

/-- Whatever the observers are, repeating an accepted provide neither runs them nor fails. -/
theorem provideWith_idempotent {env : Environment} (hd : Lawful slot.domain)
    (h : provideWith env slot object value state = .ok next) :
    provideWith env slot object value next = .ok next :=
  provideWith_unchanged env (provide_idempotent hd (provideWith_ok h)) rfl

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

/-- A failed `require` in a promise is that promise having nothing to say, not a conflict. -/
theorem promiseValue_empty {promise : Promise} {object : Object} {facts : List Fact} {name : String}
    (h : promise.compute object facts = .error (.empty name)) :
    promiseValue promise object facts = .ok none := by
  simp [promiseValue, h]

/-- Observers can only veto a promised value, and see it only when it refines the cell. -/
theorem providePromised_ok {env : Environment} {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {refined : Bool}
    (h : providePromised env slot object value facts = .ok (refined, next)) :
    provideInFacts slot object value facts = .ok (refined, next) := by
  simp only [providePromised, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i result hp
    obtain ⟨flag, after⟩ := result
    simp only at h
    split at h
    · split at h
      · cases h
      · cases h; exact hp
    · cases h; exact hp

theorem providePromised_unchanged {env : Environment} {slot : Slot kind} {object : Object} {value : kind.data}
    {facts : List Fact} (h : provideInFacts slot object value facts = .ok (false, facts)) :
    providePromised env slot object value facts = .ok (false, facts) := by
  simp [providePromised, h, bind, Except.bind]

/-- A rejecting observer of a refined slot fails the promise, as a failing `provide` would. -/
theorem providePromised_rejected {env : Environment} {slot : Slot kind} {object : Object} {value : kind.data}
    {facts next : List Fact} {conflict : Conflict}
    (h : provideInFacts slot object value facts = .ok (true, next))
    (hn : notifyObservers env slot object { facts := next } = .error conflict) :
    providePromised env slot object value facts = .error conflict := by
  simp [providePromised, h, hn, bind, Except.bind]

/-- First-order presentation of the promise loop in `runPromises`. -/
def runList (env : Environment) (object : Object) : List Promise → Bool → List Fact →
    Except Conflict (Bool × List Fact)
  | [], changed, facts => .ok (changed, facts)
  | promise :: rest, changed, facts =>
    match promiseValue promise object facts with
    | .error conflict => .error conflict
    | .ok none => runList env object rest changed facts
    | .ok (some value) =>
      match providePromised env promise.slot.2 object value facts with
      | .error conflict => .error conflict
      | .ok (refined, next) => runList env object rest (changed || refined) next

/-- The body of the loop in `runPromises`. -/
def loopBody (env : Environment) (object : Object) (promise : Promise) (s : Bool × List Fact) :
    Except Conflict (ForInStep (Bool × List Fact)) := do
  let value ← promiseValue promise object s.2
  match value with
  | some value => do
    let x ← providePromised env promise.slot.2 object value s.2
    match x with
    | (refined, next) => pure (ForInStep.yield (s.1 || refined, next))
  | _ => pure (ForInStep.yield (s.1, s.2))

private theorem forIn_runList (env : Environment) (object : Object) (promises : List Promise) (changed : Bool)
    (facts : List Fact) :
    forIn promises (changed, facts) (loopBody env object) = runList env object promises changed facts := by
  induction promises generalizing changed facts with
  | nil => rfl
  | cons promise rest ih =>
    simp only [List.forIn_cons, runList, bind, Except.bind, loopBody]
    cases hc : promiseValue promise object facts with
    | error conflict => rfl
    | ok value =>
      cases value with
      | none => exact ih changed facts
      | some value =>
        cases hp : providePromised env promise.slot.2 object value facts with
        | error conflict => simp only [hp]
        | ok result =>
          obtain ⟨refined, next⟩ := result
          simp only [hp]
          exact ih _ _

theorem runPromises_eq (env : Environment) (object : Object) (facts : List Fact) :
    runPromises env object facts = runList env object env.promises false facts := by
  have hdef : runPromises env object facts =
      (do
        let s ← forIn env.promises (false, facts) (loopBody env object)
        .ok (s.1, s.2)) := rfl
  rw [hdef, forIn_runList]
  cases runList env object env.promises false facts with
  | error conflict => rfl
  | ok result => rfl

private theorem runList_changed_mono {env : Environment} {object : Object} {promises : List Promise} {changed : Bool}
    {facts next : List Fact} {result : Bool} (h : runList env object promises changed facts = .ok (result, next))
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
        have := provideInFacts_unchanged (providePromised_ok hp)
        exact ⟨rfl, h₂.trans this⟩

/-- A round of promises reporting no change has left the table exactly as it was. -/
theorem runPromises_unchanged {env : Environment} {object : Object} {facts next : List Fact}
    (h : runPromises env object facts = .ok (false, next)) : next = facts := by
  rw [runPromises_eq] at h
  exact (runList_changed_mono h rfl).2

private theorem normalize_succ (env : Environment) (object : Object) (fuel : Nat) (facts : List Fact) :
    normalize env object (fuel + 1) facts =
      match runPromises env object facts with
      | .error conflict => .error conflict
      | .ok (changed, next) =>
        if changed then
          match normalize env object fuel next with
          | .error conflict => .error conflict
          | .ok (_, final) => .ok (true, final)
        else
          .ok (false, next) := by
  simp only [normalize, bind, Except.bind]
  cases runPromises env object facts with
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
    ∃ flag after, runPromises env object facts = .ok (flag, after) ∧
      ((flag = false ∧ changed = false ∧ final = after) ∨
        (flag = true ∧ changed = true ∧ ∃ inner, normalize env object fuel after = .ok (inner, final))) := by
  rw [normalize_succ] at h
  cases hrun : runPromises env object facts with
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
    runPromises env object next = .ok (false, next) := by
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
private theorem runList_frame {env : Environment} {object key : Object} (hkey : key ≠ object) (reader : Slot other)
    {promises : List Promise} {changed result : Bool} {facts next : List Fact}
    (h : runList env object promises changed facts = .ok (result, next)) :
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
        exact provideInFacts_frame (providePromised_ok hp) reader key (Or.inl hkey)

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

private theorem runList_refines {env : Environment} {slot : Slot kind} (hd : Lawful slot.domain) {object : Object}
    {promises : List Promise} (hc : Coherent slot promises) {changed result : Bool} {facts next : List Fact}
    (h : runList env object promises changed facts = .ok (result, next)) :
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
            rw [provideInFacts_frame (providePromised_ok hp) slot object (Or.inr (Ne.symm hname))]
            exact hex, hd.refines_refl _⟩
        · obtain ⟨pkind, pslot⟩ := promise
          simp only at hslot hp
          cases hslot
          intro existing hex
          obtain ⟨_, hold⟩ := provideInFacts_monotone hd (providePromised_ok hp)
          obtain ⟨res, hr, hre, _⟩ := hold existing hex
          exact ⟨res, hr, hre⟩

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
  have hne : slot.domain.eq value slot.domain.empty = false := by
    cases hempty : slot.domain.eq value slot.domain.empty with
    | false => rfl
    | true =>
      rw [provideInFacts_empty slot object facts hempty] at h
      cases h
  obtain ⟨result, hread, hcase⟩ := provideInFacts_read h hd hne
  rcases hcase with ⟨hnone, _, _⟩ | ⟨existing, hex, hj, hchanged⟩
  · exact Or.inl ⟨hnone, result, hread⟩
  · exact Or.inr ⟨existing, result, hex, hread, (hd.join_upper hj).1, hchanged.1 rfl⟩

/-- The promises of an environment have lawful domains and agree on what each slot name means. -/
def Coordinated (promises : List Promise) : Prop :=
  ∀ promise ∈ promises, Lawful promise.slot.2.domain ∧ Coherent promise.slot.2 promises

private theorem runList_grows {env : Environment} {object : Object} {promises : List Promise} (hw : Coordinated promises)
    {facts next : List Fact} {changed : Bool} (h : runList env object promises changed facts = .ok (true, next))
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
          rw [provideInFacts_unchanged (providePromised_ok hp)] at h
          exact hweaken (ih hrest h rfl)
        | true =>
          obtain ⟨hlaw, hcoh⟩ := hw head List.mem_cons_self
          have hcoh' : Coherent head.slot.2 rest := fun q hq => hcoh q (List.mem_cons_of_mem _ hq)
          exact ⟨head, List.mem_cons_self,
            (provideInFacts_grows hlaw (providePromised_ok hp)).refine hlaw (runList_refines hlaw hcoh' h)⟩

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

/-! ### The promises a collect runs -/

/-- `name` is reachable from `root` through the dependencies of `promises`. -/
inductive Reaches (promises : List Promise) (root : String) : String → Prop where
  | self : Reaches promises root root
  | dep {promise : Promise} {name : String} (hreach : Reaches promises root promise.slot.2.name)
      (hmem : promise ∈ promises) (hdep : name ∈ promise.deps) : Reaches promises root name

private theorem Reaches.mono {small large : List Promise} (hsub : ∀ promise ∈ small, promise ∈ large) {root name : String}
    (h : Reaches small root name) : Reaches large root name := by
  induction h with
  | self => exact .self
  | dep _ hmem hdep ih => exact .dep ih (hsub _ hmem) hdep

private theorem names_sub_demanded (pending : List Promise) (names : List String) :
    ∀ name ∈ names, name ∈ demanded pending names := by
  fun_induction demanded pending names with
  | case1 => exact fun _ h => h
  | case2 _ _ _ ih => exact fun name h => ih name (List.mem_append_left _ h)

private theorem demanded_sound {promises : List Promise} {root : String} (pending : List Promise) (names : List String)
    (hpending : ∀ promise ∈ pending, promise ∈ promises) (hnames : ∀ name ∈ names, Reaches promises root name) :
    ∀ name ∈ demanded pending names, Reaches promises root name := by
  fun_induction demanded pending names with
  | case1 => exact hnames
  | case2 pending names _ ih =>
    refine ih (fun promise hp => hpending _ (List.mem_filter.1 hp).1) ?_
    intro name hname
    rcases List.mem_append.1 hname with hold | hnew
    · exact hnames name hold
    · obtain ⟨promise, hp, hdep⟩ := List.mem_flatMap.1 hnew
      obtain ⟨hmem, hhit⟩ := List.mem_filter.1 hp
      exact .dep (hnames _ (by simpa using hhit)) (hpending _ hmem) hdep

private theorem demanded_closed {promises : List Promise} (pending : List Promise) (names : List String)
    (hinv : ∀ promise ∈ promises, promise ∈ pending ∨ ∀ dep ∈ promise.deps, dep ∈ names) :
    ∀ promise ∈ promises, promise.slot.2.name ∈ demanded pending names →
      ∀ dep ∈ promise.deps, dep ∈ demanded pending names := by
  fun_induction demanded pending names with
  | case1 pending names hstop =>
    intro promise hp hname
    rcases hinv promise hp with hpend | hdeps
    · have : promise ∈ pending.filter fun promise => names.contains promise.slot.2.name :=
        List.mem_filter.2 ⟨hpend, by simpa using hname⟩
      rw [hstop] at this
      cases this
    · exact hdeps
  | case2 pending names _ ih =>
    refine ih fun promise hp => ?_
    rcases hinv promise hp with hpend | hdeps
    · by_cases hname : names.contains promise.slot.2.name = true
      · refine Or.inr fun dep hdep => List.mem_append_right _ (List.mem_flatMap.2 ⟨promise, ?_, hdep⟩)
        exact List.mem_filter.2 ⟨hpend, hname⟩
      · exact Or.inl (List.mem_filter.2 ⟨hpend, by simpa using hname⟩)
    · exact Or.inr fun dep hdep => List.mem_append_left _ (hdeps dep hdep)

/-- `demanded` computes exactly the slots reachable through declared dependencies. -/
theorem mem_demanded_iff (promises : List Promise) (root name : String) :
    name ∈ demanded promises [root] ↔ Reaches promises root name := by
  constructor
  · refine demanded_sound promises [root] (fun _ h => h) ?_ name
    intro other hother
    rw [List.mem_singleton.1 hother]
    exact .self
  · intro h
    induction h with
    | self => exact names_sub_demanded _ _ _ List.mem_cons_self
    | dep _ hmem hdep ih =>
      exact demanded_closed promises [root] (fun promise hp => .inl hp) _ hmem ih _ hdep

theorem mem_demanding_iff (env : Environment) (root : String) (promise : Promise) :
    promise ∈ (env.demanding root).promises ↔
      promise ∈ env.promises ∧ Reaches env.promises root promise.slot.2.name := by
  simp [Environment.demanding, List.mem_filter, mem_demanded_iff]

/-- A slot's own promises run. -/
theorem demanding_own {env : Environment} {promise : Promise} (hmem : promise ∈ env.promises) :
    promise ∈ (env.demanding promise.slot.2.name).promises :=
  (mem_demanding_iff ..).2 ⟨hmem, .self⟩

/-- The promises of a declared dependency run whenever the promise that declares it does. -/
theorem demanding_closed {env : Environment} {root dep : String} {promise other : Promise}
    (hp : promise ∈ (env.demanding root).promises) (hdep : dep ∈ promise.deps)
    (hmem : other ∈ env.promises) (hname : other.slot.2.name = dep) :
    other ∈ (env.demanding root).promises :=
  (mem_demanding_iff ..).2 ⟨hmem, hname ▸ .dep ((mem_demanding_iff ..).1 hp).2 ((mem_demanding_iff ..).1 hp).1 hdep⟩

private theorem demanding_sub {env : Environment} {root : String} {promise : Promise}
    (h : promise ∈ (env.demanding root).promises) : promise ∈ env.promises :=
  ((mem_demanding_iff ..).1 h).1

/-- Asking twice for the same slot's promises asks for the same promises. -/
theorem demanding_idem (env : Environment) (root : String) :
    (env.demanding root).demanding root = env.demanding root := by
  have hreach : ∀ {name}, Reaches env.promises root name → Reaches (env.demanding root).promises root name := by
    intro name h
    induction h with
    | self => exact .self
    | dep hreach hmem hdep ih => exact .dep ih ((mem_demanding_iff ..).2 ⟨hmem, hreach⟩) hdep
  have hsame : (env.demanding root).promises.filter
      (fun promise => (demanded (env.demanding root).promises [root]).contains promise.slot.2.name) =
      (env.demanding root).promises := by
    apply List.filter_eq_self.2
    intro promise hp
    simpa [mem_demanded_iff] using hreach ((mem_demanding_iff ..).1 hp).2
  simp only [Environment.demanding] at hsame ⊢
  rw [hsame]

/-- Whatever a promise outside the slot's dependencies does, the collect is as if it did not exist:
its conflict, failure or divergence cannot fail the collect, nor can its value reach it. -/
theorem demanding_unrelated (env : Environment) (pre post : List Promise) (extra : Promise) (root : String)
    (hextra : ¬Reaches (pre ++ post) root extra.slot.2.name) :
    ({ env with promises := pre ++ extra :: post } : Environment).demanding root =
      ({ env with promises := pre ++ post } : Environment).demanding root := by
  have hiff : ∀ name, Reaches (pre ++ extra :: post) root name ↔ Reaches (pre ++ post) root name := by
    intro name
    constructor
    · intro h
      induction h with
      | self => exact .self
      | @dep promise _ _ hmem hdep ih =>
        have hne : promise ≠ extra := by
          rintro rfl
          exact hextra ih
        refine .dep ih ?_ hdep
        simp only [List.mem_append, List.mem_cons] at hmem ⊢
        rcases hmem with h | h | h
        · exact .inl h
        · exact absurd h hne
        · exact .inr h
    · refine Reaches.mono fun promise hp => ?_
      simp only [List.mem_append, List.mem_cons] at hp ⊢
      rcases hp with h | h
      · exact .inl h
      · exact .inr (.inr h)
  have hextraOut : ((demanded (pre ++ post) [root]).contains extra.slot.2.name) = false := by
    simpa [mem_demanded_iff] using hextra
  have hcontains : ∀ name, (demanded (pre ++ extra :: post) [root]).contains name =
      (demanded (pre ++ post) [root]).contains name := by
    intro name
    apply Bool.eq_iff_iff.2
    simp [mem_demanded_iff, hiff]
  simp only [Environment.demanding, List.filter_append, List.filter_cons, hcontains, hextraOut, Bool.false_eq_true,
    ↓reduceIte]

/-! ### Collect -/

private theorem collect_ok {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state fuel = .ok (value, next)) :
    ∃ changed facts found, normalize (env.demanding slot.name) object fuel state.facts = .ok (changed, facts) ∧
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

/-- A collect only ever runs the promises its slot demands. -/
theorem collect_demanding (env : Environment) (slot : Slot kind) (object : Object) (state : State) (fuel : Nat) :
    collect (env.demanding slot.name) slot object state fuel = collect env slot object state fuel := by
  simp only [collect, demanding_idem]

/-- A promise that the collected slot does not depend on cannot affect the collect, so in particular
a conflicting one cannot fail it. -/
theorem collect_unrelated (env : Environment) (pre post : List Promise) (extra : Promise) (slot : Slot kind)
    (object : Object) (state : State) (fuel : Nat) (hextra : ¬Reaches (pre ++ post) slot.name extra.slot.2.name) :
    collect { env with promises := pre ++ extra :: post } slot object state fuel =
      collect { env with promises := pre ++ post } slot object state fuel := by
  simp only [collect, demanding_unrelated env pre post extra slot.name hextra]

/-- The failure of a demanded promise, its own or a dependency's, fails the collect, as a failing
`collect` in the body of an upstream promise would. -/
theorem collect_demanded_failure {env : Environment} {slot : Slot kind} {object : Object} {state : State}
    {promise : Promise} {rest : List Promise} {conflict : Conflict} (fuel : Nat)
    (hfirst : (env.demanding slot.name).promises = promise :: rest)
    (hfail : promise.compute object state.facts = .error conflict) (hne : ∀ name, conflict ≠ .empty name) :
    collect env slot object state (fuel + 1) = .error conflict := by
  have hvalue : promiseValue promise object state.facts = .error conflict := by
    cases conflict with
    | empty name => exact absurd rfl (hne name)
    | _ => simp [promiseValue, hfail]
  simp only [collect, bind, Except.bind]
  rw [normalize_succ, runPromises_eq, hfirst]
  simp [runList, hvalue]

private theorem runList_absorbed {env : Environment} {object : Object} {promises : List Promise} {facts : List Fact}
    (h : runList env object promises false facts = .ok (false, facts)) {promise : Promise} (hmem : promise ∈ promises) :
    ∃ found, promiseValue promise object facts = .ok found ∧
      ∀ value, found = some value → provideInFacts promise.slot.2 object value facts = .ok (false, facts) := by
  induction promises with
  | nil => cases hmem
  | cons head rest ih =>
    simp only [runList] at h
    split at h
    · cases h
    · rename_i hnone
      rcases List.mem_cons.1 hmem with rfl | hmem
      · exact ⟨none, hnone, by simp⟩
      · exact ih h hmem
    · rename_i found hsome
      split at h
      · cases h
      · rename_i refined after hp
        obtain ⟨hflag, hafter⟩ := runList_changed_mono h rfl
        simp only [Bool.false_or] at hflag
        subst hflag
        have hunch := provideInFacts_unchanged (providePromised_ok hp)
        subst hunch
        rcases List.mem_cons.1 hmem with rfl | hmem
        · refine ⟨some found, hsome, fun value hv => ?_⟩
          cases hv
          exact providePromised_ok hp
        · exact ih h hmem

/-- What makes dependencies sound: when a collect succeeds, each promise it demanded has succeeded on
the final table, and has nothing left to add to it. -/
theorem collect_absorbed {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (h : collect env slot object state fuel = .ok (value, next))
    {promise : Promise} (hmem : promise ∈ (env.demanding slot.name).promises) :
    ∃ found, promiseValue promise object next.facts = .ok found ∧
      ∀ value, found = some value → provideInFacts promise.slot.2 object value next.facts = .ok (false, next.facts) := by
  obtain ⟨_, facts, _, hn, _, _, rfl⟩ := collect_ok h
  have hfix := normalize_fixpoint hn
  rw [runPromises_eq] at hfix
  exact runList_absorbed hfix hmem

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

private theorem Coordinated.demanding {env : Environment} (hw : Coordinated env.promises) (root : String) :
    Coordinated (env.demanding root).promises := fun promise hp =>
  ⟨(hw promise (demanding_sub hp)).1, fun other ho => (hw promise (demanding_sub hp)).2 other (demanding_sub ho)⟩

/-- On coordinated promises, `collect` bumps the version exactly when the facts changed. -/
theorem collect_version_iff {env : Environment} {slot : Slot kind} {object : Object} {state next : State}
    {fuel : Nat} {value : kind.data} (hw : Coordinated env.promises)
    (h : collect env slot object state fuel = .ok (value, next)) :
    next.version = state.version + 1 ↔ next.facts ≠ state.facts := by
  obtain ⟨changed, facts, _, hn, _, _, rfl⟩ := collect_ok h
  cases changed with
  | false => simpa using normalize_false_unchanged hn
  | true => simpa using normalize_true_changed (hw.demanding slot.name) hn

/-- The value `collect` returns refines anything the cell held beforehand. -/
theorem collect_refines {env : Environment} {slot : Slot kind} (hd : Lawful slot.domain) {object : Object}
    (hc : Coherent slot env.promises) {state next : State} {fuel : Nat} {value existing : kind.data}
    (h : collect env slot object state fuel = .ok (value, next))
    (hex : lookupFact slot object state.facts = .ok (some existing)) :
    Refines slot.domain existing value := by
  obtain ⟨_, facts, found, hn, hl, rfl, rfl⟩ := collect_ok h
  obtain ⟨result, hr, hre⟩ := normalize_refines hd (fun promise hp => hc promise (demanding_sub hp)) hn existing hex
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
  rw [normalize_no_promises _ (by simp [Environment.demanding, hempty])]
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

/-- `provide` bumps the version exactly when it changed the table, so `provideWith` tells observers
exactly about changes. -/
theorem provide_version_iff {slot : Slot kind} {object : Object} {value : kind.data} {state next : State}
    (hd : Lawful slot.domain) (h : provide slot object value state = .ok next) :
    next.version = state.version + 1 ↔ next.facts ≠ state.facts := by
  obtain ⟨changed, facts, hp, rfl⟩ := provide_ok_iff.1 h
  cases changed with
  | false => simpa using provideInFacts_unchanged hp
  | true => simpa using (provideInFacts_grows hd hp).ne

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
    rcases value with _ | _ | _ <;> rfl
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
    decodeFact registry encoded = .ok (some fact) := by
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
    decodeOpinion registry encoded = .ok (some opinion) := by
  simp only [encodeOpinion, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i value hv
    simp only [Except.ok.injEq] at h
    subst h
    have hdec := decodeFact_encodeFact hr hv
    simp [decodeOpinion, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
      nat_atom_repr, hdec]

private theorem mapM_roundtrip {α : Type} {encode : α → Except String Sexp} {decode : Sexp → Except String (Option α)}
    {values : List α} {encoded : List Sexp} (h : values.mapM encode = .ok encoded)
    (hrt : ∀ value ∈ values, ∀ item, encode value = .ok item → decode item = .ok (some value)) :
    encoded.mapM decode = .ok (values.map some) := by
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
        simp only [List.mapM_cons, bind, Except.bind, hd, ht, pure, Except.pure, List.map_cons]

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
        nat_atom_repr, hfr, hor, List.filterMap_map]

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

/-- **What nothing knows the slot of is skipped**, as upstream's `Record.of_binable`, and the rest of a state is read. -/
theorem decodeFact_unregistered {registry : List AnySlot} {object : Sexp} {name : String} {value : Sexp} {cls id objectName : String}
    (hobject : object = .tagged "object" [.atom cls, .atom objectName, .atom id]) (hid : ∃ n, Sexp.nat (.atom id) = .ok n)
    (hname : ∀ slot ∈ registry, slot.2.name ≠ name) :
    decodeFact registry (.tagged "fact" [object, .atom name, value]) = .ok none := by
  subst hobject
  obtain ⟨n, hn⟩ := hid
  have hfind : registry.find? (fun slot => decide (slot.2.name = name)) = none := by
    simpa using hname
  simp [decodeFact, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind, hn, hfind]

end Persist

end Bap.Proofs.Knowledge
