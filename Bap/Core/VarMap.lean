import Bap.Core.Types
import Std.Data.HashMap

namespace Bap

/-! A map of variables, as a state's environment is: its bindings in the order that they were first made, one for each variable, in an
array, with where each variable is in it. A lookup finds the place of its variable, rather than going through the bindings one after
another, and a binding of a variable that is bound already changes it where it is.

What proofs see of it is the array, and `get?` and `insert` as they are found from the array alone. What runs has them from the index
that the map has with it (`@[csimp]`), which is the same for every index of the array, so that two maps are equal when their arrays
are, whatever their indexes. -/

/-- That `index` has the place of each variable that `entries` binds, and of nothing else. Each variable is then bound once. -/
def VarMap.Indexes {α : Type} (entries : Array (Var × α)) (index : Std.HashMap Var Nat) : Prop :=
  ∀ var position, index[var]? = some position ↔ ∃ h : position < entries.size, entries[position].1 = var

structure VarMap (α : Type) where
  private mk ::
  entries : Array (Var × α)
  index : Squash { index : Std.HashMap Var Nat // VarMap.Indexes entries index }

namespace VarMap

variable {α β : Type}

/-! ### Indexes -/

/-- The index of an array whose variables are distinct, made from nothing. -/
def buildIndex (entries : Array (Var × α)) : Std.HashMap Var Nat :=
  go 0 ∅
where
  go (position : Nat) (index : Std.HashMap Var Nat) : Std.HashMap Var Nat :=
    if h : position < entries.size then go (position + 1) (index.insert entries[position].1 position) else index
  termination_by entries.size - position

/-- That the variables of an array are distinct. -/
def Distinct (entries : Array (Var × α)) : Prop :=
  ∀ i j (hi : i < entries.size) (hj : j < entries.size), entries[i].1 = entries[j].1 → i = j

theorem Indexes.distinct {entries : Array (Var × α)} {index : Std.HashMap Var Nat} (h : Indexes entries index) :
    Distinct entries := by
  intro i j hi hj he
  have hi' := (h entries[i].1 i).2 ⟨hi, rfl⟩
  have hj' := (h entries[i].1 j).2 ⟨hj, he.symm⟩
  rw [hi'] at hj'
  exact Option.some.inj hj'

private theorem buildIndex_go (entries : Array (Var × α)) (hd : Distinct entries) (position : Nat)
    (index : Std.HashMap Var Nat) (hpos : position ≤ entries.size)
    (hindex : ∀ var p, index[var]? = some p ↔ ∃ h : p < entries.size, p < position ∧ entries[p].1 = var) :
    Indexes entries (buildIndex.go entries position index) := by
  induction position, index using buildIndex.go.induct entries with
  | case1 position index h ih =>
    rw [buildIndex.go, dif_pos h]
    apply ih (by omega)
    intro var p
    rw [Std.HashMap.getElem?_insert]
    by_cases hv : entries[position].1 = var
    · simp only [hv, beq_self_eq_true, ite_true, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨h, by omega, hv⟩
      · rintro ⟨hp, hlt, he⟩
        exact (hd p position hp h (he.trans hv.symm)).symm
    · have hb : (entries[position].1 == var) = false := by simpa using hv
      simp only [hb, Bool.false_eq_true, ite_false, hindex]
      constructor
      · rintro ⟨hp, hlt, he⟩
        exact ⟨hp, by omega, he⟩
      · rintro ⟨hp, hlt, he⟩
        refine ⟨hp, ?_, he⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | rfl
        · exact hlt
        · exact absurd he hv
  | case2 position index h =>
    rw [buildIndex.go, dite_eq_right_iff.mpr (fun h' => absurd h' h)]
    intro var p
    rw [hindex]
    constructor
    · rintro ⟨hp, _, he⟩
      exact ⟨hp, he⟩
    · rintro ⟨hp, he⟩
      exact ⟨hp, by omega, he⟩

theorem buildIndex_indexes {entries : Array (Var × α)} (hd : Distinct entries) : Indexes entries (buildIndex entries) :=
  buildIndex_go entries hd 0 ∅ (Nat.zero_le _) fun var p => by simp

theorem Indexes.get?_eq {entries : Array (Var × α)} {first second : Std.HashMap Var Nat} (h₁ : Indexes entries first)
    (h₂ : Indexes entries second) (var : Var) : first[var]? = second[var]? := by
  cases hf : first[var]? with
  | none =>
    cases hs : second[var]? with
    | none => rfl
    | some p => exact absurd ((h₁ var p).2 ((h₂ var p).1 hs)) (by simp [hf])
  | some p => exact ((h₂ var p).2 ((h₁ var p).1 hf)).symm

/-! ### What a map is -/

theorem distinct (map : VarMap α) : Distinct map.entries := by
  obtain ⟨entries, index⟩ := map
  induction index using Quot.ind with
  | mk index => exact index.2.distinct

/-- Maps are equal when their bindings are. -/
theorem ext_entries {first second : VarMap α} (h : first.entries = second.entries) : first = second := by
  obtain ⟨entries, index⟩ := first
  obtain ⟨entries', index'⟩ := second
  simp only at h
  subst h
  congr 1
  exact Subsingleton.elim _ _

/-- The map of an array of distinct variables. -/
private def ofDistinct (entries : Array (Var × α)) (hd : Distinct entries) : VarMap α :=
  ⟨entries, Squash.mk ⟨buildIndex entries, buildIndex_indexes hd⟩⟩

def empty : VarMap α := ⟨#[], Squash.mk ⟨∅, fun var p => by simp⟩⟩

instance : EmptyCollection (VarMap α) := ⟨empty⟩
instance : Inhabited (VarMap α) := ⟨empty⟩

/-- The bindings, in the order that their variables were first bound. -/
def toList (map : VarMap α) : List (Var × α) := map.entries.toList

def size (map : VarMap α) : Nat := map.entries.size

/-- The place of a variable, as the array has it: what proofs see, and what reduces, as it has nothing of a hash. -/
def position (map : VarMap α) (var : Var) : Option Nat := map.entries.toList.findIdx? (·.1 == var)

theorem position_spec (map : VarMap α) (var : Var) (p : Nat) :
    map.position var = some p ↔ ∃ h : p < map.entries.size, map.entries[p].1 = var := by
  unfold position
  rw [List.findIdx?_eq_some_iff_getElem]
  simp only [Array.length_toList, Array.getElem_toList, beq_iff_eq]
  constructor
  · rintro ⟨h, he, -⟩
    exact ⟨h, he⟩
  · rintro ⟨h, he⟩
    refine ⟨h, he, fun j hj hje => ?_⟩
    have := map.distinct j p (by omega) h (hje.trans he.symm)
    omega

/-- `position`, from the index that the map has. -/
def positionFast (map : VarMap α) (var : Var) : Option Nat :=
  Quot.lift (fun index : { index : Std.HashMap Var Nat // Indexes map.entries index } => index.1[var]?)
    (fun first second _ => first.2.get?_eq second.2 var) map.index

@[csimp] theorem position_eq_fast : @position = @positionFast := by
  funext α map var
  apply Option.ext
  intro p
  rw [position_spec]
  obtain ⟨entries, index⟩ := map
  induction index using Quot.ind with
  | mk index => exact (index.2 var p).symm

theorem position_lt {map : VarMap α} {var : Var} {p : Nat} (h : map.position var = some p) : p < map.entries.size :=
  ((position_spec map var p).1 h).1

theorem position_none (map : VarMap α) (var : Var) :
    map.position var = none ↔ ∀ binding ∈ map.entries, binding.1 ≠ var := by
  constructor
  · intro h binding hm he
    obtain ⟨p, hp, rfl⟩ := Array.getElem_of_mem hm
    have := (position_spec map var p).2 ⟨hp, he⟩
    simp [h] at this
  · intro h
    cases hp : map.position var with
    | none => rfl
    | some p =>
      obtain ⟨hp', he⟩ := (position_spec map var p).1 hp
      exact absurd he (h _ (Array.getElem_mem hp'))

/-- The value of a variable. -/
def get? (map : VarMap α) (var : Var) : Option α :=
  match h : map.position var with
  | some p => some (map.entries[p]'(position_lt h)).2
  | none => none

def contains (map : VarMap α) (var : Var) : Bool := (map.position var).isSome

/-- The array with a variable bound to a value: where it is if it is bound, and after the rest otherwise. -/
private def insertEntries (map : VarMap α) (var : Var) (value : α) : Array (Var × α) :=
  match h : map.position var with
  | some p => map.entries.set p (var, value) (position_lt h)
  | none => map.entries.push (var, value)

private theorem insertEntries_distinct (map : VarMap α) (var : Var) (value : α) : Distinct (insertEntries map var value) := by
  have hd := map.distinct
  unfold insertEntries
  split
  · rename_i p h
    obtain ⟨hp, he⟩ := (position_spec map var p).1 h
    intro i j hi hj hij
    simp only [Array.size_set] at hi hj
    simp only [Array.getElem_set] at hij
    split at hij <;> split at hij
    · omega
    · rename_i hi' hj'
      exact absurd (hd p j hp hj (he.trans hij)) (by omega)
    · rename_i hi' hj'
      exact absurd (hd i p hi hp (hij.trans he.symm)) (by omega)
    · exact hd i j hi hj hij
  · rename_i h
    have hn := (position_none map var).1 h
    intro i j hi hj hij
    simp only [Array.size_push] at hi hj
    simp only [Array.getElem_push] at hij
    split at hij <;> split at hij
    · exact hd i j _ _ hij
    · exact absurd hij (hn _ (Array.getElem_mem _))
    · exact absurd hij.symm (hn _ (Array.getElem_mem _))
    · omega

/-- The map with a variable bound to a value, in place of what it was bound to. -/
def insert (map : VarMap α) (var : Var) (value : α) : VarMap α :=
  ofDistinct (insertEntries map var value) (insertEntries_distinct map var value)

private theorem indexes_set {entries : Array (Var × α)} {index : Std.HashMap Var Nat} (h : Indexes entries index) {p : Nat}
    (hp : p < entries.size) {var : Var} (he : entries[p].1 = var) (value : α) :
    Indexes (entries.set p (var, value) hp) index := by
  intro other q
  rw [h other q]
  simp only [Array.size_set, Array.getElem_set]
  constructor
  · rintro ⟨hq, hqe⟩
    refine ⟨hq, ?_⟩
    split
    · rename_i hpq
      subst hpq
      exact he.symm.trans hqe
    · exact hqe
  · rintro ⟨hq, hqe⟩
    refine ⟨hq, ?_⟩
    split at hqe
    · rename_i hpq
      subst hpq
      exact he.trans hqe
    · exact hqe

private theorem indexes_push {entries : Array (Var × α)} {index : Std.HashMap Var Nat} (h : Indexes entries index) {var : Var}
    (hn : index[var]? = none) (value : α) :
    Indexes (entries.push (var, value)) (index.insert var entries.size) := by
  intro other q
  rw [Std.HashMap.getElem?_insert]
  simp only [Array.size_push, Array.getElem_push]
  by_cases hv : var = other
  · subst hv
    simp only [beq_self_eq_true, ite_true, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨by omega, by simp⟩
    · rintro ⟨hq, hqe⟩
      split at hqe
      · rename_i hlt
        have := (h var q).2 ⟨hlt, hqe⟩
        simp [hn] at this
      · omega
  · have hb : (var == other) = false := by simpa using hv
    simp only [hb, Bool.false_eq_true, ite_false, h other q]
    constructor
    · rintro ⟨hq, hqe⟩
      exact ⟨by omega, by simp [hq, hqe]⟩
    · rintro ⟨hq, hqe⟩
      split at hqe
      · rename_i hlt
        exact ⟨hlt, hqe⟩
      · exact absurd (by simpa using hqe) hv

/-- `insert`, in the array where it can be and with the index that the map has, rather than a new one. A variable that is bound
already keeps the object that it has there. -/
def insertFast (map : VarMap α) (var : Var) (value : α) : VarMap α :=
  match map with
  | ⟨entries, index⟩ =>
    Quot.lift (fun index : { index : Std.HashMap Var Nat // Indexes entries index } =>
      match hp : index.1[var]? with
      | some p =>
        have hlt := ((index.2 var p).1 hp)
        -- The variable that is there stays, which is the same: what a later lookup compares is then the same object.
        (⟨entries.set p ((entries[p]'hlt.1).1, value) hlt.1, Squash.mk ⟨index.1, indexes_set index.2 hlt.1 rfl value⟩⟩ : VarMap α)
      | none => ⟨entries.push (var, value), Squash.mk ⟨index.1.insert var entries.size, indexes_push index.2 hp value⟩⟩)
      (fun first second _ => by
        apply ext_entries
        have := first.2.get?_eq second.2 var
        split <;> split <;> simp_all) index

@[csimp] theorem insert_eq_fast : @insert = @insertFast := by
  funext α map var value
  apply ext_entries
  obtain ⟨entries, index⟩ := map
  induction index using Quot.ind with
  | mk index =>
    have hsame : (⟨entries, Quot.mk _ index⟩ : VarMap α).position var = index.1[var]? := by
      apply Option.ext
      intro p
      rw [position_spec]
      exact (index.2 var p).symm
    simp only [insert, ofDistinct, insertFast, insertEntries]
    split <;> split
    · rename_i p h q hq
      have : p = q := by rw [hsame] at h; rw [h] at hq; exact Option.some.inj hq
      subst this
      have he := ((index.2 var p).1 hq).2
      simp only [he]
    · rename_i p h hq
      rw [hsame, hq] at h
      cases h
    · rename_i h q hq
      rw [hsame, hq] at h
      cases h
    · rfl

/-- The map with a variable bound to a value if it isn't bound yet. -/
def insertIfNew (map : VarMap α) (var : Var) (value : α) : VarMap α :=
  if map.contains var then map else map.insert var value

/-- The map of a list, whose first binding of a variable is its value. -/
def ofList (list : List (Var × α)) : VarMap α :=
  list.foldl (fun map binding => map.insertIfNew binding.1 binding.2) empty

instance : Coe (List (Var × α)) (VarMap α) := ⟨ofList⟩

/-- The bindings of both, where the first has the value of a variable that both bind. -/
def append (first second : VarMap α) : VarMap α :=
  if second.entries.isEmpty then first else ofList (first.toList ++ second.toList)

instance : Append (VarMap α) := ⟨append⟩

/-- The bindings that `keep` keeps, in their order. -/
def filter (map : VarMap α) (keep : Var × α → Bool) : VarMap α := ofList (map.toList.filter keep)

/-- Without a variable. -/
def erase (map : VarMap α) (var : Var) : VarMap α :=
  if map.contains var then map.filter (·.1 != var) else map

/-- The values changed, the variables where they were. -/
def mapValues (map : VarMap α) (change : Var → α → β) : VarMap β :=
  ⟨map.entries.map (fun binding => (binding.1, change binding.1 binding.2)),
    Quot.lift (fun index : { index : Std.HashMap Var Nat // Indexes map.entries index } => Squash.mk ⟨index.1, fun var p => by
        rw [index.2 var p]
        simp⟩) (fun _ _ _ => Subsingleton.elim _ _) map.index⟩

@[inline] def foldl (map : VarMap α) (step : β → Var × α → β) (init : β) : β := map.entries.foldl step init
@[inline] def find? (map : VarMap α) (test : Var × α → Bool) : Option (Var × α) := map.entries.find? test
@[inline] def any (map : VarMap α) (test : Var × α → Bool) : Bool := map.entries.any test
@[inline] def all (map : VarMap α) (test : Var × α → Bool) : Bool := map.entries.all test
@[inline] def isEmpty (map : VarMap α) : Bool := map.entries.isEmpty

instance [Monad m] : ForIn m (VarMap α) (Var × α) where
  forIn map init step := forIn map.entries init step

instance : Membership (Var × α) (VarMap α) := ⟨fun map binding => binding ∈ map.toList⟩

instance [Repr α] : Repr (VarMap α) := ⟨fun map precedence => reprPrec map.toList precedence⟩

instance [DecidableEq α] : DecidableEq (VarMap α) := fun first second =>
  if h : first.entries = second.entries then isTrue (ext_entries h) else isFalse fun e => h (e ▸ rfl)

/-! ### What proofs use -/

theorem ext {first second : VarMap α} (h : first.toList = second.toList) : first = second :=
  ext_entries (Array.toList_inj.1 h)

theorem nodup_keys (map : VarMap α) : (map.toList.map (·.1)).Nodup := by
  have hd := map.distinct
  rw [List.nodup_iff_eq_of_getElem_eq]
  intro i j hi hj he
  simp only [List.length_map, toList, Array.length_toList] at hi hj
  simp only [List.getElem_map, toList, Array.getElem_toList] at he
  exact hd i j hi hj he

/-- A list whose keys are distinct is. -/
theorem nodup_of_keys {list : List (Var × α)} (h : (list.map (·.1)).Nodup) : list.Nodup :=
  List.Pairwise.of_map (·.1) (fun _ _ hne he => hne (he ▸ rfl)) h

@[simp] theorem toList_empty : (empty : VarMap α).toList = [] := rfl
@[simp] theorem toList_emptyCollection : (∅ : VarMap α).toList = [] := rfl

@[simp] theorem mem_toList {map : VarMap α} {binding : Var × α} : binding ∈ map.toList ↔ binding ∈ map := Iff.rfl

theorem mem_iff {map : VarMap α} {binding : Var × α} : binding ∈ map ↔ binding ∈ map.entries := by
  show binding ∈ map.entries.toList ↔ _
  exact Array.mem_toList_iff

theorem get?_eq_some {map : VarMap α} {var : Var} {value : α} : map.get? var = some value ↔ (var, value) ∈ map := by
  rw [mem_iff]
  unfold get?
  split
  · rename_i p h
    obtain ⟨hp, he⟩ := (position_spec map var p).1 h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      have : map.entries[p] = (var, map.entries[p].2) := by rw [← he]
      exact this ▸ Array.getElem_mem hp
    · intro hm
      obtain ⟨q, hq, hqe⟩ := Array.getElem_of_mem hm
      have := map.distinct p q hp hq (by rw [he, hqe])
      subst this
      simp [hqe]
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hm
    exact (position_none map var).1 h _ hm rfl

theorem get?_eq_none {map : VarMap α} {var : Var} : map.get? var = none ↔ ∀ value, (var, value) ∉ map := by
  constructor
  · intro h value hm
    rw [← get?_eq_some] at hm
    simp [h] at hm
  · intro h
    cases hg : map.get? var with
    | none => rfl
    | some value => exact absurd (get?_eq_some.1 hg) (h value)

/-- The value of a variable is its binding in the list, which has one of it. -/
theorem get?_eq_find (map : VarMap α) (var : Var) :
    map.get? var = (map.toList.find? (·.1 == var)).map (·.2) := by
  cases hf : map.toList.find? (·.1 == var) with
  | none =>
    simp only [Option.map_none]
    rw [get?_eq_none]
    intro value hm
    have := List.find?_eq_none.1 hf _ hm
    simp at this
  | some binding =>
    have hm := List.mem_of_find?_eq_some hf
    have hk : binding.1 = var := by simpa using List.find?_some hf
    simp only [Option.map_some]
    rw [get?_eq_some]
    obtain ⟨k, v⟩ := binding
    simp only at hk
    subst hk
    exact hm

theorem contains_iff (map : VarMap α) (var : Var) : map.contains var = true ↔ ∃ value, (var, value) ∈ map := by
  unfold contains
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hlt, he⟩ := (position_spec map var p).1 hp
    refine ⟨map.entries[p].2, mem_iff.2 ?_⟩
    have : map.entries[p] = (var, map.entries[p].2) := by rw [← he]
    exact this ▸ Array.getElem_mem hlt
  · rintro ⟨value, hm⟩
    obtain ⟨q, hq, hqe⟩ := Array.getElem_of_mem (mem_iff.1 hm)
    have := (position_spec map var q).2 ⟨hq, by rw [hqe]⟩
    simp [this]

theorem contains_eq_isSome (map : VarMap α) (var : Var) : map.contains var = (map.get? var).isSome := by
  cases h : map.get? var with
  | none =>
    simp only [Option.isSome_none]
    cases hc : map.contains var
    · rfl
    · obtain ⟨value, hm⟩ := (contains_iff map var).1 hc
      exact absurd hm (get?_eq_none.1 h value)
  | some value => simpa using (contains_iff map var).2 ⟨value, get?_eq_some.1 h⟩

@[simp] theorem get?_empty (var : Var) : (empty : VarMap α).get? var = none := by
  rw [get?_eq_find]
  rfl

@[simp] theorem get?_emptyCollection (var : Var) : (∅ : VarMap α).get? var = none := get?_empty var

theorem toList_insert (map : VarMap α) (var : Var) (value : α) :
    (map.insert var value).toList =
      if map.contains var then map.toList.map (fun binding => if binding.1 = var then (var, value) else binding)
      else map.toList ++ [(var, value)] := by
  simp only [insert, ofDistinct, toList, insertEntries, contains]
  split
  · rename_i p h
    simp only [h, Option.isSome_some, ite_true]
    obtain ⟨hp, he⟩ := (position_spec map var p).1 h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [Array.toList_set, List.getElem_set, List.getElem_map, Array.getElem_toList]
    split
    · rename_i hpi
      subst hpi
      simp [he]
    · rename_i hpi
      split
      · rename_i hv
        exact absurd (map.distinct p i hp (by simpa using h2) (he.trans hv.symm)) hpi
      · rfl
  · rename_i h
    simp [h]

@[simp] theorem get?_insert (map : VarMap α) (var other : Var) (value : α) :
    (map.insert var value).get? other = if var = other then some value else map.get? other := by
  by_cases hv : var = other
  · subst hv
    simp only [ite_true]
    rw [get?_eq_some, ← mem_toList, toList_insert]
    split
    · rename_i hc
      obtain ⟨old, hm⟩ := (contains_iff map var).1 hc
      exact List.mem_map.2 ⟨(var, old), hm, by simp⟩
    · simp
  · simp only [hv, ite_false]
    cases hg : map.get? other with
    | none =>
      rw [get?_eq_none]
      intro x hm
      rw [← mem_toList, toList_insert] at hm
      split at hm
      · obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hm
        split at hbe
        · simp only [Prod.mk.injEq] at hbe
          exact hv hbe.1
        · subst hbe
          exact get?_eq_none.1 hg x hb
      · rcases List.mem_append.1 hm with hm | hm
        · exact get?_eq_none.1 hg x hm
        · simp only [List.mem_singleton, Prod.mk.injEq] at hm
          exact hv hm.1.symm
    | some x =>
      rw [get?_eq_some, ← mem_toList, toList_insert]
      have hm := get?_eq_some.1 hg
      split
      · exact List.mem_map.2 ⟨(other, x), hm, by simp [Ne.symm hv]⟩
      · exact List.mem_append_left _ hm

theorem get?_insertIfNew (map : VarMap α) (var other : Var) (value : α) :
    (map.insertIfNew var value).get? other =
      if var = other ∧ map.get? var = none then some value else map.get? other := by
  unfold insertIfNew
  rw [contains_eq_isSome]
  by_cases hv : var = other
  · subst hv
    cases h : map.get? var <;> simp [h]
  · split <;> simp [hv]

/-- The first binding of each variable, in their order. -/
def dedupFirst : List (Var × α) → List (Var × α)
  | [] => []
  | binding :: rest => binding :: (dedupFirst rest).filter (·.1 != binding.1)

@[simp] theorem get?_ofList (list : List (Var × α)) (var : Var) :
    (ofList list).get? var = (list.find? (·.1 == var)).map (·.2) := by
  suffices h : ∀ (list : List (Var × α)) (start : VarMap α),
      (list.foldl (fun map binding => map.insertIfNew binding.1 binding.2) start).get? var =
        match start.get? var with
        | some value => some value
        | none => (list.find? (·.1 == var)).map (·.2) by
    rw [ofList, h]
    simp
  intro list
  induction list with
  | nil => intro start; cases h : start.get? var <;> simp [h]
  | cons head rest ih =>
    intro start
    rw [List.foldl_cons, ih, get?_insertIfNew]
    obtain ⟨k, v⟩ := head
    by_cases hk : k = var
    · subst hk
      cases h : start.get? k <;> simp [h]
    · have hb : (k == var) = false := by simpa using hk
      simp [hk, hb, List.find?_cons]

theorem mem_of_mem_ofList {list : List (Var × α)} {binding : Var × α} (h : binding ∈ ofList list) : binding ∈ list := by
  obtain ⟨k, v⟩ := binding
  rw [← get?_eq_some, get?_ofList] at h
  cases hf : list.find? (·.1 == k) with
  | none => simp [hf] at h
  | some found =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hk : found.1 = k := by simpa using List.find?_some hf
    obtain ⟨k', v'⟩ := found
    simp only at hk h
    subst hk h
    exact List.mem_of_find?_eq_some hf

/-- What `filter` keeps, it keeps of the list. -/
theorem toList_ofList_of_nodup {list : List (Var × α)} (h : (list.map (·.1)).Nodup) : (ofList list).toList = list := by
  suffices hg : ∀ (list : List (Var × α)) (start : VarMap α), ((start.toList ++ list).map (·.1)).Nodup →
      (list.foldl (fun map binding => map.insertIfNew binding.1 binding.2) start).toList = start.toList ++ list by
    simpa [ofList] using hg list empty (by simpa using h)
  intro list
  induction list with
  | nil => intro start _; simp
  | cons head rest ih =>
    intro start hn
    rw [List.foldl_cons]
    have hnew : start.contains head.1 = false := by
      cases hc : start.contains head.1
      · rfl
      · obtain ⟨value, hm⟩ := (contains_iff start head.1).1 hc
        rw [List.map_append, List.nodup_append] at hn
        exact absurd rfl (hn.2.2 head.1 (List.mem_map.2 ⟨_, (mem_toList).2 hm, rfl⟩) head.1 (by simp))
    have hstep : (start.insertIfNew head.1 head.2).toList = start.toList ++ [head] := by
      simp [insertIfNew, hnew, toList_insert]
    rw [ih _ (by rw [hstep]; simpa using hn), hstep]
    simp

theorem toList_filter (map : VarMap α) (keep : Var × α → Bool) : (map.filter keep).toList = map.toList.filter keep :=
  toList_ofList_of_nodup (by
    have := map.nodup_keys
    exact (List.filter_sublist).map _ |>.nodup this)

theorem get?_filter (map : VarMap α) (keep : Var × α → Bool) (var : Var) :
    (map.filter keep).get? var = match map.get? var with
      | some value => if keep (var, value) then some value else none
      | none => none := by
  cases h : map.get? var with
  | none =>
    rw [get?_eq_none]
    intro value hm
    rw [← mem_toList, toList_filter] at hm
    exact get?_eq_none.1 h value (List.mem_filter.1 hm).1
  | some value =>
    simp only
    split
    · rename_i hk
      rw [get?_eq_some, ← mem_toList, toList_filter]
      exact List.mem_filter.2 ⟨get?_eq_some.1 h, hk⟩
    · rename_i hk
      rw [get?_eq_none]
      intro other hm
      rw [← mem_toList, toList_filter] at hm
      have hm' := List.mem_filter.1 hm
      have := get?_eq_some.2 hm'.1
      rw [h] at this
      cases this
      exact hk (by simpa using hm'.2)

@[simp] theorem get?_erase (map : VarMap α) (var other : Var) :
    (map.erase var).get? other = if var = other then none else map.get? other := by
  unfold erase
  split
  · rw [get?_filter]
    by_cases hv : var = other
    · subst hv
      cases map.get? var <;> simp
    · cases map.get? other <;> simp [Ne.symm hv, hv]
  · rename_i hc
    by_cases hv : var = other
    · subst hv
      simp only [ite_true]
      rw [contains_eq_isSome] at hc
      cases h : map.get? var <;> simp_all
    · simp [hv]

@[simp] theorem get?_mapValues (map : VarMap α) (change : Var → α → β) (var : Var) :
    (map.mapValues change).get? var = (map.get? var).map (change var) := by
  cases h : map.get? var with
  | none =>
    simp only [Option.map_none]
    rw [get?_eq_none]
    intro value hm
    rw [mem_iff] at hm
    simp only [mapValues, Array.mem_map] at hm
    obtain ⟨b, hb, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨k, v⟩ := b
    simp only at he
    obtain ⟨rfl, -⟩ := he
    exact get?_eq_none.1 h v (mem_iff.2 hb)
  | some value =>
    simp only [Option.map_some]
    rw [get?_eq_some, mem_iff]
    simp only [mapValues, Array.mem_map]
    exact ⟨(var, value), mem_iff.1 (get?_eq_some.1 h), rfl⟩

theorem size_eq_length (map : VarMap α) : map.size = map.toList.length := by simp [size, toList]

theorem foldl_eq (map : VarMap α) (step : β → Var × α → β) (init : β) :
    map.foldl step init = map.toList.foldl step init := by simp [foldl, toList, Array.foldl_toList]

theorem find?_eq (map : VarMap α) (test : Var × α → Bool) : map.find? test = map.toList.find? test := by
  simp [find?, toList, Array.find?_toList]

theorem any_eq (map : VarMap α) (test : Var × α → Bool) : map.any test = map.toList.any test := by
  simp [any, toList, Array.any_toList]

theorem all_eq (map : VarMap α) (test : Var × α → Bool) : map.all test = map.toList.all test := by
  simp [all, toList, Array.all_toList]

theorem get?_append (first second : VarMap α) (var : Var) :
    (first ++ second).get? var = match first.get? var with
      | some value => some value
      | none => second.get? var := by
  show (append first second).get? var = _
  unfold append
  split
  · rename_i hempty
    have hs : second.get? var = none := by
      rw [get?_eq_find]
      have : second.toList = [] := by simpa [toList] using hempty
      simp [this]
    cases first.get? var <;> simp [hs]
  · rw [get?_ofList, List.find?_append, get?_eq_find first, get?_eq_find second]
    cases first.toList.find? (·.1 == var) <;> simp

/-- Two maps that have the same value for each variable have the same bindings, in some order. -/
theorem get?_ext_perm {first second : VarMap α} (h : ∀ var, first.get? var = second.get? var) :
    first.toList.Perm second.toList := by
  apply (List.perm_ext_iff_of_nodup (nodup_of_keys first.nodup_keys) (nodup_of_keys second.nodup_keys)).2
  intro binding
  obtain ⟨k, v⟩ := binding
  rw [mem_toList, mem_toList, ← get?_eq_some, ← get?_eq_some, h]

end VarMap
end Bap
