import Std.Data.HashMap
import Std.Data.HashSet

/-! Which cached code may be on which page: what an invalidation goes by, so that a write looks at what is near it and not at all that
is cached. It may hold more than there is, as what was dropped from a cache stays here until a page is forgotten, so that what it
gives is only what to look at. `candidates_complete` says that it holds all that there is. -/

namespace Bap.Primus.CodeIndex

def pageSize : Nat := 4096

/-- The pages of an inclusive range of addresses. -/
def pagesOf (lo hi : Nat) : List Nat :=
  (List.range (hi / pageSize + 1 - lo / pageSize)).map (lo / pageSize + ·)

theorem mem_pagesOf {lo hi page : Nat} : page ∈ pagesOf lo hi ↔ lo / pageSize ≤ page ∧ page ≤ hi / pageSize := by
  simp only [pagesOf, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, h, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨page - lo / pageSize, by omega, by omega⟩

/-- From a page to the keys of what may be on it. -/
abbrev CodeIndex := Std.HashMap Nat (Std.HashSet Nat)

/-- `key` covers the addresses from `lo` to `hi`. -/
def add (index : CodeIndex) (key lo hi : Nat) : CodeIndex :=
  (pagesOf lo hi).foldl (init := index) fun index page =>
    index.insert page ((index.getD page {}).insert key)

/-- The keys of all that may be on the addresses from `lo` to `hi`, by whichever is fewer: the pages of the range or those that hold
anything. A range can be wide, as dirty ones are the span of what was written. -/
def candidates (index : CodeIndex) (lo hi : Nat) : List Nat :=
  let span := hi / pageSize + 1 - lo / pageSize
  if span ≤ index.size then
    (pagesOf lo hi).flatMap fun page => (index.getD page {}).toList
  else
    index.toList.flatMap fun entry =>
      if lo / pageSize ≤ entry.1 && entry.1 ≤ hi / pageSize then entry.2.toList else []

/-- `key` is in the index on each page from `lo` to `hi`. -/
def Covers (index : CodeIndex) (key lo hi : Nat) : Prop :=
  ∀ page ∈ pagesOf lo hi, key ∈ index.getD page {}

private theorem mem_getD_insert_self (index : CodeIndex) (page key : Nat) :
    key ∈ (index.insert page ((index.getD page {}).insert key)).getD page {} := by
  simp

private theorem insert_keeps (index : CodeIndex) (page key other at_ : Nat) (h : other ∈ index.getD at_ {}) :
    other ∈ (index.insert page ((index.getD page {}).insert key)).getD at_ {} := by
  rw [Std.HashMap.getD_insert]
  split
  · rename_i he
    have : page = at_ := by simpa using he
    subst this
    simp [h]
  · exact h

private theorem foldl_keeps (pages : List Nat) (index : CodeIndex) (key other at_ : Nat) (h : other ∈ index.getD at_ {}) :
    other ∈ (pages.foldl (init := index) fun index page =>
      index.insert page ((index.getD page {}).insert key)).getD at_ {} := by
  induction pages generalizing index with
  | nil => exact h
  | cons page rest ih => exact ih _ (insert_keeps index page key other at_ h)

private theorem foldl_adds (pages : List Nat) (index : CodeIndex) (key at_ : Nat) (h : at_ ∈ pages) :
    key ∈ (pages.foldl (init := index) fun index page =>
      index.insert page ((index.getD page {}).insert key)).getD at_ {} := by
  induction pages generalizing index with
  | nil => cases h
  | cons page rest ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_keeps rest _ key key at_ (mem_getD_insert_self index at_ key)
    · exact ih _ h

/-- What was added is covered. -/
theorem add_covers (index : CodeIndex) (key lo hi : Nat) : Covers (add index key lo hi) key lo hi :=
  fun _ hpage => foldl_adds _ index key _ hpage

/-- Adding takes nothing away. -/
theorem add_keeps (index : CodeIndex) {other lo' hi' : Nat} (key lo hi : Nat) (h : Covers index other lo' hi') :
    Covers (add index key lo hi) other lo' hi' :=
  fun page hpage => foldl_keeps _ index key other page (h page hpage)

/-- All that covers an address of a range is among what is looked at for it: an invalidation misses nothing. -/
theorem candidates_complete {index : CodeIndex} {key lo hi first last : Nat} (h : Covers index key lo hi) (hl : lo ≤ hi)
    (hr : first ≤ last) (h1 : lo ≤ last) (h2 : first ≤ hi) : key ∈ candidates index first last := by
  -- The first address that both have.
  let shared := max lo first / pageSize
  have hdiv {a b : Nat} (hab : a ≤ b) : a / pageSize ≤ b / pageSize := Nat.div_le_div_right hab
  have hs1 : lo / pageSize ≤ shared := hdiv (Nat.le_max_left ..)
  have hs2 : shared ≤ hi / pageSize := hdiv (by omega)
  have hs3 : first / pageSize ≤ shared := hdiv (Nat.le_max_right ..)
  have hs4 : shared ≤ last / pageSize := hdiv (by omega)
  have hkey : key ∈ index.getD shared {} := h shared (mem_pagesOf.2 ⟨hs1, hs2⟩)
  have hlist : key ∈ (index.getD shared {}).toList := Std.HashSet.mem_toList.2 hkey
  unfold candidates
  dsimp only
  split
  · exact List.mem_flatMap.2 ⟨shared, mem_pagesOf.2 ⟨hs3, hs4⟩, hlist⟩
  · -- It is on a page that holds something.
    have hcontains : shared ∈ index := by
      by_cases hc : shared ∈ index
      · exact hc
      · have : index.getD shared {} = {} := by
          simp [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_eq_none hc]
        rw [this] at hkey
        simp at hkey
    have hentry : (shared, index[shared]) ∈ index.toList := by
      simp [Std.HashMap.mem_toList_iff_getElem?_eq_some, Std.HashMap.getElem?_eq_some_getElem hcontains]
    refine List.mem_flatMap.2 ⟨_, hentry, ?_⟩
    have hget : index.getD shared {} = index[shared] := by
      simp [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_eq_some_getElem hcontains]
    simp only [hs3, hs4, decide_true, Bool.and_self, ↓reduceIte]
    rw [← hget]
    exact hlist

end Bap.Primus.CodeIndex
