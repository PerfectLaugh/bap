import Lean
import Bap.Primus.System
import Bap.Primus.Checkpoint
import Bap.Primus.Lifted
import Bap.Primus.Lisp
import Bap.Primus.Semantics

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Lean Elab Command in
/-- Like `open_private`, but for a private name that would clash with a public one. -/
local elab "open_private_as " mod:ident full:ident «alias»:ident : command => do
  let decl := OpenDecl.explicit «alias».getId (mkPrivateNameCore mod.getId full.getId)
  modifyScope fun scope => { scope with openDecls := decl :: scope.openDecls }

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Primus

open Bap.Primus

/-! ### Byte-addressed pages -/

section Pages

/-- Page-table well-formedness: pages are full-size and nonzero bytes sit at representable addresses. -/
def PagesWF (memory : Bap.Memory w) : Prop :=
  ∀ index page, memory.pages.get? index = some page →
    page.size = 256 ∧ ∀ offset, offset < 256 → page[offset]! ≠ 0 → index * 256 + offset < 2 ^ w

theorem pagesWF_empty : PagesWF (Bap.Memory.empty w) := by
  intro index page h
  simp [Bap.Memory.empty] at h

private theorem byteGet_eq (page : ByteArray) (offset : Nat) : page[offset]! = page.data[offset]! := by
  by_cases h : offset < page.size
  · have hd : offset < page.data.size := h
    rw [getElem!_pos page offset h, getElem!_pos page.data offset hd]
    rfl
  · have hd : ¬ offset < page.data.size := h
    rw [getElem!_neg page offset h, getElem!_neg page.data offset hd]

private theorem byteGet_set_same (page : ByteArray) (offset : Nat) (value : UInt8) (h : offset < page.size) :
    (page.set! offset value)[offset]! = value := by
  have hd : offset < page.data.size := h
  rw [byteGet_eq]
  cases page with | mk data =>
  simp only [ByteArray.set!, Array.set!_eq_setIfInBounds]
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.size_setIfInBounds, show offset < data.size from hd]

private theorem byteGet_set_other (page : ByteArray) (offset other : Nat) (value : UInt8) (h : offset ≠ other) :
    (page.set! offset value)[other]! = page[other]! := by
  rw [byteGet_eq, byteGet_eq]
  cases page with | mk data =>
  simp only [ByteArray.set!, Array.set!_eq_setIfInBounds]
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  simp only [Array.getD, Array.size_setIfInBounds]
  split
  · exact Array.getElem_setIfInBounds_ne _ h
  · rfl

private theorem size_set (page : ByteArray) (offset : Nat) (value : UInt8) :
    (page.set! offset value).size = page.size := by
  cases page with | mk data =>
  show (data.set! offset value).size = data.size
  simp

private theorem freshPage_size (n : Nat) : (ByteArray.mk (List.replicate n 0).toArray).size = n := by
  show (List.replicate n (0 : UInt8)).toArray.size = n
  simp

private theorem freshPage_get (n offset : Nat) :
    (ByteArray.mk (List.replicate n 0).toArray)[offset]! = 0 := by
  rw [byteGet_eq]
  show (List.replicate n (0 : UInt8)).toArray[offset]! = 0
  rw [Array.getElem!_eq_getD]
  simp only [Array.getD]
  split
  · simp
  · rfl

private theorem writeByte_pages_same (memory : Bap.Memory w) (address : BitVec w) (value : UInt8) :
    (Bap.Memory.writeByte memory address value).pages.get? (address.toNat / 256) =
      some (((memory.pages.get? (address.toNat / 256)).getD
        (ByteArray.mk (List.replicate Bap.Memory.pageSize 0).toArray)).set! (address.toNat % 256) value) := by
  show (memory.pages.insert (address.toNat / 256) _).get? (address.toNat / 256) = _
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
  rfl

private theorem writeByte_pages_other (memory : Bap.Memory w) (address : BitVec w) (value : UInt8)
    (index : Nat) (h : index ≠ address.toNat / 256) :
    (Bap.Memory.writeByte memory address value).pages.get? index = memory.pages.get? index := by
  show (memory.pages.insert (address.toNat / 256) _).get? index = _
  have he : compare (address.toNat / 256) index ≠ .eq := fun he =>
    h (Std.LawfulEqCmp.compare_eq_iff_eq.1 he).symm
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  simp [he]

theorem pagesWF_writeByte {memory : Bap.Memory w} (wf : PagesWF memory) (address : BitVec w) (value : UInt8) :
    PagesWF (Bap.Memory.writeByte memory address value) := by
  intro index page h
  by_cases hi : index = address.toNat / 256
  · subst hi
    rw [writeByte_pages_same] at h
    simp only [Option.some.injEq] at h
    subst h
    have hlt : address.toNat < 2 ^ w := address.isLt
    cases hold : memory.pages.get? (address.toNat / 256) with
    | none =>
      simp only [Option.getD_none]
      refine ⟨by rw [size_set, freshPage_size]; rfl, ?_⟩
      intro offset ho hn
      by_cases ho' : address.toNat % 256 = offset
      · have := Nat.div_add_mod address.toNat 256
        omega
      · rw [byteGet_set_other _ _ _ _ ho', freshPage_get] at hn
        exact absurd rfl hn
    | some old =>
      simp only [Option.getD_some]
      obtain ⟨hs, hr⟩ := wf _ _ hold
      refine ⟨by rw [size_set, hs], ?_⟩
      intro offset ho hn
      by_cases ho' : address.toNat % 256 = offset
      · have := Nat.div_add_mod address.toNat 256
        omega
      · rw [byteGet_set_other _ _ _ _ ho'] at hn
        exact hr offset ho hn
  · rw [writeByte_pages_other _ _ _ _ hi] at h
    exact wf _ _ h

private theorem page_offset_lt (a : Nat) : a % 256 < 256 := Nat.mod_lt _ (by decide)

/-- Read-after-write at the same address. -/
theorem readByte_writeByte_same {memory : Bap.Memory w} (wf : PagesWF memory)
    (address : BitVec w) (value : UInt8) :
    Bap.Memory.readByte (Bap.Memory.writeByte memory address value) address = value := by
  simp only [Bap.Memory.readByte, Bap.Memory.pageSize]
  rw [show address.toNat / 256 = address.toNat / 256 from rfl]
  have := writeByte_pages_same memory address value
  rw [this]
  simp only
  apply byteGet_set_same
  cases hold : memory.pages.get? (address.toNat / 256) with
  | none => simp only [Option.getD_none]; rw [freshPage_size]; exact page_offset_lt _
  | some old =>
    simp only [Option.getD_some]
    rw [(wf _ _ hold).1]
    exact page_offset_lt _

/-- A byte write leaves every other address unchanged. -/
theorem readByte_writeByte_other (memory : Bap.Memory w) (address other : BitVec w) (value : UInt8)
    (h : address ≠ other) :
    Bap.Memory.readByte (Bap.Memory.writeByte memory address value) other =
      Bap.Memory.readByte memory other := by
  have hne : address.toNat ≠ other.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
  simp only [Bap.Memory.readByte, Bap.Memory.pageSize]
  by_cases hi : other.toNat / 256 = address.toNat / 256
  · rw [hi, writeByte_pages_same]
    have hm : address.toNat % 256 ≠ other.toNat % 256 := by
      intro e
      have h1 := Nat.div_add_mod address.toNat 256
      have h2 := Nat.div_add_mod other.toNat 256
      omega
    simp only
    rw [byteGet_set_other _ _ _ _ hm]
    cases hold : memory.pages.get? (address.toNat / 256) with
    | none => simp only [Option.getD_none]; exact freshPage_get _ _
    | some old => rfl
  · rw [writeByte_pages_other _ _ _ _ hi]

/-- Characterisation of the sparse cell listing: exactly the nonzero bytes. -/
theorem mem_cells_iff {memory : Bap.Memory w} (wf : PagesWF memory) (address : BitVec w) (byte : UInt8) :
    (address, byte) ∈ Bap.Memory.cells memory ↔ byte ≠ 0 ∧ Bap.Memory.readByte memory address = byte := by
  simp only [Bap.Memory.cells, Bap.Memory.readByte, Bap.Memory.pageSize, List.mem_flatMap, List.mem_filterMap,
    List.mem_range]
  constructor
  · rintro ⟨⟨index, page⟩, hmem, offset, hoff, hcell⟩
    have hget : memory.pages.get? index = some page := by
      have := (Std.TreeMap.mem_toList_iff_getElem?_eq_some (t := memory.pages) (k := index) (v := page)).1 hmem
      simpa [Std.TreeMap.get?_eq_getElem?] using this
    obtain ⟨hs, hr⟩ := wf _ _ hget
    simp only at hcell hoff
    split at hcell
    · simp at hcell
    · rename_i hnz
      simp only [Option.some.injEq, Prod.mk.injEq] at hcell
      obtain ⟨ha, hb⟩ := hcell
      have hoff' : offset < 256 := hs ▸ hoff
      have hbound := hr offset hoff' hnz
      refine ⟨hb ▸ hnz, ?_⟩
      subst ha
      have htn : (BitVec.ofNat w (index * 256 + offset)).toNat = index * 256 + offset := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
      rw [htn]
      have hd : (index * 256 + offset) / 256 = index := by omega
      have hm : (index * 256 + offset) % 256 = offset := by omega
      rw [hd, hm, hget]
      exact hb
  · rintro ⟨hnz, hread⟩
    cases hget : memory.pages.get? (address.toNat / 256) with
    | none =>
      rw [hget] at hread
      exact absurd hread.symm hnz
    | some page =>
      rw [hget] at hread
      simp only at hread
      obtain ⟨hs, _⟩ := wf _ _ hget
      refine ⟨(address.toNat / 256, page), ?_, address.toNat % 256, ?_, ?_⟩
      · have := (Std.TreeMap.mem_toList_iff_getElem?_eq_some (t := memory.pages)
          (k := address.toNat / 256) (v := page)).2 (by simpa [Std.TreeMap.get?_eq_getElem?] using hget)
        exact this
      · simp only [hs]; exact page_offset_lt _
      · simp only [hread]
        simp only [hnz, ↓reduceIte]
        have h1 := Nat.div_add_mod address.toNat 256
        have : address.toNat / 256 * 256 + address.toNat % 256 = address.toNat := by omega
        rw [this]
        simp

/-- Folding byte writes: the final byte is the value of the last write to that address, if any. -/
theorem readByte_foldl_write {β : Type} (items : List β) (addr : β → BitVec w) (val : β → UInt8)
    (memory : Bap.Memory w) (address : BitVec w) (target : UInt8)
    (hitem : ∀ item ∈ items, addr item = address → val item = target)
    (hbase : (∃ item ∈ items, addr item = address) ∨ Bap.Memory.readByte memory address = target)
    (wf : PagesWF memory) :
    Bap.Memory.readByte (items.foldl (fun m c => Bap.Memory.writeByte m (addr c) (val c)) memory) address = target := by
  induction items generalizing memory with
  | nil =>
    rcases hbase with ⟨_, h, _⟩ | h
    · simp at h
    · exact h
  | cons cell rest ih =>
    simp only [List.foldl_cons]
    apply ih _ (fun c hc => hitem c (List.mem_cons_of_mem _ hc)) _ (pagesWF_writeByte wf _ _)
    by_cases hr : ∃ c ∈ rest, addr c = address
    · exact Or.inl hr
    · right
      by_cases he : addr cell = address
      · subst he
        rw [readByte_writeByte_same wf]
        exact hitem cell (by simp) rfl
      · rw [readByte_writeByte_other _ _ _ _ he]
        rcases hbase with ⟨c, hc, hca⟩ | h
        · rcases List.mem_cons.1 hc with rfl | hc'
          · exact absurd hca he
          · exact absurd ⟨c, hc', hca⟩ hr
        · exact h

theorem pagesWF_foldl_write {β : Type} (items : List β) (addr : β → BitVec w) (val : β → UInt8)
    (memory : Bap.Memory w) (wf : PagesWF memory) :
    PagesWF (items.foldl (fun m c => Bap.Memory.writeByte m (addr c) (val c)) memory) := by
  induction items generalizing memory with
  | nil => exact wf
  | cons cell rest ih => exact ih _ (pagesWF_writeByte wf _ _)

theorem readByte_empty_memory (address : BitVec w) : Bap.Memory.readByte (Bap.Memory.empty w) address = 0 := by
  simp [Bap.Memory.readByte, Bap.Memory.empty]

/-- `ofCells ∘ cells` is the identity up to observable bytes. -/
theorem readByte_ofCells_cells {memory : Bap.Memory w} (wf : PagesWF memory) (address : BitVec w) :
    Bap.Memory.readByte (Bap.Memory.ofCells (Bap.Memory.cells memory)) address =
      Bap.Memory.readByte memory address := by
  unfold Bap.Memory.ofCells
  refine readByte_foldl_write (Bap.Memory.cells memory) (fun c => c.1) (fun c => c.2) _ _ _ ?_ ?_ pagesWF_empty
  · rintro ⟨a, b⟩ hc rfl
    exact ((mem_cells_iff wf _ _).1 hc).2.symm
  · by_cases hz : Bap.Memory.readByte memory address = 0
    · right
      rw [hz]
      exact readByte_empty_memory _
    · left
      exact ⟨(address, _), (mem_cells_iff wf _ _).2 ⟨hz, rfl⟩, rfl⟩

end Pages

/-! ### Regions and permission-checked memory -/

section Regions

local notation "PMemory" => Bap.Primus.Memory

theorem region_contains_iff (region : Region) (address : Nat) :
    region.contains address = true ↔ region.lower ≤ address ∧ address < region.upper := by
  simp [Region.contains]

theorem region_empty_contains (region : Region) (h : region.upper ≤ region.lower) (address : Nat) :
    region.contains address = false := by
  simp only [Region.contains, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- Two regions with the same bounds contain the same addresses, whatever their permissions. -/
theorem region_contains_ext (left right : Region) (hl : left.lower = right.lower) (hu : left.upper = right.upper)
    (address : Nat) : left.contains address = right.contains address := by
  simp [Region.contains, hl, hu]

/-- The syntactic interval test used by `addRegion` implies the regions share no address. -/
theorem region_no_overlap_disjoint (left right : Region)
    (h : (left.lower < right.upper && right.lower < left.upper) = false) (address : Nat) :
    ¬ (left.contains address = true ∧ right.contains address = true) := by
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  simp only [region_contains_iff]
  omega

/-- For nonempty regions the interval test is exact: an overlap has a witness byte. -/
theorem region_overlap_witness (left right : Region) (hl : left.lower < left.upper)
    (hr : right.lower < right.upper) (h : left.lower < right.upper) (h' : right.lower < left.upper) :
    ∃ address, left.contains address = true ∧ right.contains address = true := by
  refine ⟨max left.lower right.lower, ?_, ?_⟩ <;> simp only [region_contains_iff] <;> omega

/-- Regions pairwise share no address. -/
def RegionsDisjoint (regions : List Region) : Prop :=
  regions.Pairwise fun left right => ∀ address, ¬ (left.contains address = true ∧ right.contains address = true)

private theorem protection_in_space (memory : PMemory) (address : Nat) (h : address < Bap.Primus.Memory.addressLimit) :
    memory.protection address = (memory.regions.find? fun region => region.contains address).map Region.protection := by
  simp only [Bap.Primus.Memory.protection, ge_iff_le, Nat.not_le.2 h, ↓reduceIte]
  cases memory.regions.find? (fun region => region.contains address) <;> rfl

/-- Nothing exists at or above the end of the 64-bit address space, whatever the region table says. -/
theorem protection_out_of_space (memory : PMemory) (address : Nat) (h : Bap.Primus.Memory.addressLimit ≤ address) :
    memory.protection address = none := by
  simp [Bap.Primus.Memory.protection, h]

theorem protection_some_in_space {memory : PMemory} {address : Nat} {p : Protection}
    (h : memory.protection address = some p) : address < Bap.Primus.Memory.addressLimit := by
  apply Classical.byContradiction
  intro hn
  rw [protection_out_of_space memory address (Nat.not_lt.1 hn)] at h
  simp at h

theorem protection_eq_none_iff (memory : PMemory) (address : Nat) :
    memory.protection address = none ↔
      Bap.Primus.Memory.addressLimit ≤ address ∨ ∀ region ∈ memory.regions, region.contains address = false := by
  by_cases hb : address < Bap.Primus.Memory.addressLimit
  · rw [protection_in_space _ _ hb]
    simp [Nat.not_le.2 hb]
  · simp [protection_out_of_space memory address (Nat.not_lt.1 hb), Nat.not_lt.1 hb]

theorem isMapped_iff (memory : PMemory) (address : Nat) :
    memory.isMapped address = true ↔
      address < Bap.Primus.Memory.addressLimit ∧ ∃ region ∈ memory.regions, region.contains address = true := by
  simp only [Bap.Primus.Memory.isMapped, Option.isSome_iff_ne_none, ne_eq, protection_eq_none_iff]
  simp [Nat.not_le]

theorem protection_of_disjoint {regions : List Region} (hd : RegionsDisjoint regions) (cells : Bap.Memory 64)
    {region : Region} (hm : region ∈ regions) {address : Nat} (hc : region.contains address = true)
    (hb : address < Bap.Primus.Memory.addressLimit) :
    Bap.Primus.Memory.protection ⟨cells, regions⟩ address = some region.protection := by
  simp only [Bap.Primus.Memory.protection, ge_iff_le, Nat.not_le.2 hb, ↓reduceIte]
  induction regions with
  | nil => simp at hm
  | cons head rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.1 hd
    rcases List.mem_cons.1 hm with rfl | hm'
    · simp [hc]
    · have hnot : head.contains address = false := by
        cases hh : head.contains address with
        | false => rfl
        | true => exact absurd ⟨hh, hc⟩ (hhead region hm' address)
      simpa [hnot] using ih hrest hm'

theorem addRegion_ok_iff (memory : PMemory) (region : Region) (result : PMemory) :
    Bap.Primus.Memory.addRegion memory region = .ok result ↔
      region.upper ≤ Bap.Primus.Memory.addressLimit ∧
      (memory.regions.any fun old => old.lower < region.upper && region.lower < old.upper) = false ∧
        result = { memory with regions := region :: memory.regions } := by
  simp only [Bap.Primus.Memory.addRegion, gt_iff_lt]
  by_cases hu : Bap.Primus.Memory.addressLimit < region.upper
  · simp [hu, Nat.not_le.2 hu, bind, Except.bind]
  · simp only [hu, ↓reduceIte, Nat.not_lt.1 hu, true_and]
    split <;> rename_i h
    · simp [h, bind, Except.bind]
    · simp [h, eq_comm, pure, Except.pure]

/-- A region crossing the end of the address space is refused. -/
theorem addRegion_out_of_range (memory : PMemory) (region : Region) (h : Bap.Primus.Memory.addressLimit < region.upper) :
    Bap.Primus.Memory.addRegion memory region = .error (.outOfRange region.lower region.upper) := by
  simp [Bap.Primus.Memory.addRegion, h]

/-- Every region in the table lies within the address space. -/
def RegionsInSpace (regions : List Region) : Prop :=
  ∀ region ∈ regions, region.upper ≤ Bap.Primus.Memory.addressLimit

theorem addRegion_in_space {memory result : PMemory} {region : Region}
    (hs : RegionsInSpace memory.regions) (h : Bap.Primus.Memory.addRegion memory region = .ok result) :
    RegionsInSpace result.regions := by
  obtain ⟨hu, _, rfl⟩ := (addRegion_ok_iff _ _ _).1 h
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hr'
  · exact hu
  · exact hs r hr'

/-- `addRegion` maintains pairwise disjointness: the overlap check is sound. -/
theorem addRegion_disjoint {memory result : PMemory} {region : Region}
    (hd : RegionsDisjoint memory.regions) (h : Bap.Primus.Memory.addRegion memory region = .ok result) :
    RegionsDisjoint result.regions := by
  obtain ⟨_, hany, rfl⟩ := (addRegion_ok_iff _ _ _).1 h
  refine List.pairwise_cons.2 ⟨?_, hd⟩
  intro old hold address
  have : (old.lower < region.upper && region.lower < old.upper) = false := by
    have := List.any_eq_false.1 hany old hold
    simpa using this
  have hc := region_no_overlap_disjoint old region this address
  exact fun hb => hc ⟨hb.2, hb.1⟩

/-- A freshly added region answers protection queries for its own addresses. -/
theorem addRegion_protection_inside {memory result : PMemory} {region : Region}
    (h : Bap.Primus.Memory.addRegion memory region = .ok result) {address : Nat}
    (hc : region.contains address = true) : result.protection address = some region.protection := by
  obtain ⟨hu, _, rfl⟩ := (addRegion_ok_iff _ _ _).1 h
  have hb : address < Bap.Primus.Memory.addressLimit := by
    have := ((region_contains_iff _ _).1 hc).2
    omega
  simp [Bap.Primus.Memory.protection, hc, Nat.not_le.2 hb]

/-- Adding a region does not disturb protection outside of it. -/
theorem addRegion_protection_outside {memory result : PMemory} {region : Region}
    (h : Bap.Primus.Memory.addRegion memory region = .ok result) {address : Nat}
    (hc : region.contains address = false) : result.protection address = memory.protection address := by
  obtain ⟨_, _, rfl⟩ := (addRegion_ok_iff _ _ _).1 h
  simp [Bap.Primus.Memory.protection, hc]

theorem loadByte_ok_iff (memory : PMemory) (address : Nat) (value : UInt8) :
    memory.loadByte address = .ok value ↔
      ∃ p, memory.protection address = some p ∧ p.readable = true ∧
        Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address) = value := by
  simp only [Bap.Primus.Memory.loadByte]
  cases hp : memory.protection address with
  | none => simp [bind, Except.bind]
  | some p =>
    cases hr : p.readable <;> simp [hr, pure, Except.pure]

theorem loadByte_unmapped (memory : PMemory) (address : Nat) (h : memory.isMapped address = false) :
    ∃ e, memory.loadByte address = .error e := by
  have : memory.protection address = none := by
    simpa [Bap.Primus.Memory.isMapped] using h
  simp [Bap.Primus.Memory.loadByte, this, bind, Except.bind]

theorem storeByte_ok_iff (memory : PMemory) (address : Nat) (value : UInt8) (result : PMemory) :
    memory.storeByte address value = .ok result ↔
      ∃ p, memory.protection address = some p ∧ p.writable = true ∧
        result = { memory with cells := Bap.Memory.writeByte memory.cells (BitVec.ofNat 64 address) value } := by
  simp only [Bap.Primus.Memory.storeByte]
  cases hp : memory.protection address with
  | none => simp [bind, Except.bind]
  | some p =>
    cases hr : p.writable
    · simp [hr, bind, Except.bind]
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, exists_eq_left', hr, true_and]
      exact eq_comm

theorem storeByte_readonly (memory : PMemory) (address : Nat) (value : UInt8) (p : Protection)
    (hp : memory.protection address = some p) (hw : p.writable = false) :
    ∃ e, memory.storeByte address value = .error e := by
  simp [Bap.Primus.Memory.storeByte, hp, hw, bind, Except.bind]

/-- Writes never change the region table, hence never change permissions. -/
theorem storeByte_protection {memory result : PMemory} {address other : Nat} {value : UInt8}
    (h : memory.storeByte address value = .ok result) :
    result.protection other = memory.protection other := by
  obtain ⟨_, _, _, rfl⟩ := (storeByte_ok_iff _ _ _ _).1 h
  rfl

/-- Read-after-write for permission-checked memory. -/
theorem loadByte_storeByte_same {memory result : PMemory} {address : Nat} {value : UInt8} {p : Protection}
    (wf : PagesWF memory.cells) (h : memory.storeByte address value = .ok result)
    (hp : memory.protection address = some p) (hr : p.readable = true) :
    result.loadByte address = .ok value := by
  refine (loadByte_ok_iff _ _ _).2 ⟨p, ?_, hr, ?_⟩
  · rw [storeByte_protection h, hp]
  · obtain ⟨_, _, _, rfl⟩ := (storeByte_ok_iff _ _ _ _).1 h
    exact readByte_writeByte_same wf _ _

/-- Frame law: a store leaves every other address untouched. Addresses never alias: the store only
succeeds inside the 64-bit space, where `BitVec.ofNat 64` is injective. -/
theorem loadByte_storeByte_other {memory result : PMemory} {address other : Nat} {value : UInt8}
    (h : memory.storeByte address value = .ok result) (hne : address ≠ other) :
    result.loadByte other = memory.loadByte other := by
  obtain ⟨p, hp, _, rfl⟩ := (storeByte_ok_iff _ _ _ _).1 h
  have ha := protection_some_in_space hp
  by_cases hb : other < Bap.Primus.Memory.addressLimit
  · have hbv : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 other := by
      intro e
      apply hne
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      have ha' : address < 2 ^ 64 := ha
      have hb' : other < 2 ^ 64 := hb
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
    simp only [Bap.Primus.Memory.loadByte, Bap.Primus.Memory.protection, readByte_writeByte_other _ _ _ _ hbv]
  · have hge := Nat.not_lt.1 hb
    simp [Bap.Primus.Memory.loadByte, protection_out_of_space _ _ hge, bind, Except.bind]

/-- A store at or above `2^64` fails, so it cannot alias a low address. -/
theorem storeByte_out_of_space (memory : PMemory) (address : Nat) (value : UInt8)
    (h : Bap.Primus.Memory.addressLimit ≤ address) :
    memory.storeByte address value = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.storeByte, protection_out_of_space _ _ h, bind, Except.bind]

theorem loadByte_out_of_space (memory : PMemory) (address : Nat) (h : Bap.Primus.Memory.addressLimit ≤ address) :
    memory.loadByte address = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.loadByte, protection_out_of_space _ _ h, bind, Except.bind]

/-- Fetching needs execute permission only. -/
theorem fetch_ok_iff (memory : PMemory) (address : Nat) (value : UInt8) :
    memory.fetch address = .ok value ↔
      ∃ p, memory.protection address = some p ∧ p.executable = true ∧
        Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address) = value := by
  simp only [Bap.Primus.Memory.fetch]
  cases hp : memory.protection address with
  | none => simp [bind, Except.bind]
  | some p =>
    cases hx : p.executable
    · simp [hx, bind, Except.bind]
    · simp [hx, pure, Except.pure]

/-- Execute-only memory can be fetched, but not read as data. -/
theorem execute_only_fetch_without_load (memory : PMemory) (address : Nat) (p : Protection)
    (hp : memory.protection address = some p) (hx : p.executable = true) (hr : p.readable = false) :
    memory.fetch address = .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address)) ∧
      memory.loadByte address = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.fetch, Bap.Primus.Memory.loadByte, hp, hx, hr, bind, Except.bind, pure, Except.pure]

/-- Readable but not executable memory is loadable, not fetchable. -/
theorem data_only_load_without_fetch (memory : PMemory) (address : Nat) (p : Protection)
    (hp : memory.protection address = some p) (hx : p.executable = false) (hr : p.readable = true) :
    memory.fetch address = .error (.notExecutable address) ∧
      memory.loadByte address = .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address)) := by
  simp [Bap.Primus.Memory.fetch, Bap.Primus.Memory.loadByte, hp, hx, hr, bind, Except.bind, pure, Except.pure]

/-! `load` and `store` validate every byte. -/

private theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} {items : List α} {result : List β}
    (h : items.mapM f = .ok result) (x : α) (hx : x ∈ items) : ∃ y, f x = .ok y := by
  induction items generalizing result with
  | nil => simp at hx
  | cons head rest ih =>
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hf : f head with
    | error e => simp [hf] at h
    | ok v =>
      simp only [hf] at h
      cases hr : List.mapM f rest with
      | error e => simp [hr] at h
      | ok vs =>
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨v, hf⟩
        · exact ih hr hx'

private theorem mapM_ok_all {α β ε : Type} {f : α → Except ε β} {items : List α}
    (h : ∀ x ∈ items, ∃ y, f x = .ok y) : ∃ result, items.mapM f = .ok result := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons head rest ih =>
    obtain ⟨v, hv⟩ := h head (by simp)
    obtain ⟨vs, hvs⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨v :: vs, ?_⟩
    simp [List.mapM_cons, hv, hvs, bind, Except.bind, pure, Except.pure]

/-- A successful multi-byte load proves every byte was readable; conversely readable bytes load. -/
theorem load_ok_iff (memory : PMemory) (address : Nat) (endian : Bap.Endian) (size : Nat) :
    (∃ value, memory.load address endian size = .ok value) ↔
      ∀ offset, offset < size → ∃ byte, memory.loadByte (address + offset) = .ok byte := by
  simp only [Bap.Primus.Memory.load, bind, Except.bind, pure, Except.pure]
  constructor
  · rintro ⟨value, hv⟩ offset ho
    cases hm : (List.range size).mapM (fun offset => memory.loadByte (address + offset)) with
    | error e => simp [hm] at hv
    | ok r => exact mapM_ok_mem hm offset (List.mem_range.2 ho)
  · intro h
    obtain ⟨r, hr⟩ := mapM_ok_all (items := List.range size)
      (f := fun offset => memory.loadByte (address + offset))
      (fun x hx => h x (List.mem_range.1 hx))
    exact ⟨_, by rw [hr]⟩

/-- A nonempty load that succeeds lies wholly inside the address space, so it cannot wrap. -/
theorem load_in_space {memory : PMemory} {address size : Nat} {endian : Bap.Endian} {value : BitVec (size * 8)}
    (h : memory.load address endian size = .ok value) (hs : 0 < size) :
    address + size ≤ Bap.Primus.Memory.addressLimit := by
  obtain ⟨byte, hb⟩ := (load_ok_iff memory address endian size).1 ⟨value, h⟩ (size - 1) (by omega)
  obtain ⟨p, hp, _⟩ := (loadByte_ok_iff _ _ _).1 hb
  have := protection_some_in_space hp
  omega

theorem load_value {memory : PMemory} {address size : Nat} {endian : Bap.Endian} {value : BitVec (size * 8)}
    (h : memory.load address endian size = .ok value) :
    value = Bap.Memory.read memory.cells (BitVec.ofNat 64 address) endian size := by
  simp only [Bap.Primus.Memory.load, bind, Except.bind, pure, Except.pure] at h
  cases hm : (List.range size).mapM (fun offset => memory.loadByte (address + offset)) with
  | error e => simp [hm] at h
  | ok r =>
    simp only [hm] at h
    exact (Except.ok.inj h).symm

/-- A successful multi-byte store proves every byte was mapped writable and keeps the region table. -/
theorem store_ok_sound {memory result : PMemory} {address size : Nat} {endian : Bap.Endian}
    {value : BitVec width} (h : memory.store address value endian size = .ok result) :
    result.regions = memory.regions ∧
      ∀ offset, offset < size → ∃ p, memory.protection (address + offset) = some p ∧ p.writable = true := by
  unfold Bap.Primus.Memory.store at h
  simp only [bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i r hm
    constructor
    · cases hw : Bap.Memory.write memory.cells (BitVec.ofNat 64 address) value endian size with
      | error e => simp [hw] at h
      | ok cells =>
        simp only [hw, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl
    · intro offset ho
      obtain ⟨_, hy⟩ := mapM_ok_mem hm offset (List.mem_range.2 ho)
      cases hp : memory.protection (address + offset) with
      | none => simp [hp] at hy
      | some p =>
        simp only [hp] at hy
        refine ⟨p, rfl, ?_⟩
        cases hw : p.writable
        · simp [hw] at hy
        · rfl

/-- A nonempty store that succeeds lies wholly inside the address space, so it cannot wrap. -/
theorem store_in_space {memory result : PMemory} {address size : Nat} {endian : Bap.Endian}
    {value : BitVec width} (h : memory.store address value endian size = .ok result) (hs : 0 < size) :
    address + size ≤ Bap.Primus.Memory.addressLimit := by
  obtain ⟨p, hp, _⟩ := (store_ok_sound h).2 (size - 1) (by omega)
  have := protection_some_in_space hp
  omega

/-- A value whose width disagrees with `size` is rejected, whatever the permissions. -/
theorem store_width_mismatch (memory : PMemory) (address size : Nat) (endian : Bap.Endian)
    (value : BitVec width) (h : size * 8 ≠ width) :
    ∃ e, memory.store address value endian size = .error e := by
  have hw : Bap.Memory.write memory.cells (BitVec.ofNat 64 address) value endian size =
      .error s!"expected {size * 8} bits, actual {width}" := by
    simp [Bap.Memory.write, h, bind, Except.bind]
  simp only [Bap.Primus.Memory.store, bind, Except.bind, hw]
  cases (List.range size).mapM (fun offset =>
      match memory.protection (address + offset) with
      | none => (Except.error (MemoryError.unmapped (address + offset)) : Except MemoryError Unit)
      | some protection =>
        if !protection.writable then .error (.readonly (address + offset)) else .ok ()) with
  | error e => exact ⟨e, rfl⟩
  | ok _ => exact ⟨_, rfl⟩

/-! `map` installs bytes; `protect` changes permissions only. -/

theorem map_ok_iff (memory : PMemory) (address : Nat) (data : ByteArray) (p : Protection) :
    (∃ result, memory.map address data p = .ok result) ↔
      address + data.size ≤ Bap.Primus.Memory.addressLimit ∧
      (memory.regions.any fun old => old.lower < address + data.size && address < old.upper) = false := by
  simp only [Bap.Primus.Memory.map, bind, Except.bind]
  cases h : Bap.Primus.Memory.addRegion memory ⟨address, address + data.size, p⟩ with
  | error e =>
    simp only [reduceCtorEq, exists_false, false_iff]
    rintro ⟨h1, h2⟩
    have := (addRegion_ok_iff memory ⟨address, address + data.size, p⟩ _).2 ⟨h1, h2, rfl⟩
    simp [h] at this
  | ok added =>
    obtain ⟨h1, h2, _⟩ := (addRegion_ok_iff _ _ _).1 h
    simp only [pure, Except.pure, Except.ok.injEq, exists_eq', true_iff]
    exact ⟨h1, h2⟩

private theorem map_result {memory result : PMemory} {address : Nat} {data : ByteArray} {p : Protection}
    (h : memory.map address data p = .ok result) :
    Bap.Primus.Memory.addRegion memory ⟨address, address + data.size, p⟩ =
        .ok { memory with regions := (⟨address, address + data.size, p⟩ : Region) :: memory.regions } ∧
      address + data.size ≤ Bap.Primus.Memory.addressLimit ∧
      result.regions = (⟨address, address + data.size, p⟩ : Region) :: memory.regions ∧
      result.cells = (List.range data.size).foldl (init := memory.cells) fun cells index =>
        Bap.Memory.writeByte cells (BitVec.ofNat 64 (address + index)) (data.get! index) := by
  simp only [Bap.Primus.Memory.map, bind, Except.bind] at h
  cases hadd : Bap.Primus.Memory.addRegion memory ⟨address, address + data.size, p⟩ with
  | error e => simp [hadd] at h
  | ok added =>
    simp only [hadd, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨hu, _, rfl⟩ := (addRegion_ok_iff _ _ _).1 hadd
    subst h
    exact ⟨rfl, hu, rfl, rfl⟩

theorem map_disjoint {memory result : PMemory} {address : Nat} {data : ByteArray} {p : Protection}
    (hd : RegionsDisjoint memory.regions) (h : memory.map address data p = .ok result) :
    RegionsDisjoint result.regions := by
  obtain ⟨hadd, _, hreg, _⟩ := map_result h
  rw [hreg]
  exact addRegion_disjoint hd hadd

/-- Loading from a freshly mapped region returns the mapped bytes. -/
theorem loadByte_map_inside {memory result : PMemory} {address : Nat} {data : ByteArray} {p : Protection}
    (wf : PagesWF memory.cells) (h : memory.map address data p = .ok result) (hr : p.readable = true)
    {index : Nat} (hi : index < data.size) :
    result.loadByte (address + index) = .ok (data.get! index) := by
  obtain ⟨_, bound, hreg, hcells⟩ := map_result h
  have bound' : address + data.size ≤ 2 ^ 64 := bound
  have hin : address + index < Bap.Primus.Memory.addressLimit := by
    have : Bap.Primus.Memory.addressLimit = 2 ^ 64 := rfl
    omega
  refine (loadByte_ok_iff _ _ _).2 ⟨p, ?_, hr, ?_⟩
  · simp [Bap.Primus.Memory.protection, hreg, Region.contains, hi, Nat.not_le.2 hin]
  · rw [hcells]
    apply readByte_foldl_write (List.range data.size)
      (fun i => BitVec.ofNat 64 (address + i)) (fun i => data.get! i) _ _ _ _ _ wf
    · intro j hj he
      have hj' := List.mem_range.1 hj
      have : address + j = address + index := by
        have := congrArg BitVec.toNat he
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      have : j = index := by omega
      simp [this]
    · exact Or.inl ⟨index, List.mem_range.2 hi, rfl⟩

/-- Mapping leaves addresses outside the new region as they were. -/
theorem loadByte_map_outside {memory result : PMemory} {address : Nat} {data : ByteArray} {p : Protection}
    (h : memory.map address data p = .ok result) {other : Nat}
    (ho : other < address ∨ address + data.size ≤ other) :
    result.loadByte other = memory.loadByte other := by
  obtain ⟨_, bound, hreg, hcells⟩ := map_result h
  have bound' : address + data.size ≤ 2 ^ 64 := bound
  by_cases hb : other < 2 ^ 64
  case neg =>
    have hge : Bap.Primus.Memory.addressLimit ≤ other := Nat.not_lt.1 hb
    rw [loadByte_out_of_space _ _ hge, loadByte_out_of_space _ _ hge]
  have hprot : result.protection other = memory.protection other := by
    have hc : (⟨address, address + data.size, p⟩ : Region).contains other = false := by
      simp only [Region.contains, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    simp [Bap.Primus.Memory.protection, hreg, hc]
  have hread : ∀ (items : List Nat) (cells : Bap.Memory 64), (∀ i ∈ items, i < data.size) →
      Bap.Memory.readByte (items.foldl (init := cells) fun cells index =>
        Bap.Memory.writeByte cells (BitVec.ofNat 64 (address + index)) (data.get! index))
        (BitVec.ofNat 64 other) = Bap.Memory.readByte cells (BitVec.ofNat 64 other) := by
    intro items
    induction items with
    | nil => intros; rfl
    | cons head rest ih =>
      intro cells hall
      simp only [List.foldl_cons]
      rw [ih _ fun i hi => hall i (List.mem_cons_of_mem _ hi)]
      apply readByte_writeByte_other
      have hh := hall head (by simp)
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb] at this
      omega
  simp only [Bap.Primus.Memory.loadByte, hprot, hcells]
  rw [hread _ _ fun i hi => List.mem_range.1 hi]

private theorem protect_regions (memory : PMemory) (lower upper : Nat) (p : Protection) :
    (memory.protect lower upper p).regions = memory.regions.map fun region =>
      if lower ≤ region.lower && region.upper ≤ upper then { region with protection := p } else region := rfl

private theorem protect_contains (lower upper : Nat) (p : Protection) (region : Region) (a : Nat) :
    (if lower ≤ region.lower && region.upper ≤ upper then { region with protection := p } else region).contains a =
      region.contains a := by
  split <;> rfl

theorem protect_disjoint {memory : PMemory} {lower upper : Nat} {p : Protection}
    (hd : RegionsDisjoint memory.regions) : RegionsDisjoint (memory.protect lower upper p).regions := by
  rw [protect_regions]
  simp only [RegionsDisjoint, List.pairwise_map, protect_contains]
  exact hd

/-- `protect` never changes which addresses are mapped. -/
theorem protect_isMapped (memory : PMemory) (lower upper : Nat) (p : Protection) (address : Nat) :
    (memory.protect lower upper p).isMapped address = memory.isMapped address := by
  have : (memory.protect lower upper p).isMapped address = true ↔ memory.isMapped address = true := by
    simp only [isMapped_iff, protect_regions, List.mem_map]
    constructor
    · rintro ⟨hb, _, ⟨r, hr, rfl⟩, hc⟩
      exact ⟨hb, r, hr, by rwa [protect_contains] at hc⟩
    · rintro ⟨hb, r, hr, hc⟩
      exact ⟨hb, _, ⟨r, hr, rfl⟩, by rwa [protect_contains]⟩
  cases h1 : (memory.protect lower upper p).isMapped address <;>
    cases h2 : memory.isMapped address <;> simp_all

/-- Regions fully inside the range take the new protection. -/
theorem protect_inside {regions : List Region} {cells : Bap.Memory 64} {lower upper address : Nat}
    {p : Protection} {region : Region} (hd : RegionsDisjoint regions) (hm : region ∈ regions)
    (hc : region.contains address = true) (hb : address < Bap.Primus.Memory.addressLimit)
    (hl : lower ≤ region.lower) (hu : region.upper ≤ upper) :
    (Bap.Primus.Memory.protect ⟨cells, regions⟩ lower upper p).protection address = some p := by
  have hd' := protect_disjoint (memory := ⟨cells, regions⟩) (lower := lower) (upper := upper) (p := p) hd
  have hmem : ({ region with protection := p } : Region) ∈
      (Bap.Primus.Memory.protect ⟨cells, regions⟩ lower upper p).regions := by
    rw [protect_regions]
    refine List.mem_map.2 ⟨region, hm, ?_⟩
    simp [hl, hu]
  exact protection_of_disjoint hd' cells hmem hc hb

/-- Regions not fully covered keep their protection: partial overlaps are ignored. -/
theorem protect_outside {regions : List Region} {cells : Bap.Memory 64} {lower upper address : Nat}
    {p : Protection} {region : Region} (hd : RegionsDisjoint regions) (hm : region ∈ regions)
    (hc : region.contains address = true) (hb : address < Bap.Primus.Memory.addressLimit)
    (hn : ¬ (lower ≤ region.lower ∧ region.upper ≤ upper)) :
    (Bap.Primus.Memory.protect ⟨cells, regions⟩ lower upper p).protection address = some region.protection := by
  have hd' := protect_disjoint (memory := ⟨cells, regions⟩) (lower := lower) (upper := upper) (p := p) hd
  have hmem : region ∈ (Bap.Primus.Memory.protect ⟨cells, regions⟩ lower upper p).regions := by
    rw [protect_regions]
    refine List.mem_map.2 ⟨region, hm, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, hn, ↓reduceIte]
  exact protection_of_disjoint hd' cells hmem hc hb

end Regions

/-! ### Checkpoint deltas -/

section Deltas

open_private Bap.Primus.Checkpoint Bap.Primus.Delta lookup applyCell

private theorem lookup_cells {memory : Bap.Memory 64} (wf : PagesWF memory) (address : BitVec 64) :
    lookup (Bap.Memory.cells memory) address =
      if Bap.Memory.readByte memory address = 0 then none else some (Bap.Memory.readByte memory address) := by
  simp only [lookup]
  cases hf : (Bap.Memory.cells memory).find? (fun cell => decide (cell.1 = address)) with
  | some cell =>
    have hmem := List.mem_of_find?_eq_some hf
    have hkey := List.find?_some hf
    simp only [decide_eq_true_eq] at hkey
    obtain ⟨a, b⟩ := cell
    obtain rfl : a = address := hkey
    obtain ⟨hnz, hread⟩ := (mem_cells_iff wf _ _).1 hmem
    simp [hread, hnz]
  | none =>
    have hz : Bap.Memory.readByte memory address = 0 := by
      apply Classical.byContradiction
      intro hne
      have hmem := (mem_cells_iff wf address _).2 ⟨hne, rfl⟩
      have := List.find?_eq_none.1 hf _ hmem
      simp at this
    simp [hz]

private theorem foldl_applyCell_eq (changes : List CellChange) (memory : Bap.Memory 64) :
    changes.foldl applyCell memory =
      changes.foldl (fun m c => Bap.Memory.writeByte m c.address (c.newValue.getD 0)) memory := by
  induction changes generalizing memory with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [applyCell]
    split <;> simp_all

private theorem mem_diff_cells {old new : Bap.Primus.Memory} (change : CellChange)
    (h : change ∈ (Delta.diff old new).cells) :
    (∃ byte, (change.address, byte) ∈ Bap.Memory.cells new.cells ∧ change.newValue = some byte) ∨
      ((∃ byte, (change.address, byte) ∈ Bap.Memory.cells old.cells) ∧ change.newValue = none ∧
        (lookup (Bap.Memory.cells new.cells) change.address).isSome = false) := by
  simp only [Delta.diff, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨⟨a, b⟩, hc, hf⟩ | ⟨⟨a, b⟩, hc, hf⟩
  · left
    simp only at hf
    split at hf
    · simp at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      exact ⟨b, hc, rfl⟩
  · right
    simp only at hf
    split at hf
    · simp at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      rename_i hn
      exact ⟨⟨b, hc⟩, rfl, by simpa using hn⟩

/-- Delta soundness: applying `diff old new` to `old` reproduces every byte and the region table of `new`. -/
theorem delta_apply_diff {old new : Bap.Primus.Memory} (wfOld : PagesWF old.cells) (wfNew : PagesWF new.cells)
    (address : BitVec 64) :
    Bap.Memory.readByte ((Delta.diff old new).apply old).cells address = Bap.Memory.readByte new.cells address ∧
      ((Delta.diff old new).apply old).regions = new.regions := by
  refine ⟨?_, rfl⟩
  simp only [Delta.apply]
  rw [foldl_applyCell_eq]
  refine readByte_foldl_write _ (fun c : CellChange => c.address) (fun c => c.newValue.getD 0) _ _ _ ?_ ?_ wfOld
  · intro change hc he
    rcases mem_diff_cells change hc with ⟨byte, hb, hv⟩ | ⟨_, hv, hn⟩
    · rw [hv]
      subst he
      exact ((mem_cells_iff wfNew _ _).1 hb).2.symm
    · rw [hv]
      subst he
      rw [lookup_cells wfNew] at hn
      simp only [Option.isSome_eq_false_iff] at hn
      split at hn
      · rename_i hz
        simp [hz]
      · simp at hn
  · by_cases hsame : Bap.Memory.readByte old.cells address = Bap.Memory.readByte new.cells address
    · exact Or.inr hsame
    · left
      by_cases hz : Bap.Memory.readByte new.cells address = 0
      · refine ⟨⟨address, some (Bap.Memory.readByte old.cells address), none⟩, ?_, rfl⟩
        simp only [Delta.diff, List.mem_append, List.mem_filterMap]
        right
        have hne : Bap.Memory.readByte old.cells address ≠ 0 := fun e => hsame (e.trans hz.symm)
        refine ⟨(address, _), (mem_cells_iff wfOld _ _).2 ⟨hne, rfl⟩, ?_⟩
        simp [lookup_cells wfNew, hz]
      · refine ⟨⟨address, lookup (Bap.Memory.cells old.cells) address,
          some (Bap.Memory.readByte new.cells address)⟩, ?_, rfl⟩
        simp only [Delta.diff, List.mem_append, List.mem_filterMap]
        left
        refine ⟨(address, _), (mem_cells_iff wfNew _ _).2 ⟨hz, rfl⟩, ?_⟩
        have : lookup (Bap.Memory.cells old.cells) address ≠ some (Bap.Memory.readByte new.cells address) := by
          rw [lookup_cells wfOld]
          split
          · simp
          · simpa using hsame
        simp [this]

/-- The delta is empty exactly when the two memories agree on every byte. -/
theorem delta_cells_empty_iff {old new : Bap.Primus.Memory} (wfOld : PagesWF old.cells)
    (wfNew : PagesWF new.cells) :
    (Delta.diff old new).cells = [] ↔
      ∀ address, Bap.Memory.readByte old.cells address = Bap.Memory.readByte new.cells address := by
  constructor
  · intro hempty address
    have := (delta_apply_diff wfOld wfNew address).1
    simpa [Delta.apply, hempty] using this
  · intro hall
    simp only [Delta.diff, List.append_eq_nil_iff, List.filterMap_eq_nil_iff]
    constructor
    · rintro ⟨a, b⟩ hc
      obtain ⟨hnz, hread⟩ := (mem_cells_iff wfNew _ _).1 hc
      have hold : Bap.Memory.readByte old.cells a = b := by rw [hall, hread]
      simp [lookup_cells wfOld, hold, hnz]
    · rintro ⟨a, b⟩ hc
      obtain ⟨hnz, hread⟩ := (mem_cells_iff wfOld _ _).1 hc
      have hnew : Bap.Memory.readByte new.cells a = b := by rw [← hall, hread]
      simp [lookup_cells wfNew, hnew, hnz]

/-- Each recorded change really is a change: `oldValue` and `newValue` differ. -/
theorem delta_entries_changed {old new : Bap.Primus.Memory} (change : CellChange)
    (h : change ∈ (Delta.diff old new).cells) : change.oldValue ≠ change.newValue := by
  simp only [Delta.diff, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨⟨a, b⟩, _, hf⟩ | ⟨⟨a, b⟩, _, hf⟩
  · simp only at hf
    split at hf
    · simp at hf
    · rename_i hne
      simp only [Option.some.injEq] at hf
      subst hf
      exact hne
  · simp only at hf
    split at hf
    · simp at hf
    · simp only [Option.some.injEq] at hf
      subst hf
      simp

end Deltas

/-! ### Mini Lisp evaluator -/

section Lisp

open Bap.Primus.Lisp
open_private Bap.Primus.Lisp Bap.Primus.Lisp lookup primitiveNames evalPrimitive atomValue quotedValue expectBool
  expectInt expectList symbolic bitOperation foldBil assignLocal

local notation "LV" => Bap.Primus.Lisp.Value

private theorem lookup_filter_other (key other : String) (entries : List (String × LV)) (h : key ≠ other) :
    List.lookup other (entries.filter fun entry => entry.1 != key) = List.lookup other entries := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨k, v⟩ := head
    by_cases hk : k = key
    · subst hk
      have hne : (other == k) = false := by simpa using Ne.symm h
      simp [List.filter_cons, List.lookup_cons, hne, ih]
    · have hne : (k != key) = true := by simpa using hk
      simp only [List.filter_cons, hne, ↓reduceIte, List.lookup_cons, ih]

theorem assoc_get_put_other (key other : String) (value : LV) (entries : List (String × LV)) (h : key ≠ other) :
    Assoc.get other (Assoc.put key value entries) = Assoc.get other entries := by
  have hne : (other == key) = false := by simpa using Ne.symm h
  simp [Assoc.get, Assoc.put, List.lookup_cons, hne, lookup_filter_other key other entries h]

/-- Variable resolution order: locals shadow globals, globals shadow primitives. -/
theorem lookup_local (name : String) (locals : Locals) (globals : Globals) (value : LV)
    (h : Assoc.get name locals = some value) : lookup name locals globals = .ok value := by
  simp [lookup, h]

theorem lookup_global (name : String) (locals : Locals) (globals : Globals) (value : LV)
    (hl : Assoc.get name locals = none) (h : Assoc.get name globals = some value) :
    lookup name locals globals = .ok value := by
  simp [lookup, hl, h]

theorem lookup_primitive (name : String) (locals : Locals) (globals : Globals)
    (hl : Assoc.get name locals = none) (hg : Assoc.get name globals = none)
    (hp : primitiveNames.contains name = true) :
    lookup name locals globals = .ok (.function (.primitive name)) := by
  simp only [lookup, hl, hg]
  split <;> simp_all

theorem lookup_unknown (name : String) (locals : Locals) (globals : Globals)
    (hl : Assoc.get name locals = none) (hg : Assoc.get name globals = none)
    (hp : primitiveNames.contains name = false) :
    lookup name locals globals = .error s!"unknown symbol {name}" := by
  simp only [lookup, hl, hg]
  split <;> simp_all

theorem evalExpr_zero (locals : Locals) (globals : Globals) (form : Sexp) :
    evalExpr 0 locals globals form = .error "Lisp evaluation fuel exhausted" := by
  rw [evalExpr]

/-- A symbol evaluates to its binding and leaves the environments alone. -/
theorem evalExpr_symbol (fuel : Nat) (locals : Locals) (globals : Globals) (atom : String) (value : LV)
    (ht : atom ≠ "true") (hf : atom ≠ "false") (hi : atom.toInt? = none) (hl : lookup atom locals globals = .ok value) :
    evalExpr (fuel + 1) locals globals (.atom atom) = .ok (value, locals, globals) := by
  rw [evalExpr]
  simp [ht, hf, hi, hl, bind, Except.bind]

theorem evalExpr_true (fuel : Nat) (locals : Locals) (globals : Globals) :
    evalExpr (fuel + 1) locals globals (.atom "true") = .ok (.bool true, locals, globals) := by
  rw [evalExpr]
  simp [atomValue]

theorem evalExpr_quote (fuel : Nat) (locals : Locals) (globals : Globals) (value : Sexp) :
    evalExpr (fuel + 1) locals globals (.list [.atom "quote", value]) = .ok (quotedValue value, locals, globals) := by
  rw [evalExpr]

theorem evalExpr_if_true {fuel : Nat} {locals after : Locals} {globals later : Globals} {condition yes no : Sexp}
    (h : evalExpr fuel locals globals condition = .ok (.bool true, after, later)) :
    evalExpr (fuel + 1) locals globals (.list [.atom "if", condition, yes, no]) =
      evalExpr fuel after later yes := by
  rw [evalExpr]
  simp [h, bind, Except.bind, expectBool]

theorem evalExpr_if_false {fuel : Nat} {locals after : Locals} {globals later : Globals} {condition yes no : Sexp}
    (h : evalExpr fuel locals globals condition = .ok (.bool false, after, later)) :
    evalExpr (fuel + 1) locals globals (.list [.atom "if", condition, yes, no]) =
      evalExpr fuel after later no := by
  rw [evalExpr]
  simp [h, bind, Except.bind, expectBool]

/-! Assignment follows Primus Lisp (`bap_primus_lisp.ml`, `set`): the innermost `let` binding of the
name if there is one, otherwise the global. -/

theorem assignLocal_get_same (name : String) (value : LV) (locals : Locals) (h : (Assoc.get name locals).isSome = true) :
    Assoc.get name (assignLocal name value locals) = some value := by
  induction locals with
  | nil => simp [Assoc.get] at h
  | cons head rest ih =>
    obtain ⟨key, old⟩ := head
    by_cases hk : key = name
    · subst hk
      simp [assignLocal, Assoc.get]
    · have hne : (name == key) = false := by simpa using Ne.symm hk
      simp only [Assoc.get, List.lookup_cons, hne, Bool.cond_false] at h ih
      simp [assignLocal, hk, Assoc.get, List.lookup_cons, hne, ih h]

theorem assignLocal_get_other (name other : String) (value : LV) (locals : Locals) (h : name ≠ other) :
    Assoc.get other (assignLocal name value locals) = Assoc.get other locals := by
  induction locals with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, old⟩ := head
    by_cases hk : key = name
    · subst hk
      have hne : (other == key) = false := by simpa using Ne.symm h
      simp [assignLocal, Assoc.get, List.lookup_cons, hne]
    · simp only [Assoc.get] at ih
      cases ho : other == key <;> simp [assignLocal, hk, Assoc.get, List.lookup_cons, ho, ih]

theorem assignLocal_length (name : String) (value : LV) (locals : Locals) :
    (assignLocal name value locals).length = locals.length := by
  induction locals with
  | nil => rfl
  | cons head rest ih =>
    simp only [assignLocal]
    split <;> simp [ih]

/-- Assignment changes the innermost binding only: a shadowed outer binding keeps its value. -/
theorem assignLocal_innermost (name : String) (inner outer value : LV) (rest : Locals) :
    assignLocal name value ((name, inner) :: (name, outer) :: rest) = (name, value) :: (name, outer) :: rest := by
  simp [assignLocal]

/-- `setq` of a `let`-bound name updates that binding and leaves the globals alone. -/
theorem evalExpr_setq_local {fuel : Nat} {locals after : Locals} {globals later : Globals} {name : String}
    {form : Sexp} {value : LV} (h : evalExpr fuel locals globals form = .ok (value, after, later))
    (bound : (Assoc.get name after).isSome = true) :
    evalExpr (fuel + 1) locals globals (.list [.atom "setq", .atom name, form]) =
      .ok (value, assignLocal name value after, later) := by
  rw [evalExpr]
  simp [h, bound, bind, Except.bind, pure, Except.pure]

/-- `setq` of any other name writes the global, which later lookups see. -/
theorem evalExpr_setq_global {fuel : Nat} {locals after : Locals} {globals later : Globals} {name : String}
    {form : Sexp} {value : LV} (h : evalExpr fuel locals globals form = .ok (value, after, later))
    (unbound : Assoc.get name after = none) :
    evalExpr (fuel + 1) locals globals (.list [.atom "setq", .atom name, form]) =
      .ok (value, after, Assoc.put name value later) := by
  rw [evalExpr]
  simp [h, unbound, bind, Except.bind, pure, Except.pure]

theorem evalExpr_lambda_captures (fuel : Nat) (locals : Locals) (globals : Globals) (params : List String) (body : Sexp) :
    evalExpr (fuel + 1) locals globals (.list [.atom "lambda", .list (params.map .atom), body]) =
      .ok (.function (.closure params body locals), locals, globals) := by
  rw [evalExpr]
  have key : ∀ f : Sexp → Except String String, (∀ name, f (.atom name) = .ok name) →
      (params.map Sexp.atom).mapM f = .ok params := by
    intro f hf
    induction params with
    | nil => rfl
    | cons p rest ih => simp only [List.map_cons, List.mapM_cons, hf, ih]; rfl
  simp only [bind, Except.bind, pure, Except.pure]
  rw [key _ (fun _ => rfl)]

/-- `progn` over nothing is unit; the environments stay as they were. -/
theorem evalExpr_progn_nil (fuel : Nat) (locals : Locals) (globals : Globals) :
    evalExpr (fuel + 1) locals globals (.list [.atom "progn"]) = .ok (.unit, locals, globals) := by
  rw [evalExpr]
  simp [bind, Except.bind, pure, Except.pure]

private theorem and_short_circuit (fuel : Nat) (forms : List Sexp) (locals : Locals) (globals : Globals) :
    forms.foldlM (m := Except String) (init := ((.bool false : LV), locals, globals)) (fun state form => do
      if !(← expectBool state.1) then
        .ok state
      else
        evalExpr fuel state.2.1 state.2.2 form) = .ok (.bool false, locals, globals) := by
  induction forms with
  | nil => rfl
  | cons head rest ih => simpa [List.foldlM_cons, expectBool, bind, Except.bind, pure, Except.pure] using ih

/-- `and` stops at the first false value: later forms are never evaluated. -/
theorem evalExpr_and_short_circuit {fuel : Nat} {locals after : Locals} {globals later : Globals} {head : Sexp}
    (rest : List Sexp) (h : evalExpr fuel locals globals head = .ok (.bool false, after, later)) :
    evalExpr (fuel + 1) locals globals (.list (.atom "and" :: head :: rest)) = .ok (.bool false, after, later) := by
  rw [evalExpr]
  simp only [List.foldlM_cons, expectBool, bind, Except.bind, pure, Except.pure, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, h]
  exact and_short_circuit fuel rest after later

private theorem or_short_circuit (fuel : Nat) (forms : List Sexp) (locals : Locals) (globals : Globals) :
    forms.foldlM (m := Except String) (init := ((.bool true : LV), locals, globals)) (fun state form => do
      if ← expectBool state.1 then
        .ok state
      else
        evalExpr fuel state.2.1 state.2.2 form) = .ok (.bool true, locals, globals) := by
  induction forms with
  | nil => rfl
  | cons head rest ih => simpa [List.foldlM_cons, expectBool, bind, Except.bind, pure, Except.pure] using ih

/-- `or` stops at the first true value. -/
theorem evalExpr_or_short_circuit {fuel : Nat} {locals after : Locals} {globals later : Globals} {head : Sexp}
    (rest : List Sexp) (h : evalExpr fuel locals globals head = .ok (.bool true, after, later)) :
    evalExpr (fuel + 1) locals globals (.list (.atom "or" :: head :: rest)) = .ok (.bool true, after, later) := by
  rw [evalExpr]
  simp only [List.foldlM_cons, expectBool, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte, h]
  exact or_short_circuit fuel rest after later

/-! Primitive arithmetic agrees with `BitVec`. -/

private theorem any_symbolic_ints (values : List (BitVec 64)) : (values.map Lisp.Value.int).any symbolic = false := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp [symbolic]

private theorem mapM_expectInt (values : List (BitVec 64)) :
    (values.map Lisp.Value.int).mapM expectInt = .ok values := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp [List.mapM_cons, ih, expectInt, bind, Except.bind, pure, Except.pure]

theorem primitive_add (values : List (BitVec 64)) :
    evalPrimitive "+" (values.map .int) = .ok (.int (values.foldl (· + ·) 0)) := by
  simp only [evalPrimitive, any_symbolic_ints, mapM_expectInt, bind, Except.bind, pure, Except.pure]
  rfl

theorem primitive_mul (values : List (BitVec 64)) :
    evalPrimitive "*" (values.map .int) = .ok (.int (values.foldl (· * ·) 1)) := by
  simp only [evalPrimitive, any_symbolic_ints, mapM_expectInt, bind, Except.bind, pure, Except.pure]
  rfl

theorem primitive_sub (first : BitVec 64) (rest : List (BitVec 64)) (h : rest ≠ []) :
    evalPrimitive "-" (.int first :: rest.map .int) = .ok (.int (rest.foldl (· - ·) first)) := by
  have hm := mapM_expectInt (first :: rest)
  have hs := any_symbolic_ints (first :: rest)
  simp only [List.map_cons] at hm hs
  cases rest with
  | nil => exact absurd rfl h
  | cons a b =>
    simp only [evalPrimitive, hs, hm, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]

theorem primitive_neg (value : BitVec 64) : evalPrimitive "-" [.int value] = .ok (.int (-value)) := by
  rfl

theorem primitive_udiv (first : BitVec 64) (rest : List (BitVec 64)) :
    evalPrimitive "/" (.int first :: rest.map .int) = .ok (.int (rest.foldl Word.udiv first)) := by
  have := mapM_expectInt (first :: rest)
  have hs := any_symbolic_ints (first :: rest)
  simp only [List.map_cons] at this hs
  simp only [evalPrimitive, hs, this, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]

/-- Division by zero follows the machine convention: all ones. -/
theorem primitive_div_zero (value : BitVec 64) :
    evalPrimitive "/" [.int value, .int 0] = .ok (.int (BitVec.allOnes 64)) := by
  have := primitive_udiv value [0]
  simpa [Word.udiv, Word.ones] using this

theorem primitive_compare (left right : BitVec 64) :
    evalPrimitive "=" [.int left, .int right] = .ok (.bool (decide (left = right))) ∧
      evalPrimitive "<" [.int left, .int right] = .ok (.bool (decide (left < right))) ∧
      evalPrimitive "<=" [.int left, .int right] = .ok (.bool (decide (left ≤ right))) ∧
      evalPrimitive ">" [.int left, .int right] = .ok (.bool (decide (left > right))) ∧
      evalPrimitive ">=" [.int left, .int right] = .ok (.bool (decide (left ≥ right))) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem primitive_not (value : Bool) : evalPrimitive "not" [.bool value] = .ok (.bool !value) := by
  rfl

theorem primitive_bit_operations (values : List (BitVec 64)) :
    evalPrimitive "bitand" (values.map .int) = .ok (.int (values.foldl (· &&& ·) 0xffffffffffffffff)) ∧
      evalPrimitive "bitor" (values.map .int) = .ok (.int (values.foldl (· ||| ·) 0)) ∧
      evalPrimitive "bitxor" (values.map .int) = .ok (.int (values.foldl (· ^^^ ·) 0)) := by
  simp only [evalPrimitive, bitOperation, any_symbolic_ints, mapM_expectInt, bind, Except.bind, pure, Except.pure]
  exact ⟨rfl, rfl, rfl⟩

/-- Pair algebra of the list primitives. -/
theorem primitive_car_cons (head : LV) (tail : List LV) :
    (do evalPrimitive "car" [← evalPrimitive "cons" [head, .list tail]]) = .ok head := by
  rfl

theorem primitive_cdr_cons (head : LV) (tail : List LV) :
    (do evalPrimitive "cdr" [← evalPrimitive "cons" [head, .list tail]]) = .ok (.list tail) := by
  rfl

theorem primitive_length (items : List LV) :
    evalPrimitive "length" [.list items] = .ok (.int (BitVec.ofNat 64 items.length)) := by
  rfl

theorem primitive_null (items : List LV) :
    evalPrimitive "null?" [.list items] = .ok (.bool items.isEmpty) := by
  rfl

theorem primitive_list_identity (items : List LV) : evalPrimitive "list" items = .ok (.list items) := by
  rfl

private theorem bind_mono {α β ε : Type} {a a' : Except ε α} {b b' : α → Except ε β} {r : β}
    (ha : ∀ v, a = .ok v → a' = .ok v) (hb : ∀ v r, b v = .ok r → b' v = .ok r)
    (h : (a >>= b) = .ok r) : (a' >>= b') = .ok r := by
  cases ha' : a with
  | error e => simp [ha', bind, Except.bind] at h
  | ok v =>
    simp only [ha', bind, Except.bind] at h
    simp only [ha _ ha', bind, Except.bind]
    exact hb _ _ h

private theorem foldlM_mono {α β ε : Type} {step step' : α → β → Except ε α}
    (hs : ∀ state item r, step state item = .ok r → step' state item = .ok r)
    (items : List β) (init : α) {r : α}
    (h : items.foldlM step init = .ok r) : items.foldlM step' init = .ok r := by
  induction items generalizing init r with
  | nil => simpa using h
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h ⊢
    exact bind_mono (fun v hv => hs _ _ _ hv) (fun v r hr => ih v hr) h

/-- Fuel monotonicity of the evaluator: a successful run is unchanged by more fuel. -/
theorem evalExpr_fuel_succ {fuel : Nat} {locals : Locals} {globals : Globals} {form : Sexp}
    {result : LV × Locals × Globals} (h : evalExpr fuel locals globals form = .ok result) :
    evalExpr (fuel + 1) locals globals form = .ok result := by
  induction fuel generalizing locals globals form result with
  | zero => rw [evalExpr] at h; simp at h
  | succ fuel ih =>
    rw [evalExpr.eq_def] at h
    rw [evalExpr.eq_def]
    simp only at h ⊢
    have list_mono : ∀ (forms : List Sexp) (init : List LV × Locals × Globals) {r : List LV × Locals × Globals},
        forms.foldlM (m := Except String) (fun state form => do
          let __x ← evalExpr fuel state.2.1 state.2.2 form
          .ok (state.1 ++ [__x.1], __x.2.1, __x.2.2)) init = .ok r →
        forms.foldlM (m := Except String) (fun state form => do
          let __x ← evalExpr (fuel + 1) state.2.1 state.2.2 form
          .ok (state.1 ++ [__x.1], __x.2.1, __x.2.2)) init = .ok r := by
      intro forms init r hr
      exact foldlM_mono (fun _ _ _ hv => bind_mono (fun _ hw => ih hw) (fun _ _ hu => hu) hv) forms init hr
    split at h
    all_goals try simp only at ⊢
    · exact h
    · exact h
    · exact h
    · split at h
      · refine bind_mono (fun _ hv => ih hv) (fun _ _ hb => bind_mono (fun _ hw => hw) (fun _ _ hc => ?_) hb) h
        split at hc
        · rw [ite_eq_left (by assumption)]; exact ih hc
        · rw [ite_eq_right (by assumption)]; exact ih hc
      · exact h
    · exact h
    · exact h
    · exact bind_mono (fun _ hv => ih hv) (fun _ _ hb => hb) h
    · refine bind_mono (fun _ hv => ?_) (fun _ _ hb => ?_) h
      · refine foldlM_mono (fun _ item _ hs => ?_) _ _ hv
        split at hs
        · exact bind_mono (fun _ hw => ih hw) (fun _ _ hu => hu) hs
        · exact hs
      · exact bind_mono (fun _ hw => list_mono _ _ hw) (fun _ _ hu => hu) hb
    · exact bind_mono (fun _ hw => list_mono _ _ hw) (fun _ _ hu => hu) h
    · refine foldlM_mono (fun _ _ _ hv => bind_mono (fun _ hw => hw) (fun _ _ hc => ?_) hv) _ _ h
      split at hc
      · rw [ite_eq_left (by assumption)]; exact hc
      · rw [ite_eq_right (by assumption)]; exact ih hc
    · refine foldlM_mono (fun _ _ _ hv => bind_mono (fun _ hw => hw) (fun _ _ hc => ?_) hv) _ _ h
      split at hc
      · rw [ite_eq_left (by assumption)]; exact hc
      · rw [ite_eq_right (by assumption)]; exact ih hc
    · refine bind_mono (fun _ hv => ih hv) (fun _ _ hb =>
        bind_mono (fun _ hw => list_mono _ _ hw) (fun _ _ hc => ?_) hb) h
      split at hc
      · exact hc
      · split at hc
        · rw [ite_eq_left (by assumption)]; exact hc
        · rw [ite_eq_right (by assumption)]
          exact bind_mono (fun _ hw => ih hw) (fun _ _ hu => hu) hc
      · exact hc

theorem evalExpr_fuel_mono {fuel extra : Nat} {locals : Locals} {globals : Globals} {form : Sexp}
    {result : LV × Locals × Globals} (h : evalExpr fuel locals globals form = .ok result) :
    evalExpr (fuel + extra) locals globals form = .ok result := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact evalExpr_fuel_succ ih

private theorem bind_ok_inv {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ v, x = .ok v ∧ f v = .ok r := by
  cases hx : x with
  | error e => simp [hx, bind, Except.bind] at h
  | ok v =>
    simp only [hx, bind, Except.bind] at h
    exact ⟨v, rfl, h⟩

private theorem foldlM_inv {α β ε : Type} (P : α → Prop) {step : α → β → Except ε α}
    (hs : ∀ state item r, P state → step state item = .ok r → P r)
    (items : List β) (init : α) {r : α} (hi : P init) (h : items.foldlM step init = .ok r) : P r := by
  induction items generalizing init r with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hi
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨v, hv, hr⟩ := bind_ok_inv h
    exact ih v (hs _ _ _ hi hv) hr

/-- Stack discipline: evaluation never changes how many local bindings are in scope. It can update
their values, but each `let` removes exactly the frames it pushed. -/
theorem evalExpr_locals_length {fuel : Nat} {locals after : Locals} {globals later : Globals} {form : Sexp}
    {value : LV} (h : evalExpr fuel locals globals form = .ok (value, after, later)) :
    after.length = locals.length := by
  induction fuel generalizing locals after globals later form value with
  | zero => rw [evalExpr] at h; simp at h
  | succ fuel ih =>
    rw [evalExpr.eq_def] at h
    simp only at h
    have list_inv : ∀ (forms : List Sexp) (init : List LV × Locals × Globals) {r : List LV × Locals × Globals},
        forms.foldlM (m := Except String) (fun state form => do
          let __x ← evalExpr fuel state.2.1 state.2.2 form
          .ok (state.1 ++ [__x.1], __x.2.1, __x.2.2)) init = .ok r → r.2.1.length = init.2.1.length := by
      intro forms init r hr
      refine foldlM_inv (fun state : List LV × Locals × Globals => state.2.1.length = init.2.1.length)
        (fun state item r hp hstep => ?_) forms init rfl hr
      obtain ⟨⟨_, _, _⟩, hv, hk⟩ := bind_ok_inv hstep
      simp only [Except.ok.injEq] at hk
      subst hk
      exact (ih hv).trans hp
    split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2.1 ▸ rfl
      · obtain ⟨_, _, hk⟩ := bind_ok_inv h
        simp only [Except.ok.injEq, Prod.mk.injEq] at hk
        exact hk.2.1 ▸ rfl
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.1 ▸ rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2.1 ▸ rfl
      · simp at h
    · split at h
      · obtain ⟨⟨_, _, _⟩, hc, hk⟩ := bind_ok_inv h
        obtain ⟨_, _, hk'⟩ := bind_ok_inv hk
        have h1 := ih hc
        split at hk'
        · exact (ih hk').trans h1
        · exact (ih hk').trans h1
      · simp at h
    · obtain ⟨_, _, hk⟩ := bind_ok_inv h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hk
      exact hk.2.1 ▸ rfl
    · obtain ⟨_, _, hk⟩ := bind_ok_inv h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hk
      exact hk.2.1 ▸ rfl
    · obtain ⟨⟨_, _, _⟩, hv, hk⟩ := bind_ok_inv h
      have h1 := ih hv
      split at hk
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hk
        rw [← hk.2.1, assignLocal_length]
        exact h1
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hk
        rw [← hk.2.1]
        exact h1
    · rename_i bindings body
      obtain ⟨⟨bound, _⟩, hb, hk⟩ := bind_ok_inv h
      obtain ⟨⟨_, final, _⟩, hl, hk'⟩ := bind_ok_inv hk
      simp only [Except.ok.injEq, Prod.mk.injEq] at hk'
      have hbody := list_inv _ _ hl
      simp only at hbody
      have hbound : bound.length = locals.length + bindings.length := by
        have key : ∀ (items : List Sexp) (init : Locals × Globals) {r : Locals × Globals},
            items.foldlM (m := Except String) (fun state binding =>
              match binding with
              | .list [.atom name, value] => do
                let __x ← evalExpr fuel state.1 state.2 value
                .ok ((name, __x.1) :: __x.2.1, __x.2.2)
              | _ => .error "invalid let binding") init = .ok r →
            r.1.length = init.1.length + items.length := by
          intro items
          induction items with
          | nil =>
            intro init r hr
            simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hr
            simp [hr]
          | cons item rest iih =>
            intro init r hr
            simp only [List.foldlM_cons] at hr
            obtain ⟨v, hv, hr'⟩ := bind_ok_inv hr
            have := iih v hr'
            split at hv
            · obtain ⟨⟨_, _, _⟩, he, hkk⟩ := bind_ok_inv hv
              simp only [Except.ok.injEq] at hkk
              subst hkk
              have hlen := ih he
              simp only [List.length_cons] at this ⊢
              omega
            · simp at hv
        exact key _ _ hb
      rw [← hk'.2.1, List.length_drop, hbody]
      omega
    · obtain ⟨⟨_, _, _⟩, hl, hk⟩ := bind_ok_inv h
      simp only [Except.ok.injEq, Prod.mk.injEq] at hk
      rw [← hk.2.1]
      exact list_inv _ _ hl
    · refine foldlM_inv (fun state : LV × Locals × Globals => state.2.1.length = locals.length)
        (fun state item r hp hstep => ?_) _ _ rfl h
      obtain ⟨_, _, hk⟩ := bind_ok_inv hstep
      split at hk
      · simp only [Except.ok.injEq] at hk
        subst hk
        exact hp
      · obtain ⟨a, b, c⟩ := r
        exact (ih hk).trans hp
    · refine foldlM_inv (fun state : LV × Locals × Globals => state.2.1.length = locals.length)
        (fun state item r hp hstep => ?_) _ _ rfl h
      obtain ⟨_, _, hk⟩ := bind_ok_inv hstep
      split at hk
      · simp only [Except.ok.injEq] at hk
        subst hk
        exact hp
      · obtain ⟨a, b, c⟩ := r
        exact (ih hk).trans hp
    · obtain ⟨⟨_, _, _⟩, hc, hk⟩ := bind_ok_inv h
      obtain ⟨⟨_, _, _⟩, hl, hk'⟩ := bind_ok_inv hk
      have h1 := ih hc
      have h2 := list_inv _ _ hl
      simp only at h2
      split at hk'
      · obtain ⟨_, _, hk''⟩ := bind_ok_inv hk'
        simp only [Except.ok.injEq, Prod.mk.injEq] at hk''
        rw [← hk''.2.1, h2]
        exact h1
      · split at hk'
        · simp at hk'
        · obtain ⟨_, _, hk''⟩ := bind_ok_inv hk'
          simp only [Except.ok.injEq, Prod.mk.injEq] at hk''
          rw [← hk''.2.1, h2]
          exact h1
      · simp at hk'

/-- `let` threads both environments through its bindings in order, and pops what it pushed. -/
theorem evalExpr_let_two {fuel : Nat} {l0 l1 l2 l3 : Locals} {g0 g1 g2 g3 : Globals} {first second : String}
    {e1 e2 body : Sexp} {v1 v2 result : LV}
    (h1 : evalExpr fuel l0 g0 e1 = .ok (v1, l1, g1))
    (h2 : evalExpr fuel ((first, v1) :: l1) g1 e2 = .ok (v2, l2, g2))
    (h3 : evalExpr fuel ((second, v2) :: l2) g2 body = .ok (result, l3, g3)) :
    evalExpr (fuel + 1) l0 g0 (.list [.atom "let", .list [.list [.atom first, e1], .list [.atom second, e2]], body]) =
      .ok (result, l3.drop 2, g3) := by
  rw [evalExpr]
  simp [List.foldlM_cons, bind, Except.bind, pure, Except.pure, h1, h2, h3]

theorem evalExpr_let_one {fuel : Nat} {l0 l1 l2 : Locals} {g0 g1 g2 : Globals} {name : String}
    {e body : Sexp} {v result : LV}
    (h1 : evalExpr fuel l0 g0 e = .ok (v, l1, g1))
    (h2 : evalExpr fuel ((name, v) :: l1) g1 body = .ok (result, l2, g2)) :
    evalExpr (fuel + 1) l0 g0 (.list [.atom "let", .list [.list [.atom name, e]], body]) =
      .ok (result, l2.drop 1, g2) := by
  rw [evalExpr]
  simp [List.foldlM_cons, bind, Except.bind, pure, Except.pure, h1, h2]

private theorem get_put_same (name : String) (value : LV) (globals : Globals) :
    Assoc.get name (Assoc.put name value globals) = some value := Assoc.get_put_same _ _ _

/-- A `setq` in an earlier `let` binding is visible to later bindings and survives the `let`. -/
theorem let_binding_sees_global_update (fuel : Nat) (first second name : String) (ht : name ≠ "true")
    (hf : name ≠ "false") (hi : name.toInt? = none) (hn : first ≠ name)
    (st : second ≠ "true") (sf : second ≠ "false") (si : second.toInt? = none) :
    evalExpr (fuel + 3) [] [] (.list [.atom "let",
      .list [.list [.atom first, .list [.atom "setq", .atom name, .list [.atom "quote", .list []]]],
        .list [.atom second, .atom name]],
      .atom second]) = .ok (.list [], [], Assoc.put name (.list []) []) := by
  have hq : evalExpr (fuel + 1) [] [] (.list [.atom "quote", .list []]) = .ok (.list [], [], []) :=
    (evalExpr_quote fuel [] [] (.list [])).trans (by simp [quotedValue])
  have h1 : evalExpr (fuel + 2) [] [] (.list [.atom "setq", .atom name, .list [.atom "quote", .list []]]) =
      .ok (.list [], [], Assoc.put name (.list []) []) := evalExpr_setq_global (name := name) hq rfl
  have hget : Assoc.get name [(first, (.list [] : LV))] = none := by
    simp [Assoc.get, List.lookup_cons, show (name == first) = false by simpa using Ne.symm hn]
  have h2 : evalExpr (fuel + 2) [(first, .list [])] (Assoc.put name (.list []) []) (.atom name) =
      .ok (.list [], [(first, .list [])], Assoc.put name (.list []) []) :=
    evalExpr_symbol _ _ _ _ _ ht hf hi (lookup_global _ _ _ _ hget (get_put_same _ _ _))
  have h3 : evalExpr (fuel + 2) [(second, .list []), (first, .list [])] (Assoc.put name (.list []) []) (.atom second) =
      .ok (.list [], [(second, .list []), (first, .list [])], Assoc.put name (.list []) []) :=
    evalExpr_symbol _ _ _ _ _ st sf si (lookup_local _ _ _ _ (by simp [Assoc.get]))
  exact (evalExpr_let_two h1 h2 h3).trans (by simp)

/-- `(let ((x 'a)) (progn (setq x 'b) x))` returns `b`: assignment reaches the binding, the binding
is gone afterwards, and neither outer locals nor globals change. -/
theorem let_setq_updates_binding (fuel : Nat) (name : String) (a b : Sexp) (locals : Locals) (globals : Globals)
    (ht : name ≠ "true") (hf : name ≠ "false") (hi : name.toInt? = none) :
    evalExpr (fuel + 4) locals globals (.list [.atom "let", .list [.list [.atom name, .list [.atom "quote", a]]],
      .list [.atom "progn", .list [.atom "setq", .atom name, .list [.atom "quote", b]], .atom name]]) =
      .ok (quotedValue b, locals, globals) := by
  have hbound : (Assoc.get name ((name, quotedValue a) :: locals)).isSome = true := by simp [Assoc.get]
  have hset : evalExpr (fuel + 2) ((name, quotedValue a) :: locals) globals
      (.list [.atom "setq", .atom name, .list [.atom "quote", b]]) =
      .ok (quotedValue b, assignLocal name (quotedValue b) ((name, quotedValue a) :: locals), globals) :=
    evalExpr_setq_local (name := name) (evalExpr_quote fuel ((name, quotedValue a) :: locals) globals b) hbound
  have hassign : assignLocal name (quotedValue b) ((name, quotedValue a) :: locals) = (name, quotedValue b) :: locals := by
    simp [assignLocal]
  rw [hassign] at hset
  have hvar : evalExpr (fuel + 2) ((name, quotedValue b) :: locals) globals (.atom name) =
      .ok (quotedValue b, (name, quotedValue b) :: locals, globals) :=
    evalExpr_symbol _ _ _ _ _ ht hf hi (lookup_local _ _ _ _ (by simp [Assoc.get]))
  have hprogn : evalExpr (fuel + 3) ((name, quotedValue a) :: locals) globals
      (.list [.atom "progn", .list [.atom "setq", .atom name, .list [.atom "quote", b]], .atom name]) =
      .ok (quotedValue b, (name, quotedValue b) :: locals, globals) := by
    rw [evalExpr]
    simp [List.foldlM_cons, bind, Except.bind, pure, Except.pure, hset, hvar]
  exact (evalExpr_let_one (evalExpr_quote (fuel + 2) locals globals a) hprogn).trans (by simp)

end Lisp
/-! ### Primus Lisp semantics helpers -/

section Semantics

open Bap.Primus.Semantics
open_private Bap.Primus.Semantics Bap.Primus.Semantics lookup lookupState primitiveNames primitiveIndex parseBasedNat
  parseInteger atomValue expectBil expectNat truth condition extend binary widthOf assignRegister assign emit
  substitute contextMatches definitionBody compilablePrimitive applyPrimitive applyPrimitiveIndex valueOnly unaryNot
  shift cast loadMemory storeMemory leadingZeros parseZ startsNumeric readLiteral checkLiterals checkForms checkBody
  wordWidth bindAssignable assignsLocal eval evalList evalSequence apply

open_private_as Bap.Primus.Semantics Bap.Primus.Semantics.compare primCompare

local notation "SV" => Bap.Primus.Semantics.Value

/-- `replicate` is an ordinary name for variable lookup: a local binding shadows it. Unbound, it
resolves to the built-in, ahead of the Lisp definition in `bits.lisp`. -/
theorem lookup_local_shadows_replicate (value : SV) (globals : Globals) :
    lookup "replicate" [("replicate", value)] globals = .ok value := by
  simp [lookup, Assoc.get]

theorem lookup_replicate_builtin (locals : Locals) (globals : Globals) (hl : Assoc.get "replicate" locals = none) :
    lookup "replicate" locals globals = .ok (.callable (.primitive "replicate")) := by
  have : "replicate".startsWith "core:" = false := by decide +kernel
  simp [lookup, this, hl]

theorem semantics_lookup_local (name : String) (locals : Locals) (globals : Globals) (value : SV)
    (h : Assoc.get name locals = some value) : lookup name locals globals = .ok value := by
  simp [lookup, h]

theorem semantics_lookup_global (name : String) (locals : Locals) (globals : Globals) (value : SV)
    (hname : (if name.startsWith "core:" then (name.drop 5).toString else name) ≠ "replicate")
    (hl : Assoc.get name locals = none) (h : Assoc.get name globals = some value) :
    lookup name locals globals = .ok value := by
  simp only [lookup, hl]
  rw [ite_eq_right hname, h]

/-- Registered operations take precedence over plain globals in stateful lookups. -/
theorem lookupState_operation (name : String) (locals : Locals) (state : State) (callable : Callable)
    (hname : (if name.startsWith "core:" then (name.drop 5).toString else name) ≠ "replicate")
    (hl : Assoc.get name locals = none) (h : state.operations.get? name = some callable) :
    lookupState name locals state = .ok (.callable callable) := by
  simp only [lookupState, hl]
  rw [ite_eq_right hname, h]

/-! Numeric literals. -/

private def digitValue (base : Nat) (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if c.toLower ≥ 'a' && c.toLower ≤ 'f' then c.toLower.toNat - 'a'.toNat + 10
  else base

private def digitStep (base value : Nat) (c : Char) : Option Nat :=
  if digitValue base c < base then some (value * base + digitValue base c) else none

private theorem parseBasedNat_eq (digits : String) (base : Nat) :
    parseBasedNat digits base = digits.toList.foldlM (digitStep base) 0 := rfl

private theorem digitValue_digitChar_aux : ∀ d : Fin 16,
    ((Nat.digitChar d).isDigit = true ∧ (Nat.digitChar d).toNat - '0'.toNat = d) ∨
      ((Nat.digitChar d).isDigit = false ∧
        (decide ((Nat.digitChar d).toLower ≥ 'a') && decide ((Nat.digitChar d).toLower ≤ 'f')) = true ∧
        (Nat.digitChar d).toLower.toNat - 'a'.toNat + 10 = d) := by
  decide

private theorem digitValue_digitChar (base d : Nat) (hd : d < 16) : digitValue base (Nat.digitChar d) = d := by
  rcases digitValue_digitChar_aux ⟨d, hd⟩ with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · simp only [digitValue]
    simp only at h1 h2
    simp only [h1, ↓reduceIte]
    exact h2
  · simp only [digitValue]
    simp only at h1 h2 h3
    simp only [h1, Bool.false_eq_true, ↓reduceIte, h2]
    exact h3

private theorem foldlM_toDigits (base : Nat) (h2 : 1 < base) (h16 : base ≤ 16) (n : Nat) :
    (Nat.toDigits base n).foldlM (digitStep base) 0 = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite h2]
    split
    · rename_i hlt
      simp [digitStep, digitValue_digitChar base n (by omega), hlt]
    · rename_i hge
      have hdiv : n / base < n := Nat.div_lt_self (by omega) h2
      have hmod : n % base < base := Nat.mod_lt _ (by omega)
      rw [List.foldlM_append, ih _ hdiv]
      have := Nat.div_add_mod n base
      rw [Nat.mul_comm] at this
      simp [digitStep, digitValue_digitChar base (n % base) (by omega), hmod, this]

/-- Round-trip for based literals: printing then parsing returns the number, for all bases up to 16. -/
theorem parseBasedNat_toDigits (base n : Nat) (h2 : 1 < base) (h16 : base ≤ 16) :
    parseBasedNat (String.ofList (Nat.toDigits base n)) base = some n := by
  rw [parseBasedNat_eq, String.toList_ofList]
  exact foldlM_toDigits base h2 h16 n

/-- A successful parse only saw in-range digits, and an out-of-range digit always rejects the literal. -/
theorem parseBasedNat_some_iff (digits : String) (base : Nat) :
    (parseBasedNat digits base).isSome = true ↔ ∀ c ∈ digits.toList, digitValue base c < base := by
  rw [parseBasedNat_eq]
  generalize digits.toList = chars
  suffices h : ∀ init, (chars.foldlM (digitStep base) init).isSome = true ↔ ∀ c ∈ chars, digitValue base c < base from h 0
  induction chars with
  | nil => simp
  | cons head rest ih =>
    intro init
    simp only [List.foldlM_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hd : digitValue base head < base
    · simp [digitStep, hd, ih]
    · simp [digitStep, hd]

theorem parseBasedNat_empty (base : Nat) : parseBasedNat "" base = some 0 := by
  rfl

/-- Intended: a bare `0x` is the integer zero. Upstream literals go through `Z.of_string`
(`bap_primus_lisp_word.ml`), and Zarith parses `"0x"` as 0 (`caml_z.c`, `ml_z_of_substring_base`). -/
theorem atomValue_bare_hex_prefix : atomValue "0x" = .int 0 := by
  have h3 : parseInteger "0x" = some (0, none) := by decide +kernel
  have h4 : ("0x" = "true") = False := by simp
  have h5 : ("0x" = "false") = False := by simp
  simp only [atomValue, h4, h5, ↓reduceIte, h3]
  rfl

/-! Value coercions. -/

theorem expectBil_int (context : Context) (value : BitVec 64) :
    expectBil context (.int value) = .ok (context.bits, .int (BitVec.ofNat context.bits value.toNat)) := rfl

/-- Reads of the zero register are the constant zero at the requested width. -/
theorem expectBil_zero_register (context : Context) (width base : Nat) :
    expectBil context (.register "XZR" width base) = .ok (width, .int (BitVec.ofNat width 0)) := rfl

/-- Reads of a sub-register truncate the base register; full-width reads are the variable itself. -/
theorem expectBil_register (context : Context) (name : String) (width base : Nat) (hn : name ≠ "XZR") :
    expectBil context (.register name width base) =
      .ok (width, if width = base then .var ⟨name, .imm base, 0, false⟩
        else .cast .low width (.var ⟨name, .imm base, 0, false⟩)) := by
  simp [expectBil, hn]

/-- `word-width` reports the width that arithmetic uses, for every bitvector value. An integer literal
has the machine word width, as in `bap_primus_lisp_semantics.ml` (`bigint x word`). -/
theorem widthOf_agrees_with_expectBil {context : Context} {value : SV} {width : Nat} {exp : Bil.Exp}
    (h : expectBil context value = .ok (width, exp)) : widthOf context value = .ok width := by
  cases value with
  | int v =>
    simp only [expectBil, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | bil w e =>
    simp only [expectBil, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | bool v =>
    simp only [expectBil, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | register name w b =>
    simp only [expectBil] at h
    split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;> rw [← h.1] <;> rfl
  | _ => simp [expectBil] at h

theorem truth_int (value : BitVec 64) : truth (.int value) = .ok (some (value != 0)) := rfl

theorem truth_bool (value : Bool) : truth (.bool value) = .ok (some value) := rfl

theorem truth_register (name : String) (width base : Nat) : truth (.register name width base) = .ok none := rfl

/-- Branch conditions are exactly the one-bit expressions. -/
theorem condition_ok_iff (context : Context) (value : SV) (exp : Bil.Exp) :
    condition context value = .ok exp ↔ expectBil context value = .ok (1, exp) := by
  simp only [condition, bind, Except.bind]
  cases h : expectBil context value with
  | error e => simp
  | ok pair =>
    obtain ⟨w, e⟩ := pair
    by_cases hw : w = 1
    · subst hw
      simp [pure, Except.pure]
    · simp [hw, Except.ok.injEq]

/-! Arithmetic widening. -/

private theorem foldl_max_ge (values : List (Nat × Bil.Exp)) (start : Nat) :
    start ≤ values.foldl (fun width value => max width value.1) start ∧
      ∀ v ∈ values, v.1 ≤ values.foldl (fun width value => max width value.1) start := by
  induction values generalizing start with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := ih (max start head.1)
    exact ⟨by omega, by omega, h2⟩

/-- Binary arithmetic rejects empty argument lists. -/
theorem binary_nil (context : Context) (op : Bil.BinOp) : binary context op [] = .error "Primus arithmetic expects an argument" :=
  rfl

private theorem binary_fold {op : Bil.BinOp} {width : Nat} (rest : List (Nat × Bil.Exp)) (init : Bil.Exp) :
    rest.foldlM (m := Except String) (init := init) (fun left (right : Nat × Bil.Exp) =>
      .ok (Bil.Exp.bin op left (extend width right.2))) =
      .ok (rest.foldl (fun left right => Bil.Exp.bin op left (extend width right.2)) init) := by
  induction rest generalizing init with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.foldlM_cons, List.foldl_cons]
    exact ih _

/-- The result of n-ary arithmetic is as wide as its widest operand: narrow operands are widened, never
truncated. -/
theorem binary_width {context : Context} {op : Bil.BinOp} {args : List SV} {first : Nat × Bil.Exp}
    {rest : List (Nat × Bil.Exp)} (h : args.mapM (expectBil context) = .ok (first :: rest)) :
    ∃ exp, binary context op args = .ok (.bil ((first :: rest).foldl (fun width value => max width value.1) first.1) exp) ∧
      ∀ v ∈ first :: rest, v.1 ≤ (first :: rest).foldl (fun width value => max width value.1) first.1 := by
  refine ⟨rest.foldl (fun left right => Bil.Exp.bin op left
    (extend ((first :: rest).foldl (fun width value => max width value.1) first.1) right.2))
    (extend ((first :: rest).foldl (fun width value => max width value.1) first.1) first.2), ?_, (foldl_max_ge _ _).2⟩
  simp only [binary, bind, Except.bind, h]
  rw [binary_fold]

theorem compare_symbols_eq (context : Context) (left right : String) :
    primCompare context .eq [.symbol left, .symbol right] = .ok (.bool (decide (left = right))) := by
  simp [primCompare, pure, Except.pure]

theorem compare_symbols_neq (context : Context) (left right : String) :
    primCompare context .neq [.symbol left, .symbol right] = .ok (.bool (decide (left ≠ right))) := by
  simp [primCompare, pure, Except.pure]

/-- Only equality tests are defined on symbols. -/
theorem compare_symbols_ordered (context : Context) (op : Bil.BinOp) (left right : String)
    (he : op ≠ .eq) (hn : op ≠ .neq) : primCompare context op [.symbol left, .symbol right] =
      .error "symbol comparison only supports equality" := by
  simp [primCompare, he, hn]

/-! Register writes. -/

/-- Writes to the zero register are dropped. -/
theorem assignRegister_zero (context : Context) (width base : Nat) (value : SV) :
    assignRegister context "XZR" width base value = .ok [] := rfl

/-- A successful register write is a single move at the register's own width. -/
theorem assignRegister_ok {context : Context} {name : String} {width : Nat} {value : SV}
    {program : Bil.Program} (hn : name ≠ "XZR") (h : assignRegister context name width width value = .ok program) :
    ∃ exp, expectBil context value = .ok (width, exp) ∧
      program = [.move ⟨name, .imm width, 0, false⟩ exp] := by
  simp only [assignRegister, hn, ↓reduceIte, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hv : expectBil context value with
  | error e => simp [hv] at h
  | ok pair =>
    obtain ⟨w, e⟩ := pair
    simp only [hv] at h
    by_cases hww : w = width
    · subst hww
      simp at h
      exact ⟨e, rfl, h.symm⟩
    · simp [hww] at h

/-- Assignment only targets registers. -/
theorem assign_non_register (context : Context) (name : String) (value : SV) :
    ∃ e, assign context (.symbol name) value = .error e := ⟨_, rfl⟩

theorem emit_assoc (state : State) (first second : Bil.Program) :
    emit (emit state first) second = emit state (first ++ second) := by
  simp [emit, List.append_assoc]

/-! Macro substitution and definition bodies. -/

private theorem substitute_nil_aux : (form : Sexp) → substitute [] form = form
  | .atom _ => by simp [substitute, Assoc.get]
  | .list items => by
    have : ∀ items : List Sexp, (∀ x ∈ items, substitute [] x = x) → items.map (substitute []) = items := by
      intro items h
      induction items with
      | nil => rfl
      | cons a b ih =>
        simp only [List.map_cons, h a (by simp), List.cons.injEq, true_and]
        exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [substitute, this items fun x _ => substitute_nil_aux x]

/-- Substituting nothing is the identity. -/
theorem substitute_nil (form : Sexp) : substitute [] form = form := substitute_nil_aux form

theorem substitute_atom (bindings : List (String × Sexp)) (atom : String) (value : Sexp)
    (h : Assoc.get atom bindings = some value) : substitute bindings (.atom atom) = value := by
  simp [substitute, h]

theorem substitute_list (bindings : List (String × Sexp)) (items : List Sexp) :
    substitute bindings (.list items) = .list (items.map (substitute bindings)) := by
  rw [substitute]

/-- Definition bodies never retain `declare` forms. -/
theorem definitionBody_no_declare (body : List Sexp) (rest : List Sexp) :
    .list (.atom "declare" :: rest) ∉ definitionBody body := by
  simp only [definitionBody]
  intro h
  split at h
  · rename_i value _ _ heq
    have hx := List.mem_cons_of_mem (Sexp.atom value) h
    rw [← heq] at hx
    simpa using (List.mem_filter.1 hx).2
  · simpa using (List.mem_filter.1 h).2

/-- A definition with no `declare` forms matches every context. -/
theorem contextMatches_no_declare (bits : Nat) (body : List Sexp)
    (h : ∀ form ∈ body, ∀ rest, form ≠ .list (.atom "declare" :: rest)) : contextMatches bits body = true := by
  simp only [contextMatches, List.all_eq_true]
  intro form hf
  split <;> first | rfl | exact absurd rfl (h _ hf _)

/-! Primitive tables: the name-indexed and compiled-index dispatchers agree. -/

theorem primitiveNames_nodup : primitiveNames.Nodup := by decide

theorem primitiveIndex_sound {name : String} {index : Nat} (h : primitiveIndex name = some index) :
    primitiveNames[index]? = some name := by
  obtain ⟨hlt, heq, _⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  rw [List.getElem?_eq_getElem hlt]
  simpa using heq

theorem primitiveIndex_complete (index : Nat) (h : index < primitiveNames.length) :
    primitiveIndex (primitiveNames[index]'h) = some index := by
  revert index
  decide

/-- The compiled evaluator's numeric dispatch implements the same primitive as the interpreter's
name dispatch, for every compilable operation and all arguments. -/
theorem primitive_tables_agree (context : Context) (index : Nat) (args : List SV)
    (hi : index < 64) (hc : compilablePrimitive index = true) :
    applyPrimitive context (primitiveNames[index]'(Nat.lt_of_lt_of_le hi (by decide))) args = applyPrimitiveIndex context index args := by
  match index, hi, hc with
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl
  | 12, _, _ => rfl
  | 20, _, _ => rfl
  | 21, _, _ => rfl
  | 22, _, _ => rfl
  | 23, _, _ => rfl
  | 24, _, _ => rfl
  | 25, _, _ => rfl
  | 26, _, _ => rfl
  | 27, _, _ => rfl
  | 28, _, _ => rfl
  | 29, _, _ => rfl
  | 30, _, _ => rfl
  | 31, _, _ => rfl
  | 32, _, _ => rfl
  | 33, _, _ => rfl
  | 34, _, _ => rfl
  | 35, _, _ => rfl
  | 36, _, _ => rfl
  | 37, _, _ => rfl
  | 38, _, _ => rfl
  | 39, _, _ => rfl
  | 40, _, _ => rfl
  | 41, _, _ => rfl
  | 42, _, _ => rcases args with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _, _ | _⟩ <;> rfl
  | 43, _, _ => rfl
  | 44, _, _ => rfl
  | 45, _, _ => rfl
  | 46, _, _ => rfl
  | 47, _, _ => rfl
  | 48, _, _ => rfl
  | 49, _, _ => rfl
  | 50, _, _ => rfl
  | 51, _, _ => rfl
  | 52, _, _ => rfl
  | 53, _, _ => rfl
  | 54, _, _ => rfl
  | 55, _, _ => rfl
  | 56, _, _ => rfl
  | 57, _, _ => rfl
  | 58, _, _ => rfl
  | 59, _, _ => rfl
  | 60, _, _ => rfl
  | 61, _, _ => rfl
  | 63, _, _ => rfl
  | 13, _, hc | 14, _, hc | 15, _, hc | 16, _, hc | 17, _, hc | 18, _, hc | 19, _, hc | 62, _, hc => exact absurd hc (by decide)
  | n + 64, hi, _ => exact absurd hi (by omega)

/-! Literals, following `bap_primus_lisp_word.ml` and Zarith's `Z.of_string`. -/

theorem parseZ_bare_prefixes : parseZ ['0', 'x'] = some 0 ∧ parseZ ['0', 'b'] = some 0 ∧ parseZ ['-', '0', 'o'] = some 0 := by
  decide +kernel

private theorem digits_no_underscore (base n : Nat) (h2 : 1 < base) (h16 : base ≤ 16) (c : Char)
    (hc : c ∈ Nat.toDigits base n) : c ≠ '_' := by
  have hd : ∀ d : Fin 16, Nat.digitChar d ≠ '_' := by decide
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite h2] at hc
    split at hc
    · rename_i hlt
      simp only [List.mem_singleton] at hc
      subst hc
      exact hd ⟨n, by omega⟩
    · rcases List.mem_append.1 hc with hl | hl
      · exact ih _ (Nat.div_lt_self (by omega) h2) hl
      · simp only [List.mem_singleton] at hl
        subst hl
        exact hd ⟨n % base, by have := Nat.mod_lt n (show 0 < base by omega); omega⟩

private theorem filter_digits (base n : Nat) (h2 : 1 < base) (h16 : base ≤ 16) :
    (Nat.toDigits base n).filter (· != '_') = Nat.toDigits base n := by
  apply List.filter_eq_self.2
  intro c hc
  simpa using digits_no_underscore base n h2 h16 c hc

private theorem digits_head (base n : Nat) (h2 : 1 < base) (h16 : base ≤ 16) :
    (Nat.toDigits base n).head? ≠ some '_' := by
  intro h
  exact digits_no_underscore base n h2 h16 _ (List.mem_of_head? h) rfl

/-- Printed numbers read back through the literal parser, in each prefixed base. -/
theorem parseZ_hex (n : Nat) : parseZ ('0' :: 'x' :: Nat.toDigits 16 n) = some (Int.ofNat n) := by
  simp [parseZ, digits_head 16 n (by decide) (by decide), filter_digits 16 n (by decide) (by decide),
    parseBasedNat_toDigits 16 n (by decide) (by decide)]

theorem parseZ_binary (n : Nat) : parseZ ('0' :: 'b' :: Nat.toDigits 2 n) = some (Int.ofNat n) := by
  simp [parseZ, digits_head 2 n (by decide) (by decide), filter_digits 2 n (by decide) (by decide),
    parseBasedNat_toDigits 2 n (by decide) (by decide)]

theorem parseZ_negative_hex (n : Nat) : parseZ ('-' :: '0' :: 'x' :: Nat.toDigits 16 n) = some (-Int.ofNat n) := by
  simp [parseZ, digits_head 16 n (by decide) (by decide), filter_digits 16 n (by decide) (by decide),
    parseBasedNat_toDigits 16 n (by decide) (by decide)]

/-- An atom that does not start like a number is a symbol, never an error. -/
theorem readLiteral_symbol (atom : String) (h : startsNumeric atom.toList = false) : readLiteral atom = .ok none := by
  simp [readLiteral, h]

private theorem span_no_colon {atom : String} (h : ':' ∉ atom.toList) :
    atom.toList.span (· != ':') = (atom.toList, []) := by
  have hall : ∀ c ∈ atom.toList, (c != ':') = true := by
    intro c hc
    have : c ≠ ':' := fun e => h (e ▸ hc)
    simpa using this
  have key : ∀ (chars acc : List Char), (∀ c ∈ chars, (c != ':') = true) →
      List.span.loop (· != ':') chars acc = (acc.reverse ++ chars, []) := by
    intro chars
    induction chars with
    | nil => intro acc _; simp [List.span.loop]
    | cons head rest ih =>
      intro acc hh
      have hhead := hh head (by simp)
      simp only [List.span.loop, hhead, ih (head :: acc) fun c hc => hh c (List.mem_cons_of_mem _ hc)]
      simp
  exact (key atom.toList [] hall).trans (by simp)

/-- An atom starting like a number either parses or is rejected: it never falls through to a symbol. -/
theorem readLiteral_numeric {atom : String} (hn : startsNumeric atom.toList = true) (hc : ':' ∉ atom.toList) :
    (∃ value, parseZ atom.toList = some value ∧ readLiteral atom = .ok (some (value, none))) ∨
      (parseZ atom.toList = none ∧ ∃ e, readLiteral atom = .error e) := by
  cases hz : parseZ atom.toList with
  | none =>
    refine Or.inr ⟨rfl, s!"malformed Primus literal {atom}", ?_⟩
    simp only [readLiteral, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, span_no_colon hc, hz]
  | some value =>
    refine Or.inl ⟨value, rfl, ?_⟩
    simp only [readLiteral, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, span_no_colon hc, hz]

private def isRejected (atom : String) : Bool :=
  match readLiteral atom with
  | .error _ => true
  | .ok _ => false

/-- Malformed literals, and that bare prefixes are not among them. -/
theorem readLiteral_examples :
    isRejected "0xzz" = true ∧ isRejected "12abc" = true ∧ isRejected "1:2:3" = true ∧ isRejected "5:abc" = true ∧
      isRejected "0x_1" = true ∧ parseInteger "0x" = some (0, none) ∧ parseInteger "1:8" = some (1, some 8) ∧
      parseInteger "-0x10" = some (-16, none) ∧ parseInteger "x1" = none := by
  decide +kernel

/-- Evaluation rejects a malformed atom rather than looking it up as a symbol. -/
theorem eval_rejects_malformed (fuel : Nat) (locals : Locals) (context : Context) (state : State) {atom e : String}
    (h : readLiteral atom = .error e) : eval (fuel + 1) locals context state (.atom atom) = .error e := by
  rw [eval]
  simp [h, bind, Except.bind]

theorem checkForms_rejects {forms : List Sexp} {form : Sexp} {e : String} (hm : form ∈ forms)
    (h : checkLiterals form = .error e) : ∃ e', checkForms forms = .error e' := by
  induction forms with
  | nil => simp at hm
  | cons head rest ih =>
    rw [checkForms]
    cases hh : checkLiterals head with
    | error e' => exact ⟨e', by simp [bind, Except.bind, hh]⟩
    | ok _ =>
      rcases List.mem_cons.1 hm with rfl | hm'
      · simp [h] at hh
      · obtain ⟨e', he⟩ := ih hm'
        exact ⟨e', by simp [bind, Except.bind, hh, he]⟩

/-- Definitions are checked when loaded, even if never called; their documentation strings are not. -/
theorem checkLiterals_definition (name : String) (params : List Sexp) (body : Sexp) (rest : List Sexp) (doc : String) :
    checkLiterals (.list (.atom "defun" :: .atom name :: .list params :: .atom doc :: body :: rest)) =
      checkForms (body :: rest) := by
  rw [checkLiterals, checkBody]

theorem checkLiterals_atom (atom : String) (e : String) (h : readLiteral atom = .error e) :
    checkLiterals (.atom atom) = .error e := by
  simp [checkLiterals, h, Functor.map, Except.map]

/-! `word-width`. -/

theorem wordWidth_nil (context : Context) : wordWidth context [] = .ok (.int (BitVec.ofNat 64 context.bits)) := rfl

theorem wordWidth_cons {context : Context} {head : SV} {rest : List SV} {widths : List Nat}
    (h : (head :: rest).mapM (widthOf context) = .ok widths) :
    wordWidth context (head :: rest) = .ok (.int (BitVec.ofNat 64 (widths.foldl max 0))) := by
  simp only [wordWidth, bind, Except.bind, h]

private theorem foldl_max_bound (widths : List Nat) (start : Nat) :
    start ≤ widths.foldl max start ∧ ∀ w ∈ widths, w ≤ widths.foldl max start := by
  induction widths generalizing start with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    obtain ⟨h1, h2⟩ := ih (max start head)
    exact ⟨by omega, by omega, h2⟩

private theorem foldl_max_mem (widths : List Nat) (start : Nat) :
    widths.foldl max start = start ∨ widths.foldl max start ∈ widths := by
  induction widths generalizing start with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (max start head) with h | h
    · rw [h]
      omega
    · exact Or.inr (Or.inr h)

/-- The maximum of the argument widths: at least each of them, and equal to one of them. -/
theorem wordWidth_is_maximum (widths : List Nat) (hne : widths ≠ []) :
    (∀ w ∈ widths, w ≤ widths.foldl max 0) ∧ widths.foldl max 0 ∈ widths := by
  refine ⟨(foldl_max_bound widths 0).2, ?_⟩
  rcases foldl_max_mem widths 0 with h | h
  · cases widths with
    | nil => exact absurd rfl hne
    | cons head rest =>
      have := (foldl_max_bound (head :: rest) 0).2 head (by simp)
      have hz : head = 0 := by omega
      subst hz
      rw [h]
      simp
  · exact h

/-! Assignment to `let` variables. -/

theorem bindAssignable_spec (context : Context) (state : State) {value : SV} {width : Nat} {exp : Bil.Exp}
    (h : expectBil context value = .ok (width, exp)) :
    bindAssignable context state value =
      .ok (.register s!"_primus_{state.nextTemp}" width width, { state with
        code := state.code ++ [.move ⟨s!"_primus_{state.nextTemp}", .imm width, 0, false⟩ exp]
        nextTemp := state.nextTemp + 1 }) := by
  simp [bindAssignable, h, bind, Except.bind]

private theorem primus_name_not_zero (n : Nat) : toString "_primus_" ++ n.repr ≠ "XZR" := by
  intro h
  have hl := congrArg String.toList h
  have hp : (toString "_primus_").toList = ['_', 'p', 'r', 'i', 'm', 'u', 's', '_'] := by decide +kernel
  have hx : "XZR".toList = ['X', 'Z', 'R'] := by decide +kernel
  rw [String.toList_append, hp, hx] at hl
  simp at hl

/-- Reads of an assignable variable see the machine variable that assignments write. -/
theorem assignable_read (context : Context) (n width : Nat) :
    expectBil context (.register s!"_primus_{n}" width width) =
      .ok (width, .var ⟨s!"_primus_{n}", .imm width, 0, false⟩) := by
  simp [expectBil, primus_name_not_zero]

theorem assignable_write (context : Context) (n width : Nat) {value : SV} {exp : Bil.Exp}
    (h : expectBil context value = .ok (width, exp)) :
    assign context (.register s!"_primus_{n}" width width) value =
      .ok [.move ⟨s!"_primus_{n}", .imm width, 0, false⟩ exp] := by
  simp [assign, assignRegister, primus_name_not_zero, h, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

/-- `let` gives a name assigned in its scope a variable of its own, directly or through a macro argument. -/
theorem assignsLocal_set (globals : Globals) (name : String) (fuel : Nat) (value : Sexp) :
    assignsLocal globals name (fuel + 1) (.list [.atom "set", .atom name, value]) = true := by
  rw [assignsLocal]
  simp

private theorem eval_atom_lookup {fuel : Nat} {locals : Locals} {context : Context} {state : State} {name : String} {value : SV}
    (hsym : readLiteral name = .ok none) (ht : name ≠ "true") (hf : name ≠ "false") (hc : name.startsWith ":" = false)
    (hl : lookupState name locals state = .ok value) :
    eval (fuel + 1) locals context state (.atom name) = .ok (value, state) := by
  rw [eval]
  simp [hsym, ht, hf, hc, hl, bind, Except.bind, pure, Except.pure]

/-- Reading a `let` variable sees its machine variable, whatever globals are called. -/
theorem eval_let_variable (fuel : Nat) (locals : Locals) (context : Context) (state : State) {name target : String}
    {width : Nat} (hsym : readLiteral name = .ok none) (ht : name ≠ "true") (hf : name ≠ "false")
    (hc : name.startsWith ":" = false) (hl : Assoc.get name locals = some (.register target width width)) :
    eval (fuel + 1) locals context state (.atom name) = .ok (.register target width width, state) :=
  eval_atom_lookup hsym ht hf hc (by simp [lookupState, hl])

/-- `(set x value)` on a `let` variable emits one move to that variable's machine variable, as upstream's
`set_` assigns the scoped variable when the name is bound. -/
theorem eval_set_let_variable (fuel : Nat) (locals : Locals) (context : Context) (state after : State)
    {name target : String} {width : Nat} {form : Sexp} {value : SV} {exp : Bil.Exp}
    (hsym : readLiteral name = .ok none) (ht : name ≠ "true") (hf : name ≠ "false") (hc : name.startsWith ":" = false)
    (hbound : Assoc.get name locals = some (.register target width width)) (hzero : target ≠ "XZR")
    (hset : Assoc.get "set" locals = none) (hops : state.operations.get? "set" = none)
    (hglobal : Assoc.get "set" state.globals = none)
    (hform : eval (fuel + 1) locals context state form = .ok (value, after))
    (hvalue : expectBil context value = .ok (width, exp)) :
    eval (fuel + 4) locals context state (.list [.atom "set", .atom name, form]) =
      .ok (value, emit after [.move ⟨target, .imm width, 0, false⟩ exp]) := by
  have hprimitive : lookupState "set" locals state = .ok (.callable (.primitive "set")) := by
    have h0 : "set".startsWith "core:" = false := by decide +kernel
    have h1 : ("set" = "replicate") = False := by simp
    have h2 : "set" ∈ primitiveNames := by decide
    have hops' : state.operations["set"]? = none := by simpa using hops
    simp [lookupState, h0, hset, hops', hglobal, h2]
  have hsymset : readLiteral "set" = .ok none := by
    apply readLiteral_symbol
    decide +kernel
  have hcolon : "set".startsWith ":" = false := by decide +kernel
  have hatom : eval (fuel + 3) locals context state (.atom "set") = .ok (.callable (.primitive "set"), state) :=
    eval_atom_lookup hsymset (by simp) (by simp) hcolon hprimitive
  have hname := eval_let_variable (fuel + 1) locals context state hsym ht hf hc hbound
  have hlist : evalList (fuel + 3) locals context state [.atom name, form] =
      .ok ([.register target width width, value], after) := by
    unfold evalList
    simp only [bind, Except.bind, hname]
    unfold evalList
    simp only [bind, Except.bind, hform]
    unfold evalList
    simp only [pure, Except.pure]
  have hassign : applyPrimitive context "set" [.register target width width, value] =
      .ok (value, [.move ⟨target, .imm width, 0, false⟩ exp]) := by
    simp [applyPrimitive, assign, assignRegister, hzero, hvalue, valueOnly, bind, Except.bind, pure, Except.pure]
  rw [eval]
  simp only [bind, Except.bind, hprimitive, hatom, hlist]
  · rw [apply]
    simp only [bind, Except.bind, hassign, pure, Except.pure]
  all_goals (intros; simp_all)

/-- A `let` whose scope assigns its name binds it to a fresh machine variable and evaluates the body with
that binding, initialised from the bound value. -/
theorem eval_let_assignable (fuel : Nat) (locals : Locals) (context : Context) (state after : State)
    {name : String} {form : Sexp} {body : List Sexp} {value : SV} {width : Nat} {exp : Bil.Exp}
    (hform : eval fuel locals context state form = .ok (value, after))
    (hvalue : expectBil context value = .ok (width, exp))
    (hassigned : ([Sexp.list [.atom name, form]] ++ body).any (assignsLocal after.globals name 64) = true) :
    eval (fuel + 1) locals context state (.list (.atom "let" :: .list [.list [.atom name, form]] :: body)) =
      evalSequence fuel ((name, .register s!"_primus_{after.nextTemp}" width width) :: locals) context
        { after with
          code := after.code ++ [.move ⟨s!"_primus_{after.nextTemp}", .imm width, 0, false⟩ exp]
          nextTemp := after.nextTemp + 1 } body := by
  rw [eval]
  · simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind, hform, hassigned, ↓reduceIte,
      bindAssignable_spec context after hvalue, pure, Except.pure]
  all_goals (intros; simp_all)

end Semantics

/-! ### Lowering helpers of the lifted executor -/

section Lifted

open Bap.Primus.Lifted
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.layout Lowering.nextSlot Lowering.ops Lowering.inputs
  Lowering.outputs Lowering.written Lowering.effectSlot Lowering.memory Lowering.checkpoints Lowering.mk
  widthOf slot temporary readVar writeVar setEffect mask narrow useMemory atCodeStop directEdges reachable
  reachable.loop syncState graphEdgeOps

/-- Slot allocation invariant: every allocated slot is below `nextSlot`, slots are distinct, and
each variable occurs at most once. -/
structure LayoutWF (lowering : Lowering) : Prop where
  bound : ∀ binding ∈ Lowering.layout lowering, binding.2 < Lowering.nextSlot lowering
  slotsDistinct : (Lowering.layout lowering).Pairwise fun left right => left.2 ≠ right.2
  varsDistinct : (Lowering.layout lowering).Pairwise fun left right => left.1 ≠ right.1

theorem layoutWF_of_nil (lowering : Lowering) (h : Lowering.layout lowering = []) : LayoutWF lowering :=
  ⟨by simp [h], by simp [h], by simp [h]⟩

theorem slot_existing (lowering : Lowering) (var : Bap.Var) (binding : Bap.Var × Nat)
    (h : (Lowering.layout lowering).find? (fun binding => binding.1 == var) = some binding) :
    slot lowering var = (lowering, binding.2) := by
  simp only [slot]
  rw [h]

theorem slot_fresh (lowering : Lowering) (var : Bap.Var)
    (h : (Lowering.layout lowering).find? (fun binding => binding.1 == var) = none) :
    (slot lowering var).2 = Lowering.nextSlot lowering ∧
      Lowering.nextSlot (slot lowering var).1 = Lowering.nextSlot lowering + 1 ∧
      Lowering.layout (slot lowering var).1 = Lowering.layout lowering ++ [(var, Lowering.nextSlot lowering)] := by
  simp only [slot]
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- Asking for a variable's slot twice returns the same slot and changes nothing. -/
theorem slot_idempotent (lowering : Lowering) (var : Bap.Var) :
    slot (slot lowering var).1 var = (slot lowering var) := by
  cases h : (Lowering.layout lowering).find? (fun binding => binding.1 == var) with
  | some binding =>
    rw [slot_existing _ _ _ h]
    exact slot_existing _ _ _ h
  | none =>
    obtain ⟨h1, h2, h3⟩ := slot_fresh lowering var h
    have hf : (Lowering.layout (slot lowering var).1).find? (fun binding => binding.1 == var) =
        some (var, Lowering.nextSlot lowering) := by
      rw [h3, List.find?_append, h]
      simp
    rw [slot_existing _ _ _ hf]
    exact Prod.ext rfl h1.symm

theorem slot_preserves_wf {lowering : Lowering} (wf : LayoutWF lowering) (var : Bap.Var) :
    LayoutWF (slot lowering var).1 := by
  cases h : (Lowering.layout lowering).find? (fun binding => binding.1 == var) with
  | some binding =>
    rw [slot_existing _ _ _ h]
    exact wf
  | none =>
    obtain ⟨_, h2, h3⟩ := slot_fresh lowering var h
    refine ⟨?_, ?_, ?_⟩
    · rw [h3, h2]
      intro binding hb
      rcases List.mem_append.1 hb with hb' | hb'
      · have := wf.bound binding hb'
        omega
      · simp only [List.mem_singleton] at hb'
        subst hb'
        simp
    · rw [h3]
      refine List.pairwise_append.2 ⟨wf.slotsDistinct, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      have := wf.bound a ha
      simp only
      omega
    · rw [h3]
      refine List.pairwise_append.2 ⟨wf.varsDistinct, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      simp only
      intro he
      have := List.find?_eq_none.1 h a ha
      simp [he] at this

/-- The slot returned for a variable is recorded in the layout. -/
theorem slot_mem_layout (lowering : Lowering) (var : Bap.Var) :
    (var, (slot lowering var).2) ∈ Lowering.layout (slot lowering var).1 := by
  cases h : (Lowering.layout lowering).find? (fun binding => binding.1 == var) with
  | some binding =>
    rw [slot_existing _ _ _ h]
    have hm := List.mem_of_find?_eq_some h
    have hv : binding.1 = var := by simpa using List.find?_some h
    subst hv
    exact hm
  | none =>
    obtain ⟨h1, _, h3⟩ := slot_fresh lowering var h
    rw [h3, h1]
    simp

theorem slot_layout_mono (lowering : Lowering) (var : Bap.Var) (binding : Bap.Var × Nat)
    (h : binding ∈ Lowering.layout lowering) : binding ∈ Lowering.layout (slot lowering var).1 := by
  cases hf : (Lowering.layout lowering).find? (fun binding => binding.1 == var) with
  | some b =>
    rw [slot_existing _ _ _ hf]
    exact h
  | none =>
    rw [(slot_fresh lowering var hf).2.2]
    exact List.mem_append_left _ h

/-- Register isolation: distinct variables are never assigned the same machine slot. -/
theorem slot_distinct {lowering : Lowering} (wf : LayoutWF lowering) {left right : Bap.Var} (hne : left ≠ right) :
    (slot lowering left).2 ≠ (slot (slot lowering left).1 right).2 := by
  have wf1 := slot_preserves_wf wf left
  have wf2 := slot_preserves_wf wf1 right
  have hl := slot_layout_mono _ right _ (slot_mem_layout lowering left)
  have hr := slot_mem_layout (slot lowering left).1 right
  intro he
  have pairwise := wf2.slotsDistinct
  rw [← he] at hr
  obtain ⟨_, _, h⟩ : ∃ a b, (a = left ∧ b = right) ∧ True := ⟨_, _, ⟨rfl, rfl⟩, trivial⟩
  have key : ∀ (L : List (Bap.Var × Nat)), L.Pairwise (fun a b => a.2 ≠ b.2) →
      ∀ a b, a ∈ L → b ∈ L → a.2 = b.2 → a = b := by
    intro L hL
    induction L with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨hx, hxs⟩ := List.pairwise_cons.1 hL
      intro a b ha hb hab
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd hab (hx _ hb')
      · exact absurd hab.symm (hx _ ha')
      · exact ih hxs a b ha' hb' hab
  have := key _ pairwise _ _ hl hr rfl
  simp only [Prod.mk.injEq] at this
  exact hne this.1

/-- Temporaries never collide with variable slots. -/
theorem temporary_fresh {lowering : Lowering} (wf : LayoutWF lowering) (binding : Bap.Var × Nat)
    (h : binding ∈ Lowering.layout lowering) : binding.2 ≠ (temporary lowering).2 := by
  have := wf.bound binding h
  simp only [temporary]
  omega

theorem temporary_preserves_wf {lowering : Lowering} (wf : LayoutWF lowering) : LayoutWF (temporary lowering).1 := by
  refine ⟨?_, wf.slotsDistinct, wf.varsDistinct⟩
  intro binding hb
  have := wf.bound binding hb
  show binding.2 < Lowering.nextSlot lowering + 1
  omega

theorem widthOf_some_iff (var : Bap.Var) (width : Nat) :
    widthOf var = some width ↔ var.typ = .imm width ∧ 0 < width ∧ width ≤ 64 := by
  simp only [widthOf]
  split
  · rename_i w hw
    by_cases hb : 0 < w ∧ w ≤ 64
    · simp only [hb.1, hb.2, decide_true, Bool.and_self, ↓reduceIte, Option.some.injEq, hw, Typ.imm.injEq]
      constructor
      · rintro rfl
        exact ⟨rfl, hb⟩
      · rintro ⟨rfl, _⟩
        rfl
    · have : (decide (0 < w) && decide (w ≤ 64)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp only [this, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, hw, Typ.imm.injEq]
      rintro ⟨rfl, h⟩
      exact hb h
  · rename_i hn
    simp only [reduceCtorEq, false_iff]
    rintro ⟨h, _⟩
    exact hn width h

/-- Only variables of width up to 64 reach the native slot file. -/
theorem readVar_none (lowering : Lowering) (var : Bap.Var) (h : widthOf var = none) :
    readVar lowering var = none := by
  simp [readVar, h]

theorem writeVar_none (lowering : Lowering) (var : Bap.Var) (h : widthOf var = none) :
    writeVar lowering var = none := by
  simp [writeVar, h]

/-- A write records the variable as written and as an output. -/
theorem writeVar_records {lowering result : Lowering} {var : Bap.Var} {index : Nat}
    (h : writeVar lowering var = some (result, index)) :
    var ∈ Lowering.written result ∧ (var, index) ∈ Lowering.outputs result ∧
      index = (slot lowering var).2 := by
  cases hw : widthOf var with
  | none => simp [writeVar, hw] at h
  | some width =>
    simp only [writeVar, hw, Option.bind_eq_bind, bind, pure, Option.bind_some] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
    · rename_i hc
      exact ⟨by simpa using hc, by simp [Lowering.outputs], rfl⟩
    · exact ⟨by simp [Lowering.written], by simp [Lowering.outputs], rfl⟩

/-- A variable already written is not treated as an input: its value does not come from the initial state. -/
theorem readVar_after_write_not_input {lowering result : Lowering} {var : Bap.Var} {index : Nat}
    (hw : var ∈ Lowering.written lowering) (h : readVar lowering var = some (result, index)) :
    Lowering.inputs result = Lowering.inputs (slot lowering var).1 := by
  cases hv : widthOf var with
  | none => simp [readVar, hv] at h
  | some width =>
    have hw' : List.contains (Lowering.written (slot lowering var).1) var = true := by
      have hmem : Lowering.written (slot lowering var).1 = Lowering.written lowering := by
        simp only [slot]
        split <;> rfl
      rw [hmem]
      simpa using hw
    simp only [readVar, hv, Option.bind_eq_bind, bind, pure, Option.bind_some, hw', Bool.true_or, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]

theorem mask_toNat (width : Nat) (h : width ≤ 64) : (mask width).toNat = 2 ^ width - 1 := by
  simp only [mask, UInt64.toNat_ofNat']
  have : 2 ^ width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h
  have hp : 0 < 2 ^ width := Nat.two_pow_pos _
  exact Nat.mod_eq_of_lt (by omega)

theorem narrow_full_width (lowering : Lowering) (width index : Nat) (h : 64 ≤ width) :
    narrow lowering width index = lowering := by
  simp [narrow, Nat.not_lt.2 h]

theorem narrow_partial (lowering : Lowering) (width index : Nat) (h : width < 64) :
    Lowering.ops (narrow lowering width index) = Lowering.ops lowering ++ [.andImm index index (mask width)] := by
  simp [narrow, h]

/-- The effect slot is allocated once and reused afterwards. -/
theorem setEffect_stable (lowering : Lowering) (slot : Nat) (value : UInt64)
    (h : Lowering.effectSlot lowering = some slot) :
    (setEffect lowering value).2 = slot ∧ Lowering.effectSlot (setEffect lowering value).1 = some slot := by
  simp [setEffect, h]

theorem setEffect_allocates (lowering : Lowering) (value : UInt64) :
    Lowering.effectSlot (setEffect lowering value).1 = some (setEffect lowering value).2 := by
  cases h : Lowering.effectSlot lowering with
  | some index => simp only [setEffect, h]
  | none => simp only [setEffect, h]

/-- A block touches at most one memory variable. -/
theorem useMemory_some {lowering result : Lowering} {var : Bap.Var} (h : useMemory lowering var = some result) :
    Lowering.memory result = some var := by
  cases ht : var.typ <;> cases hm : Lowering.memory lowering <;> simp [useMemory, ht, hm] at h
  · subst h
    rfl
  · obtain ⟨rfl, rfl⟩ := h
    exact hm

theorem useMemory_conflict (lowering : Lowering) (var existing : Bap.Var) (width cell : Nat)
    (ht : var.typ = .mem width cell) (he : Lowering.memory lowering = some existing) (hne : existing ≠ var) :
    useMemory lowering var = none := by
  simp only [useMemory, ht, he]
  simp [hne]

/-- Rolling back to a code stop restores the outputs saved at that site. -/
theorem atCodeStop_restores (lowering : Lowering) (pc : Nat) (checkpoint : Nat × List (Bap.Var × Nat))
    (h : (Lowering.checkpoints lowering).find? (fun checkpoint => checkpoint.1 = pc) = some checkpoint) :
    Lowering.outputs (atCodeStop lowering pc) = checkpoint.2 := by
  simp only [atCodeStop]
  rw [h]

theorem directEdges_length (block : Block) : (directEdges block).length ≤ 2 := by
  simp only [directEdges]
  split <;> simp

/-- Graph edges that stay inside the compiled range become gotos; all others leave through a jump. -/
theorem graphEdgeOps_internal (lowering : Lowering) (labels : List (Nat × Nat)) (edges : List (Nat × Nat))
    (source target label : Nat) (he : edges.contains (source, target) = true)
    (hl : labels.find? (fun entry => entry.1 = target) = some (target, label)) :
    graphEdgeOps lowering labels edges source target = some [.goto label] := by
  simp only [graphEdgeOps, he, ↓reduceIte]
  rw [hl]

private theorem find?_filter_of_imp {α : Type} (p q : α → Bool) (items : List α) (h : ∀ x, p x = true → q x = true) :
    (items.filter q).find? p = items.find? p := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.filter_cons, List.find?_cons]
    cases hq : q head with
    | true =>
      simp only [↓reduceIte, List.find?_cons, ih]
    | false =>
      have hp : p head = false := by
        cases hh : p head with
        | false => rfl
        | true => simp [h _ hh] at hq
      simp [hp, ih]

private theorem bindMany_latest_keys (updates : List (Bap.Var × Bap.Value)) (var : Bap.Var)
    (hv : var ∉ updates.map Prod.fst) (current : List (Bap.Var × Bap.Value))
    (hc : var ∉ current.map Prod.fst) :
    var ∉ (updates.foldl (init := current) fun current update =>
      update :: current.filter (fun binding => binding.1 != update.1)).map Prod.fst := by
  induction updates generalizing current with
  | nil => simpa using hc
  | cons head rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    simp only [List.foldl_cons]
    apply ih hv.2
    simp only [List.map_cons, List.mem_cons, not_or]
    refine ⟨hv.1, ?_⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    exact hc (List.mem_map.2 ⟨b, (List.mem_filter.1 hb).1, he⟩)

/-- Frame law of the batched register update: variables that are not updated keep their binding. -/
theorem bindMany_frame (env : Bil.Env) (updates : List (Bap.Var × Bap.Value)) (var : Bap.Var)
    (hv : var ∉ updates.map Prod.fst) : Bil.lookup (Bil.bindMany env updates) var = Bil.lookup env var := by
  simp only [Bil.bindMany, Bil.lookup]
  rw [List.find?_append]
  have hnone := bindMany_latest_keys updates var hv [] (by simp)
  have hf : (updates.foldl (init := ([] : List (Bap.Var × Bap.Value))) fun current update =>
      update :: current.filter (fun binding => binding.1 != update.1)).find? (fun binding => binding.1 == var) = none := by
    apply List.find?_eq_none.2
    intro x hx he
    apply hnone
    refine List.mem_map.2 ⟨x, hx, ?_⟩
    simpa using he
  rw [hf]
  have hfilter := find?_filter_of_imp (fun binding : Bap.Var × Bap.Value => binding.1 == var)
    (fun binding => !(updates.map Prod.fst).contains binding.1) env (by
      intro x hx
      have hxv : x.1 = var := by simpa using hx
      rw [hxv]
      simpa using hv)
  simp only [Option.none_or]
  rw [hfilter]

/-- Native execution writes back only declared outputs: every other variable is untouched. -/
theorem syncState_frame (lowering : Lowering) (state : Bil.State) (slots : Array UInt64) (var : Bap.Var)
    (hv : var ∉ (Lowering.outputs lowering).map Prod.fst) :
    Bil.lookup (syncState lowering state slots).env var = Bil.lookup state.env var := by
  simp only [syncState]
  apply bindMany_frame
  generalize Lowering.outputs lowering = outputs at hv
  induction outputs with
  | nil => simp
  | cons head rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hv
    simp only [List.foldr_cons]
    split
    · simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨hv.1, ih hv.2⟩
    · exact ih hv.2

/-! Reachability over the block graph. -/

/-- Paths in a block graph. -/
inductive Reaches (edges : List (Nat × Nat)) : Nat → Nat → Prop where
  | refl (node : Nat) : Reaches edges node node
  | step {first middle last : Nat} : (first, middle) ∈ edges → Reaches edges middle last → Reaches edges first last

private theorem reachable_loop_sound (edges : List (Nat × Nat)) (target : Nat) (fuel : Nat) (visited pending : List Nat)
    (h : reachable.loop edges target fuel visited pending = true) : ∃ node ∈ pending, Reaches edges node target := by
  induction fuel generalizing visited pending with
  | zero => simp [reachable.loop] at h
  | succ fuel ih =>
    unfold reachable.loop at h
    split at h
    · simp at h
    · rename_i current rest
      split at h
      · rename_i he
        exact ⟨current, by simp, he ▸ .refl _⟩
      · split at h
        · obtain ⟨node, hn, hr⟩ := ih _ _ h
          exact ⟨node, List.mem_cons_of_mem _ hn, hr⟩
        · obtain ⟨node, hn, hr⟩ := ih _ _ h
          rcases List.mem_append.1 hn with hnext | hrest
          · refine ⟨current, by simp, ?_⟩
            obtain ⟨⟨a, b⟩, hab, hf⟩ := List.mem_filterMap.1 hnext
            simp only at hf
            split at hf
            · rename_i ha
              simp only [Option.some.injEq] at hf
              subst ha hf
              exact .step hab hr
            · simp at hf
          · exact ⟨node, List.mem_cons_of_mem _ hrest, hr⟩

/-- Soundness of `reachable`: a positive answer always denotes a real path. -/
theorem reachable_sound (edges : List (Nat × Nat)) (source target : Nat) (h : reachable edges source target = true) :
    Reaches edges source target := by
  obtain ⟨node, hn, hr⟩ := reachable_loop_sound edges target _ _ _ h
  simp only [List.mem_singleton] at hn
  exact hn ▸ hr

private def unexplored (edges : List (Nat × Nat)) (visited : List Nat) : Nat :=
  (edges.filter fun edge => !visited.contains edge.1).length

private theorem unexplored_visit (edges : List (Nat × Nat)) (visited : List Nat) (current : Nat)
    (hc : visited.contains current = false) :
    unexplored edges (current :: visited) +
        (edges.filterMap fun (source, target) => if source = current then some target else none).length =
      unexplored edges visited := by
  simp only [unexplored]
  induction edges with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨a, b⟩ := head
    by_cases ha : a = current
    · subst ha
      have h1 : (a :: visited).contains a = true := by simp
      simp only [List.filter_cons, List.filterMap_cons, h1, hc, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · have h1 : (current :: visited).contains a = visited.contains a := by
        have hne : (a == current) = false := by simpa using ha
        simp only [List.contains_cons, hne, Bool.false_or]
      cases hv : visited.contains a <;>
        simp only [List.filter_cons, List.filterMap_cons, h1, hv, ha, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

private theorem closed_unreachable {edges : List (Nat × Nat)} {visited : List Nat} {node target : Nat}
    (hclosed : ∀ v ∈ visited, ∀ w, (v, w) ∈ edges → w ∈ visited) (htarget : target ∉ visited)
    (hr : Reaches edges node target) : node ∉ visited := by
  induction hr with
  | refl => exact htarget
  | step he _ ih => exact fun hv => ih htarget (hclosed _ hv _ he)

/-- Completeness core: with fuel for every pending node and unexplored edge, a `false` answer means
the explored set is closed and the target is unreachable from it. -/
private theorem reachable_loop_complete (edges : List (Nat × Nat)) (target : Nat) (fuel : Nat) (visited pending : List Nat)
    (hfuel : pending.length + unexplored edges visited ≤ fuel)
    (hclosed : ∀ v ∈ visited, ∀ w, (v, w) ∈ edges → w ∈ visited ∨ w ∈ pending)
    (htarget : target ∉ visited)
    (h : reachable.loop edges target fuel visited pending = false) :
    ∀ node, (node ∈ visited ∨ node ∈ pending) → ¬ Reaches edges node target := by
  induction fuel generalizing visited pending with
  | zero =>
    have hp : pending = [] := List.length_eq_zero_iff.1 (by omega)
    subst hp
    intro node hn hr
    exact closed_unreachable (fun v hv w he => by simpa using hclosed v hv w he) htarget hr (by simpa using hn)
  | succ fuel ih =>
    unfold reachable.loop at h
    split at h
    · intro node hn hr
      exact closed_unreachable (fun v hv w he => by simpa using hclosed v hv w he) htarget hr (by simpa using hn)
    · rename_i current rest
      split at h
      · simp at h
      · rename_i hne
        split at h
        · rename_i hvis
          have hmem : current ∈ visited := by simpa using hvis
          have := ih visited rest (by simp only [List.length_cons] at hfuel; omega) (fun v hv w he => by
            rcases hclosed v hv w he with hw | hw
            · exact Or.inl hw
            · rcases List.mem_cons.1 hw with rfl | hw'
              · exact Or.inl hmem
              · exact Or.inr hw') htarget h
          intro node hn
          rcases hn with hn | hn
          · exact this node (Or.inl hn)
          · rcases List.mem_cons.1 hn with rfl | hn'
            · exact this _ (Or.inl hmem)
            · exact this node (Or.inr hn')
        · rename_i hvis
          have hvisf : visited.contains current = false := by simpa using hvis
          have hcount := unexplored_visit edges visited current hvisf
          have hmem : ∀ w, (current, w) ∈ edges →
              w ∈ edges.filterMap fun (source, target) => if source = current then some target else none := by
            intro w he
            exact List.mem_filterMap.2 ⟨(current, w), he, by simp⟩
          have := ih (current :: visited) _
            (by
              have key : ∀ next : List Nat,
                  next.length = (edges.filterMap fun (source, target) =>
                    if source = current then some target else none).length →
                  (next ++ rest).length + unexplored edges (current :: visited) ≤ fuel := by
                intro next hn
                simp only [List.length_append, List.length_cons] at hfuel ⊢
                omega
              exact key _ rfl)
            (fun v hv w he => by
              rcases List.mem_cons.1 hv with rfl | hv'
              · exact Or.inr (List.mem_append_left _ (hmem w he))
              · rcases hclosed v hv' w he with hw | hw
                · exact Or.inl (List.mem_cons_of_mem _ hw)
                · rcases List.mem_cons.1 hw with rfl | hw'
                  · exact Or.inl (by simp)
                  · exact Or.inr (List.mem_append_right _ hw'))
            (by
              simp only [List.mem_cons, not_or]
              exact ⟨fun e => hne e.symm, htarget⟩) h
          intro node hn
          rcases hn with hn | hn
          · exact this node (Or.inl (List.mem_cons_of_mem _ hn))
          · rcases List.mem_cons.1 hn with rfl | hn'
            · exact this _ (Or.inl (by simp))
            · exact this node (Or.inr (List.mem_append_right _ hn'))

/-- Completeness of `reachable`: every real path is found, on every graph. -/
theorem reachable_complete (edges : List (Nat × Nat)) (source target : Nat) (h : Reaches edges source target) :
    reachable edges source target = true := by
  cases hr : reachable edges source target with
  | true => rfl
  | false =>
    have hfuel : [source].length + unexplored edges [] ≤ edges.length + 1 := by
      have := List.length_filter_le (fun edge : Nat × Nat => !([] : List Nat).contains edge.1) edges
      simp only [unexplored, List.length_singleton]
      omega
    exact absurd h (reachable_loop_complete edges target _ [] [source] hfuel (by simp) (by simp) hr source (by simp))

theorem reachable_iff (edges : List (Nat × Nat)) (source target : Nat) :
    reachable edges source target = true ↔ Reaches edges source target :=
  ⟨reachable_sound edges source target, reachable_complete edges source target⟩

theorem reachable_self (edges : List (Nat × Nat)) (node : Nat) : reachable edges node node = true :=
  reachable_complete _ _ _ (.refl node)

/-- A back edge is detected even on the smallest cycle: this used to answer `false`. -/
theorem reachable_single_edge : reachable [(1, 2)] 1 2 = true :=
  reachable_complete _ _ _ (.step (by simp) (.refl 2))

end Lifted

end Bap.Proofs.Primus
