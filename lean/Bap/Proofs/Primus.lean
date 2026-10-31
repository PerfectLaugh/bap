import Lean
import Bap.Primus.System
import Bap.Primus.Checkpoint
import Bap.Primus.Lifted
import Bap.Primus.Lisp
import Bap.Primus.Literal
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

open Lean Elab Command in
/-- Make the unfolding theorems of private definitions, which a proof cannot name before they exist. -/
local elab "realize_eq_defs " mod:ident ns:ident ids:ident* : command => do
  for id in ids.toList do
    liftCoreM <| executeReservedNameAction (mkPrivateNameCore mod.getId (ns.getId ++ id.getId ++ `eq_def))


namespace Bap.Proofs.Primus

open Bap.Primus
open Bap.Primus.Literal

private theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ v, x = .ok v ∧ f v = .ok r := by
  cases hx : x with
  | error e => simp [hx, bind, Except.bind] at h
  | ok v => exact ⟨v, rfl, by simpa [hx, bind, Except.bind] using h⟩

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
  · simp [hu, Nat.not_le.2 hu]
  · simp only [hu, ↓reduceIte, Nat.not_lt.1 hu, true_and]
    split <;> rename_i h
    · simp [h]
    · simp [h, eq_comm]

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
  | none => simp
  | some p =>
    cases hr : p.readable <;> simp [hr]

theorem loadByte_unmapped (memory : PMemory) (address : Nat) (h : memory.isMapped address = false) :
    ∃ e, memory.loadByte address = .error e := by
  have : memory.protection address = none := by
    simpa [Bap.Primus.Memory.isMapped] using h
  simp [Bap.Primus.Memory.loadByte, this]

theorem storeByte_ok_iff (memory : PMemory) (address : Nat) (value : UInt8) (result : PMemory) :
    memory.storeByte address value = .ok result ↔
      ∃ p, memory.protection address = some p ∧ p.writable = true ∧
        result = { memory with cells := Bap.Memory.writeByte memory.cells (BitVec.ofNat 64 address) value } := by
  simp only [Bap.Primus.Memory.storeByte]
  cases hp : memory.protection address with
  | none => simp
  | some p =>
    cases hr : p.writable
    · simp [hr]
    · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp only [Except.ok.injEq, Option.some.injEq, exists_eq_left', hr, true_and]
      exact eq_comm

theorem storeByte_readonly (memory : PMemory) (address : Nat) (value : UInt8) (p : Protection)
    (hp : memory.protection address = some p) (hw : p.writable = false) :
    ∃ e, memory.storeByte address value = .error e := by
  simp [Bap.Primus.Memory.storeByte, hp, hw]

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
    simp [Bap.Primus.Memory.loadByte, protection_out_of_space _ _ hge]

/-- A store at or above `2^64` fails, so it cannot alias a low address. -/
theorem storeByte_out_of_space (memory : PMemory) (address : Nat) (value : UInt8)
    (h : Bap.Primus.Memory.addressLimit ≤ address) :
    memory.storeByte address value = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.storeByte, protection_out_of_space _ _ h]

theorem loadByte_out_of_space (memory : PMemory) (address : Nat) (h : Bap.Primus.Memory.addressLimit ≤ address) :
    memory.loadByte address = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.loadByte, protection_out_of_space _ _ h]

/-- Fetching needs execute permission only. -/
theorem fetch_ok_iff (memory : PMemory) (address : Nat) (value : UInt8) :
    memory.fetch address = .ok value ↔
      ∃ p, memory.protection address = some p ∧ p.executable = true ∧
        Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address) = value := by
  simp only [Bap.Primus.Memory.fetch]
  cases hp : memory.protection address with
  | none => simp
  | some p =>
    cases hx : p.executable
    · simp [hx]
    · simp [hx]

/-- Execute-only memory can be fetched, but not read as data. -/
theorem execute_only_fetch_without_load (memory : PMemory) (address : Nat) (p : Protection)
    (hp : memory.protection address = some p) (hx : p.executable = true) (hr : p.readable = false) :
    memory.fetch address = .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address)) ∧
      memory.loadByte address = .error (.unmapped address) := by
  simp [Bap.Primus.Memory.fetch, Bap.Primus.Memory.loadByte, hp, hx, hr]

/-- Readable but not executable memory is loadable, not fetchable. -/
theorem data_only_load_without_fetch (memory : PMemory) (address : Nat) (p : Protection)
    (hp : memory.protection address = some p) (hx : p.executable = false) (hr : p.readable = true) :
    memory.fetch address = .error (.notExecutable address) ∧
      memory.loadByte address = .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address)) := by
  simp [Bap.Primus.Memory.fetch, Bap.Primus.Memory.loadByte, hp, hx, hr]

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
  simp only [Bap.Primus.Memory.load, bind, Except.bind]
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
  simp only [Bap.Primus.Memory.load, bind, Except.bind] at h
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
        simp only [hw, Except.ok.injEq] at h
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
    simp [Bap.Memory.write, h]
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
    simp only [Except.ok.injEq, exists_eq', true_iff]
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
    simp only [hadd, Except.ok.injEq] at h
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

private theorem split_cases (lower upper : Nat) (p : Protection) (region : Region) (a : Nat) :
    (∃ piece ∈ Bap.Primus.Memory.splitRegion lower upper p region, piece.contains a = true) ↔ region.contains a = true := by
  simp only [Bap.Primus.Memory.splitRegion, Bap.Primus.Region.contains, Bool.and_eq_true, decide_eq_true_eq]
  split
  · simp
  · constructor
    · rintro ⟨piece, hp, hc⟩
      simp only [List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          simp only at hc
          omega
        · simp at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only at hc
        omega
      · split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          simp only at hc
          omega
        · simp at hp
    · rintro ⟨hl, hu⟩
      by_cases h1 : a < max lower region.lower
      · refine ⟨{ region with upper := max lower region.lower }, ?_, ⟨hl, h1⟩⟩
        have : region.lower < max lower region.lower := by omega
        simp [this]
      · by_cases h2 : a < min upper region.upper
        · exact ⟨{ lower := max lower region.lower, upper := min upper region.upper, protection := p },
            by simp, ⟨by show max lower region.lower ≤ a; omega, h2⟩⟩
        · refine ⟨{ region with lower := min upper region.upper }, ?_,
            ⟨by show min upper region.upper ≤ a; omega, hu⟩⟩
          have : min upper region.upper < region.upper := by omega
          simp [this]

/-- A piece of a region holds new protection in the range and the old one elsewhere. -/
private theorem split_protection {lower upper : Nat} {p : Protection} {region piece : Region} {a : Nat}
    (hp : piece ∈ Bap.Primus.Memory.splitRegion lower upper p region) (hc : piece.contains a = true) :
    piece.protection = if lower ≤ a ∧ a < upper then p else region.protection := by
  simp only [Bap.Primus.Memory.splitRegion] at hp
  simp only [Bap.Primus.Region.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  split at hp
  · simp only [List.mem_singleton] at hp
    subst hp
    split
    · omega
    · rfl
  · simp only [List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · split at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only at hc ⊢
        exact (ite_eq_right_iff.2 fun h => absurd h (by omega)).symm
      · simp at hp
    · simp only [List.mem_singleton] at hp
      subst hp
      simp only at hc ⊢
      exact (ite_eq_left_iff.2 fun h => absurd (by omega) h).symm
    · split at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only at hc ⊢
        exact (ite_eq_right_iff.2 fun h => absurd h (by omega)).symm
      · simp at hp

private theorem split_pairwise (lower upper : Nat) (p : Protection) (region : Region) :
    (Bap.Primus.Memory.splitRegion lower upper p region).Pairwise
      fun left right => ∀ address, ¬ (left.contains address = true ∧ right.contains address = true) := by
  simp only [Bap.Primus.Memory.splitRegion]
  split
  · simp
  · simp only [List.pairwise_append, List.mem_append, Bap.Primus.Region.contains, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, by simp, ?_⟩, ?_, ?_⟩
    · split <;> simp
    · intro left hl right hr address hboth
      split at hl
      · simp only [List.mem_singleton] at hl hr
        subst hl hr
        simp only at hboth
        omega
      · simp at hl
    · split <;> simp
    · intro left hl right hr address hboth
      split at hr
      · simp only [List.mem_singleton] at hr
        subst hr
        rcases hl with hl | hl
        · split at hl
          · simp only [List.mem_singleton] at hl
            subst hl
            simp only at hboth
            omega
          · simp at hl
        · simp only [List.mem_singleton] at hl
          subst hl
          simp only at hboth
          omega
      · simp at hr

/-- Protecting keeps the regions disjoint. -/
theorem protect_disjoint {memory : PMemory} {lower upper : Nat} {p : Protection}
    (hd : RegionsDisjoint memory.regions) : RegionsDisjoint (memory.protect lower upper p).regions := by
  simp only [RegionsDisjoint, Bap.Primus.Memory.protect]
  refine List.pairwise_flatMap.2 ⟨?_, ?_⟩
  · intro region _
    exact split_pairwise lower upper p region
  · refine hd.imp ?_
    intro left right hne l hl r hr address hboth
    exact hne address ⟨(split_cases lower upper p left address).1 ⟨l, hl, hboth.1⟩,
      (split_cases lower upper p right address).1 ⟨r, hr, hboth.2⟩⟩

private theorem protect_mem {memory : PMemory} {lower upper a : Nat} {p : Protection} :
    (∃ piece ∈ (memory.protect lower upper p).regions, piece.contains a = true) ↔
      ∃ region ∈ memory.regions, region.contains a = true := by
  simp only [Bap.Primus.Memory.protect, List.mem_flatMap]
  constructor
  · rintro ⟨piece, ⟨region, hr, hp⟩, hc⟩
    exact ⟨region, hr, (split_cases lower upper p region a).1 ⟨piece, hp, hc⟩⟩
  · rintro ⟨region, hr, hc⟩
    obtain ⟨piece, hp, hpc⟩ := (split_cases lower upper p region a).2 hc
    exact ⟨piece, ⟨region, hr, hp⟩, hpc⟩

/-- `protect` never changes which addresses are mapped. -/
theorem protect_isMapped (memory : PMemory) (lower upper : Nat) (p : Protection) (address : Nat) :
    (memory.protect lower upper p).isMapped address = memory.isMapped address := by
  have : (memory.protect lower upper p).isMapped address = true ↔ memory.isMapped address = true := by
    simp only [isMapped_iff, protect_mem]
  cases h1 : (memory.protect lower upper p).isMapped address <;>
    cases h2 : memory.isMapped address <;> simp_all

/-- `protect` is exact, on partial overlaps too: a mapped byte in the range takes the new protection, and
every other byte keeps its own. -/
theorem protect_spec {memory : PMemory} {lower upper address : Nat} {p q : Protection}
    (hd : RegionsDisjoint memory.regions) (hq : memory.protection address = some q) :
    (memory.protect lower upper p).protection address =
      some (if lower ≤ address ∧ address < upper then p else q) := by
  obtain ⟨hb, region, hr, hc, hprot⟩ : address < Bap.Primus.Memory.addressLimit ∧
      ∃ region ∈ memory.regions, region.contains address = true ∧ region.protection = q := by
    have hb : address < Bap.Primus.Memory.addressLimit := protection_some_in_space hq
    unfold Bap.Primus.Memory.protection at hq
    rw [ite_eq_right (Nat.not_le.2 hb)] at hq
    split at hq
    · next region hfind =>
      simp only [Option.some.injEq] at hq
      have hc : region.contains address = true := by simpa using List.find?_some hfind
      exact ⟨hb, region, List.mem_of_find?_eq_some hfind, hc, hq⟩
    · simp at hq
  obtain ⟨piece, hp, hpc⟩ := (split_cases lower upper p region address).2 hc
  have hmem : piece ∈ (memory.protect lower upper p).regions := by
    simp only [Bap.Primus.Memory.protect, List.mem_flatMap]
    exact ⟨region, hr, hp⟩
  have := protection_of_disjoint (regions := (memory.protect lower upper p).regions)
    (protect_disjoint hd) memory.cells hmem hpc hb
  have hsplit := split_protection hp hpc
  rw [hprot] at hsplit
  rw [← hsplit]
  exact this

/-- A byte of a partially covered region takes the new protection when it is in the range. -/
theorem protect_inside {memory : PMemory} {lower upper address : Nat} {p q : Protection}
    (hd : RegionsDisjoint memory.regions) (hq : memory.protection address = some q)
    (hl : lower ≤ address) (hu : address < upper) :
    (memory.protect lower upper p).protection address = some p := by
  rw [protect_spec hd hq]; simp [hl, hu]

/-- A byte outside of the range keeps its protection. -/
theorem protect_outside {memory : PMemory} {lower upper address : Nat} {p q : Protection}
    (hd : RegionsDisjoint memory.regions) (hq : memory.protection address = some q)
    (hn : ¬ (lower ≤ address ∧ address < upper)) :
    (memory.protect lower upper p).protection address = some q := by
  rw [protect_spec hd hq]; simp only [hn, ↓reduceIte]

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
      simp [List.lookup_cons, hne, ih]
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
    (ht : atom ≠ "true") (hf : atom ≠ "false") (hi : readLiteral atom = .ok none) (hl : lookup atom locals globals = .ok value) :
    evalExpr (fuel + 1) locals globals (.atom atom) = .ok (value, locals, globals) := by
  rw [evalExpr]
  simp [ht, hf, hi, hl, bind, Except.bind]

/-- An atom that starts like a number but is not one is an error, not a symbol, as `Bad_word_literal`
upstream, even if a variable of that name exists. -/
theorem evalExpr_malformed (fuel : Nat) (locals : Locals) (globals : Globals) {atom error : String}
    (_ht : atom ≠ "true") (_hf : atom ≠ "false") (hi : readLiteral atom = .error error) :
    evalExpr (fuel + 1) locals globals (.atom atom) = .error error := by
  rw [evalExpr]
  simp [hi, bind, Except.bind]

/-- A character literal is the 8-bit code of the character. -/
private theorem readLiteral_literal_true : readLiteral "true" = .ok none := by
  have h : "true".toList = ['t', 'r', 'u', 'e'] := by decide +kernel
  simp [readLiteral, readNumeric, startsNumeric, h]

theorem readLiteral_char (c : Char) (h : c.toNat < 128) :
    readLiteral (String.ofList ['?', c]) = .ok (some (Int.ofNat c.toNat, some 8)) := by
  simp [readLiteral, h]

/-- `?` needs exactly one character after it. -/
theorem readLiteral_char_malformed (rest : List Char) (h : ∀ c, rest ≠ [c]) :
    ∃ error, readLiteral (String.ofList ('?' :: rest)) = .error error := by
  refine ⟨s!"malformed Primus literal {String.ofList ('?' :: rest)}", ?_⟩
  simp only [readLiteral, String.toList_ofList]
  cases rest with
  | nil => rfl
  | cons c cs =>
    cases cs with
    | nil => exact absurd rfl (h c)
    | cons d ds => rfl

/-- A literal with a width is a constant of that width: this is what a character literal evaluates to. -/
theorem evalExpr_typed_literal (fuel : Nat) (locals : Locals) (globals : Globals) {atom : String} {value : Int}
    {width : Nat} (ht : atom ≠ "true") (hf : atom ≠ "false") (hl : readLiteral atom = .ok (some (value, some width))) :
    evalExpr (fuel + 1) locals globals (.atom atom) =
      .ok (.bil width (.int (BitVec.ofInt width value)), locals, globals) := by
  rw [evalExpr]
  simp [ht, hf, hl, atomValue, parseInteger, bind, Except.bind]

theorem evalExpr_true (fuel : Nat) (locals : Locals) (globals : Globals) :
    evalExpr (fuel + 1) locals globals (.atom "true") = .ok (.bool true, locals, globals) := by
  have hl : readLiteral "true" = .ok none := readLiteral_literal_true
  rw [evalExpr]
  simp [atomValue, hl, bind, Except.bind]

theorem evalExpr_quote (fuel : Nat) (locals : Locals) (globals : Globals) (value : Sexp) :
    evalExpr (fuel + 1) locals globals (.list [.atom "quote", value]) = .ok (quotedValue value, locals, globals) := by
  rw [evalExpr]

theorem evalExpr_ite_true {fuel : Nat} {locals after : Locals} {globals later : Globals} {condition yes no : Sexp}
    (h : evalExpr fuel locals globals condition = .ok (.bool true, after, later)) :
    evalExpr (fuel + 1) locals globals (.list [.atom "if", condition, yes, no]) =
      evalExpr fuel after later yes := by
  rw [evalExpr]
  simp [h, bind, Except.bind, expectBool]

theorem evalExpr_ite_false {fuel : Nat} {locals after : Locals} {globals later : Globals} {condition yes no : Sexp}
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
      simp only [Assoc.get, List.lookup_cons, hne] at h ih
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
  simp [h, bound, bind, Except.bind]

/-- `setq` of any other name writes the global, which later lookups see. -/
theorem evalExpr_setq_global {fuel : Nat} {locals after : Locals} {globals later : Globals} {name : String}
    {form : Sexp} {value : LV} (h : evalExpr fuel locals globals form = .ok (value, after, later))
    (unbound : Assoc.get name after = none) :
    evalExpr (fuel + 1) locals globals (.list [.atom "setq", .atom name, form]) =
      .ok (value, after, Assoc.put name value later) := by
  rw [evalExpr]
  simp [h, unbound, bind, Except.bind]

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
  simp only [bind, Except.bind]
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
  simp only [List.foldlM_cons, expectBool, bind, Except.bind, Bool.not_true,
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
  simp only [List.foldlM_cons, expectBool, bind, Except.bind, Bool.false_eq_true, ↓reduceIte, h]
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
  simp only [evalPrimitive, any_symbolic_ints, mapM_expectInt, bind, Except.bind]
  rfl

theorem primitive_mul (values : List (BitVec 64)) :
    evalPrimitive "*" (values.map .int) = .ok (.int (values.foldl (· * ·) 1)) := by
  simp only [evalPrimitive, any_symbolic_ints, mapM_expectInt, bind, Except.bind]
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
  simp only [evalPrimitive, hs, this, bind, Except.bind, Bool.false_eq_true, ↓reduceIte]

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
  simp only [evalPrimitive, bitOperation, any_symbolic_ints, mapM_expectInt, bind, Except.bind]
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
    · obtain ⟨_, _, h⟩ := bind_ok_inv h
      split at h
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
    (hf : name ≠ "false") (hi : readLiteral name = .ok none) (hn : first ≠ name)
    (st : second ≠ "true") (sf : second ≠ "false") (si : readLiteral second = .ok none) :
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
    (ht : name ≠ "true") (hf : name ≠ "false") (hi : readLiteral name = .ok none) :
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
realize_eq_defs Bap.Primus.Semantics Bap.Primus.Semantics eval evalList evalSequence evalConditional apply evalCompiled
  evalCompiledList evalCompiledSequence evalCompiledConditional compileExp compileBindings
open_private Bap.Primus.Semantics Bap.Primus.Semantics lookup lookupState primitiveNames primitiveIndex
  atomValue expectBil expectNat truth condition extend binary widthOf assignRegister assign emit
  substitute contextMatches definitionBody compilablePrimitive applyPrimitive applyPrimitiveIndex valueOnly unaryNot
  shift cast loadMemory storeMemory leadingZeros checkLiterals checkForms checkBody
  wordWidth bindAssignable assignsLocal eval evalList evalSequence apply substituteList resolveDestination
  intrinsicResult macroExpansion macroCandidates bindMacro macroRest resolveMacro resolveFunction sameArity
  addDefinition expandBody define evalTopLevel floatOperation intrinsicCall
  evalConditional evalCompiled evalCompiledList evalCompiledSequence evalCompiledConditional
  compileExp compileSequence compileBindings freeze freezeBil resolveSymbol caseMatches quotedValue
  compileValue compileCallable compileFunction isSymbol symbolConcat symbolText intrinsicParams concatStep

open_private_as Bap.Primus.Semantics Bap.Primus.Semantics.compare primCompare
open_private_as Bap.Primus.Semantics Bap.Primus.Semantics.cast primCast

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
      simp
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
  simp [primCompare]

theorem compare_symbols_neq (context : Context) (left right : String) :
    primCompare context .neq [.symbol left, .symbol right] = .ok (.bool (decide (left ≠ right))) := by
  simp [primCompare]

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

mutual
  private theorem substitute_nil_aux : (form : Sexp) → substitute [] form = [form]
    | .atom _ => by simp [substitute, Assoc.get]
    | .list items => by rw [substitute, substituteList_nil_aux items]

  private theorem substituteList_nil_aux : (forms : List Sexp) → substituteList [] forms = forms
    | [] => by simp [substituteList]
    | form :: rest => by
      rw [substituteList, substitute_nil_aux form, substituteList_nil_aux rest]
      rfl
end

/-- Substituting nothing is the identity. -/
theorem substitute_nil (form : Sexp) : substitute [] form = [form] := substitute_nil_aux form

theorem substitute_atom (bindings : List (String × List Sexp)) (atom : String) (value : List Sexp)
    (h : Assoc.get atom bindings = some value) : substitute bindings (.atom atom) = value := by
  simp [substitute, h]

/-- A parameter inside of a list is spliced with its operands. -/
theorem substitute_list (bindings : List (String × List Sexp)) (items : List Sexp) :
    substitute bindings (.list items) = [.list (substituteList bindings items)] := by
  rw [substitute]

theorem substituteList_append (bindings : List (String × List Sexp)) (left right : List Sexp) :
    substituteList bindings (left ++ right) = substituteList bindings left ++ substituteList bindings right := by
  induction left with
  | nil => simp [substituteList]
  | cons form rest ih => simp [substituteList, ih, List.append_assoc]

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
theorem contextMatches_no_declare (context : Context) (body : List Sexp)
    (h : ∀ form ∈ body, ∀ rest, form ≠ .list (.atom "declare" :: rest)) : contextMatches context body = true := by
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
theorem readLiteral_not_char {atom : String} (h : ∀ rest, atom.toList ≠ '?' :: rest) :
    readLiteral atom = readNumeric atom atom.toList := by
  unfold readLiteral
  split
  · next heq => exact absurd heq (h _)
  · next heq => exact absurd heq (h _)
  · rfl

theorem readLiteral_symbol (atom : String) (h : startsNumeric atom.toList = false) (hq : atom.toList.head? ≠ some '?') :
    readLiteral atom = .ok none := by
  rw [readLiteral_not_char]
  · simp [readNumeric, h]
  · intro rest e
    simp [e] at hq

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
  have hbranch : ∀ rest, atom.toList ≠ '?' :: rest := by
    intro rest e
    rw [e] at hn
    simp [startsNumeric] at hn
  cases hz : parseZ atom.toList with
  | none =>
    refine Or.inr ⟨rfl, s!"malformed Primus literal {atom}", ?_⟩
    rw [readLiteral_not_char hbranch]
    simp only [readNumeric, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, span_no_colon hc, hz]
    try rfl
  | some value =>
    refine Or.inl ⟨value, rfl, ?_⟩
    rw [readLiteral_not_char hbranch]
    simp only [readNumeric, hn, Bool.not_true, Bool.false_eq_true, ↓reduceIte, span_no_colon hc, hz]
    try rfl

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
  have hne : ∀ other, readLiteral other = .ok none → other ≠ atom := by
    intro other ho he
    rw [he, h] at ho
    cases ho
  have ht : atom ≠ "true" := fun e => hne "true" (readLiteral_symbol _ (by decide +kernel) (by decide +kernel)) e.symm
  have hf : atom ≠ "false" := fun e => hne "false" (readLiteral_symbol _ (by decide +kernel) (by decide +kernel)) e.symm
  have hc : atom.startsWith ":" = false := by
    cases hs : atom.startsWith ":" with
    | false => rfl
    | true =>
      exfalso
      have hp : [':'] <+: atom.toList := by simpa using hs
      obtain ⟨rest, hrest⟩ := hp
      have hl : readLiteral atom = .ok none := by
        apply readLiteral_symbol
        · rw [← hrest]; simp [startsNumeric]
        · rw [← hrest]; simp
      rw [h] at hl
      cases hl
  rw [eval]
  simp [ht, hf, hc, h, bind, Except.bind]

theorem checkForms_rejects {forms : List Sexp} {form : Sexp} {e : String} (hm : form ∈ forms)
    (h : checkLiterals form = .error e) : ∃ e', checkForms forms = .error e' := by
  induction forms with
  | nil => simp at hm
  | cons head rest ih =>
    rw [checkForms]
    cases hh : checkLiterals head with
    | error e' => exact ⟨e', by simp [bind, Except.bind]⟩
    | ok _ =>
      rcases List.mem_cons.1 hm with rfl | hm'
      · simp [h] at hh
      · obtain ⟨e', he⟩ := ih hm'
        exact ⟨e', by simp [bind, Except.bind, he]⟩

/-- Definitions are checked when loaded, even if never called; their documentation strings are not. -/
theorem checkLiterals_definition (name : String) (params : List Sexp) (body : Sexp) (rest : List Sexp) (doc : String) :
    checkLiterals (.list (.atom "defun" :: .atom name :: .list params :: .atom doc :: body :: rest)) =
      checkForms (body :: rest) := by
  rw [checkLiterals, checkBody]

theorem checkLiterals_atom (atom : String) (e : String) (h : readLiteral atom = .error e) :
    checkLiterals (.atom atom) = .error e := by
  simp [checkLiterals, h, Except.map]

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
  simp [assign, assignRegister, primus_name_not_zero, h, bind, Except.bind, pure, Except.pure
]

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
  simp [hsym, ht, hf, hc, hl, bind, Except.bind]

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
    apply readLiteral_symbol <;> decide +kernel
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
    simp only
  have hassign : applyPrimitive context "set" [.register target width width, value] =
      .ok (value, [.move ⟨target, .imm width, 0, false⟩ exp]) := by
    simp [applyPrimitive, assign, assignRegister, hzero, hvalue, bind, Except.bind, pure, Except.pure]
  have hresult : intrinsicResult "set" = false := by decide +kernel
  have hdestination : resolveDestination after "set" [.register target width width, value] =
      [.register target width width, value] := rfl
  rw [eval]
  simp only [bind, Except.bind, hprimitive, hatom, hlist, hset, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    macroExpansion, macroCandidates]
  · rw [apply]
    simp only [bind, Except.bind, hassign, hdestination, hresult, Bool.false_eq_true, ↓reduceIte]
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

/-! ### Fuel monotonicity -/

/-- Fuel monotonicity of the semantics evaluator: more fuel never changes a success, in any of the mutually
recursive functions, of the interpreter and of the compiled code. -/
theorem eval_family_fuel_succ (fuel : Nat) :
    (∀ {locals context state forms r}, evalSequence fuel locals context state forms = .ok r →
      evalSequence (fuel + 1) locals context state forms = .ok r) ∧
    (∀ {locals context state forms r}, evalList fuel locals context state forms = .ok r →
      evalList (fuel + 1) locals context state forms = .ok r) ∧
    (∀ {locals context state test yes no r}, evalConditional fuel locals context state test yes no = .ok r →
      evalConditional (fuel + 1) locals context state test yes no = .ok r) ∧
    (∀ {context state value args r}, apply fuel context state value args = .ok r →
      apply (fuel + 1) context state value args = .ok r) ∧
    (∀ {locals context state form r}, eval fuel locals context state form = .ok r →
      eval (fuel + 1) locals context state form = .ok r) ∧
    (∀ {locals context state forms r}, evalCompiledSequence fuel locals context state forms = .ok r →
      evalCompiledSequence (fuel + 1) locals context state forms = .ok r) ∧
    (∀ {locals context state forms r}, evalCompiledList fuel locals context state forms = .ok r →
      evalCompiledList (fuel + 1) locals context state forms = .ok r) ∧
    (∀ {locals context state test yes no r}, evalCompiledConditional fuel locals context state test yes no = .ok r →
      evalCompiledConditional (fuel + 1) locals context state test yes no = .ok r) ∧
    (∀ {locals context state form r}, evalCompiled fuel locals context state form = .ok r →
      evalCompiled (fuel + 1) locals context state form = .ok r) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (rename_i h; first
      | (rw [evalSequence] at h; simp at h; done)
      | (rw [evalList] at h; simp at h; done)
      | (rw [evalConditional] at h; simp at h; done)
      | (rw [apply] at h; simp at h; done)
      | (rw [eval] at h; simp at h; done)
      | (rw [evalCompiledSequence] at h; simp at h; done)
      | (rw [evalCompiledList] at h; simp at h; done)
      | (rw [evalCompiledConditional] at h; simp at h; done)
      | (rw [evalCompiled] at h; simp at h; done))
  | succ fuel ih =>
    obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro locals context state forms r h
      rw [evalSequence.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · exact iEval h
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb => iSeq hb) h
    · intro locals context state forms r h
      rw [evalList.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iList hw) (fun _ _ hc => hc) hb) h
    · intro locals context state test yes no r h
      rw [evalConditional.eq_def] at h ⊢
      simp only at h ⊢
      refine bind_mono (fun _ hv => iEval hv) (fun _ _ hb => ?_) h
      refine bind_mono (fun _ hw => hw) (fun t _ hc => ?_) hb
      split at hc
      · exact iSeq hc
      · exact iSeq hc
      · refine bind_mono (fun _ hw => hw) (fun _ _ hd => ?_) hc
        refine bind_mono (fun _ hw => iSeq hw) (fun _ _ he => ?_) hd
        refine bind_mono (fun _ hw => iSeq hw) (fun _ _ hg => hg) he
    · intro context state value args r h
      rw [apply.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · split at h
        · exact iApply h
        · exact h
      · split at h
        · simp only [reduceCtorEq] at h
        · next hne => simp only [hne]; exact iSeq h
      · split at h
        · simp only [reduceCtorEq] at h
        · next hne => simp only [hne]; exact iCSeq h
      · exact h
      · exact h
    · intro locals context state form r h
      rw [eval.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      all_goals try simp only at ⊢
      all_goals first
        | exact h
        | exact iSeq h
        | exact iCond h
        | exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb => hb) h
        | skip
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iEval hw) (fun _ _ hc => hc) hb) h
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iEval hw) (fun _ _ hc => hc) hb) h
      · refine bind_mono (fun _ hv => iEval hv) (fun _ _ hb => ?_) h
        refine bind_mono (fun _ hw => hw) (fun _ _ hc => ?_) hb
        split at hc
        · exact hc
        · refine bind_mono (fun _ hw => hw) (fun _ _ hd => ?_) hc
          exact bind_mono (fun _ hw => iSeq hw) (fun _ _ he => he) hd
      · refine bind_mono (fun _ hv => ?_) (fun _ _ hb => iSeq hb) h
        refine foldlM_mono (fun _ _ _ hs => ?_) _ _ hv
        split at hs
        · exact bind_mono (fun _ hw => iEval hw) (fun _ _ hu => hu) hs
        · exact hs
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb =>
          bind_mono (fun _ hw => hw) (fun _ _ hc => iSeq hc) hb) h
      · refine bind_mono (fun _ hw => hw) (fun v _ hb => ?_) h
        have tail : ∀ {op : String} {ops : List Sexp} {e : Except String (Option (List Sexp))} {r : SV × State},
            (do
              let expansion ← e
              match expansion with
              | some body => evalSequence fuel locals context state body
              | none => do
                let __x ← eval fuel locals context state (Sexp.atom op)
                let __x_1 ← evalList fuel locals context __x.snd ops
                apply fuel context __x_1.snd __x.fst __x_1.fst) = .ok r →
            (do
              let expansion ← e
              match expansion with
              | some body => evalSequence (fuel + 1) locals context state body
              | none => do
                let __x ← eval (fuel + 1) locals context state (Sexp.atom op)
                let __x_1 ← evalList (fuel + 1) locals context __x.snd ops
                apply (fuel + 1) context __x_1.snd __x.fst __x_1.fst) = .ok r := by
          intro op ops e r ht
          refine bind_mono (fun _ hw => hw) (fun x _ hx => ?_) ht
          cases x with
          | some body => exact iSeq hx
          | none => exact bind_mono (fun _ hv => iEval hv) (fun _ _ hy =>
              bind_mono (fun _ hw => iList hw) (fun _ _ hz => iApply hz) hy) hx
        cases v
        case callable c =>
          dsimp only at hb ⊢
          split at hb
          · next hl => simp only [hl, ↓reduceIte]; exact tail hb
          · next hl => simp only [hl]; exact tail hb
        all_goals exact tail hb
      · exact bind_mono (fun _ hv => iEval hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iList hw) (fun _ _ hc => iApply hc) hb) h
    · intro locals context state forms r h
      rw [evalCompiledSequence.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · exact iComp h
      · exact bind_mono (fun _ hv => iComp hv) (fun _ _ hb => iCSeq hb) h
    · intro locals context state forms r h
      rw [evalCompiledList.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · exact bind_mono (fun _ hv => iComp hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iCList hw) (fun _ _ hc => hc) hb) h
    · intro locals context state test yes no r h
      rw [evalCompiledConditional.eq_def] at h ⊢
      simp only at h ⊢
      refine bind_mono (fun _ hv => iComp hv) (fun _ _ hb => ?_) h
      refine bind_mono (fun _ hw => hw) (fun t _ hc => ?_) hb
      split at hc
      · exact iCSeq hc
      · exact iCSeq hc
      · refine bind_mono (fun _ hw => hw) (fun _ _ hd => ?_) hc
        refine bind_mono (fun _ hw => iCSeq hw) (fun _ _ he => ?_) hd
        refine bind_mono (fun _ hw => iCSeq hw) (fun _ _ hg => hg) he
    · intro locals context state form r h
      rw [evalCompiled.eq_def] at h ⊢
      simp only at h ⊢
      split at h
      · exact h
      · exact h
      · exact h
      · exact bind_mono (fun _ hv => iCList hv) (fun _ _ hb => hb) h
      · exact bind_mono (fun _ hv => iComp hv) (fun _ _ hb =>
          bind_mono (fun _ hw => iCList hw) (fun _ _ hc => iApply hc) hb) h
      · exact iCCond h
      · exact bind_mono (fun _ hv => iComp hv) (fun _ _ hb => iComp hb) h
      · exact iCSeq h

theorem eval_fuel_mono {fuel extra : Nat} {locals : Locals} {context : Context} {state : State} {form : Sexp}
    {result : SV × State} (h : eval fuel locals context state form = .ok result) :
    eval (fuel + extra) locals context state form = .ok result := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact (eval_family_fuel_succ (fuel + extra)).2.2.2.2.1 ih

theorem evalCompiled_fuel_mono {fuel extra : Nat} {locals : Locals} {context : Context} {state : State} {form : CExp}
    {result : SV × State} (h : evalCompiled fuel locals context state form = .ok result) :
    evalCompiled (fuel + extra) locals context state form = .ok result := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact (eval_family_fuel_succ (fuel + extra)).2.2.2.2.2.2.2.2 ih


/-! ### Definitions selected by arity -/

/-- The number of arguments a function definition takes. -/
def functionArity : Callable → Option Nat
  | .function params .. | .compiled params .. => some params.length
  | _ => none

theorem resolveFunction_sound {count : Nat} {candidates : List Callable} {result : Callable}
    (h : resolveFunction count candidates = some result) :
    result ∈ candidates ∧ functionArity result = some count := by
  induction candidates with
  | nil => simp [resolveFunction] at h
  | cons head rest ih =>
    cases head <;> simp only [resolveFunction] at h
    case function p b e =>
      split at h
      · next hn =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_self, by simp [functionArity, hn]⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    case compiled p b e =>
      split at h
      · next hn =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_self, by simp [functionArity, hn]⟩
      · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩
    all_goals exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- A function of the call's arity is always found. -/
theorem resolveFunction_complete {count : Nat} {candidates : List Callable} {candidate : Callable}
    (hm : candidate ∈ candidates) (ha : functionArity candidate = some count) :
    ∃ result, resolveFunction count candidates = some result := by
  induction candidates with
  | nil => simp at hm
  | cons head rest ih =>
    rcases List.mem_cons.1 hm with rfl | hr
    · cases candidate <;> simp only [functionArity, Option.some.injEq, reduceCtorEq] at ha
      case function p b e => exact ⟨.function p b e, by simp [resolveFunction, ha]⟩
      case compiled p b e => exact ⟨.compiled p b e, by simp [resolveFunction, ha]⟩
    · obtain ⟨result, hres⟩ := ih hr
      cases head <;> simp only [resolveFunction]
      case function p b e =>
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, hres⟩
      case compiled p b e =>
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, hres⟩
      all_goals exact ⟨_, hres⟩

/-- No two definitions of a name are alternatives of the same call. -/
def DistinctArities (candidates : List Callable) : Prop :=
  candidates.Pairwise fun left right => sameArity left right = false

private theorem sameArity_of_arity {left right : Callable} {count : Nat} (hl : functionArity left = some count)
    (hr : functionArity right = some count) : sameArity left right = true := by
  cases left <;> cases right <;> simp_all [functionArity, sameArity]

/-- With distinct arities, the selected function is the only definition of the call's arity, so that
resolution does not depend on the order of the definitions. -/
theorem resolveFunction_unique {count : Nat} {candidates : List Callable} {result other : Callable}
    (hd : DistinctArities candidates) (h : resolveFunction count candidates = some result)
    (hm : other ∈ candidates) (ha : functionArity other = some count) : other = result := by
  have hs := resolveFunction_sound h
  have key : ∀ {items : List Callable}, DistinctArities items → ∀ {x y : Callable}, x ∈ items → y ∈ items →
      functionArity x = some count → functionArity y = some count → x = y := by
    intro items hitems
    induction items with
    | nil => intro x y hx; simp at hx
    | cons head rest ih =>
      intro x y hx hy hax hay
      obtain ⟨hhead, hrest⟩ := List.pairwise_cons.1 hitems
      rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
      · rfl
      · have := hhead y hy'
        rw [sameArity_of_arity hax hay] at this
        cases this
      · have := hhead x hx'
        rw [sameArity_of_arity hay hax] at this
        cases this
      · exact ih hrest hx' hy' hax hay
  exact key hd hm hs.1 ha hs.2

/-- A call of a name with several definitions is the call of the definition of its arity. -/
theorem apply_overloads {fuel : Nat} {context : Context} {state : State} {candidates : List Callable}
    {args : List SV} {result : Callable} (h : resolveFunction args.length candidates = some result) :
    apply (fuel + 1) context state (.callable (.overloads candidates)) args =
      apply fuel context state (.callable result) args := by
  rw [apply]
  simp only [h]

/-- A call with no definition of its arity is an error, with any fuel. -/
theorem apply_overloads_none {fuel : Nat} {context : Context} {state : State} {candidates : List Callable}
    {args : List SV} (h : resolveFunction args.length candidates = none) :
    ∃ error, apply fuel context state (.callable (.overloads candidates)) args = .error error := by
  cases fuel with
  | zero => exact ⟨_, by rw [apply]⟩
  | succ fuel => exact ⟨"no Primus function definition accepts this number of arguments", by rw [apply]; simp only [h]⟩

/-- `take_rest` accepts exactly the calls with as many operands as parameters, and with more when there is
a last parameter to take them. -/
theorem bindMacro_some_iff (params : List String) (operands : List Sexp) :
    (∃ bindings, bindMacro params operands = some bindings) ↔
      params.length = operands.length ∨ (params ≠ [] ∧ params.length < operands.length) := by
  induction params generalizing operands with
  | nil =>
    cases operands with
    | nil => simp [bindMacro]
    | cons o os => simp [bindMacro]
  | cons p ps ih =>
    cases operands with
    | nil => simp [bindMacro]
    | cons o os =>
      cases ps with
      | nil =>
        cases os with
        | nil => simp [bindMacro]
        | cons o' os' => simp [bindMacro]
      | cons p' ps' =>
        have hstep : bindMacro (p :: p' :: ps') (o :: os) =
            ((p, [o]) :: ·) <$> bindMacro (p' :: ps') os := by rw [bindMacro]; simp
        have := ih os
        simp only [List.length_cons, ne_eq, reduceCtorEq, not_false_eq_true, true_and] at this ⊢
        rw [hstep]
        constructor
        · rintro ⟨b, hb⟩
          cases hk : bindMacro (p' :: ps') os with
          | none => simp [hk] at hb
          | some bs =>
            rcases this.1 ⟨bs, hk⟩ with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
        · intro hc
          have hc' : ps'.length + 1 = os.length ∨ ps'.length + 1 < os.length := by
            rcases hc with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          obtain ⟨bs, hk⟩ := this.2 hc'
          exact ⟨(p, [o]) :: bs, by simp [hk]⟩

/-- How many operands the last parameter of a successful binding takes. -/
theorem macroRest_bindMacro {params : List String} {operands : List Sexp} {bindings : List (String × List Sexp)}
    (h : bindMacro params operands = some bindings) :
    macroRest bindings = if params = [] then 0 else operands.length + 1 - params.length := by
  induction params generalizing operands bindings with
  | nil =>
    cases operands with
    | nil => simp [bindMacro] at h; subst h; simp [macroRest]
    | cons o os => simp [bindMacro] at h
  | cons p ps ih =>
    cases operands with
    | nil => simp [bindMacro] at h
    | cons o os =>
      cases ps with
      | nil =>
        cases os with
        | nil =>
          simp [bindMacro] at h
          subst h
          simp [macroRest]
        | cons o' os' =>
          simp [bindMacro] at h
          subst h
          simp [macroRest]
      | cons p' ps' =>
        have hstep : bindMacro (p :: p' :: ps') (o :: os) =
            ((p, [o]) :: ·) <$> bindMacro (p' :: ps') os := by rw [bindMacro]; simp
        rw [hstep] at h
        cases hk : bindMacro (p' :: ps') os with
        | none => simp [hk] at h
        | some bs =>
          simp [hk] at h
          subst h
          have hrest := ih hk
          have hcount := (bindMacro_some_iff (p' :: ps') os).1 ⟨bs, hk⟩
          simp only [List.length_cons, reduceCtorEq, ite_false] at hrest hcount
          have hlast : macroRest ((p, [o]) :: bs) = macroRest bs := by
            cases bs with
            | nil =>
              simp [macroRest] at hrest
              simp at hcount
              omega
            | cons b bt => simp [macroRest]
          rw [hlast, hrest]
          simp

/-- A macro that accepts the operands is always resolved. -/
theorem resolveMacro_complete {operands : List Sexp} {candidates : List Callable} {params : List String}
    {body : List Sexp} {bindings : List (String × List Sexp)} (hm : Callable.macro params body ∈ candidates)
    (hb : bindMacro params operands = some bindings) : (resolveMacro operands candidates).isSome = true := by
  induction candidates with
  | nil => simp at hm
  | cons head tail ih =>
    cases head with
    | «macro» params' body' =>
      simp only [resolveMacro]
      rcases List.mem_cons.1 hm with he | hm'
      · simp only [Callable.macro.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        cases hr : resolveMacro operands tail with
        | none => simp [hb]
        | some other => simp only [hb]; split <;> rfl
      · have := ih hm'
        cases hr : resolveMacro operands tail with
        | none => simp [hr] at this
        | some other =>
          cases bindMacro params' operands with
          | none => rfl
          | some bs => simp only; split <;> rfl
    | _ =>
      simp only [resolveMacro]
      rcases List.mem_cons.1 hm with he | hm'
      · simp at he
      · exact ih hm'

/-- The macro definition a call selects: it is a definition of the name, it accepts the operands, and no
other definition that accepts them has fewer operands in the last parameter. -/
theorem resolveMacro_sound {operands : List Sexp} {candidates : List Callable} {rest : Nat} {body : List Sexp}
    {bindings : List (String × List Sexp)} (h : resolveMacro operands candidates = some (rest, body, bindings)) :
    (∃ params, Callable.macro params body ∈ candidates ∧ bindMacro params operands = some bindings) ∧
      rest = macroRest bindings ∧
      ∀ params other otherBindings, Callable.macro params other ∈ candidates →
        bindMacro params operands = some otherBindings → rest ≤ macroRest otherBindings := by
  induction candidates generalizing rest body bindings with
  | nil => simp [resolveMacro] at h
  | cons head tail ih =>
    cases head with
    | «macro» params' body' =>
      simp only [resolveMacro] at h
      split at h
      · rename_i bs other hb hr
        obtain ⟨r, b, os⟩ := other
        obtain ⟨⟨pp, hpp, hpb⟩, hre, hmin⟩ := ih hr
        split at h
        · next hlt =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨⟨pp, List.mem_cons_of_mem _ hpp, hpb⟩, hre, ?_⟩
          intro params other obs hm hob
          rcases List.mem_cons.1 hm with he | hm'
          · simp only [Callable.macro.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            rw [hb] at hob
            simp only [Option.some.injEq] at hob
            subst hob
            exact Nat.le_of_lt hlt
          · exact hmin _ _ _ hm' hob
        · next hlt =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine ⟨⟨params', List.mem_cons_self, hb⟩, rfl, ?_⟩
          intro params other obs hm hob
          rcases List.mem_cons.1 hm with he | hm'
          · simp only [Callable.macro.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            rw [hb] at hob
            simp only [Option.some.injEq] at hob
            subst hob
            exact Nat.le_refl _
          · exact Nat.le_trans (Nat.le_of_not_lt hlt) (hre ▸ hmin _ _ _ hm' hob)
      · rename_i bs hb hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨⟨params', List.mem_cons_self, hb⟩, rfl, ?_⟩
        intro params other obs hm hob
        rcases List.mem_cons.1 hm with he | hm'
        · simp only [Callable.macro.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          rw [hb] at hob
          simp only [Option.some.injEq] at hob
          subst hob
          exact Nat.le_refl _
        · have hsome := resolveMacro_complete hm' hob
          simp [hr] at hsome
      · rename_i o hb
        obtain ⟨⟨pp, hpp, hpb⟩, hre, hmin⟩ := ih h
        refine ⟨⟨pp, List.mem_cons_of_mem _ hpp, hpb⟩, hre, ?_⟩
        intro params other obs hm hob
        rcases List.mem_cons.1 hm with he | hm'
        · simp only [Callable.macro.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          simp [hob] at hb
        · exact hmin _ _ _ hm' hob
    | _ =>
      simp only [resolveMacro] at h
      obtain ⟨⟨pp, hpp, hpb⟩, hre, hmin⟩ := ih h
      refine ⟨⟨pp, List.mem_cons_of_mem _ hpp, hpb⟩, hre, ?_⟩
      intro params other obs hm hob
      rcases List.mem_cons.1 hm with he | hm'
      · simp at he
      · exact hmin _ _ _ hm' hob

/-- Two macro definitions with different numbers of parameters that accept the same operands take a different
number in the last parameter, so with distinct arities exactly one has the least. -/
theorem resolveMacro_unique {operands : List Sexp} {candidates : List Callable} {rest : Nat} {body other : List Sexp}
    {bindings otherBindings : List (String × List Sexp)} {params : List String}
    (hd : DistinctArities candidates) (h : resolveMacro operands candidates = some (rest, body, bindings))
    (hm : Callable.macro params other ∈ candidates) (hb : bindMacro params operands = some otherBindings)
    (hleast : macroRest otherBindings ≤ rest) : other = body ∧ otherBindings = bindings := by
  obtain ⟨⟨pp, hpp, hpb⟩, hre, hmin⟩ := resolveMacro_sound h
  have hlen : params.length = pp.length := by
    have h1 := macroRest_bindMacro hb
    have h2 := macroRest_bindMacro hpb
    have hc1 := (bindMacro_some_iff _ _).1 ⟨_, hb⟩
    have hc2 := (bindMacro_some_iff _ _).1 ⟨_, hpb⟩
    have hmin' := hmin _ _ _ hm hb
    have heq : macroRest otherBindings = macroRest bindings := by omega
    rw [heq, h2] at h1
    cases params with
    | nil =>
      cases pp with
      | nil => rfl
      | cons p ps =>
        simp at h1 hc1 hc2
        omega
    | cons q qs =>
      cases pp with
      | nil =>
        simp at h1 hc1 hc2
        omega
      | cons p ps =>
        simp at h1 hc1 hc2 ⊢
        omega
  have hsame : ∀ {items : List Callable}, DistinctArities items → Callable.macro params other ∈ items →
      Callable.macro pp body ∈ items → other = body ∧ params = pp := by
    intro items hitems
    induction items with
    | nil => intro hx; simp at hx
    | cons head rest ih =>
      intro hx hy
      obtain ⟨hhead, hrest⟩ := List.pairwise_cons.1 hitems
      rcases List.mem_cons.1 hx with he | hx' <;> rcases List.mem_cons.1 hy with he' | hy'
      · have he2 := he.trans he'.symm
        simp only [Callable.macro.injEq] at he2
        exact ⟨he2.2, he2.1⟩
      · have := hhead _ hy'
        rw [← he] at this
        simp [sameArity, hlen] at this
      · have := hhead _ hx'
        rw [← he'] at this
        simp [sameArity, hlen] at this
      · exact ih hrest hx' hy'
  obtain ⟨hbody, hparams⟩ := hsame hd hm hpp
  subst hbody hparams
  rw [hb] at hpb
  simp only [Option.some.injEq] at hpb
  exact ⟨rfl, hpb⟩

private theorem addDefinition_overloads (callable : Callable) (candidates : List Callable) :
    addDefinition callable (some (.callable (.overloads candidates))) =
      if candidates.filter (fun other => !sameArity callable other) = [] then callable
      else .overloads (callable :: candidates.filter fun other => !sameArity callable other) := by
  simp only [addDefinition]
  generalize candidates.filter (fun other => !sameArity callable other) = others
  cases others <;> simp

/-- Adding a definition keeps the arities of a name distinct, and it replaces only the definition that takes
the same calls. -/
theorem addDefinition_distinct {callable : Callable} {candidates result : List Callable}
    (hd : DistinctArities candidates)
    (h : addDefinition callable (some (.callable (.overloads candidates))) = .overloads result)
    (hnot : ∀ inner, callable ≠ .overloads inner) : DistinctArities result := by
  rw [addDefinition_overloads] at h
  split at h
  · exact absurd h (hnot _)
  · simp only [Callable.overloads.injEq] at h
    subst h
    refine List.pairwise_cons.2 ⟨?_, hd.filter _⟩
    intro other hm
    simpa using (List.mem_filter.1 hm).2

/-- The definition just added is the one a call of its arity selects. -/
theorem resolveFunction_addDefinition {callable : Callable} {candidates result : List Callable} {count : Nat}
    (ha : functionArity callable = some count)
    (h : addDefinition callable (some (.callable (.overloads candidates))) = .overloads result) :
    resolveFunction count result = some callable := by
  rw [addDefinition_overloads] at h
  split at h
  · subst h
    simp [functionArity] at ha
  · simp only [Callable.overloads.injEq] at h
    subst h
    cases callable <;> simp_all [functionArity, resolveFunction]

/-- A definition of another arity stays selectable after adding one. -/
theorem addDefinition_keeps {callable other : Callable} {candidates result : List Callable}
    (hm : other ∈ candidates) (hne : sameArity callable other = false)
    (h : addDefinition callable (some (.callable (.overloads candidates))) = .overloads result) :
    other ∈ result := by
  rw [addDefinition_overloads] at h
  have hin : other ∈ candidates.filter fun other => !sameArity callable other := by simp [hm, hne]
  split at h
  · next he => rw [he] at hin; simp at hin
  · simp only [Callable.overloads.injEq] at h
    subst h
    exact List.mem_cons_of_mem _ hin

/-- The heads with a meaning of their own in the evaluator. -/
def specialHead (head : String) : Bool :=
  head = "quote" || head = "sizeof" || head = "assert-msg" || head = "replicate" || head = "core:replicate" ||
    head = "clz" || head = "if" || head = "when" || head = "unless" || head = "progn" || head = "prog" ||
    head = "while" || head = "error" || head = "msg" || head = "let" || head = "lambda" || head = "case"

/-- A call of an ordinary name: a macro is expanded, anything else is evaluated with its arguments. -/
theorem eval_operator {operator : String} {operands : List Sexp} (fuel : Nat) (locals : Locals) (context : Context)
    (state : State) (hs : specialHead operator = false) :
    eval (fuel + 1) locals context state (.list (.atom operator :: operands)) = (do
      let expansion ← match ← lookupState operator locals state with
        | .callable callable =>
          if (Assoc.get operator locals).isSome then .ok none else macroExpansion callable operands
        | _ => .ok none
      match expansion with
      | some expanded => evalSequence fuel locals context state expanded
      | none =>
        let (callable, state) ← eval fuel locals context state (.atom operator)
        let (args, state) ← evalList fuel locals context state operands
        apply fuel context state callable args) := by
  simp only [specialHead, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hs
  rw [eval]
  · rfl
  all_goals (intros; simp_all)

/-! ### Soundness for arithmetic -/

/-- The operators that make one BIL operator of their operands. -/
def arithOp : String → Option Bil.BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div | "s/" => some .sdiv
  | "mod" => some .rem | "signed-mod" => some .smod | "signed-rem" => some .srem
  | "logand" | "bitand" => some .and | "logor" | "bitor" => some .or | "logxor" | "bitxor" => some .xor
  | _ => none

/-- The primitives that load, with the bits they load. -/
def loadBits (context : Context) : String → Option Nat
  | "load-byte" => some 8
  | "load-hword" => some 32
  | "load-word" => some context.bits
  | _ => none

/-- What an arithmetic form computes under an environment of BIL. A load is what the interpreter loads, wherever its
address evaluates to the address that the form denotes. -/
inductive Denotes (env : Bil.Env) (context : Context) (locals : Locals) : Sexp → (Σ width, BitVec width) → Prop where
  | number {atom : String} {value : Int} (ht : atom ≠ "true") (hf : atom ≠ "false") (hc : atom.startsWith ":" = false)
      (h : readLiteral atom = .ok (some (value, none))) :
      Denotes env context locals (.atom atom) ⟨context.bits, BitVec.ofNat context.bits (BitVec.ofInt 64 value).toNat⟩
  | typed {atom : String} {value : Int} {width : Nat} (ht : atom ≠ "true") (hf : atom ≠ "false")
      (hc : atom.startsWith ":" = false) (h : readLiteral atom = .ok (some (value, some width))) :
      Denotes env context locals (.atom atom) ⟨width, BitVec.ofInt width value⟩
  | bound {name : String} {value : SV} {width : Nat} {exp : Bil.Exp} {bits : BitVec width} (ht : name ≠ "true")
      (hf : name ≠ "false") (hc : name.startsWith ":" = false) (hl : readLiteral name = .ok none)
      (hv : Assoc.get name locals = some value) (he : expectBil context value = .ok (width, exp))
      (hb : Bil.evalExp env exp = .ok (.bits bits)) :
      Denotes env context locals (.atom name) ⟨width, bits⟩
  | binary {op : String} {bop : Bil.BinOp} {left right : Sexp} {w₁ w₂ : Nat} {x : BitVec w₁} {y : BitVec w₂}
      {result : BitVec (max w₁ w₂)} (hop : arithOp op = some bop) (hl : Denotes env context locals left ⟨w₁, x⟩)
      (hr : Denotes env context locals right ⟨w₂, y⟩)
      (hb : Bil.evalBin bop ⟨max w₁ w₂, Word.unsigned (max w₁ w₂) x⟩ ⟨max w₁ w₂, Word.unsigned (max w₁ w₂) y⟩ =
        .ok (.bits result)) :
      Denotes env context locals (.list [.atom op, left, right]) ⟨max w₁ w₂, result⟩
  | load {op : String} {bits : Nat} {address : Sexp} {location : BitVec context.bits} {result : BitVec bits}
      (hop : loadBits context op = some bits) (hbyte : bits % 8 = 0) (ha : Denotes env context locals address ⟨context.bits, location⟩)
      (hr : ∀ exp, Bil.evalExp env exp = .ok (.bits location) →
        Bil.evalExp env (.load (.var context.memory) exp context.endian (bits / 8)) = .ok (.bits result)) :
      Denotes env context locals (.list [.atom op, address]) ⟨bits, result⟩

private theorem loadBits_props {context : Context} {op : String} {bits : Nat} (h : loadBits context op = some bits) :
    specialHead op = false ∧ readLiteral op = .ok none ∧ op ≠ "true" ∧ op ≠ "false" ∧ op.startsWith ":" = false ∧
    op.startsWith "core:" = false ∧ op ≠ "replicate" ∧ op ∈ primitiveNames ∧ intrinsicResult op = false ∧
    (∀ (state : State) (a : SV), resolveDestination state op [a] = [a] ∧
        applyPrimitive context op [a] = (loadMemory context bits [a]) >>= valueOnly) := by
  unfold loadBits at h
  have hsym : ∀ {a : String}, a.toList.head? ≠ some '?' → startsNumeric a.toList = false → readLiteral a = .ok none :=
    fun h1 h2 => readLiteral_symbol _ h2 h1
  have hdest : ∀ (o : String) (state : State) (args : List SV),
      (o = "set" ∨ o = "set$" ∨ o = "set-symbol-value" ∨ o = "unquote") = False → resolveDestination state o args = args := by
    intro o state args ho
    unfold resolveDestination
    split
    · simp at ho
      simp [ho]
    · rfl
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    refine ⟨by decide +kernel, hsym (by decide +kernel) (by decide +kernel), by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ?_⟩ <;>
    (intro state a
     refine ⟨hdest _ _ _ (by simp), ?_⟩
     rfl)

private theorem arithOp_props {op : String} {bop : Bil.BinOp} (h : arithOp op = some bop) :
    specialHead op = false ∧ readLiteral op = .ok none ∧ op ≠ "true" ∧ op ≠ "false" ∧ op.startsWith ":" = false ∧
    op.startsWith "core:" = false ∧ op ≠ "replicate" ∧ op ∈ primitiveNames ∧ intrinsicResult op = false ∧
    (∀ (context : Context) (state : State) (a b : SV),
      resolveDestination state op [a, b] = [a, b] ∧
        applyPrimitive context op [a, b] = (binary context bop [a, b]) >>= valueOnly) := by
  unfold arithOp at h
  have hsym : ∀ {a : String}, a.toList.head? ≠ some '?' → startsNumeric a.toList = false → readLiteral a = .ok none :=
    fun h1 h2 => readLiteral_symbol _ h2 h1
  have hdest : ∀ (o : String) (state : State) (args : List SV),
      (o = "set" ∨ o = "set$" ∨ o = "set-symbol-value" ∨ o = "unquote") = False → resolveDestination state o args = args := by
    intro o state args ho
    unfold resolveDestination
    split
    · simp at ho
      simp [ho]
    · rfl
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    refine ⟨by decide +kernel, hsym (by decide +kernel) (by decide +kernel), by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide, by decide +kernel, ?_⟩ <;>
    (intro context state a b
     refine ⟨hdest _ _ _ (by simp), ?_⟩
     rfl)

private theorem binary_two {context : Context} {bop : Bil.BinOp} {a b : SV} {w₁ w₂ : Nat} {e₁ e₂ : Bil.Exp}
    (ha : expectBil context a = .ok (w₁, e₁)) (hb : expectBil context b = .ok (w₂, e₂)) :
    binary context bop [a, b] =
      .ok (.bil (max w₁ w₂) (.bin bop (.cast .unsigned (max w₁ w₂) e₁) (.cast .unsigned (max w₁ w₂) e₂))) := by
  simp [binary, List.mapM_cons, ha, hb, bind, Except.bind, pure, Except.pure, extend, List.foldlM]

private theorem emit_nil (state : State) : emit state [] = state := by
  cases state
  simp [emit]

/-- Nothing shadows an arithmetic primitive. -/
def VisiblePrimitives (locals : Locals) (state : State) : Prop :=
  (∀ op bop, arithOp op = some bop →
    Assoc.get op locals = none ∧ state.operations.get? op = none ∧ Assoc.get op state.globals = none) ∧
  ∀ op, op = "load-byte" ∨ op = "load-hword" ∨ op = "load-word" →
    Assoc.get op locals = none ∧ state.operations.get? op = none ∧ Assoc.get op state.globals = none

/-- Evaluating an arithmetic form makes no code, and its value denotes in BIL what the form computes, at any
fuel that suffices. -/
theorem eval_arithmetic_sound {env : Bil.Env} {context : Context} {locals : Locals} {form : Sexp}
    {result : Σ width, BitVec width} (hd : Denotes env context locals form result) :
    ∀ {fuel : Nat} {state after : State} {value : SV}, VisiblePrimitives locals state →
      eval fuel locals context state form = .ok (value, after) →
      after = state ∧ ∃ exp, expectBil context value = .ok (result.1, exp) ∧
        Bil.evalExp env exp = .ok (.bits result.2) := by
  induction hd with
  | number ht hf hc h =>
    intro fuel state after value _ he
    cases fuel with
    | zero => rw [eval] at he; simp at he
    | succ fuel =>
      rw [eval] at he
      simp [ht, hf, hc, h, bind, Except.bind, atomValue, parseInteger] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, _, rfl, rfl⟩
  | typed ht hf hc h =>
    intro fuel state after value _ he
    cases fuel with
    | zero => rw [eval] at he; simp at he
    | succ fuel =>
      rw [eval] at he
      simp [ht, hf, hc, h, bind, Except.bind, atomValue, parseInteger] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, _, rfl, rfl⟩
  | bound ht hf hc hl hv he hb =>
    intro fuel state after value _ hev
    cases fuel with
    | zero => rw [eval] at hev; simp at hev
    | succ fuel =>
      rw [eval] at hev
      simp [ht, hf, hc, hl, hv, bind, Except.bind, lookupState] at hev
      obtain ⟨rfl, rfl⟩ := hev
      exact ⟨rfl, _, he, hb⟩
  | @binary op bop left right w₁ w₂ x y r hop _ _ hb ihl ihr =>
    intro fuel state after value hvis hev
    obtain ⟨hs, hlit, ht, hf, hcolon, hcore, hrep, hmem, hint, hprim⟩ := arithOp_props hop
    obtain ⟨hloc, hopn, hglob⟩ := hvis.1 op bop hop
    have hlookup : lookupState op locals state = .ok (.callable (.primitive op)) := by
      have hopn' : state.operations[op]? = none := by simpa using hopn
      simp [lookupState, hloc, hopn', hglob, hcore, hrep, hmem]
    cases fuel with
    | zero => rw [eval] at hev; simp at hev
    | succ fuel =>
      rw [eval_operator fuel locals context state hs] at hev
      simp only [hlookup, hloc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, macroExpansion, macroCandidates,
        bind, Except.bind] at hev
      cases fuel with
      | zero => rw [eval] at hev; simp at hev
      | succ fuel =>
        have hatom : eval (fuel + 1) locals context state (.atom op) = .ok (.callable (.primitive op), state) := by
          rw [eval]
          simp [ht, hf, hcolon, hlit, hlookup, bind, Except.bind]
        simp only [hatom] at hev
        rw [evalList.eq_def] at hev
        simp only [bind, Except.bind] at hev
        cases hA : eval fuel locals context state left with
        | error e => simp [hA] at hev
        | ok ra =>
          obtain ⟨va, sa⟩ := ra
          obtain ⟨hsa, ea, hea, hxa⟩ := ihl hvis hA
          obtain rfl : state = sa := hsa.symm
          simp only [hA] at hev
          rw [evalList.eq_def] at hev
          cases fuel with
          | zero => simp at hev
          | succ fuel =>
            simp only [bind, Except.bind] at hev
            cases hB : eval fuel locals context state right with
            | error e => simp [hB] at hev
            | ok rb =>
              obtain ⟨vb, sb⟩ := rb
              obtain ⟨hsb, eb, heb, hyb⟩ := ihr hvis hB
              obtain rfl : state = sb := hsb.symm
              simp only [hB] at hev
              rw [evalList.eq_def] at hev
              cases fuel with
              | zero => simp at hev
              | succ fuel =>
                simp only at hev
                rw [apply] at hev
                obtain ⟨hdest, happ⟩ := hprim context state va vb
                simp only [bind, Except.bind, hdest, happ, binary_two hea heb, valueOnly, pure, Except.pure, hint,
                  Bool.false_eq_true, ↓reduceIte, emit_nil, Except.ok.injEq, Prod.mk.injEq] at hev
                obtain ⟨rfl, hst⟩ := hev
                refine ⟨hst.symm, _, rfl, ?_⟩
                simp only [Bil.evalExp, hxa, hyb, bind, Except.bind, Value.asBits]
                exact hb
  | @load op bits address location result hop hbyte _ hr ih =>
    intro fuel state after value hvis hev
    obtain ⟨hs, hlit, ht, hf, hcolon, hcore, hrep, hmem, hint, hprim⟩ := loadBits_props hop
    have hname : op = "load-byte" ∨ op = "load-hword" ∨ op = "load-word" := by
      unfold loadBits at hop
      split at hop <;> simp_all
    obtain ⟨hloc, hopn, hglob⟩ := hvis.2 op hname
    have hlookup : lookupState op locals state = .ok (.callable (.primitive op)) := by
      have hopn' : state.operations[op]? = none := by simpa using hopn
      simp [lookupState, hloc, hopn', hglob, hcore, hrep, hmem]
    cases fuel with
    | zero => rw [eval] at hev; simp at hev
    | succ fuel =>
      rw [eval_operator fuel locals context state hs] at hev
      simp only [hlookup, hloc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, macroExpansion, macroCandidates,
        bind, Except.bind] at hev
      cases fuel with
      | zero => rw [eval] at hev; simp at hev
      | succ fuel =>
        have hatom : eval (fuel + 1) locals context state (.atom op) = .ok (.callable (.primitive op), state) := by
          rw [eval]
          simp [ht, hf, hcolon, hlit, hlookup, bind, Except.bind]
        simp only [hatom] at hev
        rw [evalList.eq_def] at hev
        simp only [bind, Except.bind] at hev
        cases hA : eval fuel locals context state address with
        | error e => simp [hA] at hev
        | ok ra =>
          obtain ⟨va, sa⟩ := ra
          obtain ⟨hsa, ea, hea, hxa⟩ := ih hvis hA
          obtain rfl : state = sa := hsa.symm
          simp only [hA] at hev
          rw [evalList.eq_def] at hev
          cases fuel with
          | zero => simp at hev
          | succ fuel =>
            simp only at hev
            rw [apply] at hev
            obtain ⟨hdest, happ⟩ := hprim state va
            have hload : loadMemory context bits [va] =
                .ok (.bil bits (.load (.var context.memory) ea context.endian (bits / 8))) := by
              simp [loadMemory, hbyte, hea, bind, Except.bind]
            simp only [bind, Except.bind, hdest, happ, hload, valueOnly, pure, Except.pure, hint,
              Bool.false_eq_true, ↓reduceIte, emit_nil, Except.ok.injEq, Prod.mk.injEq] at hev
            obtain ⟨rfl, hst⟩ := hev
            exact ⟨hst.symm, _, rfl, hr _ hxa⟩


/-! ### Evaluation keeps the definitions -/

/-- Only code and temporaries change during evaluation. -/
def Keeps (first second : State) : Prop :=
  second.globals = first.globals ∧ second.operations = first.operations

theorem Keeps.refl (state : State) : Keeps state state := ⟨rfl, rfl⟩

theorem Keeps.trans {a b c : State} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

private theorem keeps_emit (state : State) (code : Bil.Program) : Keeps state (emit state code) := ⟨rfl, rfl⟩

private theorem keeps_freezeBil (state : State) (width : Nat) (exp : Bil.Exp) :
    Keeps state (freezeBil state width exp).2 := by
  unfold freezeBil
  split <;> exact ⟨rfl, rfl⟩

private theorem keeps_freeze (context : Context) (state : State) (value : SV) :
    Keeps state (freeze context state value).2 := by
  unfold freeze
  split
  · exact keeps_freezeBil _ _ _
  · split
    · exact keeps_freezeBil _ _ _
    · exact Keeps.refl _
  · exact Keeps.refl _

private theorem keeps_bindAssignable {context : Context} {state after : State} {value result : SV}
    (h : bindAssignable context state value = .ok (result, after)) : Keeps state after := by
  unfold bindAssignable at h
  obtain ⟨_, _, h⟩ := bind_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact ⟨rfl, rfl⟩

private theorem foldl_state_inv {α β : Type} {P : α → Prop} {f : α → β → Except String α}
    (hs : ∀ cur item r, P cur → f cur item = .ok r → P r) (items : List β) (init : α) {r : α}
    (hi : P init) (h : items.foldlM f init = .ok r) : P r := by
  induction items generalizing init with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hi
  | cons head rest ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨mid, hm, h⟩ := bind_ok h
    exact ih mid (hs _ _ _ hi hm) h

/-- Evaluating forms and compiled code never changes the definitions: only a source file does. -/
theorem eval_family_keeps (fuel : Nat) :
    (∀ {locals context state forms value after}, evalSequence fuel locals context state forms = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state forms value after}, evalList fuel locals context state forms = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state test yes no value after}, evalConditional fuel locals context state test yes no = .ok (value, after) →
      Keeps state after) ∧
    (∀ {context state callable args value after}, apply fuel context state callable args = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state form value after}, eval fuel locals context state form = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state forms value after}, evalCompiledSequence fuel locals context state forms = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state forms value after}, evalCompiledList fuel locals context state forms = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state test yes no value after}, evalCompiledConditional fuel locals context state test yes no = .ok (value, after) →
      Keeps state after) ∧
    (∀ {locals context state form value after}, evalCompiled fuel locals context state form = .ok (value, after) →
      Keeps state after) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> (rename_i h; first
      | (rw [evalSequence] at h; simp at h; done)
      | (rw [evalList] at h; simp at h; done)
      | (rw [evalConditional] at h; simp at h; done)
      | (rw [apply] at h; simp at h; done)
      | (rw [eval] at h; simp at h; done)
      | (rw [evalCompiledSequence] at h; simp at h; done)
      | (rw [evalCompiledList] at h; simp at h; done)
      | (rw [evalCompiledConditional] at h; simp at h; done)
      | (rw [evalCompiled] at h; simp at h; done))
  | succ fuel ih =>
    obtain ⟨iSeq, iList, iCond, iApply, iEval, iCSeq, iCList, iCCond, iComp⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro locals context state forms value after h
      rw [evalSequence.eq_def] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · exact iEval h
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        exact (iEval h1).trans (iSeq h2)
    · intro locals context state forms value after h
      rw [evalList.eq_def] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h3, h4⟩ := bind_ok h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h4
        obtain ⟨_, rfl⟩ := h4
        exact (iEval h1).trans (iList h3)
    · intro locals context state test yes no value after h
      rw [evalConditional.eq_def] at h
      simp only at h
      obtain ⟨⟨t, s⟩, h1, h2⟩ := bind_ok h
      have hk1 := iEval h1
      obtain ⟨tv, _, h3⟩ := bind_ok h2
      split at h3
      · exact hk1.trans (iSeq h3)
      · exact hk1.trans (iSeq h3)
      · obtain ⟨_, _, h4⟩ := bind_ok h3
        obtain ⟨⟨_, ys⟩, h5, h6⟩ := bind_ok h4
        obtain ⟨⟨_, ns⟩, h7, h8⟩ := bind_ok h6
        split at h8
        · obtain ⟨_, _, h9⟩ := bind_ok h8
          obtain ⟨_, _, h10⟩ := bind_ok h9
          simp only [Except.ok.injEq, Prod.mk.injEq] at h10
          obtain ⟨_, rfl⟩ := h10
          exact hk1
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h8
          obtain ⟨_, rfl⟩ := h8
          exact hk1
    · intro context state callable args value after h
      rw [apply.eq_def] at h
      simp only at h
      split at h
      · obtain ⟨⟨v, code⟩, _, h2⟩ := bind_ok h
        simp only at h2
        split at h2
        · simp only [Except.ok.injEq] at h2
          have := keeps_freeze context (emit state code) v
          rw [h2] at this
          exact (keeps_emit _ _).trans this
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h2
          obtain ⟨_, rfl⟩ := h2
          exact keeps_emit _ _
      · split at h
        · exact iApply h
        · simp at h
      · split at h
        · simp at h
        · exact iSeq h
      · split at h
        · simp at h
        · exact iCSeq h
      · simp at h
      · simp at h
    · intro locals context state form value after h
      rw [eval.eq_def] at h
      simp only at h
      split at h
      all_goals first
        | exact iSeq h
        | exact iCond h
        | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact Keeps.refl _)
        | (simp at h; done)
        | skip
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact Keeps.refl _
        · obtain ⟨_, _, h⟩ := bind_ok h
          split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact Keeps.refl _
          · obtain ⟨_, _, h⟩ := bind_ok h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            exact Keeps.refl _
      · have he : after = state := by
          repeat' split at h
          all_goals (first | (simp at h; done) | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2.symm))
        rw [he]
        exact Keeps.refl _
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact iEval h1
        · simp at h
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h2, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        split at h
        · simp at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (iEval h1).trans (iEval h2)
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h2, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        split at h
        · simp at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact (iEval h1).trans (iEval h2)
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact iEval h1
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        have hk1 : Keeps state s := by
          have := iEval h1
          exact ⟨this.1, this.2⟩
        obtain ⟨_, _, h⟩ := bind_ok h
        split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨hk1.1, hk1.2⟩
        · obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨⟨_, s2⟩, h2, h⟩ := bind_ok h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have h3 := iSeq h2
          exact ⟨h3.1.trans hk1.1, h3.2.trans hk1.2⟩
      · split at h <;> simp at h
      · obtain ⟨⟨l, s⟩, h1, h2⟩ := bind_ok h
        have hk1 : Keeps state s := by
          refine foldl_state_inv (P := fun c : Locals × State => Keeps state c.2) (fun cur item r hi hm => ?_) _ _
            (Keeps.refl _) h1
          split at hm
          · obtain ⟨⟨v, s1⟩, h3, hm⟩ := bind_ok hm
            refine Keeps.trans hi ((iEval h3).trans ?_)
            split at hm
            · obtain ⟨⟨v2, s2⟩, h4, hm⟩ := bind_ok hm
              simp only [Except.ok.injEq] at hm
              subst hm
              exact keeps_bindAssignable h4
            · simp only [Except.ok.injEq] at hm
              subst hm
              exact keeps_freeze _ _ _
          · simp at hm
        exact hk1.trans (iSeq h2)
      · obtain ⟨_, _, h⟩ := bind_ok h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨_, _, h⟩ := bind_ok h
        exact (iEval h1).trans (iSeq h)
      · obtain ⟨v, _, h⟩ := bind_ok h
        have tail : ∀ {op : String} {ops : List Sexp} {e : Except String (Option (List Sexp))}, (e >>= fun expansion =>
            match expansion with
            | some body => evalSequence fuel locals context state body
            | none => do
              let x ← eval fuel locals context state (Sexp.atom op)
              let y ← evalList fuel locals context x.2 ops
              apply fuel context y.2 x.1 y.1) = .ok (value, after) → Keeps state after := by
          intro op ops e he
          obtain ⟨x, _, he⟩ := bind_ok he
          cases x with
          | some expanded => exact iSeq he
          | none =>
            obtain ⟨⟨_, s⟩, h1, he⟩ := bind_ok he
            obtain ⟨⟨_, s2⟩, h2, he⟩ := bind_ok he
            exact (iEval h1).trans ((iList h2).trans (iApply he))
        split at h
        · split at h
          · exact tail h
          · exact tail h
        · exact tail h
      · obtain ⟨⟨_, s⟩, h1, h⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h2, h⟩ := bind_ok h
        exact (iEval h1).trans ((iList h2).trans (iApply h))
    · intro locals context state forms value after h
      rw [evalCompiledSequence.eq_def] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · exact iComp h
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        exact (iComp h1).trans (iCSeq h2)
    · intro locals context state forms value after h
      rw [evalCompiledList.eq_def] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h3, h4⟩ := bind_ok h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h4
        obtain ⟨_, rfl⟩ := h4
        exact (iComp h1).trans (iCList h3)
    · intro locals context state test yes no value after h
      rw [evalCompiledConditional.eq_def] at h
      simp only at h
      obtain ⟨⟨t, s⟩, h1, h2⟩ := bind_ok h
      have hk1 := iComp h1
      obtain ⟨tv, _, h3⟩ := bind_ok h2
      split at h3
      · exact hk1.trans (iCSeq h3)
      · exact hk1.trans (iCSeq h3)
      · obtain ⟨_, _, h4⟩ := bind_ok h3
        obtain ⟨⟨_, ys⟩, h5, h6⟩ := bind_ok h4
        obtain ⟨⟨_, ns⟩, h7, h8⟩ := bind_ok h6
        split at h8
        · obtain ⟨_, _, h9⟩ := bind_ok h8
          obtain ⟨_, _, h10⟩ := bind_ok h9
          simp only [Except.ok.injEq, Prod.mk.injEq] at h10
          obtain ⟨_, rfl⟩ := h10
          exact hk1
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h8
          obtain ⟨_, rfl⟩ := h8
          exact hk1
    · intro locals context state form value after h
      rw [evalCompiled.eq_def] at h
      simp only at h
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        exact Keeps.refl _
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact Keeps.refl _
        · simp at h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact Keeps.refl _
        · simp at h
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        obtain ⟨⟨_, code⟩, h3, h4⟩ := bind_ok h2
        simp only [Except.ok.injEq, Prod.mk.injEq] at h4
        obtain ⟨_, rfl⟩ := h4
        exact (iCList h1).trans (keeps_emit _ _)
      · obtain ⟨⟨_, s⟩, h1, h2⟩ := bind_ok h
        obtain ⟨⟨_, s2⟩, h3, h4⟩ := bind_ok h2
        exact (iComp h1).trans ((iCList h3).trans (iApply h4))
      · exact iCCond h
      · obtain ⟨⟨v, s⟩, h1, h2⟩ := bind_ok h
        exact (iComp h1).trans ((keeps_freeze context s v).trans (iComp h2))
      · exact iCSeq h


/-! ### Compiled code agrees with the interpreter -/

/-- That a family indexed by fuel succeeds with a result at some fuel. -/
def Succeeds {α : Type} (family : Nat → Except String α) (result : α) : Prop := ∃ fuel, family fuel = .ok result

/-- More fuel keeps a success. -/
def FuelMono {α : Type} (family : Nat → Except String α) : Prop :=
  ∀ ⦃fuel result⦄, family fuel = .ok result → family (fuel + 1) = .ok result

private theorem FuelMono.add {α : Type} {family : Nat → Except String α} (h : FuelMono family) {fuel extra : Nat}
    {result : α} (hf : family fuel = .ok result) : family (fuel + extra) = .ok result := by
  induction extra with
  | zero => exact hf
  | succ extra ih => exact h ih

private theorem FuelMono.le {α : Type} {family : Nat → Except String α} (h : FuelMono family) {fuel other : Nat}
    {result : α} (hf : family fuel = .ok result) (hle : fuel ≤ other) : family other = .ok result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact h.add hf

private theorem FuelMono.const {α : Type} (value : Except String α) : FuelMono fun _ => value := fun _ _ h => h

private theorem FuelMono.bind {α β : Type} {family : Nat → Except String α} {next : Nat → α → Except String β}
    (hf : FuelMono family) (hn : ∀ x, FuelMono fun fuel => next fuel x) :
    FuelMono fun fuel => family fuel >>= next fuel := by
  intro fuel result h
  obtain ⟨x, h1, h2⟩ := bind_ok h
  simp only [hf h1]
  exact hn x h2

/-- A success of a composition is a success of its parts, at the larger fuel. -/
theorem succeeds_bind {α β : Type} {family : Nat → Except String α} {next : Nat → α → Except String β} {result : β}
    (hf : FuelMono family) (hn : ∀ x, FuelMono fun fuel => next fuel x) :
    Succeeds (fun fuel => family fuel >>= next fuel) result ↔
      ∃ x, Succeeds family x ∧ Succeeds (fun fuel => next fuel x) result := by
  constructor
  · rintro ⟨fuel, h⟩
    obtain ⟨x, h1, h2⟩ := bind_ok h
    exact ⟨x, ⟨fuel, h1⟩, ⟨fuel, h2⟩⟩
  · rintro ⟨x, ⟨f1, h1⟩, ⟨f2, h2⟩⟩
    refine ⟨max f1 f2, ?_⟩
    simp only [hf.le h1 (Nat.le_max_left _ _), bind, Except.bind]
    exact (hn x).le h2 (Nat.le_max_right _ _)

/-- Reaching a family that fails without fuel is reaching it one step later. -/
theorem succeeds_succ {α : Type} {family : Nat → Except String α} {result : α} (hm : FuelMono family) :
    Succeeds family result ↔ Succeeds (fun fuel => family (fuel + 1)) result := by
  constructor
  · rintro ⟨fuel, h⟩
    exact ⟨fuel, hm h⟩
  · rintro ⟨fuel, h⟩
    exact ⟨fuel + 1, h⟩

section Families

variable (context : Context)

theorem evalSequence_mono (locals : Locals) (state : State) (forms : List Sexp) :
    FuelMono fun fuel => evalSequence fuel locals context state forms :=
  fun _ _ h => (eval_family_fuel_succ _).1 h

theorem evalList_mono (locals : Locals) (state : State) (forms : List Sexp) :
    FuelMono fun fuel => evalList fuel locals context state forms :=
  fun _ _ h => (eval_family_fuel_succ _).2.1 h

theorem evalConditional_mono (locals : Locals) (state : State) (test : Sexp) (yes no : List Sexp) :
    FuelMono fun fuel => evalConditional fuel locals context state test yes no :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.1 h

theorem apply_mono (state : State) (value : SV) (args : List SV) :
    FuelMono fun fuel => apply fuel context state value args :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.1 h

theorem eval_mono (locals : Locals) (state : State) (form : Sexp) :
    FuelMono fun fuel => eval fuel locals context state form :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.2.1 h

theorem evalCompiledSequence_mono (locals : Locals) (state : State) (forms : List CExp) :
    FuelMono fun fuel => evalCompiledSequence fuel locals context state forms :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.2.2.1 h

theorem evalCompiledList_mono (locals : Locals) (state : State) (forms : List CExp) :
    FuelMono fun fuel => evalCompiledList fuel locals context state forms :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.2.2.2.1 h

theorem evalCompiledConditional_mono (locals : Locals) (state : State) (test : CExp) (yes no : List CExp) :
    FuelMono fun fuel => evalCompiledConditional fuel locals context state test yes no :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.2.2.2.2.1 h

theorem evalCompiled_mono (locals : Locals) (state : State) (form : CExp) :
    FuelMono fun fuel => evalCompiled fuel locals context state form :=
  fun _ _ h => (eval_family_fuel_succ _).2.2.2.2.2.2.2.2 h

end Families

/-- The state that compiled code runs in: the definitions it was compiled against, compiled, and an index of the
functions that agrees with them. -/
structure Compat (globals : Globals) (state : State) : Prop where
  definitions : state.globals = compileGlobals globals
  index : ∀ name, state.operations.get? name =
    match Assoc.get name state.globals with
    | some (.callable callable) => some callable
    | _ => none

theorem Compat.keep {globals : Globals} {first second : State} (h : Compat globals first) (hk : Keeps first second) :
    Compat globals second where
  definitions := hk.1.trans h.definitions
  index := by
    intro name
    rw [hk.2, hk.1]
    exact h.index name

/-- The names the code was compiled for and the values the two evaluators bind them to. -/
def Aligned (names : List String) (locals clocals : Locals) : Prop :=
  locals.map Prod.fst = names ∧ clocals.map Prod.snd = locals.map Prod.snd

/-! Names. -/

private theorem get_compileGlobals (globals table : Globals) (name : String) :
    Assoc.get name (table.map fun binding => (binding.1, compileValue globals binding.2)) =
      (Assoc.get name table).map (compileValue globals) := by
  induction table with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    simp only [Assoc.get, List.map_cons, List.lookup_cons] at ih ⊢
    by_cases h : name == key <;> simp [h, ih]

private theorem compileFunction_cases (globals : Globals) (params : List String) (body : List Sexp)
    (env : List (String × SV)) :
    compileFunction globals (.function params body env) = .function params body env ∨
      ∃ compiled, compileFunction globals (.function params body env) = .compiled params compiled env := by
  simp only [compileFunction]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

private theorem macroCandidates_compile (globals : Globals) (callable : Callable) :
    macroCandidates (compileCallable globals callable) = macroCandidates callable := by
  cases callable with
  | overloads candidates =>
    simp only [compileCallable, macroCandidates]
    induction candidates with
    | nil => rfl
    | cons head rest ih =>
      simp only [List.map_cons, List.filter_cons]
      cases head with
      | function p b e =>
        rcases compileFunction_cases globals p b e with hc | ⟨body, hc⟩ <;> rw [hc] <;> simpa using ih
      | «macro» p b => simp [compileFunction, ih]
      | compiled p b e => simpa [compileFunction] using ih
      | primitive n => simpa [compileFunction] using ih
      | overloads c => simpa [compileFunction] using ih
  | «macro» p b => rfl
  | function p b e =>
    simp only [compileCallable, compileFunction]
    split <;> rfl
  | compiled p b e => rfl
  | primitive n => rfl

private theorem macroExpansion_compile (globals : Globals) (callable : Callable) (operands : List Sexp) :
    macroExpansion (compileCallable globals callable) operands = macroExpansion callable operands := by
  simp only [macroExpansion, macroCandidates_compile]

/-- Which names assign a local does not depend on how the functions were compiled. -/
theorem assignsLocal_compile (globals : Globals) (name : String) (fuel : Nat) (form : Sexp) :
    assignsLocal (compileGlobals globals) name fuel form = assignsLocal globals name fuel form := by
  induction fuel generalizing form with
  | zero => simp [assignsLocal]
  | succ fuel ih =>
    have hget : ∀ operator, Assoc.get operator (compileGlobals globals) =
        (Assoc.get operator globals).map (compileValue globals) := get_compileGlobals globals globals
    cases form with
    | atom a => simp [assignsLocal]
    | list items =>
      cases items with
      | nil => simp [assignsLocal]
      | cons head tail =>
        cases head with
        | list inner => simp only [assignsLocal, ih]
        | atom operator =>
          simp only [assignsLocal, hget, ih]
          cases Assoc.get operator globals with
          | none => rfl
          | some value =>
            cases value <;> simp only [Option.map, compileValue, macroCandidates_compile]

private theorem lookupState_compat {globals : Globals} {state : State} (h : Compat globals state) (name : String)
    (locals : Locals) : lookupState name locals state = lookup name locals state.globals := by
  have key : ∀ fallback : Except String SV,
      (match state.operations.get? name with
        | some callable => Except.ok (Value.callable callable)
        | none =>
          match Assoc.get name state.globals with
          | some value => Except.ok value
          | none => fallback) =
      (match Assoc.get name state.globals with
        | some value => Except.ok value
        | none => fallback) := by
    intro fallback
    rw [h.index name]
    cases Assoc.get name state.globals with
    | none => rfl
    | some value => cases value <;> rfl
  simp only [lookupState, lookup]
  cases Assoc.get name locals with
  | some value => with_reducible rfl
  | none =>
    simp only
    generalize (if name.startsWith "core:" = true then (name.drop 5).toString else name) = primitive
    by_cases hr : primitive = "replicate"
    · simp only [hr, ↓reduceIte]
    · simp only [hr, ↓reduceIte]
      exact key _

private theorem local_slot {atom : String} {names : List String} {locals clocals : Locals} {slot : Nat}
    (ha : Aligned names locals clocals) (hs : names.findIdx? (· == atom) = some slot) :
    ∃ binding, clocals[slot]? = some binding ∧ Assoc.get atom locals = some binding.2 := by
  obtain ⟨h1, h2⟩ := ha
  subst h1
  induction locals generalizing clocals slot with
  | nil => simp at hs
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    cases clocals with
    | nil => simp at h2
    | cons chead crest =>
      simp only [List.map_cons, List.cons.injEq] at h2
      by_cases hk : key = atom
      · subst hk
        simp [List.findIdx?_cons] at hs
        subst hs
        exact ⟨chead, rfl, by simp [Assoc.get, h2.1]⟩
      · have hb : (key == atom) = false := by simpa using hk
        simp only [List.map_cons, List.findIdx?_cons, hb] at hs
        cases hrest : List.findIdx? (· == atom) (rest.map Prod.fst) with
        | none => simp [hrest] at hs
        | some inner =>
          simp [hrest] at hs
          subst hs
          obtain ⟨b, hb1, hb2⟩ := ih h2.2 hrest
          refine ⟨b, by simpa using hb1, ?_⟩
          have hne : (atom == key) = false := by
            simp [Ne.symm hk]
          simpa [Assoc.get, List.lookup_cons, hne] using hb2

private theorem local_none {atom : String} {names : List String} {locals clocals : Locals}
    (ha : Aligned names locals clocals) (hs : names.findIdx? (· == atom) = none) :
    Assoc.get atom locals = none := by
  obtain ⟨h1, h2⟩ := ha
  subst h1
  clear h2
  induction locals with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have hk : ¬ key = atom := by
      intro e
      subst e
      simp [List.findIdx?_cons] at hs
    have hb : (key == atom) = false := by simpa using hk
    simp only [List.map_cons, List.findIdx?_cons, hb] at hs
    have hrest : List.findIdx? (· == atom) (rest.map Prod.fst) = none := by
      cases hr : List.findIdx? (· == atom) (rest.map Prod.fst) with
      | none => rfl
      | some inner => simp [hr] at hs
    have hne : (atom == key) = false := by
      simp [Ne.symm hk]
    simpa [Assoc.get, List.lookup_cons, hne] using ih hrest

private theorem global_slot {atom : String} {globals table : Globals} {slot : Nat}
    (hs : table.findIdx? (fun binding => binding.1 == atom) = some slot) :
    ∃ binding, (table.map fun binding => (binding.1, compileValue globals binding.2))[slot]? = some binding ∧
      Assoc.get atom (table.map fun binding => (binding.1, compileValue globals binding.2)) = some binding.2 := by
  induction table generalizing slot with
  | nil => simp at hs
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases hk : key = atom
    · subst hk
      simp [List.findIdx?_cons] at hs
      subst hs
      exact ⟨_, rfl, by simp [Assoc.get]⟩
    · have hb : (key == atom) = false := by simpa using hk
      simp only [List.findIdx?_cons, hb] at hs
      cases hrest : List.findIdx? (fun binding : String × SV => binding.1 == atom) rest with
      | none => simp [hrest] at hs
      | some inner =>
        simp [hrest] at hs
        subst hs
        obtain ⟨b, hb1, hb2⟩ := ih hrest
        refine ⟨b, by simpa using hb1, ?_⟩
        have hne : (atom == key) = false := by
          simp [Ne.symm hk]
        simpa [Assoc.get, List.lookup_cons, hne] using hb2


/-! Conditionals: the two evaluators have the same body, around their recursive calls. -/

/-- The body of `evalConditional` and of `evalCompiledConditional`. -/
def conditionalBody (context : Context) (test : Nat → Except String (SV × State))
    (yes no : Nat → State → Except String (SV × State)) (fuel : Nat) : Except String (SV × State) := do
  let (testValue, state) ← test fuel
  match ← truth testValue with
  | some true => yes fuel state
  | some false => no fuel state
  | none =>
    let condition ← condition context testValue
    let (yesValue, yesState) ← yes fuel { state with code := [] }
    let (noValue, noState) ← no fuel { state with code := [] }
    let state := { state with nextTemp := max yesState.nextTemp noState.nextTemp }
    if yesState.code.isEmpty && noState.code.isEmpty then do
      let (yesWidth, yes) ← expectBil context yesValue
      let (noWidth, no) ← expectBil context noValue
      let width := max yesWidth noWidth
      .ok (.bil width (.ite condition (extend width yes) (extend width no)), state)
    else
      .ok (.unit, emit state [.ifElse condition yesState.code noState.code])

theorem conditional_transfer {context : Context} {P : State → Prop}
    {test test' : Nat → Except String (SV × State)} {yes yes' no no' : Nat → State → Except String (SV × State)}
    (ht' : FuelMono test') (hy' : ∀ s, FuelMono fun f => yes' f s) (hn' : ∀ s, FuelMono fun f => no' f s)
    (hP : ∀ s, P s → P { s with code := [] })
    (ht : ∀ r, Succeeds test r → Succeeds test' r ∧ P r.2)
    (hy : ∀ s r, P s → Succeeds (fun f => yes f s) r → Succeeds (fun f => yes' f s) r)
    (hn : ∀ s r, P s → Succeeds (fun f => no f s) r → Succeeds (fun f => no' f s) r) {r : SV × State}
    (h : Succeeds (conditionalBody context test yes no) r) : Succeeds (conditionalBody context test' yes' no') r := by
  obtain ⟨fuel, h⟩ := h
  simp only [conditionalBody] at h
  obtain ⟨⟨tv, s⟩, h1, h⟩ := bind_ok h
  obtain ⟨⟨f1, h1'⟩, hps⟩ := ht _ ⟨fuel, h1⟩
  obtain ⟨tr, h2, h⟩ := bind_ok h
  have hbase : ∀ g, f1 ≤ g → test' g = .ok (tv, s) := fun g hg => ht'.le h1' hg
  match tr, h with
  | some true, h =>
    obtain ⟨f2, h3⟩ := hy s _ hps ⟨fuel, h⟩
    refine ⟨max f1 f2, ?_⟩
    simp only [conditionalBody, hbase _ (Nat.le_max_left _ _), bind, Except.bind, h2]
    exact (hy' s).le h3 (Nat.le_max_right _ _)
  | some false, h =>
    obtain ⟨f2, h3⟩ := hn s _ hps ⟨fuel, h⟩
    refine ⟨max f1 f2, ?_⟩
    simp only [conditionalBody, hbase _ (Nat.le_max_left _ _), bind, Except.bind, h2]
    exact (hn' s).le h3 (Nat.le_max_right _ _)
  | none, h =>
    obtain ⟨c, h3, h⟩ := bind_ok h
    obtain ⟨⟨yv, ys⟩, h4, h⟩ := bind_ok h
    obtain ⟨⟨nv, ns⟩, h5, h⟩ := bind_ok h
    obtain ⟨f2, h4'⟩ := hy _ _ (hP s hps) ⟨fuel, h4⟩
    obtain ⟨f3, h5'⟩ := hn _ _ (hP s hps) ⟨fuel, h5⟩
    refine ⟨max f1 (max f2 f3), ?_⟩
    have g1 := hbase (max f1 (max f2 f3)) (Nat.le_max_left _ _)
    have g2 := (hy' _).le h4' (show f2 ≤ max f1 (max f2 f3) by omega)
    have g3 := (hn' _).le h5' (show f3 ≤ max f1 (max f2 f3) by omega)
    simp only [conditionalBody, g1, bind, Except.bind, h2, h3]
    simp only [g2, g3]
    exact h

theorem evalConditional_body (fuel : Nat) (locals : Locals) (context : Context) (state : State) (test : Sexp)
    (yes no : List Sexp) :
    evalConditional (fuel + 1) locals context state test yes no =
      conditionalBody context (fun f => eval f locals context state test)
        (fun f s => evalSequence f locals context s yes) (fun f s => evalSequence f locals context s no) fuel := by
  rw [evalConditional.eq_def]
  rfl

theorem evalCompiledConditional_body (fuel : Nat) (locals : Locals) (context : Context) (state : State) (test : CExp)
    (yes no : List CExp) :
    evalCompiledConditional (fuel + 1) locals context state test yes no =
      conditionalBody context (fun f => evalCompiled f locals context state test)
        (fun f s => evalCompiledSequence f locals context s yes) (fun f s => evalCompiledSequence f locals context s no) fuel := by
  rw [evalCompiledConditional.eq_def]
  rfl

/-- The results of two families agree. -/
def SameResults {α : Type} (first second : Nat → Except String α) : Prop :=
  ∀ r, Succeeds first r ↔ Succeeds second r

theorem conditional_agrees {context : Context} {P : State → Prop} {clocals locals : Locals} {state : State}
    {ctest : CExp} {cyes cno : List CExp} {test : Sexp} {yes no : List Sexp}
    (hP : ∀ s, P s → P { s with code := [] })
    (hkeep : ∀ {r}, Succeeds (fun f => eval f locals context state test) r → P r.2)
    (ht : SameResults (fun f => evalCompiled f clocals context state ctest) (fun f => eval f locals context state test))
    (hy : ∀ s, P s → SameResults (fun f => evalCompiledSequence f clocals context s cyes)
      (fun f => evalSequence f locals context s yes))
    (hn : ∀ s, P s → SameResults (fun f => evalCompiledSequence f clocals context s cno)
      (fun f => evalSequence f locals context s no)) :
    SameResults (fun f => evalCompiledConditional f clocals context state ctest cyes cno)
      (fun f => evalConditional f locals context state test yes no) := by
  intro r
  rw [succeeds_succ (evalCompiledConditional_mono context clocals state ctest cyes cno),
    succeeds_succ (evalConditional_mono context locals state test yes no)]
  simp only [evalConditional_body, evalCompiledConditional_body]
  constructor
  · exact conditional_transfer (eval_mono context locals state test) (fun s => evalSequence_mono context locals s yes)
      (fun s => evalSequence_mono context locals s no) hP
      (fun r hr => have h := (ht r).1 hr; ⟨h, hkeep h⟩)
      (fun s r hs h => ((hy s hs) r).1 h) (fun s r hs h => ((hn s hs) r).1 h)
  · exact conditional_transfer (evalCompiled_mono context clocals state ctest)
      (fun s => evalCompiledSequence_mono context clocals s cyes) (fun s => evalCompiledSequence_mono context clocals s cno) hP
      (fun r hr => ⟨(ht r).2 hr, hkeep hr⟩)
      (fun s r hs h => ((hy s hs) r).2 h) (fun s r hs h => ((hn s hs) r).2 h)

/-! Lists of forms. -/

/-- Two lists of the same length, related at each position. -/
inductive Related {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Related R [] []
  | cons {a b as bs} : R a b → Related R as bs → Related R (a :: as) (b :: bs)

/-- A compiled form that agrees with its source form, from any state in `P`. -/
def FormAgrees (context : Context) (P : State → Prop) (clocals locals : Locals) (compiled : CExp) (form : Sexp) : Prop :=
  ∀ s, P s → SameResults (fun f => evalCompiled f clocals context s compiled) (fun f => eval f locals context s form)

theorem sequence_agrees {context : Context} {P : State → Prop} {clocals locals : Locals}
    (hkeep : ∀ {s f form v after}, P s → eval f locals context s form = .ok (v, after) → P after)
    {compiled : List CExp} {forms : List Sexp} (h : Related (FormAgrees context P clocals locals) compiled forms) :
    ∀ s, P s → SameResults (fun f => evalCompiledSequence f clocals context s compiled)
      (fun f => evalSequence f locals context s forms) := by
  induction h with
  | nil =>
    intro s _ r
    rw [succeeds_succ (evalCompiledSequence_mono context clocals s []), succeeds_succ (evalSequence_mono context locals s [])]
    have h1 : ∀ fuel, evalCompiledSequence (fuel + 1) clocals context s [] = .ok (.unit, s) := by
      intro fuel
      rw [evalCompiledSequence.eq_def]
    have h2 : ∀ fuel, evalSequence (fuel + 1) locals context s [] = .ok (.unit, s) := by
      intro fuel
      rw [evalSequence.eq_def]
    simp only [h1, h2]
  | @cons c f cs fs hd hrest ih =>
    intro s hs r
    rw [succeeds_succ (evalCompiledSequence_mono context clocals s (c :: cs)),
      succeeds_succ (evalSequence_mono context locals s (f :: fs))]
    cases hrest with
    | nil =>
      simp only [evalCompiledSequence.eq_def, evalSequence.eq_def]
      exact hd s hs r
    | @cons c2 f2 cs2 fs2 h1 h2 =>
      have hC : ∀ fuel, evalCompiledSequence (fuel + 1) clocals context s (c :: c2 :: cs2) =
          evalCompiled fuel clocals context s c >>= fun x => evalCompiledSequence fuel clocals context x.2 (c2 :: cs2) := by
        intro fuel
        rw [evalCompiledSequence.eq_def]
      have hE : ∀ fuel, evalSequence (fuel + 1) locals context s (f :: f2 :: fs2) =
          eval fuel locals context s f >>= fun x => evalSequence fuel locals context x.2 (f2 :: fs2) := by
        intro fuel
        rw [evalSequence.eq_def]
      simp only [hC, hE]
      rw [succeeds_bind (evalCompiled_mono context clocals s c) (fun x => evalCompiledSequence_mono context clocals x.2 (c2 :: cs2)),
        succeeds_bind (eval_mono context locals s f) (fun x => evalSequence_mono context locals x.2 (f2 :: fs2))]
      constructor
      · rintro ⟨x, hx, hr⟩
        have hx' := (hd s hs x).1 hx
        obtain ⟨g, hg⟩ := hx'
        exact ⟨x, ⟨g, hg⟩, (ih x.2 (hkeep hs hg) r).1 hr⟩
      · rintro ⟨x, hx, hr⟩
        obtain ⟨g, hg⟩ := hx
        exact ⟨x, (hd s hs x).2 ⟨g, hg⟩, (ih x.2 (hkeep hs hg) r).2 hr⟩

theorem list_agrees {context : Context} {P : State → Prop} {clocals locals : Locals}
    (hkeep : ∀ {s f form v after}, P s → eval f locals context s form = .ok (v, after) → P after)
    {compiled : List CExp} {forms : List Sexp} (h : Related (FormAgrees context P clocals locals) compiled forms) :
    ∀ s, P s → SameResults (fun f => evalCompiledList f clocals context s compiled)
      (fun f => evalList f locals context s forms) := by
  induction h with
  | nil =>
    intro s _ r
    rw [succeeds_succ (evalCompiledList_mono context clocals s []), succeeds_succ (evalList_mono context locals s [])]
    have h1 : ∀ fuel, evalCompiledList (fuel + 1) clocals context s [] = .ok ([], s) := by
      intro fuel
      rw [evalCompiledList.eq_def]
    have h2 : ∀ fuel, evalList (fuel + 1) locals context s [] = .ok ([], s) := by
      intro fuel
      rw [evalList.eq_def]
    simp only [h1, h2]
  | @cons c f cs fs hd _ ih =>
    intro s hs r
    rw [succeeds_succ (evalCompiledList_mono context clocals s (c :: cs)),
      succeeds_succ (evalList_mono context locals s (f :: fs))]
    have hC : ∀ fuel, evalCompiledList (fuel + 1) clocals context s (c :: cs) =
        evalCompiled fuel clocals context s c >>= fun x =>
          evalCompiledList fuel clocals context x.2 cs >>= fun y => .ok (x.1 :: y.1, y.2) := by
      intro fuel
      rw [evalCompiledList.eq_def]
    have hE : ∀ fuel, evalList (fuel + 1) locals context s (f :: fs) =
        eval fuel locals context s f >>= fun x =>
          evalList fuel locals context x.2 fs >>= fun y => .ok (x.1 :: y.1, y.2) := by
      intro fuel
      rw [evalList.eq_def]
    simp only [hC, hE]
    have mC : ∀ x : SV × State, FuelMono fun fuel => evalCompiledList fuel clocals context x.2 cs >>= fun y =>
        (Except.ok (x.1 :: y.1, y.2) : Except String (List SV × State)) := fun x =>
      FuelMono.bind (evalCompiledList_mono context clocals x.2 cs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _
    have mE : ∀ x : SV × State, FuelMono fun fuel => evalList fuel locals context x.2 fs >>= fun y =>
        (Except.ok (x.1 :: y.1, y.2) : Except String (List SV × State)) := fun x =>
      FuelMono.bind (evalList_mono context locals x.2 fs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _
    rw [succeeds_bind (evalCompiled_mono context clocals s c) mC, succeeds_bind (eval_mono context locals s f) mE]
    constructor
    · rintro ⟨x, hx, hr⟩
      obtain ⟨g, hg⟩ := (hd s hs x).1 hx
      refine ⟨x, ⟨g, hg⟩, ?_⟩
      rw [succeeds_bind (evalCompiledList_mono context clocals x.2 cs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _] at hr
      rw [succeeds_bind (evalList_mono context locals x.2 fs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _]
      obtain ⟨y, hy, hv⟩ := hr
      exact ⟨y, (ih x.2 (hkeep hs hg) y).1 hy, hv⟩
    · rintro ⟨x, ⟨g, hg⟩, hr⟩
      refine ⟨x, (hd s hs x).2 ⟨g, hg⟩, ?_⟩
      rw [succeeds_bind (evalList_mono context locals x.2 fs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _] at hr
      rw [succeeds_bind (evalCompiledList_mono context clocals x.2 cs) (next := fun _ y => .ok (x.1 :: y.1, y.2))
        fun _ => FuelMono.const _]
      obtain ⟨y, hy, hv⟩ := hr
      exact ⟨y, (ih x.2 (hkeep hs hg) y).2 hy, hv⟩


private theorem compat_clear {globals : Globals} {s : State} (h : Compat globals s) : Compat globals { s with code := [] } :=
  h.keep ⟨rfl, rfl⟩

private theorem compat_eval {globals : Globals} {context : Context} {locals : Locals} {s after : State} {f : Nat}
    {form : Sexp} {v : SV} (h : Compat globals s) (he : eval f locals context s form = .ok (v, after)) :
    Compat globals after :=
  h.keep ((eval_family_keeps f).2.2.2.2.1 he)

private theorem mapM_related {context : Context} {P : State → Prop} {clocals locals : Locals} {compile : Sexp → Option CExp}
    (hc : ∀ form c, compile form = some c → FormAgrees context P clocals locals c form) {forms : List Sexp} {cs : List CExp}
    (h : forms.mapM compile = some cs) : Related (FormAgrees context P clocals locals) cs forms := by
  induction forms generalizing cs with
  | nil =>
    simp at h
    subst h
    exact .nil
  | cons form rest ih =>
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hf : compile form with
    | none => simp [hf] at h
    | some c =>
      simp only [hf] at h
      cases hr : rest.mapM compile with
      | none => simp [hr] at h
      | some tail =>
        simp [hr, pure] at h
        subst h
        exact .cons (hc _ _ hf) (ih hr)

/-- The step of `let` in the evaluator. -/
def letStep (fuel : Nat) (context : Context) (bindings body : List Sexp) (current : Locals × State) (binding : Sexp) :
    Except String (Locals × State) := do
  match binding with
  | .list [.atom name, value] =>
    let (value, state) ← eval fuel current.1 context current.2 value
    if (bindings ++ body).any (assignsLocal state.globals name 64) then
      let (value, state) ← bindAssignable context state value
      .ok ((name, value) :: current.1, state)
    else
      let (value, state) := freeze context state value
      .ok ((name, value) :: current.1, state)
  | _ => .error "invalid Primus let binding"

private theorem lookup_visible {name : String} {names : List String} {locals clocals : Locals}
    (ha : Aligned names locals clocals) (hl : Assoc.get name locals = none) :
    Assoc.get name (names.map fun name => (name, Value.unit)) = none := by
  obtain ⟨h1, h2⟩ := ha
  subst h1
  clear h2
  induction locals with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    have e : List.map (fun name => (name, Value.unit)) (List.map Prod.fst ((key, value) :: rest)) =
        (key, Value.unit) :: List.map (fun name => (name, Value.unit)) (List.map Prod.fst rest) := rfl
    rw [e]
    simp only [Assoc.get, List.lookup_cons] at hl ih ⊢
    cases hk : name == key
    · simp only [hk] at hl ⊢
      exact ih hl
    · simp [hk] at hl

private theorem lookup_visible_some {name : String} {names : List String} {locals clocals : Locals}
    {value : SV} (ha : Aligned names locals clocals) (hl : Assoc.get name locals = some value) :
    Assoc.get name (names.map fun name => (name, Value.unit)) = some .unit := by
  obtain ⟨h1, h2⟩ := ha
  subst h1
  clear h2
  induction locals with
  | nil => simp [Assoc.get] at hl
  | cons head rest ih =>
    obtain ⟨key, v⟩ := head
    have e : List.map (fun name => (name, Value.unit)) (List.map Prod.fst ((key, v) :: rest)) =
        (key, Value.unit) :: List.map (fun name => (name, Value.unit)) (List.map Prod.fst rest) := rfl
    rw [e]
    simp only [Assoc.get, List.lookup_cons] at hl ih ⊢
    cases hk : name == key
    · simp only [hk] at hl ⊢
      exact ih hl
    · simp only

/-- A name resolves to the compiled form of what it resolves to in the definitions compiled from. -/
private theorem lookup_compile (globals : Globals) (name : String) (locals : Locals)
    (hl : Assoc.get name locals = none) (visible : Locals) (hv : Assoc.get name visible = none) :
    lookup name locals (compileGlobals globals) = (lookup name visible globals).map (compileValue globals) := by
  have hget : Assoc.get name (compileGlobals globals) = (Assoc.get name globals).map (compileValue globals) :=
    get_compileGlobals globals globals name
  simp only [lookup, hl, hv, hget]
  generalize (if name.startsWith "core:" = true then (name.drop 5).toString else name) = primitive
  by_cases hr : primitive = "replicate"
  · simp only [hr, ↓reduceIte]
    rfl
  · simp only [hr, ↓reduceIte]
    cases Assoc.get name globals with
    | some value => rfl
    | none =>
      simp only [Option.map]
      by_cases hp : primitiveNames.contains primitive = true
      · simp only [hp, ↓reduceIte]
        rfl
      · simp only [hp]
        rfl

/-- The part of the operator case after the expansion, on the two sides. -/
private theorem call_agrees {context : Context} {globals : Globals} {clocals locals : Locals} {s : State} {catom : CExp}
    {atom : Sexp} {cargs : List CExp} {operands : List Sexp} (hs : Compat globals s)
    (hatom : FormAgrees context (Compat globals) clocals locals catom atom)
    (hargs : ∀ s, Compat globals s → SameResults (fun f => evalCompiledList f clocals context s cargs)
      (fun f => evalList f locals context s operands)) :
    SameResults
      (fun f => evalCompiled f clocals context s catom >>= fun x =>
        evalCompiledList f clocals context x.2 cargs >>= fun y => apply f context y.2 x.1 y.1)
      (fun f => eval f locals context s atom >>= fun x =>
        evalList f locals context x.2 operands >>= fun y => apply f context y.2 x.1 y.1) := by
  intro r
  have mC : ∀ x : SV × State, FuelMono fun f => evalCompiledList f clocals context x.2 cargs >>= fun y =>
      apply f context y.2 x.1 y.1 := fun x =>
    FuelMono.bind (evalCompiledList_mono context clocals x.2 cargs) (next := fun f y => apply f context y.2 x.1 y.1)
      fun y => apply_mono context y.2 x.1 y.1
  have mE : ∀ x : SV × State, FuelMono fun f => evalList f locals context x.2 operands >>= fun y =>
      apply f context y.2 x.1 y.1 := fun x =>
    FuelMono.bind (evalList_mono context locals x.2 operands) (next := fun f y => apply f context y.2 x.1 y.1)
      fun y => apply_mono context y.2 x.1 y.1
  rw [succeeds_bind (evalCompiled_mono context clocals s catom) mC, succeeds_bind (eval_mono context locals s atom) mE]
  have inner : ∀ x : SV × State, Compat globals x.2 → (Succeeds (fun f => evalCompiledList f clocals context x.2 cargs >>= fun y =>
      apply f context y.2 x.1 y.1) r ↔ Succeeds (fun f => evalList f locals context x.2 operands >>= fun y =>
      apply f context y.2 x.1 y.1) r) := by
    intro x hx
    rw [succeeds_bind (evalCompiledList_mono context clocals x.2 cargs) (next := fun f y => apply f context y.2 x.1 y.1)
        fun y => apply_mono context y.2 x.1 y.1,
      succeeds_bind (evalList_mono context locals x.2 operands) (next := fun f y => apply f context y.2 x.1 y.1)
        fun y => apply_mono context y.2 x.1 y.1]
    constructor
    · rintro ⟨y, hy, ha⟩
      exact ⟨y, (hargs x.2 hx y).1 hy, ha⟩
    · rintro ⟨y, hy, ha⟩
      exact ⟨y, (hargs x.2 hx y).2 hy, ha⟩
  constructor
  · rintro ⟨x, hx, hrest⟩
    obtain ⟨g, hg⟩ := (hatom s hs x).1 hx
    have hc : Compat globals x.2 := compat_eval hs hg
    exact ⟨x, ⟨g, hg⟩, (inner x hc).1 hrest⟩
  · rintro ⟨x, ⟨g, hg⟩, hrest⟩
    have hc : Compat globals x.2 := compat_eval hs hg
    exact ⟨x, (hatom s hs x).2 ⟨g, hg⟩, (inner x hc).2 hrest⟩

/-- The compilable primitives need neither a copy of their result nor a symbol resolved, but for the assignments. -/
private theorem compilable_properties : ∀ index : Fin 64, compilablePrimitive index.1 = true →
    intrinsicResult (primitiveNames[index.1]'(Nat.lt_of_lt_of_le index.2 (by decide))) = false ∧
    ((primitiveNames[index.1]'(Nat.lt_of_lt_of_le index.2 (by decide))) = "unquote") = False ∧
    (((primitiveNames[index.1]'(Nat.lt_of_lt_of_le index.2 (by decide))) = "set" ∨
      (primitiveNames[index.1]'(Nat.lt_of_lt_of_le index.2 (by decide))) = "set$" ∨
      (primitiveNames[index.1]'(Nat.lt_of_lt_of_le index.2 (by decide))) = "set-symbol-value") ↔
      (index.1 = 38 ∨ index.1 = 39 ∨ index.1 = 40)) := by
  decide +kernel

private theorem oget {α β : Type} {x : Option α} {f : α → Option β} {r : β} (h : (x >>= f) = some r) :
    ∃ v, x = some v ∧ f v = some r := by
  cases hx : x with
  | none => simp [hx] at h
  | some v => exact ⟨v, rfl, by simpa [hx] using h⟩

private theorem omap {α β : Type} {x : Option α} {f : α → β} {r : β} (h : (f <$> x) = some r) :
    ∃ v, x = some v ∧ f v = r := by
  cases hx : x with
  | none => simp [hx] at h
  | some v => exact ⟨v, rfl, by simpa [hx] using h⟩

private theorem emit_nil' (state : State) : emit state [] = state := by
  cases state
  simp [emit]

private theorem apply_body (fuel : Nat) (clocals : Locals) (context : Context) (s : State) (a : CExp) (b : List CExp) :
    evalCompiled (fuel + 1) clocals context s (.apply a b) =
      evalCompiled fuel clocals context s a >>= fun x =>
        evalCompiledList fuel clocals context x.2 b >>= fun y => apply fuel context y.2 x.1 y.1 := by
  rw [evalCompiled.eq_def]

private theorem single_list {context : Context} {clocals : Locals} {s : State} {v : CExp} {r : List SV × State} :
    Succeeds (fun f => evalCompiledList f clocals context s [v]) r ↔
      ∃ x, Succeeds (fun f => evalCompiled f clocals context s v) x ∧ r = ([x.1], x.2) := by
  rw [succeeds_succ (evalCompiledList_mono context clocals s [v])]
  have hC : ∀ f, evalCompiledList (f + 1) clocals context s [v] =
      evalCompiled f clocals context s v >>= fun x =>
        evalCompiledList f clocals context x.2 [] >>= fun y => .ok (x.1 :: y.1, y.2) := by
    intro f
    rw [evalCompiledList.eq_def]
  simp only [hC]
  have m : ∀ x : SV × State, FuelMono fun f => evalCompiledList f clocals context x.2 [] >>= fun y =>
      (Except.ok (x.1 :: y.1, y.2) : Except String (List SV × State)) := fun x =>
    FuelMono.bind (evalCompiledList_mono context clocals x.2 []) (next := fun _ y => .ok (x.1 :: y.1, y.2))
      fun _ => FuelMono.const _
  rw [succeeds_bind (evalCompiled_mono context clocals s v) m]
  have hnil : ∀ x : SV × State, Succeeds (fun f => evalCompiledList f clocals context x.2 [] >>= fun y =>
      (Except.ok (x.1 :: y.1, y.2) : Except String (List SV × State))) r ↔ r = ([x.1], x.2) := by
    intro x
    constructor
    · rintro ⟨f, hf⟩
      obtain ⟨y, h1, h2⟩ := bind_ok hf
      cases f with
      | zero => rw [evalCompiledList.eq_def] at h1; simp at h1
      | succ f =>
        rw [evalCompiledList.eq_def] at h1
        simp only [Except.ok.injEq] at h1 h2
        subst h1
        exact h2.symm
    · intro e
      refine ⟨1, ?_⟩
      show (evalCompiledList 1 clocals context x.2 [] >>= fun y =>
        (Except.ok (x.1 :: y.1, y.2) : Except String (List SV × State))) = .ok r
      rw [evalCompiledList.eq_def]
      simp only [bind, Except.bind, e]
  constructor
  · rintro ⟨x, hx, hr⟩
    exact ⟨x, hx, (hnil x).1 hr⟩
  · rintro ⟨x, hx, hr⟩
    exact ⟨x, hx, (hnil x).2 hr⟩

private theorem resolve_agree (state : State) (name : String) (operation : Nat) (args : List SV)
    (hu : (name = "unquote") = False)
    (hs : (name = "set" ∨ name = "set$" ∨ name = "set-symbol-value") ↔ (operation = 38 ∨ operation = 39 ∨ operation = 40)) :
    resolveDestination state name args =
      if (operation = 38 || operation = 39 || operation = 40) then resolveSymbol state args else args := by
  unfold resolveDestination
  split
  · by_cases hc : operation = 38 ∨ operation = 39 ∨ operation = 40
    · have hn := hs.2 hc
      have h1 : (decide (operation = 38) || decide (operation = 39) || decide (operation = 40)) = true := by
        rcases hc with hc | hc | hc <;> simp [hc]
      have h2 : (decide (name = "set") || decide (name = "set$") || decide (name = "set-symbol-value") ||
          decide (name = "unquote")) = true := by
        rcases hn with hn | hn | hn <;> simp [hn]
      simp only [h1, h2, ↓reduceIte]
    · have hn : ¬ (name = "set" ∨ name = "set$" ∨ name = "set-symbol-value") := fun e => hc (hs.1 e)
      have h1 : (decide (operation = 38) || decide (operation = 39) || decide (operation = 40)) = false := by
        simp only [not_or] at hc
        simp [hc.1, hc.2.1, hc.2.2]
      have h2 : (decide (name = "set") || decide (name = "set$") || decide (name = "set-symbol-value") ||
          decide (name = "unquote")) = false := by
        simp only [not_or] at hn
        simp [hn.1, hn.2.1, hn.2.2, hu]
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
  · next hnot =>
    cases args with
    | nil => split <;> rfl
    | cons head tail =>
      cases head
      case symbol n => exact (hnot _ _ rfl).elim
      all_goals (split <;> rfl)

/-- A compiled primitive has the result of the name it was compiled from. -/
private theorem primitive_step {context : Context} {name : String} {operation : Nat} (s : State) (args : List SV) (fuel : Nat)
    (hi : primitiveIndex name = some operation) (hc : compilablePrimitive operation = true) :
    apply (fuel + 1) context s (.callable (.primitive name)) args =
      (applyPrimitiveIndex context operation
        (if (operation = 38 || operation = 39 || operation = 40) then resolveSymbol s args else args) >>= fun p =>
        (.ok (p.1, emit s p.2) : Except String (SV × State))) := by
  have hle : operation < 64 := by
    simp only [compilablePrimitive, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  have hlen : operation < primitiveNames.length := Nat.lt_of_lt_of_le hle (by decide)
  have hname : primitiveNames[operation]'hlen = name := by
    have := primitiveIndex_sound hi
    rw [List.getElem?_eq_getElem hlen] at this
    simpa using this
  obtain ⟨hr, hu, hset⟩ := compilable_properties ⟨operation, hle⟩ hc
  simp only at hr hu hset
  subst hname
  rw [apply]
  simp only [hr, Bool.false_eq_true, ↓reduceIte, resolve_agree s _ operation args hu hset,
    primitive_tables_agree context operation _ hle hc]

private theorem letStep_mono (context : Context) (bindings body : List Sexp) (current : Locals × State) (binding : Sexp) :
    FuelMono fun f => letStep f context bindings body current binding := by
  intro f r h
  simp only [letStep] at h ⊢
  split at h
  · obtain ⟨x, h1, h2⟩ := bind_ok h
    simp only [(eval_mono context current.1 current.2 _) h1, bind, Except.bind]
    exact h2
  · exact h

private theorem foldl_let_mono (context : Context) (all body rest : List Sexp) (init : Locals × State) :
    FuelMono fun f => rest.foldlM (letStep f context all body) init := by
  induction rest generalizing init with
  | nil => intro f r h; exact h
  | cons head tail ih =>
    intro f r h
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨x, h1, h2⟩ := bind_ok h
    simp only [(letStep_mono context all body init head) h1, bind, Except.bind]
    exact ih x h2

private theorem compile_rest_mono (context : Context) (all body rest : List Sexp) (init : Locals × State) :
    FuelMono fun f => rest.foldlM (letStep f context all body) init >>= fun x => evalSequence f x.1 context x.2 body :=
  FuelMono.bind (foldl_let_mono context all body rest init) (next := fun f x => evalSequence f x.1 context x.2 body)
    fun x => evalSequence_mono context x.1 x.2 body

private theorem except_bind_assoc {α β γ ε : Type} (a : Except ε α) (b : α → Except ε β) (c : β → Except ε γ) :
    (a >>= b) >>= c = a >>= fun x => b x >>= c := by
  cases a <;> rfl

theorem compile_agrees (globals : Globals) (context : Context) (n : Nat) :
    (∀ {names locals clocals form c}, Aligned names locals clocals → compileExp globals names n form = some c →
      FormAgrees context (Compat globals) clocals locals c form) ∧
    (∀ {names locals clocals all bindings body c}, Aligned names locals clocals →
      compileBindings globals names all n bindings body = some c → ∀ s, Compat globals s →
      SameResults (fun f => evalCompiled f clocals context s c)
        (fun f => bindings.foldlM (letStep f context all body) (locals, s) >>= fun x =>
          evalSequence f x.1 context x.2 body)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro names locals clocals form c _ h
      rw [compileExp.eq_def] at h
      simp at h
    · intro names locals clocals all bindings body c _ h
      rw [compileBindings.eq_def] at h
      simp at h
  | succ n ih =>
    obtain ⟨ihE, ihB⟩ := ih
    have hkeep : ∀ {locals s f form v after}, Compat globals s → eval f locals context s form = .ok (v, after) →
        Compat globals after := fun hs he => compat_eval hs he
    have hseq : ∀ {names locals clocals forms cs}, Aligned names locals clocals →
        compileSequence globals names n forms = some cs → ∀ s, Compat globals s →
        SameResults (fun f => evalCompiledSequence f clocals context s cs) (fun f => evalSequence f locals context s forms) := by
      intro names locals clocals forms cs ha h
      rw [compileSequence] at h
      exact sequence_agrees hkeep (mapM_related (fun form c hc => ihE ha hc) h)
    refine ⟨?_, ?_⟩
    · intro names locals clocals form c ha h s hs r
      rw [succeeds_succ (evalCompiled_mono context clocals s c), succeeds_succ (eval_mono context locals s form)]
      rw [compileExp.eq_def] at h
      simp only at h
      split at h
      · -- an atom
        rename_i atom
        have hvalue : ∀ {v : SV}, Succeeds (fun _ => (.ok (v, s) : Except String (SV × State))) r ↔
            Succeeds (fun f => evalCompiled (f + 1) clocals context s (.value v)) r := by
          intro v
          have hC : ∀ f, evalCompiled (f + 1) clocals context s (.value v) = .ok (v, s) := by
            intro f
            rw [evalCompiled.eq_def]
          simp only [hC]
        split at h
        · next hcond =>
          simp only [Option.some.injEq] at h
          subst h
          rw [← hvalue]
          have hE : ∀ f, eval (f + 1) locals context s (.atom atom) = .ok (atomValue atom, s) := by
            intro f
            rw [eval]
            simp only [hcond, ↓reduceIte]
          simp only [hE]
        · next hcond =>
          have hE : ∀ f, eval (f + 1) locals context s (.atom atom) =
              (do
                match ← readLiteral atom with
                | some _ => .ok (atomValue atom, s)
                | none => .ok (← lookupState atom locals s, s)) := by
            intro f
            rw [eval]
            simp only [hcond, Bool.false_eq_true, ↓reduceIte]
            rfl
          simp only [hE]
          split at h
          · simp at h
          · next hl =>
            simp only [Option.some.injEq] at h
            subst h
            rw [← hvalue]
            simp only [hl, bind, Except.bind]
          · next hl =>
            simp only [hl, bind, Except.bind]
            split at h
            · next slot hslot =>
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨binding, hb, hg⟩ := local_slot ha hslot
              have hC : ∀ f, evalCompiled (f + 1) clocals context s (.local slot) = .ok (binding.2, s) := by
                intro f
                rw [evalCompiled.eq_def]
                simp only [hb]
              simp only [hC, lookupState, hg]
            · next hnone =>
              by_cases hrep : (if atom.startsWith "core:" = true then (atom.drop 5).toString else atom) = "replicate"
              · simp only [hrep, ↓reduceIte] at h
                simp at h
              · simp only [hrep, ↓reduceIte] at h
                cases hg : globals.findIdx? (fun binding => binding.1 == atom) with
                | none => simp [hg] at h
                | some slot =>
                  simp only [hg, Option.map_some, Option.some.injEq] at h
                  subst h
                  obtain ⟨binding, hb, hget⟩ := global_slot (globals := globals) hg
                  have hb' : s.globals[slot]? = some binding := by rw [hs.definitions]; exact hb
                  have hget' : Assoc.get atom s.globals = some binding.2 := by rw [hs.definitions]; exact hget
                  have hC : ∀ f, evalCompiled (f + 1) clocals context s (.global slot) = .ok (binding.2, s) := by
                    intro f
                    rw [evalCompiled.eq_def]
                    simp only [hb']
                  have hL : lookupState atom locals s = .ok binding.2 := by
                    rw [lookupState_compat hs]
                    simp only [lookup, local_none ha hnone, hrep, ↓reduceIte, hget']
                  simp only [hC, hL]
      · simp only [Option.some.injEq] at h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.value (.list [])) = .ok (.list [], s) := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list []) = .ok (.list [], s) := by
          intro f
          rw [eval]
        simp only [hC, hE]
      · simp only [Option.some.injEq] at h
        subst h
        rename_i value
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.value (quotedValue value)) = .ok (quotedValue value, s) := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list [.atom "quote", value]) = .ok (quotedValue value, s) := by
          intro f
          rw [eval]
        simp only [hC, hE]
      · simp at h
      · simp at h
      · -- clz
        rename_i value
        obtain ⟨cv, hv, h⟩ := oget h
        simp only [Option.some.injEq] at h
        subst h
        have hagree := ihE ha hv s hs
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.primitive 63 [cv]) =
            evalCompiledList f clocals context s [cv] >>= fun x =>
              leadingZeros context x.1 >>= fun y => (.ok (y, emit x.2 []) : Except String (SV × State)) := by
          intro f
          rw [evalCompiled.eq_def]
          have h63 : (decide (63 = 38) || decide (63 = 39) || decide (63 = 40)) = false := rfl
          simp only [bind, Except.bind, h63, Bool.false_eq_true, ↓reduceIte, applyPrimitiveIndex, valueOnly, pure, Except.pure]
          cases evalCompiledList f clocals context s [cv] with
          | error e => rfl
          | ok a =>
            simp only
            cases leadingZeros context a.1 with
            | error e => rfl
            | ok b => rfl
        have hE : ∀ f, eval (f + 1) locals context s (.list [.atom "clz", value]) =
            eval f locals context s value >>= fun x =>
              leadingZeros context [x.1] >>= fun y => (.ok (y, x.2) : Except String (SV × State)) := by
          intro f
          rw [eval]
        simp only [hC, hE]
        rw [succeeds_bind (evalCompiledList_mono context clocals s [cv])
            (next := fun _ x => leadingZeros context x.1 >>= fun y => .ok (y, emit x.2 [])) fun _ => FuelMono.const _,
          succeeds_bind (eval_mono context locals s value)
            (next := fun _ x => leadingZeros context [x.1] >>= fun y => .ok (y, x.2)) fun _ => FuelMono.const _]
        constructor
        · rintro ⟨x, hx, hrest⟩
          obtain ⟨y, hy, rfl⟩ := single_list.1 hx
          refine ⟨y, (hagree y).1 hy, ?_⟩
          obtain ⟨g, hg⟩ := hrest
          refine ⟨g, ?_⟩
          simpa [emit_nil'] using hg
        · rintro ⟨y, hy, hrest⟩
          refine ⟨_, single_list.2 ⟨y, (hagree y).2 hy, rfl⟩, ?_⟩
          obtain ⟨g, hg⟩ := hrest
          refine ⟨g, ?_⟩
          simpa [emit_nil'] using hg
      · -- if
        rename_i test yes no
        obtain ⟨ct, ht, h⟩ := oget h
        obtain ⟨cy, hy, h⟩ := oget h
        obtain ⟨cn, hn, h⟩ := oget h
        simp only [Option.some.injEq] at h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.ifElse ct [cy] [cn]) =
            evalCompiledConditional f clocals context s ct [cy] [cn] := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list [.atom "if", test, yes, no]) =
            evalConditional f locals context s test [yes] [no] := by
          intro f
          rw [eval]
        simp only [hC, hE]
        exact conditional_agrees (fun _ => compat_clear)
          (fun ⟨f, hf⟩ => hkeep hs hf) (ihE ha ht s hs)
          (sequence_agrees hkeep (.cons (ihE ha hy) .nil)) (sequence_agrees hkeep (.cons (ihE ha hn) .nil)) r
      · -- when
        rename_i test body
        obtain ⟨ct, ht, h⟩ := oget h
        obtain ⟨cb, hb, h⟩ := oget h
        simp only [Option.some.injEq] at h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.ifElse ct cb []) =
            evalCompiledConditional f clocals context s ct cb [] := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom "when" :: test :: body)) =
            evalConditional f locals context s test body [] := by
          intro f
          rw [eval]
        simp only [hC, hE]
        exact conditional_agrees (fun _ => compat_clear)
          (fun ⟨f, hf⟩ => hkeep hs hf) (ihE ha ht s hs) (hseq ha hb) (sequence_agrees hkeep .nil) r
      · -- unless
        rename_i test body
        obtain ⟨ct, ht, h⟩ := oget h
        obtain ⟨cb, hb, h⟩ := oget h
        simp only [Option.some.injEq] at h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.ifElse ct [] cb) =
            evalCompiledConditional f clocals context s ct [] cb := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom "unless" :: test :: body)) =
            evalConditional f locals context s test [] body := by
          intro f
          rw [eval]
        simp only [hC, hE]
        exact conditional_agrees (fun _ => compat_clear)
          (fun ⟨f, hf⟩ => hkeep hs hf) (ihE ha ht s hs) (sequence_agrees hkeep .nil) (hseq ha hb) r
      · -- progn
        rename_i body
        obtain ⟨cb, hb, h⟩ := omap h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.sequence cb) = evalCompiledSequence f clocals context s cb := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom "progn" :: body)) = evalSequence f locals context s body := by
          intro f
          rw [eval]
        simp only [hC, hE]
        exact hseq ha hb s hs r
      · -- prog
        rename_i body
        obtain ⟨cb, hb, h⟩ := omap h
        subst h
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.sequence cb) = evalCompiledSequence f clocals context s cb := by
          intro f
          rw [evalCompiled.eq_def]
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom "prog" :: body)) = evalSequence f locals context s body := by
          intro f
          rw [eval]
        simp only [hC, hE]
        exact hseq ha hb s hs r
      · -- let
        rename_i bindings body
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom "let" :: .list bindings :: body)) =
            bindings.foldlM (letStep f context bindings body) (locals, s) >>= fun x =>
              evalSequence f x.1 context x.2 body := by
          intro f
          rw [eval]
          rfl
        simp only [hE]
        rw [← succeeds_succ (evalCompiled_mono context clocals s c)]
        exact ihB ha h s hs r
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · simp at h
      · -- a call of a name
        rename_i operator operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        have hE : ∀ f, eval (f + 1) locals context s (.list (.atom operator :: operands)) = (do
            let expansion ← match ← lookupState operator locals s with
              | .callable callable =>
                if (Assoc.get operator locals).isSome then .ok none else macroExpansion callable operands
              | _ => .ok none
            match expansion with
            | some expanded => evalSequence f locals context s expanded
            | none =>
              eval f locals context s (.atom operator) >>= fun x =>
                evalList f locals context x.2 operands >>= fun y => apply f context y.2 x.1 y.1) := by
          intro f
          rw [eval]
          · rfl
          all_goals (intros; simp_all)
        split at h
        · simp at h
        · next hsym =>
          have hcond : (decide (operator = "true") || decide (operator = "false") || operator.startsWith ":") = false := by
            cases hb : (decide (operator = "true") || decide (operator = "false") || operator.startsWith ":")
            · rfl
            · simp only [hb, Bool.true_or] at hsym
              simp at hsym
          have hlit : readLiteral operator = .ok none := by
            cases hb : isSymbol operator
            · simp [hb] at hsym
            · simp only [isSymbol] at hb
              split at hb
              · assumption
              · cases hb
          have hatomE : ∀ {v : SV}, lookupState operator locals s = .ok v → ∀ g,
              eval (g + 1) locals context s (.atom operator) = .ok (v, s) := by
            intro v hv g
            rw [eval]
            simp only [hcond, Bool.false_eq_true, ↓reduceIte, hlit, hv]
            rfl
          have hargsAgree : ∀ {cargs}, operands.mapM (compileExp globals names n) = some cargs → ∀ s, Compat globals s →
              SameResults (fun f => evalCompiledList f clocals context s cargs) (fun f => evalList f locals context s operands) :=
            fun h => list_agrees hkeep (mapM_related (fun form c hc => ihE ha hc) h)
          -- the call itself, once no macro applies
          have hcall : ∀ {catom cargs}, compileExp globals names n (.atom operator) = some catom →
              operands.mapM (compileExp globals names n) = some cargs →
              (match lookupState operator locals s with
                | .error e => (.error e : Except String (Option (List Sexp)))
                | .ok (.callable callable) =>
                  if (Assoc.get operator locals).isSome then .ok none else macroExpansion callable operands
                | .ok _ => .ok none) = .ok none →
              (Succeeds (fun f => evalCompiled (f + 1) clocals context s (.apply catom cargs)) r ↔
                Succeeds (fun f => eval (f + 1) locals context s (.list (.atom operator :: operands))) r) := by
            intro catom cargs hc1 hc2 hnone
            have hE' : ∀ f, eval (f + 1) locals context s (.list (.atom operator :: operands)) =
                eval f locals context s (.atom operator) >>= fun x =>
                  evalList f locals context x.2 operands >>= fun y => apply f context y.2 x.1 y.1 := by
              intro f
              rw [hE]
              simp only [bind, Except.bind]
              cases hl : lookupState operator locals s with
              | error e => simp only [hl] at hnone; cases hnone
              | ok v =>
                simp only [hl] at hnone
                cases v
                all_goals first
                  | (simp only; try rfl)
                  | skip
                case callable callable =>
                  by_cases hi : (Assoc.get operator locals).isSome = true
                  · simp only [hi, ↓reduceIte]
                  · have hi' : (Assoc.get operator locals).isSome = false := by simpa using hi
                    simp only [hi', Bool.false_eq_true, ↓reduceIte] at hnone ⊢
                    simp only [hnone]
            simp only [apply_body, hE']
            exact call_agrees hs (ihE ha hc1) (hargsAgree hc2) r
          have hvisible : ∀ {v : SV}, Assoc.get operator locals = some v →
              lookup operator (names.map fun name => (name, Value.unit)) globals = .ok .unit := by
            intro v hv
            simp only [lookup, lookup_visible_some ha hv]
          have hstate : Assoc.get operator locals = none → lookupState operator locals s =
              (lookup operator (names.map fun name => (name, Value.unit)) globals).map (compileValue globals) := by
            intro hl
            rw [lookupState_compat hs, hs.definitions]
            exact lookup_compile globals operator locals hl _ (lookup_visible ha hl)
          generalize hrv : lookup operator (names.map fun name => (name, Value.unit)) globals = rv at h hvisible hstate
          have hnotlocal : ∀ {w : Callable}, rv = .ok (.callable w) → Assoc.get operator locals = none := by
            intro w hw
            cases hl : Assoc.get operator locals with
            | none => rfl
            | some v =>
              rw [hvisible hl] at hw
              cases hw
          simp only [Bool.not_eq_true'] at h
          split at h
          · -- a primitive
            rename_i name
            have hl := hnotlocal rfl
            have hL : lookupState operator locals s = .ok (.callable (.primitive name)) := by
              rw [hstate hl]
              rfl
            obtain ⟨operation, hindex, h⟩ := oget h
            have hcomp : compilablePrimitive operation = true := by
              cases hc : compilablePrimitive operation
              · simp [hc] at h
              · rfl
            simp only [hcomp] at h
            obtain ⟨cargs, hcargs, h⟩ := oget h
            simp only [Option.some.injEq] at h
            subst h
            have hagree := hargsAgree hcargs s hs
            have hC : ∀ f, evalCompiled (f + 1) clocals context s (.primitive operation cargs) =
                evalCompiledList f clocals context s cargs >>= fun a =>
                  apply 1 context a.2 (.callable (.primitive name)) a.1 := by
              intro f
              rw [evalCompiled.eq_def]
              simp only [primitive_step (fuel := 0) _ _ hindex hcomp]
            have hE' : ∀ f, eval (f + 1) locals context s (.list (.atom operator :: operands)) =
                eval f locals context s (.atom operator) >>= fun x =>
                  evalList f locals context x.2 operands >>= fun y => apply f context y.2 x.1 y.1 := by
              intro f
              rw [hE]
              simp only [hL, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, macroExpansion, macroCandidates,
                bind, Except.bind]
            simp only [hC, hE']
            have hstep : ∀ (g : Nat) (st : State) (a : List SV), apply (g + 1) context st (.callable (.primitive name)) a =
                apply 1 context st (.callable (.primitive name)) a := by
              intro g st a
              rw [primitive_step (fuel := g) st a hindex hcomp, primitive_step (fuel := 0) st a hindex hcomp]
            constructor
            · rintro ⟨f, hf⟩
              obtain ⟨y, h1, h2⟩ := bind_ok hf
              obtain ⟨g, hg⟩ := (hagree y).1 ⟨f, h1⟩
              refine ⟨g + 1, ?_⟩
              simp only [hatomE hL g, bind, Except.bind]
              have := evalList_mono context locals s operands hg
              simp only at this
              simp only [this]
              rw [hstep]
              exact h2
            · rintro ⟨f, hf⟩
              cases f with
              | zero =>
                obtain ⟨x, hx, _⟩ := bind_ok hf
                rw [eval.eq_def] at hx
                simp at hx
              | succ g =>
                simp only [hatomE hL g, bind, Except.bind] at hf
                obtain ⟨y, h1, h2⟩ := bind_ok hf
                obtain ⟨g', hg'⟩ := (hagree y).2 ⟨g + 1, h1⟩
                rw [hstep] at h2
                refine ⟨g', ?_⟩
                simp only [hg', bind, Except.bind]
                exact h2
          · -- a definition
            rename_i callable hnotprim
            have hl := hnotlocal rfl
            have hL : lookupState operator locals s = .ok (.callable (compileCallable globals callable)) := by
              rw [hstate hl]
              rfl
            have hexp : macroExpansion (compileCallable globals callable) operands = macroExpansion callable operands :=
              macroExpansion_compile globals callable operands
            split at h
            · next expanded hmac =>
              obtain ⟨cb, hb, h⟩ := omap h
              subst h
              have hC : ∀ f, evalCompiled (f + 1) clocals context s (.sequence cb) = evalCompiledSequence f clocals context s cb := by
                intro f
                rw [evalCompiled.eq_def]
              have hE' : ∀ f, eval (f + 1) locals context s (.list (.atom operator :: operands)) =
                  evalSequence f locals context s expanded := by
                intro f
                rw [hE]
                simp only [hL, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hexp, hmac, bind, Except.bind]
              simp only [hC, hE']
              exact hseq ha hb s hs r
            · next hmac =>
              obtain ⟨ca, hca, h⟩ := oget h
              obtain ⟨args, hargs, h⟩ := oget h
              simp only [Option.some.injEq] at h
              subst h
              refine hcall hca hargs ?_
              simp only [hL, hl, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hexp, hmac]
            · simp at h
          · -- anything else
            rename_i hprim hother
            obtain ⟨ca, hca, h⟩ := oget h
            obtain ⟨args, hargs, h⟩ := oget h
            simp only [Option.some.injEq] at h
            subst h
            refine hcall hca hargs ?_
            cases hl : Assoc.get operator locals with
            | some v =>
              have hsome : (Assoc.get operator locals).isSome = true := by simp [hl]
              have hv : lookupState operator locals s = .ok v := by
                simp only [lookupState, hl]
              simp only [hv]
              cases v
              all_goals first
                | rfl
                | (simp only [hsome, ↓reduceIte])
            | none =>
              have hs' := hstate hl
              cases rv with
              | error e =>
                exfalso
                cases n with
                | zero => rw [compileExp.eq_def] at hca; simp at hca
                | succ m =>
                  rw [compileExp.eq_def] at hca
                  simp only [hcond, Bool.false_eq_true, ↓reduceIte, hlit] at hca
                  have hnames : names.findIdx? (· == operator) = none := by
                    cases hf : names.findIdx? (· == operator) with
                    | none => rfl
                    | some slot =>
                      obtain ⟨b, _, hb⟩ := local_slot ha hf
                      rw [hl] at hb
                      cases hb
                  simp only [hnames] at hca
                  by_cases hrep : (if operator.startsWith "core:" = true then (operator.drop 5).toString else operator) = "replicate"
                  · simp only [hrep, ↓reduceIte] at hca
                    simp at hca
                  · simp only [hrep, ↓reduceIte] at hca
                    cases hfg : globals.findIdx? (fun binding => binding.1 == operator) with
                    | none => simp [hfg] at hca
                    | some slot =>
                      obtain ⟨b, _, hb⟩ := global_slot (globals := globals) hfg
                      have hget := get_compileGlobals globals globals operator
                      rw [hget] at hb
                      cases hgg : Assoc.get operator globals with
                      | none => simp [hgg] at hb
                      | some gv =>
                        simp only [lookup, lookup_visible ha hl, hrep, ↓reduceIte, hgg] at hrv
                        cases hrv
              | ok v =>
                have hL : lookupState operator locals s = .ok (compileValue globals v) := hs'
                cases v
                case callable c => exact (hother _ rfl).elim
                all_goals simp only [hL, compileValue]
      · -- a call of a value
        rename_i operator operands _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        obtain ⟨ca, hca, h⟩ := oget h
        obtain ⟨args, hargs, h⟩ := oget h
        simp only [Option.some.injEq] at h
        subst h
        have hE : ∀ f, eval (f + 1) locals context s (.list (operator :: operands)) =
            eval f locals context s operator >>= fun x =>
              evalList f locals context x.2 operands >>= fun y => apply f context y.2 x.1 y.1 := by
          intro f
          rw [eval]
          all_goals (intros; simp_all)
        simp only [apply_body, hE]
        exact call_agrees hs (ihE ha hca)
          (list_agrees hkeep (mapM_related (fun form c hc => ihE ha hc) hargs)) r
    · intro names locals clocals all bindings body c ha h s hs r
      rw [compileBindings.eq_def] at h
      simp only at h
      split at h
      · -- no bindings
        obtain ⟨cb, hb, h⟩ := omap h
        subst h
        rw [succeeds_succ (evalCompiled_mono context clocals s _)]
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.sequence cb) = evalCompiledSequence f clocals context s cb := by
          intro f
          rw [evalCompiled.eq_def]
        simp only [hC, List.foldlM_nil, pure, Except.pure, bind, Except.bind]
        exact hseq ha hb s hs r
      · -- a binding
        rename_i name value rest
        have hany : (all ++ body).any (assignsLocal globals name 64) = false := by
          cases hc : (all ++ body).any (assignsLocal globals name 64)
          · rfl
          · simp [hc] at h
        simp only [hany, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨cv, hv, h⟩ := oget h
        obtain ⟨cr, hr, h⟩ := omap h
        subst h
        have hagreeV := ihE ha hv s hs
        have hC : ∀ f, evalCompiled (f + 1) clocals context s (.letIn cv cr) =
            evalCompiled f clocals context s cv >>= fun x =>
              evalCompiled f (("", (freeze context x.2 x.1).1) :: clocals) context (freeze context x.2 x.1).2 cr := by
          intro f
          rw [evalCompiled.eq_def]
        -- the step on a compatible state
        have hstep : ∀ f (x : SV × State), Compat globals x.2 → eval f locals context s value = .ok x →
            letStep f context all body (locals, s) (.list [.atom name, value]) =
              .ok ((name, (freeze context x.2 x.1).1) :: locals, (freeze context x.2 x.1).2) := by
          intro f x hx hev
          have hanyx : (all ++ body).any (assignsLocal x.2.globals name 64) = false := by
            have hf : assignsLocal x.2.globals name 64 = assignsLocal globals name 64 := by
              rw [hx.definitions]
              funext form
              exact assignsLocal_compile globals name 64 form
            rw [hf, hany]
          simp only [letStep, hev, bind, Except.bind, hanyx, Bool.false_eq_true, ↓reduceIte]
        have hrestAgree : ∀ x : SV × State, Compat globals x.2 → SameResults
            (fun f => evalCompiled f (("", (freeze context x.2 x.1).1) :: clocals) context (freeze context x.2 x.1).2 cr)
            (fun f => rest.foldlM (letStep f context all body) ((name, (freeze context x.2 x.1).1) :: locals, (freeze context x.2 x.1).2) >>=
              fun y => evalSequence f y.1 context y.2 body) := by
          intro x hx
          refine ihB ⟨?_, ?_⟩ hr _ (hx.keep (keeps_freeze context x.2 x.1))
          · simp [ha.1]
          · simp [ha.2]
        rw [succeeds_succ (evalCompiled_mono context clocals s _)]
        simp only [hC]
        have mCont : ∀ x : SV × State, FuelMono fun f =>
            evalCompiled f (("", (freeze context x.2 x.1).1) :: clocals) context (freeze context x.2 x.1).2 cr :=
          fun x => evalCompiled_mono context _ _ cr
        rw [succeeds_bind (evalCompiled_mono context clocals s cv) mCont]
        simp only [List.foldlM_cons, except_bind_assoc]
        rw [succeeds_bind (letStep_mono context all body (locals, s) _)
          (fun mid => compile_rest_mono context all body rest mid)]
        constructor
        · rintro ⟨x, hx, hrest⟩
          obtain ⟨g, hg⟩ := (hagreeV x).1 hx
          have hcx := compat_eval hs hg
          exact ⟨_, ⟨g, hstep g x hcx hg⟩, (hrestAgree x hcx r).1 hrest⟩
        · rintro ⟨mid, ⟨g, hg⟩, hrest⟩
          have hg2 := hg
          simp only [letStep] at hg2
          obtain ⟨x, h1, _⟩ := bind_ok hg2
          have hcx := compat_eval hs h1
          have hg3 : letStep g context all body (locals, s) (.list [.atom name, value]) = .ok mid := hg
          rw [hstep g x hcx h1] at hg3
          simp only [Except.ok.injEq] at hg3
          subst hg3
          exact ⟨x, (hagreeV x).2 ⟨g, h1⟩, (hrestAgree x hcx r).2 hrest⟩
      · simp at h

/-- Compiled code agrees with the interpreter: where a form compiles, the two evaluators have the same successes,
with the same value and the same code, from any state with the definitions the form was compiled against. -/
theorem evalCompiled_agrees_eval {globals : Globals} {context : Context} {names : List String} {locals clocals : Locals}
    {form : Sexp} {compiled : CExp} {fuel : Nat} (ha : Aligned names locals clocals)
    (h : compileExp globals names fuel form = some compiled) {state : State} (hs : Compat globals state)
    (result : SV × State) :
    (∃ f, evalCompiled f clocals context state compiled = .ok result) ↔ ∃ f, eval f locals context state form = .ok result :=
  (compile_agrees globals context fuel).1 ha h state hs result

/-- The state a function is lifted in, when its definitions are compiled with `compileGlobals`. -/
theorem compat_of_index {globals : Globals} {state : State} (hg : state.globals = compileGlobals globals)
    (hi : ∀ name, state.operations.get? name =
      match Assoc.get name state.globals with
      | some (.callable callable) => some callable
      | _ => none) : Compat globals state := ⟨hg, hi⟩

/-- The index of `Environment.ofGlobals` agrees with the definitions: a name has the function that the first of its
bindings defines, if that does define one. -/
theorem ofGlobals_operations (globals : Globals) (name : String) :
    (Environment.ofGlobals globals).operations.get? name =
      match Assoc.get name (Environment.ofGlobals globals).globals with
      | some (.callable callable) => some callable
      | _ => none := by
  simp only [Environment.ofGlobals, Assoc.get]
  induction globals with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, List.lookup_cons]
    by_cases hk : name = key
    · subst hk
      cases value <;> simp
    · have hb : (name == key) = false := by simpa using hk
      have hb' : (key == name) = false := by simpa using Ne.symm hk
      simp only [hb]
      simp only [Std.HashMap.get?_eq_getElem?] at ih ⊢
      cases value <;>
        simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hb', Bool.false_eq_true, ↓reduceIte] <;>
        exact ih

/-- The state a function is lifted in by `liftWith`, for definitions compiled by `compileGlobals`, as in `lift`. -/
def liftState (globals : Globals) : State :=
  { globals := (Environment.ofGlobals (compileGlobals globals)).globals
    operations := (Environment.ofGlobals (compileGlobals globals)).operations }

theorem compat_ofGlobals (globals : Globals) : Compat globals (liftState globals) where
  definitions := rfl
  index := ofGlobals_operations (compileGlobals globals)

/-- Compiled code agrees with the interpreter on what `lift` runs it on, without a hypothesis about the state. -/
theorem evalCompiled_agrees_eval_ofGlobals {globals : Globals} {context : Context} {names : List String}
    {locals clocals : Locals} {form : Sexp} {compiled : CExp} {fuel : Nat} (ha : Aligned names locals clocals)
    (h : compileExp globals names fuel form = some compiled) (result : SV × State) :
    (∃ f, evalCompiled f clocals context (liftState globals) compiled = .ok result) ↔
      ∃ f, eval f locals context (liftState globals) form = .ok result :=
  evalCompiled_agrees_eval ha h (compat_ofGlobals globals) result
/-! Forms that make code. What the value of a form is, and what the code it makes does. -/

/-- A conditional on a value that is not known yet, with branches that make no code, is a BIL conditional on it, which
selects the branch that the condition says, in the larger of the two widths. -/
theorem evalConditional_dynamic {fuel : Nat} {locals : Locals} {context : Context} {state tested : State} {test : Sexp}
    {yes no : List Sexp} {value yesValue noValue : SV} {exp yesExp noExp : Bil.Exp} {yesWidth noWidth : Nat}
    {yesState noState : State} (ht : eval fuel locals context state test = .ok (value, tested))
    (hn : truth value = .ok none) (hc : condition context value = .ok exp)
    (hy : evalSequence fuel locals context { tested with code := [] } yes = .ok (yesValue, yesState))
    (hno : evalSequence fuel locals context { tested with code := [] } no = .ok (noValue, noState))
    (hyc : yesState.code = []) (hnc : noState.code = [])
    (hye : expectBil context yesValue = .ok (yesWidth, yesExp)) (hne : expectBil context noValue = .ok (noWidth, noExp)) :
    evalConditional (fuel + 1) locals context state test yes no =
      .ok (.bil (max yesWidth noWidth) (.ite exp (extend (max yesWidth noWidth) yesExp) (extend (max yesWidth noWidth) noExp)),
        { tested with nextTemp := max yesState.nextTemp noState.nextTemp }) := by
  rw [evalConditional]
  simp [ht, hn, hc, hy, hno, hyc, hnc, hye, hne, bind, Except.bind]

/-- Which is what the evaluation of the conditional says, at any environment. -/
theorem evalExp_conditional {env : Bil.Env} {exp yes no : Bil.Exp} {width : Nat} {bit : BitVec 1} {value : Bap.Value}
    (hc : Bil.evalExp env exp = .ok (.bits bit)) (h : Bil.evalExp env (if bit = 1 then extend width yes else extend width no) = .ok value) :
    Bil.evalExp env (.ite exp (extend width yes) (extend width no)) = .ok value := by
  rw [Bil.evalExp]
  simp only [hc, bind, Except.bind, Value.asBits]
  by_cases hb : bit = 1
  · simp only [hb, ↓reduceDIte, ↓reduceIte] at h ⊢
    exact h
  · simp only [hb, ↓reduceDIte, ↓reduceIte] at h ⊢
    exact h

/-- `freeze` keeps the value: either it depends on nothing, or a temporary that the code it adds moves it to, which is
fresh when `nextTemp` is, holds it from then on. This is what a `let` binding evaluates to. -/
theorem freezeBil_sound (state : State) (width : Nat) (exp : Bil.Exp) (env : Bil.Env) (value : Bap.Value) :
    (freezeBil state width exp).2.code = state.code ∧ (freezeBil state width exp).1 = .bil width exp ∨
      ∃ temporary : Bap.Var, (freezeBil state width exp).1 = .bil width (.var temporary) ∧
        (freezeBil state width exp).2.code = state.code ++ [.move temporary exp] ∧
        Bil.evalExp (Bil.bind env temporary value) (.var temporary) = .ok value := by
  unfold freezeBil
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨_, rfl, rfl, ?_⟩
    simp [Bil.evalExp, Bil.lookup, Bil.bind]

/-- `set` of a register of its own width is a move to it. -/
theorem assign_register {context : Context} {name : String} {width : Nat} {value : SV} {exp : Bil.Exp}
    (hn : name ≠ "XZR") (he : expectBil context value = .ok (width, exp)) :
    assign context (.register name width width) value = .ok [.move ⟨name, .imm width, 0, false⟩ exp] := by
  simp [assign, assignRegister, hn, he, bind, Except.bind, pure, Except.pure]

/-- `store-word` is a store to the memory of the context, and running it is `Memory.write`. -/
theorem storeMemory_write {context : Context} {address value : SV} {addressExp valueExp : Bil.Exp} {valueWidth : Nat}
    (ha : expectBil context address = .ok (context.bits, addressExp)) (hv : expectBil context value = .ok (valueWidth, valueExp))
    (hb : valueWidth % 8 = 0) :
    storeMemory context [address, value] =
      .ok [.move context.memory (.store (.var context.memory) addressExp valueExp context.endian (valueWidth / 8))] := by
  simp [storeMemory, ha, hv, hb, bind, Except.bind, pure, Except.pure]

/-! ### Parameters, symbols and intrinsics -/

/-- `defparameter` binds the name to the value of its form. -/
theorem evalTopLevel_defparameter {context : Context} {state after : State} {name : String} {form : Sexp}
    {rest : List Sexp} {value : SV} (h : eval 100000 [] context state form = .ok (value, after)) :
    evalTopLevel context state (.list (.atom "defparameter" :: .atom name :: form :: rest)) =
      .ok { after with globals := Assoc.put name value after.globals } := by
  rw [evalTopLevel]
  · simp only [h, bind, Except.bind]
  all_goals (intros; simp_all)

private theorem mapM_symbolText (names : List String) :
    (names.map Value.symbol).mapM symbolText = .ok names := by
  induction names with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons, List.mapM_cons, symbolText, bind, Except.bind, ih, pure, Except.pure]

private theorem span_no_sep (names : List String) (h : ":sep" ∉ names) :
    names.span (· != ":sep") = (names, []) := by
  have key : ∀ (items acc : List String), ":sep" ∉ items →
      List.span.loop (· != ":sep") items acc = (acc.reverse ++ items, []) := by
    intro items
    induction items with
    | nil => intro acc _; simp [List.span.loop]
    | cons head rest ih =>
      intro acc hm
      have hne : head ≠ ":sep" := fun e => hm (e ▸ List.mem_cons_self)
      have hb : (head != ":sep") = true := by simpa using hne
      simp only [List.span.loop, hb, ih (head :: acc) fun e => hm (List.mem_cons_of_mem _ e)]
      simp
  exact (key names [] h).trans (by simp)

/-- Symbols concatenate in order, with nothing between them when no separator is given. -/
theorem symbolConcat_plain (names : List String) (h : ":sep" ∉ names) :
    symbolConcat (names.map Value.symbol) = .ok (.symbol (String.join names)) := by
  simp only [symbolConcat, mapM_symbolText, bind, Except.bind, span_no_sep names h]

/-- With a separator, it is between the symbols. -/
theorem symbolConcat_separator (names : List String) (separator : String) (h : ":sep" ∉ names) :
    symbolConcat (names.map Value.symbol ++ [.symbol ":sep", .symbol separator]) =
      .ok (.symbol (String.intercalate separator names)) := by
  have hmap : names.map Value.symbol ++ [Value.symbol ":sep", .symbol separator] =
      (names ++ [":sep", separator]).map Value.symbol := by simp
  rw [hmap]
  simp only [symbolConcat, mapM_symbolText, bind, Except.bind]
  have key : ∀ (items acc : List String), ":sep" ∉ items →
      List.span.loop (· != ":sep") (items ++ [":sep", separator]) acc = (acc.reverse ++ items, [":sep", separator]) := by
    intro items
    induction items with
    | nil => intro acc _; simp [List.span.loop]
    | cons head rest ih =>
      intro acc hm
      have hne : head ≠ ":sep" := fun e => hm (e ▸ List.mem_cons_self)
      have hb : (head != ":sep") = true := by simpa using hne
      simp only [List.cons_append, List.span.loop, hb, ih (head :: acc) fun e => hm (List.mem_cons_of_mem _ e)]
      simp
  have hspan : (names ++ [":sep", separator]).span (· != ":sep") = (names, [":sep", separator]) :=
    (key names [] h).trans (by simp)
  simp only [hspan]

/-- An intrinsic's result is the output variable, and the call is its inputs followed by the special. Without a
keyword among the inputs, that is the whole of the code. -/
theorem intrinsicParams_inputs (key : String) (current inputs : List SV)
    (h : ∀ keyword, Value.symbol keyword ∈ inputs → keyword ≠ ":result" ∧ keyword ≠ ":writes" ∧ keyword ≠ ":stores" ∧
      keyword ≠ ":aborts") (width : BitVec 64) :
    intrinsicParams key current (inputs ++ [.symbol ":result", .int width]) =
      [(key, current.reverse ++ inputs), (":result", [.int width])] := by
  induction inputs generalizing current with
  | nil => simp [intrinsicParams]
  | cons head rest ih =>
    have hstep : ∀ tail, intrinsicParams key current (head :: tail) = intrinsicParams key (head :: current) tail := by
      intro tail
      cases head
      case symbol keyword =>
        obtain ⟨h1, h2, h3, h4⟩ := h keyword List.mem_cons_self
        simp [intrinsicParams, h1, h2, h3, h4]
      all_goals simp [intrinsicParams]
    rw [List.cons_append, hstep, ih (head :: current) (fun keyword hk => h keyword (List.mem_cons_of_mem _ hk))]
    simp

/-- The next call of an intrinsic overwrites `intrinsic:y0`, so the value of a call is a copy in a fresh temporary. -/
theorem freeze_intrinsic_copy (context : Context) (state : State) (width : Nat) :
    freeze context state (.bil width (.var ⟨"intrinsic:y0", .imm width, 0, false⟩)) =
      (.bil width (.var ⟨s!"_primus_{state.nextTemp}", .imm width, 0, false⟩),
        { state with
          code := state.code ++ [.move ⟨s!"_primus_{state.nextTemp}", .imm width, 0, false⟩
            (.var ⟨"intrinsic:y0", .imm width, 0, false⟩)]
          nextTemp := state.nextTemp + 1 }) := by
  simp [freeze, freezeBil, Bil.evalExp, Bil.lookup]

/-- A primitive with an intrinsic's result has it copied by the call. -/
theorem intrinsicResult_call : intrinsicResult "intrinsic" = true ∧ intrinsicResult "+." = true ∧
    intrinsicResult "is-nan" = true := by
  decide +kernel

/-- The empty high part, when a value has the width of its register. -/
theorem cast_high_empty (context : Context) (value : SV) {source : Nat} {exp : Bil.Exp}
    (h : expectBil context value = .ok (source, exp)) :
    primCast context .high [.int 0, value] = .ok (.bil 0 (.int 0#0)) := by
  simp [primCast, expectNat, h, bind, Except.bind]

/-- An empty part changes nothing in a concatenation. -/
theorem concatStep_empty (context : Context) (current : Nat × Bil.Exp) :
    concatStep context current (.bil 0 (.int 0#0)) = .ok current := by
  simp [concatStep, expectBil, bind, Except.bind]

theorem concatStep_first (context : Context) (exp : Bil.Exp) {value : SV} {width : Nat} {right : Bil.Exp}
    (h : expectBil context value = .ok (width, right)) (hw : width ≠ 0) :
    concatStep context (0, exp) value = .ok (width, right) := by
  simp [concatStep, h, hw, bind, Except.bind]

end Semantics

/-! ### Lowering helpers of the lifted executor -/

section Lifted

open Bap.Primus.Lifted
open_private Bap.Primus.Lifted Bap.Primus.Lifted Lowering Lowering.layout Lowering.nextSlot Lowering.ops Lowering.inputs
  Lowering.outputs Lowering.written Lowering.effectSlot Lowering.memory Lowering.checkpoints Lowering.mk
  widthOf slot temporary readVar writeVar setEffect mask narrow useMemory atCodeStop directEdges reachable
  reachable.loop syncState graphEdgeOps Lowering.nextLabel Lowering.next Operand Operand.slot Operand.width Operand.mk
  lowerExp lowerMove lowerStmt lowerStatements immediate signExtend isSigned isComparison binaryOp addressOf readsMemory
  jumpConstant jumpSlot encodeState slotBits syncUpdates reachedOutputs withoutBindings useMemoryAt wrapSafe recordWrite

open_private Bap.Bil.Eval Bap.Bil evalUn expectMemory

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
    simp only [writeVar, hw, bind, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_, rfl⟩
    · show var ∈ (if _ then _ else _)
      split
      · rename_i hc
        simpa using hc
      · simp
    · show (var, (slot lowering var).2) ∈ (if _ then _ else _)
      split
      · rename_i hc
        simpa using hc
      · simp

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
    simp only [readVar, hv, bind, Option.bind_some, hw', Bool.true_or, ↓reduceIte,
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
  unfold useMemory at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · next hm =>
    split at h
    · next he =>
      simp only [Option.some.injEq] at h
      subst h
      rw [hm]
      exact congrArg some (eq_of_beq he)
    · simp at h
  · simp at h

/-- An access goes to `useMemory`, once its size is safe on that memory. -/
theorem useMemoryAt_some {lowering result : Lowering} {var : Bap.Var} {size : Nat}
    (h : useMemoryAt lowering var size = some result) : useMemory lowering var = some result := by
  unfold useMemoryAt at h
  split at h
  · exact h
  · simp at h

theorem useMemory_conflict (lowering : Lowering) (var existing : Bap.Var) (width : Nat)
    (ht : var.typ = .mem width 8) (he : Lowering.memory lowering = some existing) (hne : existing ≠ var) :
    useMemory lowering var = none := by
  simp only [useMemory, ht, he]
  simp [hne]

/-- Rolling back to a code stop restores the outputs saved at that site. -/
theorem atCodeStop_restores (lowering : Lowering) (pc : Nat) (checkpoint : Nat × List (Bap.Var × Nat))
    (h : (Lowering.checkpoints lowering).find? (fun checkpoint => checkpoint.1 = pc) = some checkpoint) :
    Lowering.outputs (atCodeStop lowering pc) = checkpoint.2 := by
  simp only [atCodeStop]
  rw [h]

theorem directEdges_length (block : Block) (chain : Bool) : (directEdges block chain).length ≤ 2 := by
  simp only [directEdges]
  split <;> (try split) <;> simp

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

/-- Taking out the bindings of other variables changes nothing about a variable. -/
private theorem find?_withoutBindings (env : Bil.Env) (pending : List Bap.Var) {var : Bap.Var} (hv : var ∉ pending) :
    (withoutBindings pending env).find? (fun binding => binding.1 == var) =
      env.find? (fun binding => binding.1 == var) := by
  induction env generalizing pending with
  | nil => simp [withoutBindings]
  | cons head rest ih =>
    simp only [withoutBindings]
    split
    · rfl
    · split
      · rename_i hc
        have hne : head.1 ≠ var := by
          intro he
          exact hv (he ▸ (by simpa using hc))
        have hb : (head.1 == var) = false := by simpa using hne
        rw [ih _ (fun hm => hv (List.mem_of_mem_erase hm))]
        simp [hb]
      · simp only [List.find?_cons, ih _ hv]

/-- Native execution writes back only declared outputs: every other variable is untouched. -/
theorem syncState_frame (lowering : Lowering) (state : Bil.State) (slots : Array UInt64) (var : Bap.Var)
    (hv : var ∉ (Lowering.outputs lowering).map Prod.fst) :
    Bil.lookup (syncState lowering state slots).env var = Bil.lookup state.env var := by
  simp only [syncState]
  have hv : var ∉ (reachedOutputs lowering slots).map Prod.fst := by
    intro hm
    apply hv
    obtain ⟨output, ho, he⟩ := List.mem_map.1 hm
    refine List.mem_map.2 ⟨output, ?_, he⟩
    unfold reachedOutputs at ho
    split at ho
    · exact ho
    · exact (List.mem_filter.1 ho).1
  have hkeys : var ∉ (syncUpdates (reachedOutputs lowering slots) slots).map Prod.fst := by
    generalize reachedOutputs lowering slots = outputs at hv
    induction outputs with
    | nil => simp [syncUpdates]
    | cons head rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hv
      simp only [syncUpdates, List.foldr_cons]
      split
      · simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨hv.1, ih hv.2⟩
      · exact ih hv.2
  generalize syncUpdates (reachedOutputs lowering slots) slots = updates at hkeys
  simp only [Bil.lookup, List.find?_append]
  have hnone : updates.find? (fun binding => binding.1 == var) = none := by
    apply List.find?_eq_none.2
    intro x hx he
    exact hkeys (List.mem_map.2 ⟨x, hx, by simpa using he⟩)
  rw [hnone, find?_withoutBindings _ _ hkeys]
  rfl

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

/-! ### A semantics of the native operations

`bap_jit.cpp` turns the operations into LLVM IR, which cannot be verified here. These definitions state what
each operation does in terms of that IR, and everything below is proved against them. -/

abbrev Word64 := BitVec 64

/-- The machine that runs operations: 64-bit slots and a byte-addressed memory. `view` is where an address goes.
Native code has `id` for it, and then a multi-byte access at the end of an address space narrower than 64 bits
goes past it. On a machine whose `view` wraps at the end of the address space, such an access does what the
interpreter does. Accesses that do not pass the end do the same on both (`denoteLoad_view`, `denoteStore_view`), and
the ones that do, native code does not get to make (`Lifted.wrapSafe`). -/
structure Machine where
  slots : Nat → Word64
  memory : Word64 → UInt8
  view : Word64 → Word64 := id
  /-- Which slots a `move` wrote. No native code keeps this: it is what the proofs say about the flags of a range with. -/
  moved : Nat → Bool := fun _ => false
  /-- The environment that a run started from, likewise. -/
  origin : Bil.Env := []

def Machine.write (machine : Machine) (slot : Nat) (value : Word64) : Machine :=
  { machine with slots := fun other => if other = slot then value else machine.slots other }

@[simp] theorem Machine.write_slots (machine : Machine) (slot other : Nat) (value : Word64) :
    (machine.write slot value).slots other = if other = slot then value else machine.slots other := rfl

@[simp] theorem Machine.write_memory (machine : Machine) (slot : Nat) (value : Word64) :
    (machine.write slot value).memory = machine.memory := rfl

/-- A `move`: a write that counts as one of a variable. -/
def Machine.markMove (machine : Machine) (slot : Nat) (value : Word64) : Machine :=
  { machine.write slot value with moved := fun other => other == slot || machine.moved other }

@[simp] theorem Machine.markMove_slots (machine : Machine) (slot other : Nat) (value : Word64) :
    (machine.markMove slot value).slots other = if other = slot then value else machine.slots other := rfl

@[simp] theorem Machine.markMove_memory (machine : Machine) (slot : Nat) (value : Word64) :
    (machine.markMove slot value).memory = machine.memory := rfl

private def flag (condition : Bool) : Word64 := if condition then 1 else 0

/-- `case 5` of `bap_jit.cpp`. -/
def denoteBin : Jit.BinOp → Word64 → Word64 → Word64
  | .add, l, r => l + r
  | .sub, l, r => l - r
  | .mul, l, r => l * r
  | .and, l, r => l &&& r
  | .or, l, r => l ||| r
  | .xor, l, r => l ^^^ r
  | .lshift, l, r => if 64 ≤ r.toNat then 0 else l <<< r.toNat
  | .rshift, l, r => if 64 ≤ r.toNat then 0 else l >>> r.toNat
  | .eq, l, r => flag (l == r)
  | .neq, l, r => flag (l != r)
  | .lt, l, r => flag (decide (l.toNat < r.toNat))
  | .le, l, r => flag (decide (l.toNat ≤ r.toNat))
  | .gt, l, r => flag (decide (r.toNat < l.toNat))
  | .ge, l, r => flag (decide (r.toNat ≤ l.toNat))
  | .udiv, l, r => if r = 0 then BitVec.allOnes 64 else l / r
  | .urem, l, r => if r = 0 then l else l % r
  | .sdiv, l, r =>
    if r = 0 then (if l.msb then 1 else BitVec.allOnes 64) else if l = BitVec.intMin 64 ∧ r = BitVec.allOnes 64 then l else l.sdiv r
  | .srem, l, r =>
    if r = 0 then l else if l = BitVec.intMin 64 ∧ r = BitVec.allOnes 64 then 0 else l.srem r
  | .slt, l, r => flag (decide (l.toInt < r.toInt))
  | .sle, l, r => flag (decide (l.toInt ≤ r.toInt))
  | .sgt, l, r => flag (decide (r.toInt < l.toInt))
  | .sge, l, r => flag (decide (r.toInt ≤ l.toInt))

/-- `case 7`: a shift left and an arithmetic shift right. -/
def denoteSignExtend (width : Nat) (value : Word64) : Word64 :=
  if width < 64 then (value <<< (64 - width)).sshiftRight (64 - width) else value

/-- `case 11`: the amount saturates at the width. -/
def denoteAshr (width : Nat) (value amount : Word64) : Word64 :=
  value.sshiftRight (if width ≤ amount.toNat then width - 1 else amount.toNat)

/-- `case 15`: a byte at a time, each or-ed in at its position. -/
def denoteLoad (memory : Word64 → UInt8) (base : Word64) (size : Nat) (big : Bool) : Word64 :=
  (List.range size).foldl (fun result index =>
    result ||| (BitVec.ofNat 64 (memory (base + BitVec.ofNat 64 index)).toNat <<<
      ((if big then size - 1 - index else index) * 8))) 0

/-- `case 16`: a byte at a time, the later bytes over the earlier. -/
def denoteStore (memory : Word64 → UInt8) (view : Word64 → Word64) (base value : Word64) (size : Nat) (big : Bool) :
    Word64 → UInt8 :=
  (List.range size).foldl (fun memory index address =>
    if address = view (base + BitVec.ofNat 64 index) then
      UInt8.ofNat ((value >>> ((if big then size - 1 - index else index) * 8)).toNat % 256)
    else memory address) memory

/-- The effect of an operation on the machine, for the operations that continue with the next one. -/
def step (machine : Machine) : Jit.Op → Machine
  | .set dst immediate => machine.write dst immediate.toBitVec
  | .move dst src => machine.markMove dst (machine.slots src)
  | .add dst src immediate => machine.write dst (machine.slots src + immediate.toBitVec)
  | .bin op dst left right => machine.write dst (denoteBin op (machine.slots left) (machine.slots right))
  | .andImm dst src immediate => machine.write dst (machine.slots src &&& immediate.toBitVec)
  | .signExtend width dst src => machine.write dst (denoteSignExtend width (machine.slots src))
  | .select dst condition yes no =>
    machine.write dst (if machine.slots condition ≠ 0 then machine.slots yes else machine.slots no)
  | .neg dst src => machine.write dst (-machine.slots src)
  | .not dst src => machine.write dst (~~~machine.slots src)
  | .ashr width dst left right => machine.write dst (denoteAshr width (machine.slots left) (machine.slots right))
  | .memLoad dst address size big =>
    machine.write dst (denoteLoad (fun address => machine.memory (machine.view address)) (machine.slots address) size big)
  | .memStore address value size big =>
    { machine with
      memory := denoteStore machine.memory machine.view (machine.slots address) (machine.slots value) size big }
  | _ => machine

def runOps (machine : Machine) (ops : List Jit.Op) : Machine := ops.foldl step machine

@[simp] theorem runOps_nil (machine : Machine) : runOps machine [] = machine := rfl
@[simp] theorem runOps_cons (machine : Machine) (op : Jit.Op) (ops : List Jit.Op) :
    runOps machine (op :: ops) = runOps (step machine op) ops := rfl
theorem runOps_append (machine : Machine) (first second : List Jit.Op) :
    runOps machine (first ++ second) = runOps (runOps machine first) second := by
  simp [runOps, List.foldl_append]

/-- A slot holds a value when it is the value extended with zeros. Lowering keeps this for all operands. -/
def Holds {width : Nat} (slot : Word64) (value : BitVec width) : Prop := slot.toNat = value.toNat

/-! The operators at a width of at most 64 bits, on slots that hold their operands. -/

section Operators

variable {w : Nat} {l r : Word64} {a b : BitVec w}

private theorem pow_dvd_64 (hw : w ≤ 64) : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw

private theorem mod_narrow (hw : w ≤ 64) (n : Nat) : n % 2 ^ 64 % 2 ^ w = n % 2 ^ w :=
  Nat.mod_mod_of_dvd n (pow_dvd_64 hw)

theorem mask_toBitVec_toNat (hw : w ≤ 64) : (mask w).toBitVec.toNat = 2 ^ w - 1 := by
  have h1 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [mask]
  exact Nat.mod_eq_of_lt (by omega)

/-- Narrowing is the remainder. -/
theorem and_mask_toNat (hw : w ≤ 64) (v : Word64) : (v &&& (mask w).toBitVec).toNat = v.toNat % 2 ^ w := by
  simp only [BitVec.toNat_and, mask_toBitVec_toNat hw]
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- What `narrow` makes of the slot: the value in the operator's width. -/
def narrowed (w : Nat) (v : Word64) : Nat := v.toNat % 2 ^ w

theorem narrow_add (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l + r) = (a + b).toNat := by
  simp only [Holds] at hl hr
  simp only [narrowed, BitVec.toNat_add, hl, hr, mod_narrow hw]

theorem narrow_mul (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l * r) = (a * b).toNat := by
  simp only [Holds] at hl hr
  simp only [narrowed, BitVec.toNat_mul, hl, hr, mod_narrow hw]

theorem narrow_sub (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l - r) = (a - b).toNat := by
  simp only [Holds] at hl hr
  simp only [narrowed, BitVec.toNat_sub, hl, hr, mod_narrow hw]
  have hb := b.isLt
  have h1 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  obtain ⟨k, hk⟩ := pow_dvd_64 hw
  have : 2 ^ 64 - b.toNat + a.toNat = (2 ^ w - b.toNat + a.toNat) + 2 ^ w * (k - 1) := by
    have hk1 : 1 ≤ k := by
      rcases k with _ | k
      · simp at hk
      · omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [hk, Nat.mul_add]
    omega
  rw [this, Nat.add_mul_mod_self_left]

theorem narrow_neg (hw : w ≤ 64) (hv : Holds l a) : narrowed w (-l) = (-a).toNat := by
  have : -l = 0 - l := by simp
  have h2 : -a = 0 - a := by simp
  rw [this, h2]
  exact narrow_sub hw (by simp [Holds]) hv

theorem narrow_not (hw : w ≤ 64) (hv : Holds l a) : narrowed w (~~~l) = (~~~a).toNat := by
  simp only [Holds] at hv
  have hb := a.isLt
  have hle : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  simp only [narrowed, BitVec.toNat_not, hv]
  obtain ⟨k, hk⟩ := pow_dvd_64 hw
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk
    · omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have : 2 ^ 64 - 1 - a.toNat = (2 ^ w - 1 - a.toNat) + 2 ^ w * j := by
    rw [hk, Nat.mul_add]
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem narrow_and (_hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l &&& r) = (a &&& b).toNat := by
  simp only [Holds] at hl hr
  have := (a &&& b).isLt
  simp only [narrowed, BitVec.toNat_and, hl, hr]
  simpa using Nat.mod_eq_of_lt this

theorem narrow_or (_hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l ||| r) = (a ||| b).toNat := by
  simp only [Holds] at hl hr
  have := (a ||| b).isLt
  simp only [narrowed, BitVec.toNat_or, hl, hr]
  simpa using Nat.mod_eq_of_lt this

theorem narrow_xor (_hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) : narrowed w (l ^^^ r) = (a ^^^ b).toNat := by
  simp only [Holds] at hl hr
  have := (a ^^^ b).isLt
  simp only [narrowed, BitVec.toNat_xor, hl, hr]
  simpa using Nat.mod_eq_of_lt this

/-- A shift of 64 or more leaves nothing, in the native code by a check and in BIL at any width. -/
theorem narrow_lshift (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) :
    narrowed w (denoteBin .lshift l r) = (Word.shl a b).toNat := by
  simp only [Holds] at hl hr
  have hval : (Word.shl a b).toNat = a.toNat * 2 ^ b.toNat % 2 ^ w := by
    simp only [Word.shl, Word.toNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [hval]
  simp only [narrowed, denoteBin, hr]
  split
  · next hge =>
    have : 2 ^ w ∣ 2 ^ b.toNat := Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨k, hk⟩ := this
    rw [hk, ← Nat.mul_assoc, Nat.mul_comm a.toNat, Nat.mul_assoc, Nat.mul_mod_right]
    simp
  · simp only [BitVec.toNat_shiftLeft, hl, Nat.shiftLeft_eq, mod_narrow hw]

theorem narrow_rshift (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) :
    narrowed w (denoteBin .rshift l r) = (Word.lshr a b).toNat := by
  simp only [Holds] at hl hr
  have ha := a.isLt
  have hval : (Word.lshr a b).toNat = a.toNat / 2 ^ b.toNat := by
    simp only [Word.lshr, Word.toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [hval]
  simp only [narrowed, denoteBin, hr]
  split
  · next hge =>
    have hlt : a.toNat < 2 ^ b.toNat := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.div_eq_of_lt hlt]
    simp
  · simp only [BitVec.toNat_ushiftRight, hl, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)

theorem narrow_udiv (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) :
    narrowed w (denoteBin .udiv l r) = (Word.udiv a b).toNat := by
  simp only [Holds] at hl hr
  have ha := a.isLt
  have hzero : r = 0 ↔ b = 0 := by
    constructor
    · intro e; subst e; exact BitVec.eq_of_toNat_eq (by simpa using hr.symm)
    · intro e; subst e; exact BitVec.eq_of_toNat_eq (by simpa using hr)
  simp only [narrowed, denoteBin, Word.udiv, hzero]
  split
  · simp only [BitVec.toNat_allOnes, Word.ones, Word.toNat]
    have h1 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
    have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
    obtain ⟨k, hk⟩ := pow_dvd_64 hw
    have hk1 : 1 ≤ k := by
      rcases k with _ | k
      · simp at hk
      · omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : 2 ^ 64 - 1 = (2 ^ w - 1) + 2 ^ w * j := by
      rw [hk, Nat.mul_add]
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp only [BitVec.toNat_udiv, hl, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)

theorem narrow_urem (_hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) :
    narrowed w (denoteBin .urem l r) = (Word.urem a b).toNat := by
  simp only [Holds] at hl hr
  have ha := a.isLt
  have hzero : r = 0 ↔ b = 0 := by
    constructor
    · intro e; subst e; exact BitVec.eq_of_toNat_eq (by simpa using hr.symm)
    · intro e; subst e; exact BitVec.eq_of_toNat_eq (by simpa using hr)
  simp only [narrowed, denoteBin, Word.urem, hzero]
  split
  · simp only [hl]
    exact Nat.mod_eq_of_lt ha
  · simp only [BitVec.toNat_umod, hl, hr]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)

/-! Comparisons give one bit. -/

private theorem flag_toNat (c : Bool) : (flag c).toNat = c.toNat := by
  cases c <;> simp [flag]

theorem compare_eq (hl : Holds l a) (hr : Holds r b) : (denoteBin .eq l r).toNat = (Word.eq a b).toNat := by
  simp only [Holds] at hl hr
  have : (l == r) = (a == b) := by
    have h1 : l = r ↔ a = b := by
      rw [BitVec.toNat_eq, BitVec.toNat_eq, hl, hr]
    cases h : (a == b) <;> simp_all
  simp only [denoteBin, this, Word.eq, Word.bool, flag_toNat, Word.toNat]
  cases (a == b) <;> rfl

theorem compare_neq (hl : Holds l a) (hr : Holds r b) : (denoteBin .neq l r).toNat = (Word.neq a b).toNat := by
  simp only [Holds] at hl hr
  have : (l != r) = (a != b) := by
    have h1 : l = r ↔ a = b := by
      rw [BitVec.toNat_eq, BitVec.toNat_eq, hl, hr]
    cases h : (a != b) <;> simp_all
  simp only [denoteBin, this, Word.neq, Word.bool, flag_toNat, Word.toNat]
  cases (a != b) <;> rfl

private theorem bool_toNat (c : Prop) [Decidable c] : (Word.bool (decide c)).toNat = (flag (decide c)).toNat := by
  by_cases h : c <;> simp [Word.bool, flag, h, Word.toNat]

theorem compare_lt (hl : Holds l a) (hr : Holds r b) : (denoteBin .lt l r).toNat = (Word.lt a b).toNat := by
  simp only [Holds] at hl hr
  simp only [denoteBin, hl, hr, Word.lt, BitVec.lt_def, ← bool_toNat]

theorem compare_le (hl : Holds l a) (hr : Holds r b) : (denoteBin .le l r).toNat = (Word.le a b).toNat := by
  simp only [Holds] at hl hr
  simp only [denoteBin, hl, hr, Word.le, BitVec.le_def, ← bool_toNat]

theorem compare_gt (hl : Holds l a) (hr : Holds r b) : (denoteBin .gt l r).toNat = (Word.lt b a).toNat := by
  simp only [Holds] at hl hr
  simp only [denoteBin, hl, hr, Word.lt, BitVec.lt_def, ← bool_toNat]

theorem compare_ge (hl : Holds l a) (hr : Holds r b) : (denoteBin .ge l r).toNat = (Word.le b a).toNat := by
  simp only [Holds] at hl hr
  simp only [denoteBin, hl, hr, Word.le, BitVec.le_def, ← bool_toNat]

end Operators

/-! The signed operators read the sign extension of their operands. -/

section Signed

variable {w : Nat} {l r : Word64} {a b : BitVec w}

/-- The native sign extension of a slot that holds a value is the sign extension of the value. -/
theorem denoteSignExtend_holds (h0 : 0 < w) (hw : w ≤ 64) (hl : Holds l a) :
    denoteSignExtend w l = a.signExtend 64 := by
  have hval : l = a.setWidth 64 := BitVec.eq_of_toNat_eq (by
    simp only [Holds] at hl
    simp only [BitVec.toNat_setWidth, hl]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hw))).symm)
  subst hval
  unfold denoteSignExtend
  split
  · next hlt =>
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
    by_cases h1 : i < w
    · have h2 : 64 - w + i < 64 := by omega
      simp [h2, h1, show ¬ (64 ≤ i) by omega, show ¬ (64 - w + i < 64 - w) by omega,
        show 64 - w + i - (64 - w) = i by omega]
    · have h2 : ¬ (64 - w + i < 64) := by omega
      have h3 : (64 - 1 < 64 - w) = False := by simp; omega
      have h4 : 64 - 1 - (64 - w) = w - 1 := by omega
      simp [h2, h1, h3, h4, show ¬ (64 ≤ i) by omega, show i < 64 by omega]
      omega
  · have : w = 64 := by omega
    subst this
    simp

private theorem bridge {x : Word64} {y : BitVec w} (hw : w ≤ 64)
    (h : x.toInt % (2 ^ w : Nat) = y.toInt % (2 ^ w : Nat)) : narrowed w x = y.toNat := by
  have h1 : narrowed w x = (BitVec.ofInt w x.toInt).toNat := by
    have : BitVec.ofInt w x.toInt = x.setWidth w := by
      have := BitVec.signExtend_eq_setWidth_of_le x hw
      simpa [BitVec.signExtend] using this
    rw [this]
    simp [narrowed, BitVec.toNat_setWidth]
  have h2 : y.toNat = (BitVec.ofInt w y.toInt).toNat := by simp
  rw [h1, h2, BitVec.toNat_ofInt, BitVec.toNat_ofInt, h]

private theorem sext_toInt (hw : w ≤ 64) : (a.signExtend 64).toInt = a.toInt :=
  BitVec.toInt_signExtend_of_le hw

private theorem sext_eq_zero (hw : w ≤ 64) : a.signExtend 64 = 0 ↔ a = 0 := by
  constructor
  · intro h
    have : (a.signExtend 64).toInt = (0 : BitVec 64).toInt := by rw [h]
    rw [sext_toInt hw] at this
    apply BitVec.eq_of_toInt_eq
    simpa using this
  · intro h
    subst h
    apply BitVec.eq_of_toInt_eq
    rw [sext_toInt hw]
    simp

private theorem allOnes_narrow (hw : w ≤ 64) : narrowed w (BitVec.allOnes 64) = (BitVec.allOnes w).toNat := by
  simp only [narrowed, BitVec.toNat_allOnes]
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨k, hk⟩ : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  have hle : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp at hk
    · omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have : 2 ^ 64 - 1 = (2 ^ w - 1) + 2 ^ w * j := by
    rw [hk, Nat.mul_add]
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

private theorem sext_msb (hw : w ≤ 64) (h0 : 0 < w) : (a.signExtend 64).msb = a.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
  have : ¬ (64 - 1 < w) ∨ w = 64 := by omega
  rcases this with h | h
  · simp [h, BitVec.msb_eq_getLsbD_last]
  · subst h; simp [BitVec.msb_eq_getLsbD_last]

private theorem smtSDiv_zero (a : BitVec w) : a.smtSDiv 0 = if a.msb then 1 else BitVec.allOnes w := by
  unfold BitVec.smtSDiv BitVec.smtUDiv
  cases h : a.msb
  · simp [BitVec.msb_zero]
  · simp only [ite_true]
    simp [← BitVec.neg_one_eq_allOnes]

private theorem smtSDiv_of_ne (a b : BitVec w) (hb : b ≠ 0) : a.smtSDiv b = a.sdiv b := by
  have hn : -b ≠ 0 := by simpa using hb
  unfold BitVec.smtSDiv BitVec.sdiv BitVec.smtUDiv
  cases a.msb <;> cases b.msb <;> simp
  all_goals intro h; first | exact absurd h hb | exact absurd h hn

/-- Signed division on 64 bits of the extensions is signed division at the width, also of the most negative
value by -1, which wraps at the width and not on 64 bits. -/
theorem narrow_sdiv (hw : w ≤ 64) :
    narrowed w (denoteBin .sdiv (a.signExtend 64) (b.signExtend 64)) = (Word.sdiv a b).toNat := by
  by_cases hb : b = 0
  · subst hb
    have : (0 : BitVec w).signExtend 64 = 0 := (sext_eq_zero hw).2 rfl
    simp only [denoteBin, this, Word.sdiv, ite_true, smtSDiv_zero]
    rcases Nat.eq_zero_or_pos w with rfl | h0
    · simp [narrowed, Nat.mod_one, BitVec.eq_nil a, Word.toNat]
    · rw [sext_msb hw h0]
      cases a.msb
      · simpa [Word.toNat] using allOnes_narrow hw
      · simp [narrowed, Word.toNat]
  · have hne : b.signExtend 64 ≠ 0 := fun e => hb ((sext_eq_zero hw).1 e)
    have hstep : denoteBin .sdiv (a.signExtend 64) (b.signExtend 64) = (a.signExtend 64).sdiv (b.signExtend 64) := by
      simp only [denoteBin, hne, ite_false]
      split
      · next ho =>
        obtain ⟨h1, h2⟩ := ho
        rw [h1, h2, ← BitVec.neg_one_eq_allOnes, BitVec.intMin_sdiv_neg_one]
      · rfl
    simp only [Word.sdiv, smtSDiv_of_ne a b hb]
    rw [hstep]
    apply bridge hw
    rw [BitVec.toInt_sdiv, BitVec.toInt_sdiv, sext_toInt hw, sext_toInt hw, Int.bmod_emod]
    have hdvd : ((2 ^ w : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) := Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow 2 hw)
    rw [← Int.emod_emod_of_dvd _ hdvd, Int.bmod_emod, Int.emod_emod_of_dvd _ hdvd]

/-- Signed remainder takes the sign of the dividend, at any width. -/
theorem narrow_srem (hw : w ≤ 64) :
    narrowed w (denoteBin .srem (a.signExtend 64) (b.signExtend 64)) = (Word.srem a b).toNat := by
  by_cases hb : b = 0
  · subst hb
    have : (0 : BitVec w).signExtend 64 = 0 := (sext_eq_zero hw).2 rfl
    simp only [denoteBin, this, Word.srem, ite_true, Word.toNat]
    apply bridge hw
    rw [sext_toInt hw]
  · have hne : b.signExtend 64 ≠ 0 := fun e => hb ((sext_eq_zero hw).1 e)
    have hstep : denoteBin .srem (a.signExtend 64) (b.signExtend 64) = (a.signExtend 64).srem (b.signExtend 64) := by
      simp only [denoteBin, hne, ite_false]
      split
      · next ho =>
        obtain ⟨h1, h2⟩ := ho
        apply BitVec.eq_of_toInt_eq
        rw [h1, h2, BitVec.toInt_srem, BitVec.toInt_allOnes]
        simp
      · rfl
    simp only [Word.srem, hb, ite_false, Word.toNat]
    rw [hstep]
    apply bridge hw
    rw [BitVec.toInt_srem, BitVec.toInt_srem, sext_toInt hw, sext_toInt hw]

private theorem flag_toNat' (c : Bool) : (flag c).toNat = c.toNat := by
  cases c <;> simp [flag]

private theorem word_bool_toNat (c : Bool) : BitVec.toNat (Word.bool c) = c.toNat := by
  cases c <;> rfl

theorem compare_slt (hw : w ≤ 64) :
    (denoteBin .slt (a.signExtend 64) (b.signExtend 64)).toNat = (Word.slt a b).toNat := by
  simp only [denoteBin, flag_toNat', Word.slt, word_bool_toNat, sext_toInt hw, BitVec.slt_eq_decide, Word.toNat]

theorem compare_sle (hw : w ≤ 64) :
    (denoteBin .sle (a.signExtend 64) (b.signExtend 64)).toNat = (Word.sle a b).toNat := by
  simp only [denoteBin, flag_toNat', Word.sle, word_bool_toNat, sext_toInt hw, BitVec.sle_eq_decide, Word.toNat]

theorem compare_sgt (hw : w ≤ 64) :
    (denoteBin .sgt (a.signExtend 64) (b.signExtend 64)).toNat = (Word.slt b a).toNat := by
  simp only [denoteBin, flag_toNat', Word.slt, word_bool_toNat, sext_toInt hw, BitVec.slt_eq_decide, Word.toNat]

theorem compare_sge (hw : w ≤ 64) :
    (denoteBin .sge (a.signExtend 64) (b.signExtend 64)).toNat = (Word.sle b a).toNat := by
  simp only [denoteBin, flag_toNat', Word.sle, word_bool_toNat, sext_toInt hw, BitVec.sle_eq_decide, Word.toNat]

private theorem shift_saturates (h0 : 0 < w) {n : Nat} (hn : w ≤ n) :
    a.toInt >>> (w - 1) = a.toInt >>> n := by
  have hu : a.toInt < ((2 ^ (w - 1) : Nat) : Int) := by
    have := BitVec.toInt_lt (x := a)
    simpa [Int.natCast_pow] using this
  have hl : -((2 ^ (w - 1) : Nat) : Int) ≤ a.toInt := by
    have := BitVec.le_toInt a
    simpa [Int.natCast_pow] using this
  have hpn : ((2 ^ (w - 1) : Nat) : Int) ≤ ((2 ^ n : Nat) : Int) :=
    Int.ofNat_le.2 (Nat.pow_le_pow_right (by decide) (by omega))
  have hp0 : (0 : Int) < ((2 ^ (w - 1) : Nat) : Int) := by
    have := Nat.two_pow_pos (w - 1)
    omega
  simp only [Int.shiftRight_eq_div_pow]
  by_cases hs : 0 ≤ a.toInt
  · rw [Int.ediv_eq_zero_of_lt hs (by omega), Int.ediv_eq_zero_of_lt hs (by omega)]
  · have key : ∀ d : Int, 0 < d → -d ≤ a.toInt → a.toInt / d = -1 := by
      intro d hd hle
      have h1 : (a.toInt + d * 1) / d = a.toInt / d + 1 := Int.add_mul_ediv_left _ _ (by omega)
      have h2 : (a.toInt + d * 1) / d = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
      omega
    rw [key _ hp0 (by omega), key _ (by omega) (by omega)]

/-- An arithmetic shift of the extension, also by the width or more, which saturates in the native code. -/
theorem narrow_ashr (h0 : 0 < w) (hw : w ≤ 64) (hr : Holds r b) :
    narrowed w (denoteAshr w (a.signExtend 64) r) = (Word.ashr a b).toNat := by
  simp only [Holds] at hr
  simp only [Word.ashr, Word.toNat]
  apply bridge hw
  simp only [denoteAshr, hr, BitVec.toInt_sshiftRight, sext_toInt hw]
  split
  · next hge => rw [shift_saturates h0 hge]
  · rfl

/-- The signed casts. -/
theorem narrow_cast_signed {width : Nat} (hw : w ≤ 64) (hle : w ≤ width) (hwidth : width ≤ 64) :
    narrowed width (a.signExtend 64) = (Word.signed width a).toNat := by
  apply bridge hwidth
  rw [sext_toInt hw, Word.signed, BitVec.toInt_signExtend_of_le hle]

end Signed


/-! ### Lowering of expressions -/

/-- The slot an operation writes. -/
def opDst : Jit.Op → Option Nat
  | .set dst _ | .move dst _ | .add dst _ _ | .bin _ dst _ _ | .andImm dst _ _ | .signExtend _ dst _
  | .select dst _ _ _ | .neg dst _ | .not dst _ | .ashr _ dst _ _ | .memLoad dst _ _ _ => some dst
  | _ => none

/-- The operations of an expression: they continue with the next one and only write a slot. -/
def isExpressionOp : Jit.Op → Bool
  | .set .. | .move .. | .add .. | .bin .. | .andImm .. | .signExtend .. | .select .. | .neg .. | .not ..
  | .ashr .. | .memLoad .. => true
  | _ => false

theorem step_slot_other {machine : Machine} {op : Jit.Op} {slot : Nat} (hp : isExpressionOp op = true)
    (hd : ∀ dst, opDst op = some dst → dst ≠ slot) : (step machine op).slots slot = machine.slots slot := by
  cases op <;> simp only [isExpressionOp, Bool.false_eq_true] at hp <;>
    simp only [opDst, Option.some.injEq, forall_eq'] at hd <;> simp [step, hd.symm]

theorem step_memory {machine : Machine} {op : Jit.Op} (hp : isExpressionOp op = true) :
    (step machine op).memory = machine.memory := by
  cases op <;> simp only [isExpressionOp, Bool.false_eq_true] at hp <;> simp [step]

theorem runOps_slot_other {machine : Machine} {ops : List Jit.Op} {slot : Nat}
    (hp : ∀ op ∈ ops, isExpressionOp op = true) (hd : ∀ op ∈ ops, ∀ dst, opDst op = some dst → dst ≠ slot) :
    (runOps machine ops).slots slot = machine.slots slot := by
  induction ops generalizing machine with
  | nil => rfl
  | cons op rest ih =>
    rw [runOps_cons, ih (fun o ho => hp o (List.mem_cons_of_mem _ ho)) (fun o ho => hd o (List.mem_cons_of_mem _ ho))]
    exact step_slot_other (hp op List.mem_cons_self) (hd op List.mem_cons_self)

theorem step_view (machine : Machine) (op : Jit.Op) : (step machine op).view = machine.view := by
  cases op <;> rfl

theorem runOps_view (machine : Machine) (ops : List Jit.Op) : (runOps machine ops).view = machine.view := by
  induction ops generalizing machine with
  | nil => rfl
  | cons op rest ih => rw [runOps_cons, ih, step_view]

theorem step_origin (machine : Machine) (op : Jit.Op) : (step machine op).origin = machine.origin := by
  cases op <;> rfl

theorem runOps_origin (machine : Machine) (ops : List Jit.Op) : (runOps machine ops).origin = machine.origin := by
  induction ops generalizing machine with
  | nil => rfl
  | cons op rest ih => rw [runOps_cons, ih, step_origin]

theorem step_moved_mono {machine : Machine} (op : Jit.Op) {slot : Nat} (h : machine.moved slot = true) :
    (step machine op).moved slot = true := by
  cases op <;> first | exact h | simp [step, Machine.markMove, h]

theorem runOps_moved_mono {machine : Machine} (ops : List Jit.Op) {slot : Nat} (h : machine.moved slot = true) :
    (runOps machine ops).moved slot = true := by
  induction ops generalizing machine with
  | nil => exact h
  | cons op rest ih => exact ih (step_moved_mono op h)

theorem step_moved_new {machine : Machine} {op : Jit.Op} {slot : Nat} (h : (step machine op).moved slot = true) :
    machine.moved slot = true ∨ opDst op = some slot := by
  cases op <;> first
    | exact Or.inl h
    | (simp only [step, Machine.markMove, Bool.or_eq_true, beq_iff_eq] at h
       rcases h with h | h
       · exact Or.inr (by simp [opDst, h])
       · exact Or.inl h)

theorem runOps_moved_new {machine : Machine} {ops : List Jit.Op} {slot : Nat} (h : (runOps machine ops).moved slot = true) :
    machine.moved slot = true ∨ ∃ op ∈ ops, opDst op = some slot := by
  induction ops generalizing machine with
  | nil => exact Or.inl h
  | cons op rest ih =>
    rcases ih h with h | ⟨o, ho, hd⟩
    · rcases step_moved_new h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨op, List.mem_cons_self, h⟩
    · exact Or.inr ⟨o, List.mem_cons_of_mem _ ho, hd⟩

theorem runOps_memory {machine : Machine} {ops : List Jit.Op} (hp : ∀ op ∈ ops, isExpressionOp op = true) :
    (runOps machine ops).memory = machine.memory := by
  induction ops generalizing machine with
  | nil => rfl
  | cons op rest ih =>
    rw [runOps_cons, ih fun o ho => hp o (List.mem_cons_of_mem _ ho)]
    exact step_memory (hp op List.mem_cons_self)

/-- What lowering an expression does to the lowering state: it appends `new`, whose operations only write
slots allocated meanwhile that belong to no variable. -/
structure Extends (first second : Lowering) (new : List Jit.Op) : Prop where
  ops : Lowering.ops second = Lowering.ops first ++ new
  next : Lowering.nextSlot first ≤ Lowering.nextSlot second
  extra : ∃ extra, Lowering.layout second = Lowering.layout first ++ extra ∧
    ∀ binding ∈ extra, Lowering.nextSlot first ≤ binding.2 ∧ binding.2 < Lowering.nextSlot second
  pure : ∀ op ∈ new, isExpressionOp op = true
  writes : ∀ op ∈ new, ∀ dst, opDst op = some dst →
    Lowering.nextSlot first ≤ dst ∧ dst < Lowering.nextSlot second ∧ ∀ var, (var, dst) ∉ Lowering.layout second
  distinct : (Lowering.layout first).Pairwise (fun left right => left.2 ≠ right.2) →
    (Lowering.layout second).Pairwise (fun left right => left.2 ≠ right.2)
  vars : (Lowering.layout first).Pairwise (fun left right => left.1 ≠ right.1) →
    (Lowering.layout second).Pairwise (fun left right => left.1 ≠ right.1)
  memory : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var
  written : Lowering.written second = Lowering.written first
  outputs : Lowering.outputs second = Lowering.outputs first
  nextLabel : Lowering.nextLabel second = Lowering.nextLabel first
  effect : Lowering.effectSlot second = Lowering.effectSlot first
  stable : Lowering.next second = Lowering.next first

theorem Extends.refl (lowering : Lowering) : Extends lowering lowering [] where
  ops := by simp
  next := Nat.le_refl _
  extra := ⟨[], by simp, by simp⟩
  pure := by simp
  writes := by simp
  distinct := id
  vars := id
  memory := fun _ h => h
  written := rfl
  outputs := rfl
  nextLabel := rfl
  effect := rfl
  stable := rfl

theorem Extends.wf {first second : Lowering} {new : List Jit.Op} (h : Extends first second new)
    (wf : LayoutWF first) : LayoutWF second where
  bound := by
    obtain ⟨extra, he, hx⟩ := h.extra
    intro binding hb
    rw [he] at hb
    rcases List.mem_append.1 hb with hb | hb
    · exact Nat.lt_of_lt_of_le (wf.bound _ hb) h.next
    · exact (hx _ hb).2
  slotsDistinct := h.distinct wf.slotsDistinct
  varsDistinct := h.vars wf.varsDistinct

/-- Operations appended by the tail of an expression: fresh slots above the ones so far. -/
theorem Extends.tail {first second : Lowering} {new : List Jit.Op} (count : Nat)
    (wf : LayoutWF first)
    (hops : Lowering.ops second = Lowering.ops first ++ new)
    (hnext : Lowering.nextSlot second = Lowering.nextSlot first + count)
    (hlayout : Lowering.layout second = Lowering.layout first)
    (hmemory : Lowering.memory second = Lowering.memory first)
    (hwritten : Lowering.written second = Lowering.written first)
    (houtputs : Lowering.outputs second = Lowering.outputs first)
    (hlabel : Lowering.nextLabel second = Lowering.nextLabel first)
    (heffect : Lowering.effectSlot second = Lowering.effectSlot first)
    (hstable : Lowering.next second = Lowering.next first)
    (hpure : ∀ op ∈ new, isExpressionOp op = true)
    (hwrites : ∀ op ∈ new, ∀ dst, opDst op = some dst →
      Lowering.nextSlot first ≤ dst ∧ dst < Lowering.nextSlot first + count) :
    Extends first second new where
  ops := hops
  next := by omega
  extra := ⟨[], by simp [hlayout], by simp⟩
  pure := hpure
  writes := by
    intro op hop dst hd
    obtain ⟨h1, h2⟩ := hwrites op hop dst hd
    refine ⟨h1, by omega, ?_⟩
    intro var hm
    rw [hlayout] at hm
    have := wf.bound _ hm
    simp only at this
    omega
  distinct := fun h => hlayout ▸ h
  vars := fun h => hlayout ▸ h
  memory := fun var h => hmemory ▸ h
  written := hwritten
  outputs := houtputs
  nextLabel := hlabel
  effect := heffect
  stable := hstable

theorem Extends.trans {first second third : Lowering} {left right : List Jit.Op}
    (hl : Extends first second left) (hr : Extends second third right) (_wf : LayoutWF first) :
    Extends first third (left ++ right) where
  ops := by rw [hr.ops, hl.ops, List.append_assoc]
  next := Nat.le_trans hl.next hr.next
  extra := by
    obtain ⟨e1, h1, hx1⟩ := hl.extra
    obtain ⟨e2, h2, hx2⟩ := hr.extra
    refine ⟨e1 ++ e2, by rw [h2, h1, List.append_assoc], ?_⟩
    intro binding hb
    rcases List.mem_append.1 hb with hb | hb
    · exact ⟨(hx1 _ hb).1, Nat.lt_of_lt_of_le (hx1 _ hb).2 hr.next⟩
    · exact ⟨Nat.le_trans hl.next (hx2 _ hb).1, (hx2 _ hb).2⟩
  pure := by
    intro op hop
    rcases List.mem_append.1 hop with h | h
    · exact hl.pure _ h
    · exact hr.pure _ h
  writes := by
    intro op hop dst hd
    rcases List.mem_append.1 hop with h | h
    · obtain ⟨a, b, c⟩ := hl.writes op h dst hd
      refine ⟨a, Nat.lt_of_lt_of_le b hr.next, ?_⟩
      intro var hm
      obtain ⟨e2, h2, hx2⟩ := hr.extra
      rw [h2] at hm
      rcases List.mem_append.1 hm with hm | hm
      · exact c var hm
      · have := (hx2 _ hm).1
        simp only at this
        omega
    · obtain ⟨a, b, c⟩ := hr.writes op h dst hd
      exact ⟨Nat.le_trans hl.next a, b, c⟩
  distinct := fun h => hr.distinct (hl.distinct h)
  vars := fun h => hr.vars (hl.vars h)
  memory := fun var h => hr.memory var (hl.memory var h)
  written := by rw [hr.written, hl.written]
  outputs := by rw [hr.outputs, hl.outputs]
  nextLabel := by rw [hr.nextLabel, hl.nextLabel]
  effect := by rw [hr.effect, hl.effect]
  stable := by rw [hr.stable, hl.stable]

/-- A slot not written by `new`: below the first allocation, or allocated later, or of a variable. -/
theorem Extends.frame {first second : Lowering} {new : List Jit.Op} (h : Extends first second new) (machine : Machine)
    {slot : Nat} (hs : slot < Lowering.nextSlot first ∨ Lowering.nextSlot second ≤ slot ∨
      ∃ var, (var, slot) ∈ Lowering.layout second) :
    (runOps machine new).slots slot = machine.slots slot := by
  apply runOps_slot_other h.pure
  intro op hop dst hd he
  subst he
  obtain ⟨a, b, c⟩ := h.writes op hop _ hd
  rcases hs with hs | hs | ⟨var, hv⟩
  · omega
  · omega
  · exact c var hv

/-- The machine holds the environment: each variable with a value, in its slot. -/
def SlotsAgree (env : Bil.Env) (machine : Machine) (layout : List (Bap.Var × Nat)) : Prop :=
  ∀ binding ∈ layout, ∀ value, Bil.lookup env binding.1 = .ok value →
    ∃ (width : Nat) (bits : BitVec width), value = .bits bits ∧ widthOf binding.1 = some width ∧
      Holds (machine.slots binding.2) bits

/-- The memory of the machine is the memory of the variable at the addresses of an access of at most 8 bytes,
through its `view`: see `memoryAgrees_of_window`, which says that this holds of any memory and machine whose `view`
wraps with the address space, and the same address space. -/
def MemoryAgrees (env : Bil.Env) (machine : Machine) (lowering : Lowering) : Prop :=
  ∀ var, Lowering.memory lowering = some var → ∀ (width : Nat) (memory : Bap.Memory width),
    Bil.lookup env var = .ok (.memory memory) → ∀ (address : BitVec width) (offset : Nat), offset < 8 →
      machine.memory (machine.view (address.setWidth 64 + BitVec.ofNat 64 offset)) =
        Bap.Memory.readByte memory (address + BitVec.ofNat width offset)

/-- What lowering of an expression establishes for an operand. -/
structure Lowers (env : Bil.Env) (machine : Machine) (first second : Lowering) (new : List Jit.Op) (operand : Operand)
    (exp : Bil.Exp) : Prop where
  value : ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) →
    Operand.width operand = width ∧ Holds ((runOps machine new).slots (Operand.slot operand)) bits

theorem SlotsAgree.mono {env : Bil.Env} {machine : Machine} {first second : List (Bap.Var × Nat)}
    (h : SlotsAgree env machine second) (hs : ∀ b ∈ first, b ∈ second) : SlotsAgree env machine first :=
  fun b hb => h b (hs b hb)

/-- Running the operations of a sub-expression keeps the agreement on the layout of any later state. -/
theorem SlotsAgree.after {env : Bil.Env} {machine : Machine} {first second : Lowering} {new : List Jit.Op}
    {layout : List (Bap.Var × Nat)} (h : SlotsAgree env machine layout) (he : Extends first second new)
    (hlayout : ∀ b ∈ layout, b ∈ Lowering.layout second ∨ Lowering.nextSlot second ≤ b.2) :
    SlotsAgree env (runOps machine new) layout := by
  intro binding hb value hv
  obtain ⟨width, bits, h1, h2, h3⟩ := h binding hb value hv
  refine ⟨width, bits, h1, h2, ?_⟩
  have : (runOps machine new).slots binding.2 = machine.slots binding.2 := by
    apply he.frame
    rcases hlayout binding hb with hm | hm
    · exact Or.inr (Or.inr ⟨binding.1, hm⟩)
    · exact Or.inr (Or.inl hm)
  rw [Holds, this]
  exact h3

theorem Extends.laterLayout {first second third : Lowering} {new : List Jit.Op}
    (_h1 : Extends first second new) (h2 : Extends second third new') :
    ∀ b ∈ Lowering.layout third, b ∈ Lowering.layout second ∨ Lowering.nextSlot second ≤ b.2 := by
  obtain ⟨e, he, hx⟩ := h2.extra
  intro b hb
  rw [he] at hb
  rcases List.mem_append.1 hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr (hx _ hb).1

theorem MemoryAgrees.after {env : Bil.Env} {machine : Machine} {lowering : Lowering} {new : List Jit.Op}
    (h : MemoryAgrees env machine lowering) (hp : ∀ op ∈ new, isExpressionOp op = true) :
    MemoryAgrees env (runOps machine new) lowering := by
  intro var hv width memory hm address offset ho
  rw [runOps_memory hp, runOps_view]
  exact h var hv width memory hm address offset ho

theorem MemoryAgrees.mono {env : Bil.Env} {machine : Machine} {first second : Lowering}
    (h : MemoryAgrees env machine second) (he : ∀ var, Lowering.memory first = some var → Lowering.memory second = some var) :
    MemoryAgrees env machine first :=
  fun var hv => h var (he var hv)

/-- `narrow`: the operations it adds. -/
def narrowOps (width dst : Nat) : List Jit.Op :=
  if width < 64 then [.andImm dst dst (mask width)] else []

private theorem narrow_ops (lowering : Lowering) (width dst : Nat) :
    Lowering.ops (narrow lowering width dst) = Lowering.ops lowering ++ narrowOps width dst := by
  unfold narrow narrowOps
  split
  · rfl
  · simp

private theorem narrow_nextSlot (l : Lowering) (w d : Nat) : Lowering.nextSlot (narrow l w d) = Lowering.nextSlot l := by
  unfold narrow; split <;> rfl
private theorem narrow_layout (l : Lowering) (w d : Nat) : Lowering.layout (narrow l w d) = Lowering.layout l := by
  unfold narrow; split <;> rfl
private theorem narrow_memory (l : Lowering) (w d : Nat) : Lowering.memory (narrow l w d) = Lowering.memory l := by
  unfold narrow; split <;> rfl
private theorem narrow_written (l : Lowering) (w d : Nat) : Lowering.written (narrow l w d) = Lowering.written l := by
  unfold narrow; split <;> rfl
private theorem narrow_outputs (l : Lowering) (w d : Nat) : Lowering.outputs (narrow l w d) = Lowering.outputs l := by
  unfold narrow; split <;> rfl
private theorem narrow_nextLabel (l : Lowering) (w d : Nat) : Lowering.nextLabel (narrow l w d) = Lowering.nextLabel l := by
  unfold narrow; split <;> rfl
private theorem narrow_effectSlot (l : Lowering) (w d : Nat) : Lowering.effectSlot (narrow l w d) = Lowering.effectSlot l := by
  unfold narrow; split <;> rfl
private theorem narrow_next (l : Lowering) (w d : Nat) : Lowering.next (narrow l w d) = Lowering.next l := by
  unfold narrow; split <;> rfl

theorem narrowOps_pure (width dst : Nat) : ∀ op ∈ narrowOps width dst, isExpressionOp op = true := by
  intro op hop
  unfold narrowOps at hop
  split at hop
  · simp only [List.mem_singleton] at hop
    subst hop
    rfl
  · simp at hop

theorem narrowOps_writes (width dst : Nat) : ∀ op ∈ narrowOps width dst, ∀ d, opDst op = some d → d = dst := by
  intro op hop d hd
  unfold narrowOps at hop
  split at hop
  · simp only [List.mem_singleton] at hop
    subst hop
    simpa [opDst] using hd.symm
  · simp at hop

theorem narrowOps_value {width dst : Nat} (hw : width ≤ 64) (machine : Machine) :
    ((runOps machine (narrowOps width dst)).slots dst).toNat = narrowed width (machine.slots dst) := by
  unfold narrowOps
  split
  · simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, narrowed]
    exact and_mask_toNat hw _
  · have : width = 64 := by omega
    subst this
    simp only [runOps_nil, narrowed]
    exact (Nat.mod_eq_of_lt (machine.slots dst).isLt).symm


/-! Inversion of the interpreter. -/

private theorem asBits_ok {value : Bap.Value} {result : Σ width, BitVec width} (h : Value.asBits value = .ok result) :
    value = .bits result.2 := by
  cases value <;> simp [Value.asBits] at h
  subst h
  rfl

/-- A value of a bit expression. -/
private theorem eval_bits {env : Bil.Env} {exp : Bil.Exp} {result : Σ width, BitVec width}
    (hv : ∃ v, Bil.evalExp env exp = .ok v ∧ Value.asBits v = .ok result) :
    Bil.evalExp env exp = .ok (.bits result.2) := by
  obtain ⟨v, h1, h2⟩ := hv
  rw [h1, asBits_ok h2]

theorem evalExp_un_inv {env : Bil.Env} {op : Bil.UnOp} {exp : Bil.Exp} {value : Bap.Value}
    (h : Bil.evalExp env (.un op exp) = .ok value) :
    ∃ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) ∧
      value = (match op with | .neg => .bits (-bits) | .not => .bits (~~~bits)) := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨r, h3, h4⟩ := bind_ok h2
  simp only [Except.ok.injEq] at h4
  refine ⟨r.1, r.2, by rw [h1, asBits_ok h3], ?_⟩
  cases op <;> exact h4.symm

theorem evalExp_bin_inv {env : Bil.Env} {op : Bil.BinOp} {left right : Bil.Exp} {value : Bap.Value}
    (h : Bil.evalExp env (.bin op left right) = .ok value) :
    ∃ (w₁ : Nat) (x : BitVec w₁) (w₂ : Nat) (y : BitVec w₂), Bil.evalExp env left = .ok (.bits x) ∧
      Bil.evalExp env right = .ok (.bits y) ∧ Bil.evalBin op ⟨w₁, x⟩ ⟨w₂, y⟩ = .ok value := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨l, h3, h4⟩ := bind_ok h2
  obtain ⟨v', h5, h6⟩ := bind_ok h4
  obtain ⟨r, h7, h8⟩ := bind_ok h6
  exact ⟨l.1, l.2, r.1, r.2, by rw [h1, asBits_ok h3], by rw [h5, asBits_ok h7], h8⟩

theorem evalExp_ite_inv {env : Bil.Env} {condition yes no : Bil.Exp} {value : Bap.Value}
    (h : Bil.evalExp env (.ite condition yes no) = .ok value) :
    ∃ bit : BitVec 1, Bil.evalExp env condition = .ok (.bits bit) ∧
      (if bit = 1 then Bil.evalExp env yes else Bil.evalExp env no) = .ok value := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨r, h3, h4⟩ := bind_ok h2
  obtain ⟨width, bit⟩ := r
  simp only at h4
  split at h4
  · next hw =>
    subst hw
    exact ⟨bit, by rw [h1, asBits_ok h3], h4⟩
  · simp at h4

theorem evalExp_extract_inv {env : Bil.Env} {high low : Nat} {exp : Bil.Exp} {value : Bap.Value}
    (h : Bil.evalExp env (.extract high low exp) = .ok value) :
    ∃ (width : Nat) (bits : BitVec width) (result : BitVec (high - low + 1)), Bil.evalExp env exp = .ok (.bits bits) ∧
      Word.extract high low bits = .ok result ∧ value = .bits result := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨r, h3, h4⟩ := bind_ok h2
  obtain ⟨x, h5, h6⟩ := bind_ok h4
  simp only [Except.ok.injEq] at h6
  exact ⟨r.1, r.2, x, by rw [h1, asBits_ok h3], h5, h6.symm⟩

theorem evalExp_cast_inv {env : Bil.Env} {kind : Bil.Cast} {target : Nat} {exp : Bil.Exp} {value : Bap.Value}
    (h : Bil.evalExp env (.cast kind target exp) = .ok value) :
    ∃ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) ∧
      match kind with
      | .low => value = .bits (Word.low target bits)
      | .unsigned => value = .bits (Word.unsigned target bits)
      | .signed => value = .bits (Word.signed target bits)
      | .high => ∃ result, Word.high target bits = .ok result ∧ value = .bits result := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨r, h3, h4⟩ := bind_ok h2
  refine ⟨r.1, r.2, by rw [h1, asBits_ok h3], ?_⟩
  cases kind <;> simp only [Except.ok.injEq] at h4
  · exact h4.symm
  · obtain ⟨x, h5, h6⟩ := bind_ok h4
    simp only [Except.ok.injEq] at h6
    exact ⟨x, h5, h6.symm⟩
  · exact h4.symm
  · exact h4.symm

theorem evalExp_load_inv {env : Bil.Env} {memory address : Bil.Exp} {endian : Endian} {size : Nat} {value : Bap.Value}
    (h : Bil.evalExp env (.load memory address endian size) = .ok value) :
    ∃ (width : Nat) (cells : Bap.Memory width) (bits : BitVec width), Bil.evalExp env memory = .ok (.memory cells) ∧
      Bil.evalExp env address = .ok (.bits bits) ∧ value = .bits (Bap.Memory.read cells bits endian size) := by
  rw [Bil.evalExp] at h
  obtain ⟨v, h1, h2⟩ := bind_ok h
  obtain ⟨m, h3, h4⟩ := bind_ok h2
  obtain ⟨w, cells⟩ := m
  obtain ⟨v', h5, h6⟩ := bind_ok h4
  obtain ⟨a, h7, h8⟩ := bind_ok h6
  obtain ⟨aw, bits⟩ := a
  simp only at h8
  split at h8
  · next hw =>
    subst hw
    simp only [Except.ok.injEq] at h8
    cases v <;> simp only [expectMemory, reduceCtorEq, Except.ok.injEq] at h3
    cases h3
    exact ⟨_, _, bits, h1, by rw [h5, asBits_ok h7], h8.symm⟩
  · simp at h8

/-- From a value of a bits sort there is one width. -/
private theorem bits_inj {w₁ w₂ : Nat} {x : BitVec w₁} {y : BitVec w₂}
    (h : (Value.bits x : Bap.Value) = .bits y) : ∃ he : w₁ = w₂, he ▸ x = y := by
  cases h
  exact ⟨rfl, rfl⟩


theorem immediate_toNat {width : Nat} (hw : width ≤ 64) (value : BitVec width) :
    (immediate value).toBitVec.toNat = value.toNat := by
  simp only [immediate]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by decide) hw))

/-- A lowered operand: the operations, and that they compute the value of the expression. -/
def Lowered (first second : Lowering) (operand : Operand) (exp : Bil.Exp) : Prop :=
  ∃ new, Extends first second new ∧ Operand.slot operand < Lowering.nextSlot second ∧
    0 < Operand.width operand ∧ Operand.width operand ≤ 64 ∧
    ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout second) →
      MemoryAgrees env machine second →
      ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) →
        Operand.width operand = width ∧ Holds ((runOps machine new).slots (Operand.slot operand)) bits

theorem lowered_int {width : Nat} {value : BitVec width} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first) (h : lowerExp first (.int value) = some (second, operand)) :
    Lowered first second operand (.int value) := by
  rw [lowerExp] at h
  split at h
  · next hc =>
    simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨[.set (Lowering.nextSlot first) (immediate value)], Extends.tail 1 wf rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_ ?_,
      Nat.lt_succ_self _, hc.1, hc.2, ?_⟩
    · simp [isExpressionOp]
    · intro op hop dst hd
      simp only [List.mem_singleton] at hop
      subst hop
      simp only [opDst, Option.some.injEq] at hd
      omega
    · intro env machine _ _ w bits he
      simp only [Bil.evalExp, Except.ok.injEq] at he
      cases he
      refine ⟨rfl, ?_⟩
      simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, Holds]
      exact immediate_toNat hc.2 _
  · simp at h

/-- A lowering that differs in the inputs at most. -/
structure SameButInputs (first second : Lowering) : Prop where
  ops : Lowering.ops second = Lowering.ops first
  nextSlot : Lowering.nextSlot second = Lowering.nextSlot first
  layout : Lowering.layout second = Lowering.layout first
  memory : Lowering.memory second = Lowering.memory first
  written : Lowering.written second = Lowering.written first
  outputs : Lowering.outputs second = Lowering.outputs first
  nextLabel : Lowering.nextLabel second = Lowering.nextLabel first
  effect : Lowering.effectSlot second = Lowering.effectSlot first
  next : Lowering.next second = Lowering.next first

private theorem obind {α β : Type} {x : Option α} {f : α → Option β} {r : β} (h : (x >>= f) = some r) :
    ∃ v, x = some v ∧ f v = some r := by
  cases hx : x with
  | none => simp [hx] at h
  | some v => exact ⟨v, rfl, by simpa [hx] using h⟩

private theorem slot_fields (first : Lowering) (var : Bap.Var) :
    Lowering.ops (slot first var).1 = Lowering.ops first ∧ Lowering.memory (slot first var).1 = Lowering.memory first ∧
    Lowering.written (slot first var).1 = Lowering.written first ∧
    Lowering.outputs (slot first var).1 = Lowering.outputs first ∧
    Lowering.nextLabel (slot first var).1 = Lowering.nextLabel first ∧
    Lowering.effectSlot (slot first var).1 = Lowering.effectSlot first ∧
    Lowering.next (slot first var).1 = Lowering.next first := by
  unfold slot
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem slot_extends {first : Lowering} (wf : LayoutWF first) (var : Bap.Var) :
    Extends first (slot first var).1 [] := by
  cases h : (Lowering.layout first).find? (fun binding => binding.1 == var) with
  | some binding =>
    rw [slot_existing _ _ _ h]
    exact Extends.refl first
  | none =>
    obtain ⟨h1, h2, h3⟩ := slot_fresh first var h
    have wf' := slot_preserves_wf wf var
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := slot_fields first var
    exact {
      ops := by simp [f1]
      next := by omega
      extra := ⟨_, h3, by simp [h2]⟩
      pure := by simp
      writes := by simp
      distinct := fun _ => wf'.slotsDistinct
      vars := fun _ => wf'.varsDistinct
      memory := fun _ hm => by rw [f2]; exact hm
      written := f3
      outputs := f4
      nextLabel := f5
      effect := f6
      stable := f7 }

theorem readVar_inv {first second : Lowering} {var : Bap.Var} {index : Nat} (h : readVar first var = some (second, index)) :
    index = (slot first var).2 ∧ SameButInputs (slot first var).1 second := by
  cases hw : widthOf var with
  | none => simp [readVar, hw] at h
  | some width =>
    simp only [readVar, hw, bind, Option.bind_some] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
      exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem Extends.same {first second third : Lowering} {new : List Jit.Op} (h : Extends first second new)
    (hs : SameButInputs second third) : Extends first third new where
  ops := by rw [hs.ops, h.ops]
  next := by rw [hs.nextSlot]; exact h.next
  extra := by rw [hs.layout, hs.nextSlot]; exact h.extra
  pure := h.pure
  writes := by rw [hs.layout, hs.nextSlot]; exact h.writes
  distinct := by rw [hs.layout]; exact h.distinct
  vars := by rw [hs.layout]; exact h.vars
  memory := by rw [hs.memory]; exact h.memory
  written := by rw [hs.written]; exact h.written
  outputs := by rw [hs.outputs]; exact h.outputs
  nextLabel := by rw [hs.nextLabel]; exact h.nextLabel
  effect := by rw [hs.effect]; exact h.effect
  stable := by rw [hs.next]; exact h.stable

theorem lowered_var {var : Bap.Var} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first) (h : lowerExp first (.var var) = some (second, operand)) :
    Lowered first second operand (.var var) := by
  rw [lowerExp] at h
  obtain ⟨width, hw, h⟩ := obind h
  obtain ⟨⟨result, index⟩, hrv, h⟩ := obind h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hindex, hsame⟩ := readVar_inv hrv
  subst hindex
  have hext := (slot_extends wf var).same hsame
  have hwf := slot_preserves_wf wf var
  have hmem : (var, (slot first var).2) ∈ Lowering.layout result :=
    hsame.layout ▸ slot_mem_layout first var
  have hw64 : 0 < width ∧ width ≤ 64 := by
    have := (widthOf_some_iff var width).1 hw
    omega
  refine ⟨[], hext, ?_, hw64.1, hw64.2, ?_⟩
  · rw [hsame.nextSlot]
    exact hwf.bound _ (slot_mem_layout first var)
  · intro env machine hslots _ w bits he
    simp only [Bil.evalExp] at he
    obtain ⟨w', bits', h1, h2, h3⟩ := hslots _ hmem _ he
    simp only [hw, Option.some.injEq] at h2
    subst h2
    cases h1
    exact ⟨rfl, h3⟩


/-- The operand of a sub-expression, in a later machine. -/
private theorem operand_after {second third : Lowering} {new later : List Jit.Op} {operand : Operand}
    {width : Nat} {bits : BitVec width} {machine : Machine} (hs : Operand.slot operand < Lowering.nextSlot second)
    (he : Extends second third later) (hv : Holds ((runOps machine new).slots (Operand.slot operand)) bits) :
    Holds ((runOps (runOps machine new) later).slots (Operand.slot operand)) bits := by
  rw [Holds, he.frame _ (Or.inl hs)]
  exact hv

/-- A sub-expression reads the machine in the state where its operations start. -/
private theorem agree_first {env : Bil.Env} {machine : Machine} {first second third : Lowering} {new later : List Jit.Op}
    (_h1 : Extends first second new) (h2 : Extends second third later) (hs : SlotsAgree env machine (Lowering.layout third)) :
    SlotsAgree env machine (Lowering.layout second) := by
  obtain ⟨e, he, _⟩ := h2.extra
  exact SlotsAgree.mono hs fun b hb => by rw [he]; exact List.mem_append_left _ hb

private theorem memory_first {env : Bil.Env} {machine : Machine} {second third : Lowering} {later : List Jit.Op}
    (h2 : Extends second third later) (hm : MemoryAgrees env machine third) : MemoryAgrees env machine second :=
  hm.mono h2.memory

/-- The agreement after the operations of the first of two sub-expressions. -/
private theorem agree_next {env : Bil.Env} {machine : Machine} {first second third : Lowering} {new later : List Jit.Op}
    (h1 : Extends first second new) (h2 : Extends second third later) (hs : SlotsAgree env machine (Lowering.layout third)) :
    SlotsAgree env (runOps machine new) (Lowering.layout third) :=
  hs.after h1 (h1.laterLayout h2)

theorem extends_narrow {first second : Lowering} {pre : List Jit.Op} {count width dst : Nat} (wf : LayoutWF first)
    (hops : Lowering.ops second = Lowering.ops first ++ pre)
    (hnext : Lowering.nextSlot second = Lowering.nextSlot first + count)
    (hlayout : Lowering.layout second = Lowering.layout first)
    (hmemory : Lowering.memory second = Lowering.memory first)
    (hwritten : Lowering.written second = Lowering.written first)
    (houtputs : Lowering.outputs second = Lowering.outputs first)
    (hlabel : Lowering.nextLabel second = Lowering.nextLabel first)
    (heffect : Lowering.effectSlot second = Lowering.effectSlot first)
    (hstable : Lowering.next second = Lowering.next first)
    (hpure : ∀ op ∈ pre, isExpressionOp op = true)
    (hwrites : ∀ op ∈ pre, ∀ d, opDst op = some d → Lowering.nextSlot first ≤ d ∧ d < Lowering.nextSlot first + count)
    (hdst : Lowering.nextSlot first ≤ dst ∧ dst < Lowering.nextSlot first + count) :
    Extends first (narrow second width dst) (pre ++ narrowOps width dst) := by
  refine Extends.tail count wf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [narrow_ops, hops, List.append_assoc]
  · rw [narrow_nextSlot, hnext]
  · rw [narrow_layout, hlayout]
  · rw [narrow_memory, hmemory]
  · rw [narrow_written, hwritten]
  · rw [narrow_outputs, houtputs]
  · rw [narrow_nextLabel, hlabel]
  · rw [narrow_effectSlot, heffect]
  · rw [narrow_next, hstable]
  · intro op hop
    rcases List.mem_append.1 hop with h | h
    · exact hpure op h
    · exact narrowOps_pure _ _ op h
  · intro op hop d hd
    rcases List.mem_append.1 hop with h | h
    · exact hwrites op h d hd
    · rw [narrowOps_writes _ _ op h d hd]
      exact hdst

theorem value_narrow {pre : List Jit.Op} {width dst : Nat} {bits : BitVec width} {machine : Machine} (hw : width ≤ 64)
    (h : narrowed width ((runOps machine pre).slots dst) = bits.toNat) :
    Holds ((runOps machine (pre ++ narrowOps width dst)).slots dst) bits := by
  rw [Holds, runOps_append, narrowOps_value hw, h]

theorem lowered_tail {first mid second : Lowering} {new tail : List Jit.Op} {operand : Operand} {exp : Bil.Exp}
    (wf : LayoutWF first) (he : Extends first mid new) (htail : Extends mid second tail)
    (hslot : Operand.slot operand < Lowering.nextSlot second) (h0 : 0 < Operand.width operand)
    (h64 : Operand.width operand ≤ 64)
    (hv : ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout mid) →
      MemoryAgrees env machine mid → ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env exp = .ok (.bits bits) →
        Operand.width operand = width ∧ Holds ((runOps (runOps machine new) tail).slots (Operand.slot operand)) bits) :
    Lowered first second operand exp := by
  refine ⟨new ++ tail, he.trans htail wf, hslot, h0, h64, ?_⟩
  intro env machine hs hm width bits hev
  rw [runOps_append]
  exact hv env machine (agree_first he htail hs) (memory_first htail hm) width bits hev

/-- The operands of a binary operator are in their slots after both their operations. -/
private theorem operands_hold {l0 l1 l2 : Lowering} {newL newR : List Jit.Op} {o1 o2 : Operand} {left right : Bil.Exp}
    {env : Bil.Env} {machine : Machine} {w₁ w₂ : Nat} {x : BitVec w₁} {y : BitVec w₂}
    (hL : Extends l0 l1 newL) (hR : Extends l1 l2 newR) (hs1 : Operand.slot o1 < Lowering.nextSlot l1)
    (vL : ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout l1) →
      MemoryAgrees env machine l1 → ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env left = .ok (.bits bits) →
        Operand.width o1 = width ∧ Holds ((runOps machine newL).slots (Operand.slot o1)) bits)
    (vR : ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout l2) →
      MemoryAgrees env machine l2 → ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env right = .ok (.bits bits) →
        Operand.width o2 = width ∧ Holds ((runOps machine newR).slots (Operand.slot o2)) bits)
    (hs : SlotsAgree env machine (Lowering.layout l2)) (hm : MemoryAgrees env machine l2)
    (hx : Bil.evalExp env left = .ok (.bits x)) (hy : Bil.evalExp env right = .ok (.bits y)) :
    Operand.width o1 = w₁ ∧ Operand.width o2 = w₂ ∧
      Holds ((runOps machine (newL ++ newR)).slots (Operand.slot o1)) x ∧
      Holds ((runOps machine (newL ++ newR)).slots (Operand.slot o2)) y := by
  obtain ⟨h1, h2⟩ := vL env machine (agree_first hL hR hs) (memory_first hR hm) _ x hx
  obtain ⟨h3, h4⟩ := vR env (runOps machine newL) (agree_next hL hR hs)
    (MemoryAgrees.after hm hL.pure) _ y hy
  rw [runOps_append]
  exact ⟨h1, h3, operand_after hs1 hR h2, h4⟩

theorem lowered_un {op : Bil.UnOp} {value : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first value = some (second, operand) →
      Lowered first second operand value)
    (h : lowerExp first (.un op value) = some (second, operand)) : Lowered first second operand (.un op value) := by
  rw [lowerExp] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨new, he, hslot, h0, h64, hval⟩ := ih wf h1
  have wf1 := he.wf wf
  have hw : ∀ op : Jit.Op, opDst op = some (Lowering.nextSlot l1) →
      ∀ o ∈ [op], ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 1 := by
    intro op hop o ho d hd
    simp only [List.mem_singleton] at ho
    subst ho
    rw [hop] at hd
    simp only [Option.some.injEq] at hd
    omega
  cases op <;> simp only [temporary, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  case neg =>
    refine lowered_tail wf he (extends_narrow (pre := [.neg (Lowering.nextSlot l1) (Operand.slot o1)]) (count := 1)
      wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp [isExpressionOp]) (hw _ rfl) (by omega))
      (by rw [narrow_nextSlot]; exact Nat.lt_succ_self _) h0 h64 ?_
    intro env machine hs hm w bits hev
    obtain ⟨w₀, x, hx, hb⟩ := evalExp_un_inv hev
    obtain ⟨rfl, hx'⟩ := hval env machine hs hm _ x hx
    simp only at hb
    cases hb
    refine ⟨rfl, ?_⟩
    apply value_narrow h64
    simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true]
    exact narrow_neg h64 hx'
  case not =>
    refine lowered_tail wf he (extends_narrow (pre := [.not (Lowering.nextSlot l1) (Operand.slot o1)]) (count := 1)
      wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (by simp [isExpressionOp]) (hw _ rfl) (by omega))
      (by rw [narrow_nextSlot]; exact Nat.lt_succ_self _) h0 h64 ?_
    intro env machine hs hm w bits hev
    obtain ⟨w₀, x, hx, hb⟩ := evalExp_un_inv hev
    obtain ⟨rfl, hx'⟩ := hval env machine hs hm _ x hx
    simp only at hb
    cases hb
    refine ⟨rfl, ?_⟩
    apply value_narrow h64
    simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true]
    exact narrow_not h64 hx'


/-- The value of a one-bit comparison is its own low bit. -/
private theorem narrowed_one {v : Word64} {b : Word 1} (h : v.toNat = BitVec.toNat b) : narrowed 1 v = BitVec.toNat b := by
  simp only [narrowed, h]
  exact Nat.mod_eq_of_lt b.isLt

/-- Each operator with a native operation: on slots that hold the operands, with the extension for a signed
one, the narrowed result is the value in the interpreter. -/
theorem binary_correct {op : Bil.BinOp} {native : Jit.BinOp} {w : Nat} {a b : BitVec w} {l r : Word64}
    (hop : binaryOp op = some native) (h0 : 0 < w) (hw : w ≤ 64) (hl : Holds l a) (hr : Holds r b) :
    let l' := if isSigned native then denoteSignExtend w l else l
    let r' := if isSigned native then denoteSignExtend w r else r
    ∃ (result : BitVec (if isComparison native then 1 else w)), Bil.evalBin op ⟨w, a⟩ ⟨w, b⟩ = .ok (.bits result) ∧
      narrowed (if isComparison native then 1 else w) (denoteBin native l' r') = result.toNat := by
  have hsl := denoteSignExtend_holds h0 hw hl
  have hsr := denoteSignExtend_holds h0 hw hr
  cases op <;> simp only [binaryOp, Option.some.injEq, reduceCtorEq] at hop <;> subst hop <;>
    simp only [isSigned, isComparison, Bool.false_eq_true, ite_false, ite_true, hsl, hsr]
  case add => exact ⟨a + b, by simp [Bil.evalBin], narrow_add hw hl hr⟩
  case sub => exact ⟨a - b, by simp [Bil.evalBin], narrow_sub hw hl hr⟩
  case mul => exact ⟨a * b, by simp [Bil.evalBin], narrow_mul hw hl hr⟩
  case div => exact ⟨Word.udiv a b, by simp [Bil.evalBin], narrow_udiv hw hl hr⟩
  case sdiv => exact ⟨Word.sdiv a b, by simp [Bil.evalBin], narrow_sdiv hw⟩
  case rem => exact ⟨Word.urem a b, by simp [Bil.evalBin], narrow_urem hw hl hr⟩
  case srem => exact ⟨Word.srem a b, by simp [Bil.evalBin], narrow_srem hw⟩
  case lshift => exact ⟨Word.shl a b, by simp [Bil.evalBin], narrow_lshift hw hl hr⟩
  case rshift => exact ⟨Word.lshr a b, by simp [Bil.evalBin], narrow_rshift hw hl hr⟩
  case and => exact ⟨a &&& b, by simp [Bil.evalBin], narrow_and hw hl hr⟩
  case or => exact ⟨a ||| b, by simp [Bil.evalBin], narrow_or hw hl hr⟩
  case xor => exact ⟨a ^^^ b, by simp [Bil.evalBin], narrow_xor hw hl hr⟩
  case eq => exact ⟨Word.eq a b, by simp [Bil.evalBin], narrowed_one (compare_eq hl hr)⟩
  case neq => exact ⟨Word.neq a b, by simp [Bil.evalBin], narrowed_one (compare_neq hl hr)⟩
  case lt => exact ⟨Word.lt a b, by simp [Bil.evalBin], narrowed_one (compare_lt hl hr)⟩
  case le => exact ⟨Word.le a b, by simp [Bil.evalBin], narrowed_one (compare_le hl hr)⟩
  case gt => exact ⟨Word.lt b a, by simp [Bil.evalBin], narrowed_one (compare_gt hl hr)⟩
  case ge => exact ⟨Word.le b a, by simp [Bil.evalBin], narrowed_one (compare_ge hl hr)⟩
  case slt => exact ⟨Word.slt a b, by simp [Bil.evalBin], narrowed_one (compare_slt hw)⟩
  case sle => exact ⟨Word.sle a b, by simp [Bil.evalBin], narrowed_one (compare_sle hw)⟩
  case sgt => exact ⟨Word.slt b a, by simp [Bil.evalBin], narrowed_one (compare_sgt hw)⟩
  case sge => exact ⟨Word.sle b a, by simp [Bil.evalBin], narrowed_one (compare_sge hw)⟩

/-- The interpreter's result determines width and value. -/
private theorem same_bits {w₁ w₂ : Nat} {x : BitVec w₁} {y : BitVec w₂} {v : Word64}
    (h : (Value.bits x : Bap.Value) = .bits y) (hx : narrowed w₁ v = x.toNat) : w₁ = w₂ ∧ narrowed w₂ v = y.toNat := by
  cases h
  exact ⟨rfl, hx⟩

theorem lowered_binary {op : Bil.BinOp} {left right : Bil.Exp} {first second : Lowering} {operand : Operand}
    (hne1 : op ≠ .smod) (hne2 : op ≠ .ashift) (wf : LayoutWF first)
    (ihl : ∀ {first second operand}, LayoutWF first → lowerExp first left = some (second, operand) →
      Lowered first second operand left)
    (ihr : ∀ {first second operand}, LayoutWF first → lowerExp first right = some (second, operand) →
      Lowered first second operand right)
    (h : lowerExp first (.bin op left right) = some (second, operand)) :
    Lowered first second operand (.bin op left right) := by
  rw [lowerExp] at h
  · obtain ⟨native, hop, h⟩ := obind h
    obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
    obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
    obtain ⟨newL, heL, hsL, h0L, h64L, vL⟩ := ihl wf h1
    have wf1 := heL.wf wf
    obtain ⟨newR, heR, hsR, h0R, h64R, vR⟩ := ihr wf1 h2
    have wf2 := heR.wf wf1
    have hwidth : Operand.width o1 = Operand.width o2 := by
      by_cases hc : Operand.width o1 = Operand.width o2
      · exact hc
      · simp [hc] at h
    simp only [hwidth, bne_self_eq_false, Bool.false_eq_true, ite_false, signExtend, temporary, bind,
      Option.bind, Option.some.injEq, Prod.mk.injEq] at h
    have hsL2 : Operand.slot o1 < Lowering.nextSlot l2 := Nat.lt_of_lt_of_le hsL heR.next
    have hheL := heL.trans heR wf
    cases hsigned : isSigned native
    · simp only [hsigned, Bool.false_eq_true, ite_false] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcount : ∀ o ∈ [Jit.Op.bin native (Lowering.nextSlot l2) (Operand.slot o1) (Operand.slot o2)],
          ∀ d, opDst o = some d → Lowering.nextSlot l2 ≤ d ∧ d < Lowering.nextSlot l2 + 1 := by
        intro o ho d hd
        simp only [List.mem_singleton] at ho
        subst ho
        simp only [opDst, Option.some.injEq] at hd
        omega
      refine lowered_tail wf hheL (extends_narrow (count := 1) wf2 rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (by simp [isExpressionOp]) hcount (by omega)) (by rw [narrow_nextSlot]; exact Nat.lt_succ_self _)
        (by simp only; split <;> omega) (by simp only; split <;> omega) ?_
      intro env machine hs hm w bits hev
      obtain ⟨w₁, x, w₂, y, hx, hy, hb⟩ := evalExp_bin_inv hev
      obtain ⟨hw1, hw2, hxv, hyv⟩ := operands_hold heL heR hsL vL vR hs hm hx hy
      subst hw1
      obtain rfl : w₂ = Operand.width o1 := by omega
      obtain ⟨result, hres, hnar⟩ := binary_correct hop h0L h64L hxv hyv
      simp only [hsigned, Bool.false_eq_true, ite_false] at hres hnar
      rw [hres] at hb
      simp only [Except.ok.injEq] at hb
      have hwd : (if isComparison native = true then 1 else Operand.width o1) ≤ 64 := by split <;> omega
      cases hb
      rw [← hwidth]
      refine ⟨rfl, ?_⟩
      apply value_narrow hwd
      simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true]
      exact hnar
    · simp only [hsigned, ite_true] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcount : ∀ o ∈ [Jit.Op.signExtend (Operand.width o2) (Lowering.nextSlot l2) (Operand.slot o1),
            .signExtend (Operand.width o2) (Lowering.nextSlot l2 + 1) (Operand.slot o2),
            Jit.Op.bin native (Lowering.nextSlot l2 + 1 + 1) (Lowering.nextSlot l2) (Lowering.nextSlot l2 + 1)],
          ∀ d, opDst o = some d → Lowering.nextSlot l2 ≤ d ∧ d < Lowering.nextSlot l2 + 3 := by
        intro o ho d hd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl | rfl <;> simp only [opDst, Option.some.injEq] at hd <;> omega
      refine lowered_tail wf hheL (extends_narrow (count := 3) wf2 ?_ rfl rfl rfl rfl rfl rfl rfl rfl
        ?_ hcount (by omega)) (by rw [narrow_nextSlot]; simp) (by simp only; split <;> omega)
        (by simp only; split <;> omega) ?_
      · simp [List.append_assoc]
      · simp [isExpressionOp]
      intro env machine hs hm w bits hev
      obtain ⟨w₁, x, w₂, y, hx, hy, hb⟩ := evalExp_bin_inv hev
      obtain ⟨hw1, hw2, hxv, hyv⟩ := operands_hold heL heR hsL vL vR hs hm hx hy
      subst hw1
      obtain rfl : w₂ = Operand.width o1 := by omega
      obtain ⟨result, hres, hnar⟩ := binary_correct hop h0L h64L hxv hyv
      simp only [hsigned, ite_true] at hres hnar
      rw [hres] at hb
      simp only [Except.ok.injEq] at hb
      have hwd : (if isComparison native = true then 1 else Operand.width o1) ≤ 64 := by split <;> omega
      cases hb
      rw [← hwidth]
      refine ⟨rfl, ?_⟩
      apply value_narrow hwd
      have hl2 : Operand.slot o1 < Lowering.nextSlot l2 := hsL2
      have hr2 : Operand.slot o2 < Lowering.nextSlot l2 := hsR
      have n1 : Operand.slot o2 ≠ Lowering.nextSlot l2 := by omega
      have a1 : Lowering.nextSlot l2 + 1 ≠ Lowering.nextSlot l2 := by omega
      have a2 : Lowering.nextSlot l2 ≠ Lowering.nextSlot l2 + 1 := by omega
      simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, n1, ite_false, a1, a2]
      exact hnar
  · exact hne1
  · exact hne2

theorem lowered_ashift {left right : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ihl : ∀ {first second operand}, LayoutWF first → lowerExp first left = some (second, operand) →
      Lowered first second operand left)
    (ihr : ∀ {first second operand}, LayoutWF first → lowerExp first right = some (second, operand) →
      Lowered first second operand right)
    (h : lowerExp first (.bin .ashift left right) = some (second, operand)) :
    Lowered first second operand (.bin .ashift left right) := by
  rw [lowerExp] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
  obtain ⟨newL, heL, hsL, h0L, h64L, vL⟩ := ihl wf h1
  have wf1 := heL.wf wf
  obtain ⟨newR, heR, hsR, h0R, h64R, vR⟩ := ihr wf1 h2
  have wf2 := heR.wf wf1
  have hwidth : Operand.width o1 = Operand.width o2 := by
    by_cases hc : Operand.width o1 = Operand.width o2
    · exact hc
    · simp [hc] at h
  simp only [hwidth, bne_self_eq_false, Bool.false_eq_true, ite_false, signExtend, temporary, bind,
    Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hsL2 : Operand.slot o1 < Lowering.nextSlot l2 := Nat.lt_of_lt_of_le hsL heR.next
  have hcount : ∀ o ∈ [Jit.Op.signExtend (Operand.width o2) (Lowering.nextSlot l2) (Operand.slot o1),
        Jit.Op.ashr (Operand.width o2) (Lowering.nextSlot l2 + 1) (Lowering.nextSlot l2) (Operand.slot o2)],
      ∀ d, opDst o = some d → Lowering.nextSlot l2 ≤ d ∧ d < Lowering.nextSlot l2 + 2 := by
    intro o ho d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp only [opDst, Option.some.injEq] at hd <;> omega
  refine lowered_tail wf (heL.trans heR wf) (extends_narrow (count := 2) wf2 ?_ rfl rfl rfl rfl rfl rfl rfl rfl
    ?_ hcount (by omega)) (by rw [narrow_nextSlot]; simp) h0R h64R ?_
  · simp [List.append_assoc]
  · simp [isExpressionOp]
  intro env machine hs hm w bits hev
  obtain ⟨w₁, x, w₂, y, hx, hy, hb⟩ := evalExp_bin_inv hev
  obtain ⟨hw1, hw2, hxv, hyv⟩ := operands_hold heL heR hsL vL vR hs hm hx hy
  subst hw1
  obtain rfl : w₂ = Operand.width o1 := by omega
  simp only [Bil.evalBin, Except.ok.injEq, dite_true] at hb
  cases hb
  rw [← hwidth]
  refine ⟨rfl, ?_⟩
  apply value_narrow h64L
  have n1 : Operand.slot o2 ≠ Lowering.nextSlot l2 := by omega
  have a1 : Lowering.nextSlot l2 + 1 ≠ Lowering.nextSlot l2 := by omega
  simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, n1, ite_false, a1,
    denoteSignExtend_holds h0L h64L hxv]
  exact narrow_ashr h0L h64L hyv

theorem lowered_ite {condition yes no : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ihc : ∀ {first second operand}, LayoutWF first → lowerExp first condition = some (second, operand) →
      Lowered first second operand condition)
    (ihy : ∀ {first second operand}, LayoutWF first → lowerExp first yes = some (second, operand) →
      Lowered first second operand yes)
    (ihn : ∀ {first second operand}, LayoutWF first → lowerExp first no = some (second, operand) →
      Lowered first second operand no)
    (h : lowerExp first (.ite condition yes no) = some (second, operand)) :
    Lowered first second operand (.ite condition yes no) := by
  rw [lowerExp] at h
  have hpure : (readsMemory yes || readsMemory no) = false := by
    by_cases hc : (readsMemory yes || readsMemory no) = true
    · simp [hc] at h
    · simpa using hc
  simp only [hpure, Bool.false_eq_true, ite_false] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
  obtain ⟨⟨l3, o3⟩, h3, h⟩ := obind h
  obtain ⟨newC, heC, hsC, h0C, h64C, vC⟩ := ihc wf h1
  have wf1 := heC.wf wf
  obtain ⟨newY, heY, hsY, h0Y, h64Y, vY⟩ := ihy wf1 h2
  have wf2 := heY.wf wf1
  obtain ⟨newN, heN, hsN, h0N, h64N, vN⟩ := ihn wf2 h3
  have wf3 := heN.wf wf2
  have hc1 : Operand.width o1 = 1 := by
    by_cases hc : Operand.width o1 = 1
    · exact hc
    · simp [hc] at h
  have hwidth : Operand.width o2 = Operand.width o3 := by
    by_cases hc : Operand.width o2 = Operand.width o3
    · exact hc
    · simp [hc] at h
  simp only [hc1, hwidth, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ite_false, temporary, bind,
    Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have heYN := heY.trans heN wf1
  have hcount : ∀ o ∈ [Jit.Op.select (Lowering.nextSlot l3) (Operand.slot o1) (Operand.slot o2) (Operand.slot o3)],
      ∀ d, opDst o = some d → Lowering.nextSlot l3 ≤ d ∧ d < Lowering.nextSlot l3 + 1 := by
    intro o ho d hd
    simp only [List.mem_singleton] at ho
    subst ho
    simp only [opDst, Option.some.injEq] at hd
    omega
  have hC3 : Operand.slot o1 < Lowering.nextSlot l3 := Nat.lt_of_lt_of_le hsC (Nat.le_trans heY.next heN.next)
  have hY3 : Operand.slot o2 < Lowering.nextSlot l3 := Nat.lt_of_lt_of_le hsY heN.next
  refine lowered_tail wf (heC.trans heYN wf) (Extends.tail 1 wf3 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [isExpressionOp]) hcount) (Nat.lt_succ_self _) h0N h64N ?_
  intro env machine hs hm w bits hev
  obtain ⟨bit, hbit, hb⟩ := evalExp_ite_inv hev
  obtain ⟨_, hcv⟩ := vC env machine (agree_first heC heYN hs) (memory_first heYN hm) 1 bit hbit
  have hs1 := agree_next heC heYN hs
  have hm1 := MemoryAgrees.after hm heC.pure
  have hs2 := agree_next heY heN hs1
  have hm2 := MemoryAgrees.after hm1 heY.pure
  rw [runOps_append, runOps_append]
  simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true]
  have hc3 : Holds ((runOps (runOps (runOps machine newC) newY) newN).slots (Operand.slot o1)) bit :=
    operand_after (Nat.lt_of_lt_of_le hsC heY.next) heN (operand_after hsC heY hcv)
  have hcond : (runOps (runOps (runOps machine newC) newY) newN).slots (Operand.slot o1) ≠ 0 ↔ bit = 1 := by
    simp only [Holds] at hc3
    have hb1 : bit.toNat < 2 := by simpa using bit.isLt
    have hone : BitVec.toNat (1 : BitVec 1) = 1 := rfl
    constructor
    · intro hne
      apply BitVec.eq_of_toNat_eq
      have : BitVec.toNat ((runOps (runOps (runOps machine newC) newY) newN).slots (Operand.slot o1)) ≠ 0 := by
        intro e
        exact hne (BitVec.eq_of_toNat_eq (by simpa using e))
      omega
    · intro e
      subst e
      intro hz
      rw [hz, hone] at hc3
      simp at hc3
  split at hb
  · next ht =>
    obtain ⟨hw, hy⟩ := vY env (runOps machine newC) (agree_first heY heN hs1) (memory_first heN hm1) w bits hb
    subst hw
    refine ⟨hwidth.symm, ?_⟩
    simp only [hcond, ht, ite_true]
    exact operand_after hsY heN hy
  · next ht =>
    obtain ⟨hw, hy⟩ := vN env (runOps (runOps machine newC) newY) hs2 hm2 w bits hb
    subst hw
    refine ⟨rfl, ?_⟩
    simp only [hcond, ht, ite_false]
    exact hy

/-- A shift of a slot by a constant below 64, then a mask: extraction and the high cast. -/
private theorem shifted_mask {v : Word64} {low target : Nat} (hlow : low < 64) (ht : target ≤ 64) :
    ((denoteBin .rshift v (UInt64.ofNat low).toBitVec) &&& (mask target).toBitVec).toNat =
      (v.toNat >>> low) % 2 ^ target := by
  rw [and_mask_toNat ht]
  have hval : (UInt64.ofNat low).toBitVec.toNat = low := by
    have he : (UInt64.ofNat low).toBitVec = BitVec.ofNat 64 low := rfl
    rw [he, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hlow (by decide))
  simp only [denoteBin, hval, show ¬ 64 ≤ low by omega, ite_false, BitVec.toNat_ushiftRight]

theorem lowered_extract {high low : Nat} {value : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first value = some (second, operand) →
      Lowered first second operand value)
    (h : lowerExp first (.extract high low value) = some (second, operand)) :
    Lowered first second operand (.extract high low value) := by
  rw [lowerExp] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨new, he, hslot, h0, h64, hval⟩ := ih wf h1
  have wf1 := he.wf wf
  have hc : ¬ (high < low ∨ high ≥ Operand.width o1) := by
    intro hc
    have : (decide (high < low) || decide (high ≥ Operand.width o1)) = true := by simpa using hc
    simp [this] at h
  have hb : (decide (high < low) || decide (high ≥ Operand.width o1)) = false := by simpa using hc
  simp only [hb, Bool.false_eq_true, ite_false, temporary, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hcount : ∀ o ∈ [Jit.Op.set (Lowering.nextSlot l1) (UInt64.ofNat low),
        Jit.Op.bin .rshift (Lowering.nextSlot l1 + 1) (Operand.slot o1) (Lowering.nextSlot l1),
        Jit.Op.andImm (Lowering.nextSlot l1 + 1 + 1) (Lowering.nextSlot l1 + 1) (mask (high - low + 1))],
      ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 3 := by
    intro o ho d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> simp only [opDst, Option.some.injEq] at hd <;> omega
  refine lowered_tail wf he (Extends.tail 3 wf1 ?_ rfl rfl rfl rfl rfl rfl rfl rfl ?_ hcount)
    (by simp) (by simp) (by simp; omega) ?_
  · simp [List.append_assoc]
  · simp [isExpressionOp]
  intro env machine hs hm w bits hev
  obtain ⟨w₀, x, result, hx, hr, hv⟩ := evalExp_extract_inv hev
  obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
  cases hv
  refine ⟨rfl, ?_⟩
  have hbits : result = BitVec.extractLsb high low x := by
    simp only [Word.extract] at hr
    split at hr
    · simp at hr
    · split at hr
      · simp at hr
      · simpa using hr.symm
  have n1 : Operand.slot o1 ≠ Lowering.nextSlot l1 := by omega
  have a1 : Lowering.nextSlot l1 + 1 ≠ Lowering.nextSlot l1 := by omega
  have a2 : Lowering.nextSlot l1 ≠ Lowering.nextSlot l1 + 1 := by omega
  simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, n1, ite_false, a1, Holds]
  rw [shifted_mask (by omega) (by omega), hbits, BitVec.extractLsb_toNat, hxv]

theorem lowered_cast_high {target : Nat} {value : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first value = some (second, operand) →
      Lowered first second operand value)
    (h : lowerExp first (.cast .high target value) = some (second, operand)) :
    Lowered first second operand (.cast .high target value) := by
  rw [lowerExp] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨new, he, hslot, h0, h64, hval⟩ := ih wf h1
  have wf1 := he.wf wf
  have hc : ¬ (target = 0 ∨ target > Operand.width o1) := by
    intro hc
    have : (decide (target = 0) || decide (target > Operand.width o1)) = true := by simpa using hc
    simp [this] at h
  have hb : (decide (target = 0) || decide (target > Operand.width o1)) = false := by simpa using hc
  simp only [hb, Bool.false_eq_true, ite_false, temporary, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hcount : ∀ o ∈ [Jit.Op.set (Lowering.nextSlot l1) (UInt64.ofNat (Operand.width o1 - target)),
        Jit.Op.bin .rshift (Lowering.nextSlot l1 + 1) (Operand.slot o1) (Lowering.nextSlot l1),
        Jit.Op.andImm (Lowering.nextSlot l1 + 1 + 1) (Lowering.nextSlot l1 + 1) (mask target)],
      ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 3 := by
    intro o ho d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> simp only [opDst, Option.some.injEq] at hd <;> omega
  refine lowered_tail wf he (Extends.tail 3 wf1 ?_ rfl rfl rfl rfl rfl rfl rfl rfl ?_ hcount)
    (by simp) (by simp; omega) (by simp; omega) ?_
  · simp [List.append_assoc]
  · simp [isExpressionOp]
  intro env machine hs hm w bits hev
  obtain ⟨w₀, x, hx, hv⟩ := evalExp_cast_inv hev
  obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
  obtain ⟨result, hr, hv⟩ := hv
  cases hv
  refine ⟨rfl, ?_⟩
  have hbits : result = BitVec.zeroExtend target (BitVec.ushiftRight x (Operand.width o1 - target)) := by
    simp only [Word.high] at hr
    split at hr
    · simpa using hr.symm
    · simp at hr
  have n1 : Operand.slot o1 ≠ Lowering.nextSlot l1 := by omega
  have a1 : Lowering.nextSlot l1 + 1 ≠ Lowering.nextSlot l1 := by omega
  have a2 : Lowering.nextSlot l1 ≠ Lowering.nextSlot l1 + 1 := by omega
  simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, n1, ite_false, a1, Holds]
  rw [shifted_mask (by omega) (by omega), hbits]
  simp only [Holds] at hxv
  simp [BitVec.toNat_setWidth, hxv]

theorem lowered_cast_signed {target : Nat} {value : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first value = some (second, operand) →
      Lowered first second operand value)
    (h : lowerExp first (.cast .signed target value) = some (second, operand)) :
    Lowered first second operand (.cast .signed target value) := by
  rw [lowerExp] at h
  have hc : ¬ (target = 0 ∨ target > 64) := by
    intro hc
    have : (decide (target = 0) || decide (target > 64)) = true := by simpa using hc
    simp [this] at h
  have hb : (decide (target = 0) || decide (target > 64)) = false := by simpa using hc
  simp only [hb, Bool.false_eq_true, ite_false] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨new, he, hslot, h0, h64, hval⟩ := ih wf h1
  have wf1 := he.wf wf
  by_cases hge : target ≥ Operand.width o1
  · simp only [hge, ite_true, signExtend, temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcount : ∀ o ∈ [Jit.Op.signExtend (Operand.width o1) (Lowering.nextSlot l1) (Operand.slot o1)],
        ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 1 := by
      intro o ho d hd
      simp only [List.mem_singleton] at ho
      subst ho
      simp only [opDst, Option.some.injEq] at hd
      omega
    refine lowered_tail wf he (extends_narrow (count := 1) wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by simp [isExpressionOp]) hcount (by omega)) (by rw [narrow_nextSlot]; exact Nat.lt_succ_self _)
      (by simp only; omega) (by simp only; omega) ?_
    intro env machine hs hm w bits hev
    obtain ⟨w₀, x, hx, hv⟩ := evalExp_cast_inv hev
    obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
    cases hv
    refine ⟨rfl, ?_⟩
    apply value_narrow (by omega)
    simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true,
      denoteSignExtend_holds h0 h64 hxv]
    exact narrow_cast_signed h64 hge (by omega)
  · simp only [hge, ite_false, temporary, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcount : ∀ o ∈ [Jit.Op.andImm (Lowering.nextSlot l1) (Operand.slot o1) (mask target)],
        ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 1 := by
      intro o ho d hd
      simp only [List.mem_singleton] at ho
      subst ho
      simp only [opDst, Option.some.injEq] at hd
      omega
    refine lowered_tail wf he (Extends.tail 1 wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by simp [isExpressionOp]) hcount) (Nat.lt_succ_self _) (by simp only; omega) (by simp only; omega) ?_
    intro env machine hs hm w bits hev
    obtain ⟨w₀, x, hx, hv⟩ := evalExp_cast_inv hev
    obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
    cases hv
    refine ⟨rfl, ?_⟩
    simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, Holds]
    rw [and_mask_toNat (by omega), hxv, Word.signed,
      BitVec.signExtend_eq_setWidth_of_le x (by omega), BitVec.toNat_setWidth]

private theorem cast_zero_value {kind : Bil.Cast} {target width : Nat} {exp : Bil.Exp} {env : Bil.Env} {bits : BitVec width}
    (hk : kind = .low ∨ kind = .unsigned) (h : Bil.evalExp env (.cast kind target exp) = .ok (.bits bits)) :
    ∃ (w₀ : Nat) (x : BitVec w₀), Bil.evalExp env exp = .ok (.bits x) ∧ target = width ∧
      BitVec.toNat bits = x.toNat % 2 ^ target := by
  obtain ⟨w₀, x, hx, hv⟩ := evalExp_cast_inv h
  refine ⟨w₀, x, hx, ?_⟩
  rcases hk with rfl | rfl
  · simp only at hv
    cases hv
    exact ⟨rfl, by simp [Word.low, BitVec.toNat_setWidth]⟩
  · simp only at hv
    cases hv
    exact ⟨rfl, by simp [Word.unsigned, BitVec.toNat_setWidth]⟩

/-- `low` and `unsigned` keep the low bits or extend with zeros. -/
theorem lowered_cast_zero {kind : Bil.Cast} {target : Nat} {value : Bil.Exp} {first second : Lowering} {operand : Operand}
    (hk : kind = .low ∨ kind = .unsigned) (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first value = some (second, operand) →
      Lowered first second operand value)
    (h : lowerExp first (.cast kind target value) = some (second, operand)) :
    Lowered first second operand (.cast kind target value) := by
  have hne1 : kind ≠ .signed := by rcases hk with rfl | rfl <;> simp
  have hne2 : kind ≠ .high := by rcases hk with rfl | rfl <;> simp
  rw [lowerExp] at h
  · have hkk : (kind != .low && kind != .unsigned) = false := by rcases hk with rfl | rfl <;> rfl
    have hc : ¬ (target = 0 ∨ target > 64) := by
      intro hc
      have : ((kind != .low && kind != .unsigned) || decide (target = 0) || decide (target > 64)) = true := by
        rcases hc with hc | hc <;> simp [hc]
      simp [this] at h
    have hb : ((kind != .low && kind != .unsigned) || decide (target = 0) || decide (target > 64)) = false := by
      simp [hkk]
      omega
    simp only [hb, Bool.false_eq_true, ite_false] at h
    obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
    obtain ⟨new, he, hslot, h0, h64, hval⟩ := ih wf h1
    have wf1 := he.wf wf
    by_cases hge : target ≥ Operand.width o1
    · simp only [hge, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine lowered_tail wf he (Extends.refl l1) hslot (by simp only; omega) (by simp only; omega) ?_
      intro env machine hs hm w bits hev
      obtain ⟨w₀, x, hx, hw, hbits⟩ := cast_zero_value hk hev
      obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
      refine ⟨hw, ?_⟩
      simp only [Holds] at hxv
      simp only [runOps_nil, Holds, hbits, hxv]
      exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hge))).symm
    · simp only [hge, ite_false, temporary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hcount : ∀ o ∈ [Jit.Op.andImm (Lowering.nextSlot l1) (Operand.slot o1) (mask target)],
          ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 1 := by
        intro o ho d hd
        simp only [List.mem_singleton] at ho
        subst ho
        simp only [opDst, Option.some.injEq] at hd
        omega
      refine lowered_tail wf he (Extends.tail 1 wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (by simp [isExpressionOp]) hcount) (Nat.lt_succ_self _) (by simp only; omega) (by simp only; omega) ?_
      intro env machine hs hm w bits hev
      obtain ⟨w₀, x, hx, hw, hbits⟩ := cast_zero_value hk hev
      obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ x hx
      refine ⟨hw, ?_⟩
      simp only [runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, Holds]
      simp only [Holds] at hxv
      rw [and_mask_toNat (by omega), hxv, hbits]
  · exact hne1
  · exact hne2

/-! ### Memory -/

private theorem or_shift_low {acc byte shift : Nat} (hacc : acc < 2 ^ shift) :
    acc ||| (byte <<< shift) = acc + byte * 2 ^ shift := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm byte, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hacc, Nat.add_comm]

/-- A byte shifted within a 64-bit slot. -/
private theorem shifted_byte {byte : UInt8} {shift : Nat} (hs : shift + 8 ≤ 64) :
    (BitVec.ofNat 64 byte.toNat <<< shift).toNat = byte.toNat <<< shift := by
  have hb : byte.toNat < 2 ^ 8 := byte.toNat_lt
  have hb64 : byte.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by decide))
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb64]
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  calc byte.toNat * 2 ^ shift < 2 ^ 8 * 2 ^ shift := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
    _ = 2 ^ (8 + shift) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)

/-- The little-endian sum of the first bytes. -/
private def littleValue (byte : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => littleValue byte k + byte k * 2 ^ (k * 8)

private theorem littleValue_lt (byte : Nat → Nat) (h : ∀ i, byte i < 2 ^ 8) (k : Nat) :
    littleValue byte k < 2 ^ (k * 8) := by
  induction k with
  | zero => simp [littleValue]
  | succ k ih =>
    simp only [littleValue]
    have h1 : (byte k + 1) * 2 ^ (k * 8) ≤ 2 ^ 8 * 2 ^ (k * 8) :=
      Nat.mul_le_mul_right _ (h k)
    have h2 : 2 ^ ((k + 1) * 8) = 2 ^ 8 * 2 ^ (k * 8) := by
      rw [Nat.add_mul, Nat.pow_add, Nat.mul_comm]
    rw [h2]
    rw [Nat.add_mul] at h1
    omega

/-- The big-endian value of the first bytes. -/
private def bigValue (byte : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => bigValue byte k * 256 + byte k

private theorem bigValue_lt (byte : Nat → Nat) (h : ∀ i, byte i < 2 ^ 8) (k : Nat) :
    bigValue byte k < 2 ^ (k * 8) := by
  induction k with
  | zero => simp [bigValue]
  | succ k ih =>
    simp only [bigValue]
    have h2 : 2 ^ ((k + 1) * 8) = 2 ^ (k * 8) * 256 := by
      rw [Nat.add_mul, Nat.pow_add]
    have h3 : (bigValue byte k + 1) * 256 ≤ 2 ^ (k * 8) * 256 := Nat.mul_le_mul_right _ ih
    have hb := h k
    rw [Nat.add_mul] at h3
    simp at hb
    omega

private theorem range_foldl_succ {α : Type} (f : α → Nat → α) (init : α) (k : Nat) :
    (List.range (k + 1)).foldl f init = f ((List.range k).foldl f init) k := by
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The native load is the little-endian value. -/
private theorem load_little (memory : Word64 → UInt8) (base : Word64) {size : Nat} (k : Nat) (hk : k ≤ size) (hs : size ≤ 8) :
    ((List.range k).foldl (fun result index =>
      result ||| (BitVec.ofNat 64 (memory (base + BitVec.ofNat 64 index)).toNat <<< (index * 8))) 0#64).toNat =
      littleValue (fun i => (memory (base + BitVec.ofNat 64 i)).toNat) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [range_foldl_succ, BitVec.toNat_or, ih (by omega), littleValue]
    rw [shifted_byte (by omega), or_shift_low]
    exact littleValue_lt _ (fun i => (memory (base + BitVec.ofNat 64 i)).toNat_lt) k

/-- The native load is the big-endian value: the bytes so far are above the ones to come. -/
private theorem load_big (memory : Word64 → UInt8) (base : Word64) {size : Nat} (k : Nat) (hk : k ≤ size) (hs : size ≤ 8) :
    ((List.range k).foldl (fun result index =>
      result ||| (BitVec.ofNat 64 (memory (base + BitVec.ofNat 64 index)).toNat <<<
        ((size - 1 - index) * 8))) 0#64).toNat =
      bigValue (fun i => (memory (base + BitVec.ofNat 64 i)).toNat) k * 2 ^ ((size - k) * 8) := by
  induction k with
  | zero => simp [bigValue]
  | succ k ih =>
    rw [range_foldl_succ, BitVec.toNat_or, ih (by omega), bigValue]
    rw [shifted_byte (by omega), Nat.shiftLeft_eq]
    have hp : (size - k) * 8 = (size - (k + 1)) * 8 + 8 := by
      have : size - k = (size - (k + 1)) + 1 := by omega
      rw [this, Nat.add_mul]
    have hshift : size - 1 - k = size - (k + 1) := by omega
    have hbyte : (memory (base + BitVec.ofNat 64 k)).toNat < 2 ^ 8 := (memory (base + BitVec.ofNat 64 k)).toNat_lt
    rw [hshift, hp]
    generalize (memory (base + BitVec.ofNat 64 k)).toNat = byte at hbyte ⊢
    generalize bigValue _ k = value
    generalize (size - (k + 1)) * 8 = shift
    have h1 : value * 2 ^ (shift + 8) = (value * 2 ^ 8) * 2 ^ shift := by
      rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm (2 ^ shift)]
    have h2 : (value * 2 ^ 8 ||| byte) = value * 256 + byte := by
      rw [Nat.mul_comm value, ← Nat.two_pow_add_eq_or_of_lt hbyte]
    rw [h1, ← Nat.shiftLeft_eq (value * 2 ^ 8) shift, ← Nat.shiftLeft_eq byte shift, ← Nat.shiftLeft_or_distrib, h2,
      Nat.shiftLeft_eq]

private theorem bigValue_congr {f g : Nat → Nat} {k : Nat} (h : ∀ i, i < k → f i = g i) : bigValue f k = bigValue g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [bigValue]
    rw [ih fun i hi => h i (by omega), h k (by omega)]

private theorem littleValue_congr {f g : Nat → Nat} {k : Nat} (h : ∀ i, i < k → f i = g i) :
    littleValue f k = littleValue g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [littleValue]
    rw [ih fun i hi => h i (by omega), h k (by omega)]

private theorem read_big (g : Nat → UInt8) (k : Nat) :
    ((List.range k).map g).foldl (fun result byte => result * 256 + byte.toNat) 0 =
      bigValue (fun i => (g i).toNat) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih, bigValue]
    rfl

private theorem read_little (g : Nat → UInt8) (k init : Nat) :
    (((List.range k).map g).reverse).foldl (fun result byte => result * 256 + byte.toNat) init =
      init * 2 ^ (k * 8) + littleValue (fun i => (g i).toNat) k := by
  induction k generalizing init with
  | zero => simp [littleValue]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.foldl_cons]
    rw [ih, littleValue]
    have : 2 ^ ((k + 1) * 8) = 256 * 2 ^ (k * 8) := by
      rw [Nat.add_mul, Nat.pow_add, Nat.mul_comm]
    rw [this, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (g k).toNat, Nat.add_assoc, Nat.add_comm ((2 ^ (k * 8)) * _),
      Nat.mul_comm (2 ^ (k * 8))]

/-- The native load of at most 8 bytes reads what the interpreter reads, in either byte order. -/
theorem denoteLoad_read {width size : Nat} {cells : Bap.Memory width} {address : BitVec width} {memory : Word64 → UInt8}
    (endian : Endian) (hs : size ≤ 8) (_hw : width ≤ 64)
    (hagree : ∀ offset, offset < 8 → memory (address.setWidth 64 + BitVec.ofNat 64 offset) =
      Bap.Memory.readByte cells (address + BitVec.ofNat width offset)) :
    (denoteLoad memory (address.setWidth 64) size (endian == .big)).toNat =
      (Bap.Memory.read cells address endian size).toNat := by
  have hbytes : ∀ i, (memory (address.setWidth 64 + BitVec.ofNat 64 i)).toNat < 2 ^ 8 := fun i => UInt8.toNat_lt _
  simp only [Bap.Memory.read, BitVec.toNat_ofNat]
  cases endian with
  | little =>
    have h1 := load_little memory (address.setWidth 64) (size := size) size (Nat.le_refl _) hs
    have h1' : (denoteLoad memory (address.setWidth 64) size (Endian.little == .big)).toNat = _ := h1
    rw [h1', read_little]
    simp only [Nat.zero_mul, Nat.zero_add]
    have hc : littleValue (fun i => (memory (address.setWidth 64 + BitVec.ofNat 64 i)).toNat) size =
        littleValue (fun i => (Bap.Memory.readByte cells (address + BitVec.ofNat width i)).toNat) size :=
      littleValue_congr fun i hi => by rw [hagree i (by omega)]
    rw [← hc]
    exact (Nat.mod_eq_of_lt (littleValue_lt _ hbytes size)).symm
  | big =>
    have h1 := load_big memory (address.setWidth 64) (size := size) size (Nat.le_refl _) hs
    have h1' : (denoteLoad memory (address.setWidth 64) size (Endian.big == .big)).toNat = _ := h1
    rw [h1', read_big]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
    have hc : bigValue (fun i => (memory (address.setWidth 64 + BitVec.ofNat 64 i)).toNat) size =
        bigValue (fun i => (Bap.Memory.readByte cells (address + BitVec.ofNat width i)).toNat) size :=
      bigValue_congr fun i hi => by rw [hagree i (by omega)]
    rw [← hc]
    exact (Nat.mod_eq_of_lt (bigValue_lt _ hbytes size)).symm

theorem useMemory_extends {first second : Lowering} {var : Bap.Var} (h : useMemory first var = some second) :
    Extends first second [] := by
  unfold useMemory at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    next hm =>
    exact {
      ops := by simp
      next := Nat.le_refl _
      extra := ⟨[], by simp, by simp⟩
      pure := by simp
      writes := by simp
      distinct := id
      vars := id
      memory := fun v hv => by rw [hm] at hv; simp at hv
      written := rfl
      outputs := rfl
      nextLabel := rfl
      effect := rfl
      stable := rfl }
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Extends.refl first
    · simp at h
  · simp at h

theorem lowered_load {var : Bap.Var} {address : Bil.Exp} {endian : Endian} {size : Nat} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ih : ∀ {first second operand}, LayoutWF first → lowerExp first address = some (second, operand) →
      Lowered first second operand address)
    (h : lowerExp first (.load (.var var) address endian size) = some (second, operand)) :
    Lowered first second operand (.load (.var var) address endian size) := by
  rw [lowerExp] at h
  obtain ⟨v0, hv0, h⟩ := obind h
  simp only [Option.some.injEq] at hv0
  subst hv0
  obtain ⟨l0, h0, h⟩ := obind h
  have h0 := useMemoryAt_some h0
  have he0 := useMemory_extends h0
  have wf0 := he0.wf wf
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨new, he, hslot, hp, h64, hval⟩ := ih wf0 h1
  have wf1 := he.wf wf0
  have hc : ¬ (size = 0 ∨ size > 8) := by
    intro hc
    have : (decide (size = 0) || decide (size > 8) || !addressOf var (Operand.width o1)) = true := by
      rcases hc with hc | hc <;> simp [hc]
    simp [this] at h
  have hb : (decide (size = 0) || decide (size > 8) || !addressOf var (Operand.width o1)) = false := by
    by_cases hd : (decide (size = 0) || decide (size > 8) || !addressOf var (Operand.width o1)) = false
    · exact hd
    · simp only [Bool.not_eq_false] at hd
      simp [hd] at h
  simp only [hb, Bool.false_eq_true, ite_false, temporary, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hcount : ∀ o ∈ [Jit.Op.memLoad (Lowering.nextSlot l1) (Operand.slot o1) size (endian == .big)],
      ∀ d, opDst o = some d → Lowering.nextSlot l1 ≤ d ∧ d < Lowering.nextSlot l1 + 1 := by
    intro o ho d hd
    simp only [List.mem_singleton] at ho
    subst ho
    simp only [opDst, Option.some.injEq] at hd
    omega
  have hwf := he0.trans he wf
  refine lowered_tail wf hwf (Extends.tail 1 wf1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [isExpressionOp]) hcount) (Nat.lt_succ_self _) (by simp only; omega) (by simp only; omega) ?_
  intro env machine hs hm w bits hev
  obtain ⟨wa, cells, addressBits, hcells, haddr, hv⟩ := evalExp_load_inv hev
  obtain ⟨rfl, hxv⟩ := hval env machine hs hm _ addressBits haddr
  cases hv
  refine ⟨rfl, ?_⟩
  simp only [List.nil_append, runOps_cons, runOps_nil, step, Machine.write_slots, ite_true, Holds]
  have hsize : size ≤ 8 := by omega
  have hbase : (runOps machine new).slots (Operand.slot o1) = addressBits.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [Holds] at hxv
    rw [hxv, BitVec.toNat_setWidth]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le addressBits.isLt (Nat.pow_le_pow_right (by decide) h64))).symm
  have hagree : ∀ offset, offset < 8 →
      (fun address => (runOps machine new).memory ((runOps machine new).view address))
        (addressBits.setWidth 64 + BitVec.ofNat 64 offset) =
      Bap.Memory.readByte cells (addressBits + BitVec.ofNat _ offset) := by
    intro offset ho
    show (runOps machine new).memory ((runOps machine new).view _) = _
    rw [runOps_memory he.pure, runOps_view]
    apply hm var (he.memory var (useMemory_some h0)) _ cells _ _ _ ho
    simpa [Bil.evalExp] using hcells
  rw [hbase]
  exact denoteLoad_read endian hsize h64 hagree

/-! `smod`: the sign of a nonzero result follows the divisor, `smod x 0 = x`. -/

private theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (x y : α) : (if c then x else y) = x := by
  simp [h]

private theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (x y : α) : (if c then x else y) = y := by
  simp [h]

private theorem slt_zero_ne {w : Nat} (a : BitVec w) (hw : w ≤ 64) :
    denoteBin .slt (a.signExtend 64) (0 : Word64) ≠ 0 ↔ a.msb = true := by
  have hval : (a.signExtend 64).toInt = a.toInt := BitVec.toInt_signExtend_of_le hw
  have hneg : a.toInt < 0 ↔ a.msb = true := by
    rw [BitVec.msb_eq_toInt]
    simp
  simp only [denoteBin, flag, hval]
  by_cases h : a.toInt < 0
  · simp [h, hneg.1 h]
  · have : a.msb = false := by
      cases hm : a.msb
      · rfl
      · exact absurd (hneg.2 hm) h
    simp [h, this]

/-- The operations of `smod` after the signs and the absolute values, on slots with these values. -/
private theorem smod_tail {w : Nat} {a b : BitVec w} {leftSign rightSign negatedLeft negatedRight l r : Word64} (hw : w ≤ 64)
    (hls : leftSign ≠ 0 ↔ a.msb = true) (hrs : rightSign ≠ 0 ↔ b.msb = true)
    (hnl : Holds negatedLeft (-a)) (hnr : Holds negatedRight (-b)) (hl : Holds l a) (hr : Holds r b) :
    let absLeft := if leftSign ≠ 0 then negatedLeft else l
    let absRight := if rightSign ≠ 0 then negatedRight else r
    let remainder := denoteBin .urem absLeft absRight
    let negated := -remainder
    let leftResult := if leftSign ≠ 0 then negated + r else remainder
    let bothResult := if leftSign ≠ 0 then negated else remainder + r
    let rightResult := if rightSign ≠ 0 then bothResult else leftResult
    narrowed w (if denoteBin .eq remainder 0 ≠ 0 then remainder else rightResult) = (Word.smod a b).toNat := by
  intro absLeft absRight remainder negated leftResult bothResult rightResult
  let u : BitVec w := (if a.msb then -a else a) % (if b.msb then -b else b)
  have hrem : Holds remainder u := by
    have h1 : Holds absLeft (if a.msb then -a else a) := by
      cases hm : a.msb
      · have : ¬ leftSign ≠ 0 := fun h => by rw [hls.1 h] at hm; cases hm
        simp only [absLeft, ite_neg' this]
        simpa using hl
      · have : leftSign ≠ 0 := hls.2 hm
        simp only [absLeft, ite_pos' this]
        simpa using hnl
    have h2 : Holds absRight (if b.msb then -b else b) := by
      cases hm : b.msb
      · have : ¬ rightSign ≠ 0 := fun h => by rw [hrs.1 h] at hm; cases hm
        simp only [absRight, ite_neg' this]
        simpa using hr
      · have : rightSign ≠ 0 := hrs.2 hm
        simp only [absRight, ite_pos' this]
        simpa using hnr
    simp only [Holds] at h1 h2 ⊢
    simp only [remainder, denoteBin, u, BitVec.toNat_umod]
    split
    · next hz =>
      have h3 : BitVec.toNat (if b.msb = true then -b else b) = 0 := by
        rw [← h2, hz]
        rfl
      rw [h1, h3, Nat.mod_zero]
    · simp only [BitVec.toNat_umod, h1, h2]
  have hremlt : narrowed w remainder = u.toNat := by
    have he : remainder.toNat = u.toNat := hrem
    simp only [narrowed, he]
    exact Nat.mod_eq_of_lt u.isLt
  have hzero : denoteBin .eq remainder 0 ≠ 0 ↔ u = 0 := by
    have he : remainder.toNat = u.toNat := hrem
    have : remainder = 0 ↔ u = 0 := by
      constructor
      · intro e
        rw [e] at he
        exact BitVec.eq_of_toNat_eq (by simpa using he.symm)
      · intro e
        rw [e] at he
        exact BitVec.eq_of_toNat_eq (by simpa using he)
    simp only [denoteBin, flag, this.symm]
    by_cases h : remainder = 0 <;> simp [h]
  have hsub : ∀ {x : Word64}, -x + r = r - x := by
    intro x
    rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
  simp only [Word.smod, Word.toNat, BitVec.smod]
  cases hma : a.msb <;> cases hmb : b.msb
  · have h1 : ¬ leftSign ≠ 0 := fun h => by rw [hls.1 h] at hma; cases hma
    have h2 : ¬ rightSign ≠ 0 := fun h => by rw [hrs.1 h] at hmb; cases hmb
    have hu : u = a.umod b := by simp [u, hma, hmb]
    have e1 : rightResult = remainder := by
      simp only [rightResult, leftResult, ite_neg' h1, ite_neg' h2]
    simp only [e1, ite_self]
    rw [hremlt, hu]
  · have h1 : ¬ leftSign ≠ 0 := fun h => by rw [hls.1 h] at hma; cases hma
    have h2 : rightSign ≠ 0 := hrs.2 hmb
    have hu : u = a.umod b.neg := by simp [u, hma, hmb]
    have e1 : rightResult = remainder + r := by
      simp only [rightResult, bothResult, ite_neg' h1, ite_pos' h2]
    simp only [e1]
    rw [← hu]
    by_cases hz : u = 0
    · rw [ite_pos' (hzero.2 hz), hremlt, ite_pos' (show u = BitVec.zero w from hz)]
    · have hn : ¬ denoteBin .eq remainder 0 ≠ 0 := fun h => hz (hzero.1 h)
      rw [ite_neg' hn, ite_neg' (show ¬ u = BitVec.zero w from hz)]
      exact narrow_add hw hrem hr
  · have h1 : leftSign ≠ 0 := hls.2 hma
    have h2 : ¬ rightSign ≠ 0 := fun h => by rw [hrs.1 h] at hmb; cases hmb
    have hu : u = (a.neg).umod b := by simp [u, hma, hmb]
    have e1 : rightResult = r - remainder := by
      simp only [rightResult, leftResult, ite_pos' h1, ite_neg' h2, negated, hsub]
    simp only [e1]
    rw [← hu]
    by_cases hz : u = 0
    · rw [ite_pos' (hzero.2 hz), hremlt, ite_pos' (show u = BitVec.zero w from hz)]
    · have hn : ¬ denoteBin .eq remainder 0 ≠ 0 := fun h => hz (hzero.1 h)
      rw [ite_neg' hn, ite_neg' (show ¬ u = BitVec.zero w from hz)]
      exact narrow_sub hw hr hrem
  · have h1 : leftSign ≠ 0 := hls.2 hma
    have h2 : rightSign ≠ 0 := hrs.2 hmb
    have hu : u = (a.neg).umod b.neg := by simp [u, hma, hmb]
    have e1 : rightResult = -remainder := by
      simp only [rightResult, bothResult, ite_pos' h1, ite_pos' h2, negated]
    simp only [e1]
    rw [← hu]
    by_cases hz : u = 0
    · rw [ite_pos' (hzero.2 hz), hremlt, hz]
      simp [BitVec.neg]
    · have hn : ¬ denoteBin .eq remainder 0 ≠ 0 := fun h => hz (hzero.1 h)
      rw [ite_neg' hn]
      exact narrow_neg hw hrem

theorem lowered_smod {left right : Bil.Exp} {first second : Lowering} {operand : Operand}
    (wf : LayoutWF first)
    (ihl : ∀ {first second operand}, LayoutWF first → lowerExp first left = some (second, operand) →
      Lowered first second operand left)
    (ihr : ∀ {first second operand}, LayoutWF first → lowerExp first right = some (second, operand) →
      Lowered first second operand right)
    (h : lowerExp first (.bin .smod left right) = some (second, operand)) :
    Lowered first second operand (.bin .smod left right) := by
  rw [lowerExp] at h
  obtain ⟨⟨l1, o1⟩, h1, h⟩ := obind h
  obtain ⟨⟨l2, o2⟩, h2, h⟩ := obind h
  obtain ⟨newL, heL, hsL, h0L, h64L, vL⟩ := ihl wf h1
  have wf1 := heL.wf wf
  obtain ⟨newR, heR, hsR, h0R, h64R, vR⟩ := ihr wf1 h2
  have wf2 := heR.wf wf1
  have hwidth : Operand.width o1 = Operand.width o2 := by
    by_cases hc : Operand.width o1 = Operand.width o2
    · exact hc
    · simp [hc] at h
  simp only [hwidth, bne_self_eq_false, Bool.false_eq_true, ite_false, signExtend, temporary, bind,
    Option.bind, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hsL2 : Operand.slot o1 < Lowering.nextSlot l2 := Nat.lt_of_lt_of_le hsL heR.next
  have hheL := heL.trans heR wf
  generalize hw : Operand.width o2 = w at *
  generalize hn : Lowering.nextSlot l2 = n at *
  have hcount : ∀ o ∈ ([.set n 0, .signExtend w (n + 1) (Operand.slot o1), .signExtend w (n + 2) (Operand.slot o2),
      .bin .slt (n + 3) (n + 1) n, .bin .slt (n + 4) (n + 2) n,
      .neg (n + 5) (Operand.slot o1), .neg (n + 6) (Operand.slot o2)] : List Jit.Op) ++ narrowOps w (n + 5) ++ narrowOps w (n + 6) ++ [
      .select (n + 7) (n + 3) (n + 5) (Operand.slot o1), .select (n + 8) (n + 4) (n + 6) (Operand.slot o2),
      .bin .urem (n + 9) (n + 7) (n + 8), .neg (n + 10) (n + 9),
      .bin .add (n + 11) (n + 10) (Operand.slot o2), .bin .add (n + 12) (n + 9) (Operand.slot o2),
      .select (n + 13) (n + 3) (n + 11) (n + 9), .select (n + 14) (n + 3) (n + 10) (n + 12),
      .select (n + 15) (n + 4) (n + 14) (n + 13), .bin .eq (n + 16) (n + 9) n,
      .select (n + 17) (n + 16) (n + 9) (n + 15)],
      ∀ d, opDst o = some d → n ≤ d ∧ d < n + 18 := by
    intro o ho d hd
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ((ho | ho) | ho) | ho
    · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [opDst, Option.some.injEq] at hd <;> omega
    · rw [narrowOps_writes _ _ _ ho _ hd]
      omega
    · rw [narrowOps_writes _ _ _ ho _ hd]
      omega
    · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [opDst, Option.some.injEq] at hd <;> omega
  have hpure : ∀ o ∈ ([.set n 0, .signExtend w (n + 1) (Operand.slot o1), .signExtend w (n + 2) (Operand.slot o2),
      .bin .slt (n + 3) (n + 1) n, .bin .slt (n + 4) (n + 2) n,
      .neg (n + 5) (Operand.slot o1), .neg (n + 6) (Operand.slot o2)] : List Jit.Op) ++ narrowOps w (n + 5) ++ narrowOps w (n + 6) ++ [
      .select (n + 7) (n + 3) (n + 5) (Operand.slot o1), .select (n + 8) (n + 4) (n + 6) (Operand.slot o2),
      .bin .urem (n + 9) (n + 7) (n + 8), .neg (n + 10) (n + 9),
      .bin .add (n + 11) (n + 10) (Operand.slot o2), .bin .add (n + 12) (n + 9) (Operand.slot o2),
      .select (n + 13) (n + 3) (n + 11) (n + 9), .select (n + 14) (n + 3) (n + 10) (n + 12),
      .select (n + 15) (n + 4) (n + 14) (n + 13), .bin .eq (n + 16) (n + 9) n,
      .select (n + 17) (n + 16) (n + 9) (n + 15)], isExpressionOp o = true := by
    intro o ho
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ((ho | ho) | ho) | ho
    · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · exact narrowOps_pure _ _ _ ho
    · exact narrowOps_pure _ _ _ ho
    · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  subst hn
  simp only [narrow_nextSlot, narrow_ops, narrow_layout, narrow_memory, narrow_written, narrow_outputs, narrow_nextLabel,
    narrow_effectSlot, narrow_next, Nat.add_assoc, Nat.reduceAdd]
  refine lowered_tail wf hheL (extends_narrow (count := 18) wf2 ?_ rfl rfl rfl rfl rfl rfl rfl rfl hpure hcount (by omega))
    (by rw [narrow_nextSlot]; simp) (by simp only; omega) (by simp only; omega) ?_
  · simp [List.append_assoc]
  intro env machine hs hm width bits hev
  obtain ⟨w₁, x, w₂, y, hx, hy, hb⟩ := evalExp_bin_inv hev
  obtain ⟨hw1, hw2, hxv, hyv⟩ := operands_hold heL heR hsL vL
    (fun e m a c wi bi he => by have := vR e m a c wi bi he; rwa [← hw] at this) hs hm hx hy
  obtain rfl : w = w₁ := by omega
  obtain rfl : w = w₂ := by omega
  simp only [Bil.evalBin, Except.ok.injEq, dite_true] at hb
  cases hb
  refine ⟨rfl, ?_⟩
  have h64w : w ≤ 64 := by omega
  have h0w : 0 < w := by omega
  apply value_narrow h64w
  generalize hM0 : runOps machine (newL ++ newR) = M0 at *
  generalize Operand.slot o1 = L at *
  generalize Operand.slot o2 = R at *
  generalize Lowering.nextSlot l2 = n at *
  have hLk : ∀ k, L ≠ n + k := fun k => by omega
  have hRk : ∀ k, R ≠ n + k := fun k => by omega
  have hLn : L ≠ n := by omega
  have hRn : R ≠ n := by omega
  have hsx := denoteSignExtend_holds h0w h64w hxv
  have hsy := denoteSignExtend_holds h0w h64w hyv
  rw [runOps_append, runOps_append, runOps_append]
  generalize hM1 : runOps M0 [.set n 0, .signExtend w (n + 1) L, .signExtend w (n + 2) R,
      .bin .slt (n + 3) (n + 1) n, .bin .slt (n + 4) (n + 2) n,
      .neg (n + 5) L, .neg (n + 6) R] = M1
  have m3 : M1.slots (n + 3) = denoteBin .slt (x.signExtend 64) 0 := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn, hsx, hsy]
  have m4 : M1.slots (n + 4) = denoteBin .slt (y.signExtend 64) 0 := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn, hsx, hsy]
  have m5 : M1.slots (n + 5) = -M0.slots L := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn]
  have m6 : M1.slots (n + 6) = -M0.slots R := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn]
  have mL : M1.slots L = M0.slots L := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn]
  have mR : M1.slots R = M0.slots R := by
    subst hM1
    simp [step, hLk, hRk, hLn, hRn]
  have m0 : M1.slots n = 0 := by
    subst hM1
    simp [step]
  have hxh : Holds (M1.slots L) x := by rw [mL]; exact hxv
  have hyh : Holds (M1.slots R) y := by rw [mR]; exact hyv
  have hnx : Holds ((runOps (runOps M1 (narrowOps w (n + 5))) (narrowOps w (n + 6))).slots (n + 5)) (-x) := by
    show BitVec.toNat _ = _
    rw [runOps_slot_other (narrowOps_pure _ _) (fun o ho d hd => by rw [narrowOps_writes _ _ _ ho _ hd]; omega),
      narrowOps_value h64w, m5]
    exact narrow_neg h64w hxv
  have hny : Holds ((runOps (runOps M1 (narrowOps w (n + 5))) (narrowOps w (n + 6))).slots (n + 6)) (-y) := by
    show BitVec.toNat _ = _
    rw [narrowOps_value h64w, runOps_slot_other (narrowOps_pure _ _) (fun o ho d hd => by rw [narrowOps_writes _ _ _ ho _ hd]; omega),
      m6]
    exact narrow_neg h64w hyv
  have hframe : ∀ i, i ≠ n + 5 → i ≠ n + 6 →
      (runOps (runOps M1 (narrowOps w (n + 5))) (narrowOps w (n + 6))).slots i = M1.slots i := by
    intro i h5 h6
    rw [runOps_slot_other (narrowOps_pure _ _) (fun o ho d hd => by rw [narrowOps_writes _ _ _ ho _ hd]; exact fun e => h6 e.symm),
      runOps_slot_other (narrowOps_pure _ _) (fun o ho d hd => by rw [narrowOps_writes _ _ _ ho _ hd]; exact fun e => h5 e.symm)]
  generalize runOps (runOps M1 (narrowOps w (n + 5))) (narrowOps w (n + 6)) = M3 at *
  have hls : M3.slots (n + 3) ≠ 0 ↔ x.msb = true := by
    rw [hframe _ (by omega) (by omega), m3]
    exact slt_zero_ne x h64w
  have hrs : M3.slots (n + 4) ≠ 0 ↔ y.msb = true := by
    rw [hframe _ (by omega) (by omega), m4]
    exact slt_zero_ne y h64w
  have hxh3 : Holds (M3.slots L) x := by rw [Holds, hframe L (hLk 5) (hLk 6)]; exact hxh
  have hyh3 : Holds (M3.slots R) y := by rw [Holds, hframe R (hRk 5) (hRk 6)]; exact hyh
  have key := smod_tail h64w hls hrs hnx hny hxh3 hyh3
  have hz3 : M3.slots n = 0 := by
    rw [hframe _ (by omega) (by omega), m0]
  simp only [runOps_cons, runOps_nil, step, Machine.write_slots, Nat.add_left_cancel_iff, Nat.reduceEqDiff, hRk,
    Nat.left_eq_add, hz3, reduceCtorEq, Nat.reduceEqDiff, ite_true, ite_false]
  exact key

/-- Lowering of expressions is correct: the operations appended for an expression leave its value, in the
width of the operand and extended with zeros, in the slot of the operand, whenever the interpreter has a value
for it, and they only write fresh slots. This covers every operator, narrow widths, sign extensions, division
by zero, and `smod`. -/
theorem lowerExp_correct (exp : Bil.Exp) : ∀ {first second : Lowering} {operand : Operand}, LayoutWF first →
    lowerExp first exp = some (second, operand) → Lowered first second operand exp := by
  induction exp with
  | int value => exact fun wf h => lowered_int wf h
  | var var => exact fun wf h => lowered_var wf h
  | load memory address endian size ih₁ ih₂ =>
    intro first second operand wf h
    cases memory
    case var var => exact lowered_load wf ih₂ h
    all_goals (rw [lowerExp] at h; simp at h; all_goals (intros; simp_all))
  | store memory address value endian size _ _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | bin op left right ihl ihr =>
    intro first second operand wf h
    cases op
    case smod => exact lowered_smod wf ihl ihr h
    case ashift => exact lowered_ashift wf ihl ihr h
    all_goals exact lowered_binary (by simp) (by simp) wf ihl ihr h
  | un op value ih => exact fun wf h => lowered_un wf ih h
  | cast kind target value ih =>
    intro first second operand wf h
    cases kind
    case low => exact lowered_cast_zero (Or.inl rfl) wf ih h
    case unsigned => exact lowered_cast_zero (Or.inr rfl) wf ih h
    case signed => exact lowered_cast_signed wf ih h
    case high => exact lowered_cast_high wf ih h
  | letIn var value body _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | ite condition yes no ihc ihy ihn => exact fun wf h => lowered_ite wf ihc ihy ihn h
  | extract high low value ih => exact fun wf h => lowered_extract wf ih h
  | concat left right _ _ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)
  | unknown message typ =>
    intro first second operand wf h
    rw [lowerExp] at h
    · simp at h
    all_goals (intros; simp_all)

/-! ### Lowering of statements

`move` and `jmp`, whose operations run in a line, and what the fixes of the control flow give. -/

private theorem writeVar_inv {first second : Lowering} {var : Bap.Var} {index : Nat} (h : writeVar first var = some (second, index)) :
    index = (slot first var).2 ∧ Lowering.ops second = Lowering.ops first ∧
      Lowering.nextSlot second = Lowering.nextSlot (slot first var).1 ∧
      Lowering.layout second = Lowering.layout (slot first var).1 ∧
      Lowering.memory second = Lowering.memory first := by
  cases hw : widthOf var with
  | none => simp [writeVar, hw] at h
  | some width =>
    simp only [writeVar, hw, bind, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨f1, f2, _⟩ := slot_fields first var
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, f1, rfl, rfl, f2⟩

private theorem pairwise_same {α β : Type} {items : List α} {f : α → β}
    (h : items.Pairwise fun left right => f left ≠ f right) {a b : α} (ha : a ∈ items) (hb : b ∈ items)
    (he : f a = f b) : a = b := by
  induction items with
  | nil => simp at ha
  | cons head rest ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd he (h1 _ hb')
    · exact absurd he.symm (h1 _ ha')
    · exact ih h2 ha' hb'

private theorem lookup_bind_other {env : Bil.Env} {var other : Bap.Var} {value : Bap.Value} (h : other ≠ var) :
    Bil.lookup (Bil.bind env var value) other = Bil.lookup env other := by
  have hbe : ∀ a b : Bap.Var, (a == b) = decide (a = b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · have : (a == b) = false := by
        cases he : (a == b)
        · rfl
        · exact absurd (eq_of_beq he) hab
      simp [hab, this]
  simp only [Bil.lookup, Bil.bind, List.find?_cons]
  have hne : (var == other) = false := by simp [hbe, Ne.symm h]
  simp only [hne]
  have hfilter : ∀ items : List (Bap.Var × Bap.Value), (items.filter fun binding => binding.1 != var).find? (fun binding => binding.1 == other) =
      items.find? fun binding => binding.1 == other := by
    intro items
    induction items with
    | nil => rfl
    | cons head rest ih =>
      by_cases hv : head.1 = var
      · have h1 : (head.1 != var) = false := by simp [hv]
        have h2 : (head.1 == other) = false := by simp [hbe, hv, Ne.symm h]
        simp [h1, h2, ih]
      · have h1 : (head.1 != var) = true := by simp [hv]
        simp only [List.filter_cons, h1, ↓reduceIte, List.find?_cons, ih]
  rw [hfilter]

private theorem lookup_bind_same (env : Bil.Env) (var : Bap.Var) (value : Bap.Value) :
    Bil.lookup (Bil.bind env var value) var = .ok value := by
  simp [Bil.lookup, Bil.bind]

/-- A move to a register, after running its operations: the slot of the register holds the value of the
expression, and the machine holds the environment with the register bound to it. -/
theorem lowerMove_register {first second : Lowering} {dst : Bap.Var} {value : Bil.Exp} {width : Nat} (wf : LayoutWF first)
    (hw : widthOf dst = some width) (h : lowerMove first dst value = some second) :
    ∃ new, Lowering.ops second = Lowering.ops first ++ new ∧
      ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout second) →
        MemoryAgrees env machine second → ∀ (bits : BitVec width), Bil.evalExp env value = .ok (.bits bits) →
        SlotsAgree (Bil.bind env dst (.bits bits)) (runOps machine new) (Lowering.layout second) := by
  have htyp := (widthOf_some_iff dst width).1 hw
  rw [lowerMove] at h
  · obtain ⟨width', hw', h⟩ := obind h
    rw [hw] at hw'
    simp only [Option.some.injEq] at hw'
    subst hw'
    obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
    obtain ⟨newE, he, hslot, h0, h64, hval⟩ := lowerExp_correct value wf h1
    have wfm := he.wf wf
    have hwidth : Operand.width operand = width := by
      by_cases hc : Operand.width operand = width
      · exact hc
      · simp [hc] at h
    simp only [hwidth, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨⟨after, index⟩, h2, h⟩ := obind h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hindex, hops, hnext, hlayout, hmemory⟩ := writeVar_inv h2
    subst hindex
    have hext := slot_extends wfm dst
    have hwfs := slot_preserves_wf wfm dst
    have hin : ∀ b ∈ Lowering.layout mid, b ∈ Lowering.layout (slot mid dst).1 := fun b hb => slot_layout_mono mid dst b hb
    refine ⟨newE ++ [.move (slot mid dst).2 (Operand.slot operand)], ?_, ?_⟩
    · show Lowering.ops after ++ _ = _
      rw [hops, he.ops, List.append_assoc]
    · intro env machine hs hm bits hev
      have hs' : SlotsAgree env machine (Lowering.layout (slot mid dst).1) := hlayout ▸ hs
      have hsmid : SlotsAgree env machine (Lowering.layout mid) := hs'.mono hin
      have hmmid : MemoryAgrees env machine mid := by
        intro var hv
        exact hm var (by show Lowering.memory after = _; rw [hmemory]; exact hv)
      obtain ⟨_, hvalue⟩ := hval env machine hsmid hmmid _ _ hev
      have hdst : (dst, (slot mid dst).2) ∈ Lowering.layout (slot mid dst).1 := slot_mem_layout mid dst
      intro binding hb val hlookup
      have hb' : binding ∈ Lowering.layout (slot mid dst).1 := hlayout ▸ hb
      rw [runOps_append]
      by_cases hbd : binding.1 = dst
      · have hsame : binding = (dst, (slot mid dst).2) := pairwise_same hwfs.varsDistinct hb' hdst hbd
        subst hsame
        rw [lookup_bind_same] at hlookup
        simp only [Except.ok.injEq] at hlookup
        subst hlookup
        refine ⟨width, bits, rfl, hw, ?_⟩
        simp only [runOps_cons, runOps_nil, step, Machine.markMove_slots, ↓reduceIte]
        exact hvalue
      · rw [lookup_bind_other hbd] at hlookup
        obtain ⟨w, x, hv, hwb, hholds⟩ := hs' _ hb' _ hlookup
        refine ⟨w, x, hv, hwb, ?_⟩
        have hne : binding.2 ≠ (slot mid dst).2 := by
          intro e
          exact hbd (congrArg Prod.fst (pairwise_same hwfs.slotsDistinct hb' hdst e))
        simp only [runOps_cons, runOps_nil, step, Machine.markMove_slots, hne, ↓reduceIte]
        have hframe : (runOps machine newE).slots binding.2 = machine.slots binding.2 := by
          apply he.frame
          obtain ⟨extra, hx, hxs⟩ := hext.extra
          rw [hx] at hb'
          rcases List.mem_append.1 hb' with hm' | hm'
          · exact Or.inr (Or.inr ⟨binding.1, hm'⟩)
          · exact Or.inr (Or.inl (hxs _ hm').1)
        rw [Holds, hframe]
        exact hholds
  all_goals (intros; simp_all)

/-- A jump to a computed target: the operations end by returning the slot that holds the value of the target. -/
theorem lowerStmt_jump {first second : Lowering} {target : Bil.Exp} {terminated : Bool} (wf : LayoutWF first)
    (hnot : ∀ (width : Nat) (value : BitVec width), target ≠ .int value)
    (h : lowerStmt first (.jmp target) = some (second, terminated)) :
    terminated = true ∧ ∃ (mid : Lowering) (operand : Operand) (new : List Jit.Op), Extends first mid new ∧
      (Lowering.ops second).getLast? = some (.jumpSlot (Operand.slot operand)) ∧
      ∀ (env : Bil.Env) (machine : Machine), SlotsAgree env machine (Lowering.layout mid) → MemoryAgrees env machine mid →
        ∀ (width : Nat) (bits : BitVec width), Bil.evalExp env target = .ok (.bits bits) →
          Holds ((runOps machine new).slots (Operand.slot operand)) bits := by
  rw [lowerStmt] at h
  · obtain ⟨⟨mid, operand⟩, h1, h⟩ := obind h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨new, he, _, _, _, hval⟩ := lowerExp_correct target wf h1
    refine ⟨rfl, mid, operand, new, he, ?_, fun env machine hs hm width bits hev => (hval env machine hs hm width bits hev).2⟩
    simp [jumpSlot]
  · intro width value he
    exact hnot width value he

/-- A constant jump target fits a slot. -/
theorem lowerStmt_jump_constant {first second : Lowering} {width : Nat} {target : BitVec width} {terminated : Bool}
    (h : lowerStmt first (.jmp (.int target)) = some (second, terminated)) :
    width ≤ 64 ∧ terminated = true ∧
      (Lowering.ops second).getLast? = some (.jump (UInt64.ofNat target.toNat)) := by
  rw [lowerStmt] at h
  split at h
  · next hw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hw, rfl, by simp [jumpConstant]; rfl⟩
  · simp at h

/-! What the lowering of control flow is built to keep. -/

/-- A load only reads a memory of bytes through an address of its width. -/
theorem lowerExp_load_address {first second : Lowering} {operand : Operand} {var : Bap.Var} {address : Bil.Exp}
    {endian : Endian} {size : Nat} (h : lowerExp first (.load (.var var) address endian size) = some (second, operand)) :
    ∃ width, var.typ = .mem width 8 ∧ 1 ≤ size ∧ size ≤ 8 := by
  rw [lowerExp] at h
  obtain ⟨v0, hv0, h⟩ := obind h
  simp only [Option.some.injEq] at hv0
  subst hv0
  obtain ⟨l0, h0, h⟩ := obind h
  have h0 := useMemoryAt_some h0
  obtain ⟨⟨l1, o1⟩, _, h⟩ := obind h
  have hc : ¬ (size = 0 ∨ size > 8) := by
    intro hc
    have : (decide (size = 0) || decide (size > 8) || !addressOf var (Operand.width o1)) = true := by
      rcases hc with hc | hc <;> simp [hc]
    simp [this] at h
  have hmem : ∃ width, var.typ = Bap.Typ.mem width 8 := by
    cases hty : var.typ with
    | mem a c =>
      by_cases hc : c = 8
      · exact ⟨a, by rw [hc]⟩
      · exfalso
        unfold useMemory at h0
        rw [hty] at h0
        split at h0 <;> simp_all
    | _ =>
      exfalso
      unfold useMemory at h0
      rw [hty] at h0
      simp at h0
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw, by omega, by omega⟩

/-- An `ite` lowered to a native select has alternatives without loads, which a select evaluates both. -/
theorem lowerExp_ite_pure {first second : Lowering} {operand : Operand} {condition yes no : Bil.Exp}
    (h : lowerExp first (.ite condition yes no) = some (second, operand)) :
    readsMemory yes = false ∧ readsMemory no = false := by
  rw [lowerExp] at h
  cases hy : readsMemory yes <;> cases hn : readsMemory no <;> simp [hy, hn] at h ⊢

/-- A loop continues with the next statement: it is not terminated, and its operations end with the label that
the failed condition goes to. -/
theorem lowerStmt_while_continues {first second : Lowering} {condition : Bil.Exp} {body : Bil.Program} {terminated : Bool}
    (h : lowerStmt first (.while condition body) = some (second, terminated)) :
    terminated = false ∧ (Lowering.ops second).getLast? = some (.label (Lowering.nextLabel first + 3)) := by
  rw [lowerStmt] at h
  simp only [temporary] at h
  obtain ⟨⟨l1, o1⟩, _, h⟩ := obind h
  have hw : Operand.width o1 = 1 := by
    by_cases hc : Operand.width o1 = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨l2, t⟩, _, h⟩ := obind h
  split at h
  · simp at h
  · simp only [setEffect] at h
    split at h <;> simp only [temporary, Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

/-- A conditional keeps what its else branch allocated, also when only that branch jumps: the slots, the inputs it
reads, and the labels stay in the result. -/
theorem lowerStmt_ifElse_keeps {first second : Lowering} {condition : Bil.Exp} {yes no : Bil.Program} {terminated : Bool}
    (h : lowerStmt first (.ifElse condition yes no) = some (second, terminated)) :
    ∃ start mid noTerminated, lowerStatements start no = some (mid, noTerminated) ∧
      Lowering.layout second = Lowering.layout mid ∧ Lowering.nextSlot second = Lowering.nextSlot mid ∧
      Lowering.nextLabel second = Lowering.nextLabel mid ∧ Lowering.inputs second = Lowering.inputs mid := by
  rw [lowerStmt] at h
  obtain ⟨⟨l1, o1⟩, _, h⟩ := obind h
  have hw : Operand.width o1 = 1 := by
    by_cases hc : Operand.width o1 = 1
    · exact hc
    · simp [hc] at h
  simp only [hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨l2, t⟩, _, h⟩ := obind h
  obtain ⟨⟨l3, t2⟩, h3, h⟩ := obind h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, l3, t2, h3, rfl, rfl, rfl, rfl⟩


end Lifted

end Bap.Proofs.Primus
