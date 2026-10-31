import Lean
import Bap.Emu.Checkpoint
import Bap.Emu.Diff
import Bap.Emu.Shell
import Bap.Emu.Project
import Bap.Emu.Jni
import Std.Data.String.ToNat

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Emu

open Bap.Emu

/-! ### Sparse memory cells -/

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

/-! ### Regions -/

section Regions

open_private Bap.Emu Bap.Emu overlaps lookupRegion memoryWidth initializeMemory syscallRegisters callAbi mipsWord
  mipsDelayed mipsLikely mipsCompact

theorem region_contains_iff (region : Bap.Emu.Region) (address : Nat) :
    region.contains address = true ↔
      region.address ≤ address ∧ address < region.address + region.data.size := by
  simp [Bap.Emu.Region.contains]

theorem region_empty_contains (region : Bap.Emu.Region) (h : region.data.size = 0) (address : Nat) :
    region.contains address = false := by
  simp only [Bap.Emu.Region.contains, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem overlaps_comm (left right : Bap.Emu.Region) : overlaps left right = overlaps right left := by
  simp only [overlaps, Bool.and_comm]

/-- The overlap check rejects exactly regions that share a byte, when both are nonempty. -/
theorem overlaps_iff_shared_byte (left right : Bap.Emu.Region) (hl : 0 < left.data.size) (hr : 0 < right.data.size) :
    overlaps left right = true ↔ ∃ address, left.contains address = true ∧ right.contains address = true := by
  simp only [overlaps, Bool.and_eq_true, decide_eq_true_eq, region_contains_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨max left.address right.address, by omega, by omega⟩
  · rintro ⟨a, h1, h2⟩
    omega

/-- Non-overlapping regions share no byte, even if one is empty. -/
theorem no_overlap_disjoint (left right : Bap.Emu.Region) (h : overlaps left right = false) (address : Nat) :
    ¬ (left.contains address = true ∧ right.contains address = true) := by
  simp only [overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  simp only [region_contains_iff]
  omega

theorem lookupRegion_sound {regions : List Bap.Emu.Region} {address : Nat} {region : Bap.Emu.Region}
    (h : lookupRegion regions address = some region) : region ∈ regions ∧ region.contains address = true :=
  have h' : regions.find? (fun region => region.contains address) = some region := h
  have hc := List.find?_some h'
  ⟨List.mem_of_find?_eq_some h', hc⟩

theorem lookupRegion_none_iff (regions : List Bap.Emu.Region) (address : Nat) :
    lookupRegion regions address = none ↔ ∀ region ∈ regions, region.contains address = false := by
  simp [lookupRegion]

/-- In a disjoint table a region is found for each of its addresses. -/
theorem lookupRegion_disjoint {regions : List Bap.Emu.Region} {address : Nat} {region : Bap.Emu.Region}
    (hd : regions.Pairwise fun l r => ∀ a, ¬ (l.contains a = true ∧ r.contains a = true))
    (hm : region ∈ regions) (hc : region.contains address = true) :
    lookupRegion regions address = some region := by
  simp only [lookupRegion]
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

theorem memoryWidth_ok_iff (config : Config) (width : Nat) :
    memoryWidth config = .ok width ↔ config.memory.typ = .mem width 8 := by
  simp only [memoryWidth]
  split
  · rename_i w hw
    simp [hw]
  · rename_i hn
    simp only [reduceCtorEq, false_iff]
    exact hn width

/-- Region tables with an overlapping pair are refused at construction. -/
theorem initializeMemory_rejects_overlap (config : Config) (regions : List Bap.Emu.Region)
    (left right : Bap.Emu.Region) (hl : left ∈ regions) (hr : right ∈ regions) (hne : left ≠ right)
    (ho : overlaps left right = true) : ∃ e, initializeMemory config regions = .error e := by
  have hany : (regions.any fun left => regions.any fun right => left != right && overlaps left right) = true := by
    refine List.any_eq_true.2 ⟨left, hl, List.any_eq_true.2 ⟨right, hr, ?_⟩⟩
    simp [hne, ho]
  simp only [initializeMemory, bind, Except.bind]
  cases memoryWidth config with
  | error e => exact ⟨e, rfl⟩
  | ok w => simp [hany, throw, throwThe, MonadExceptOf.throw]

/-! ABI tables and MIPS delay-slot decoding. -/

theorem syscallRegisters_six_arguments (abi : SyscallAbi) : (syscallRegisters abi).2.1.length = 6 := by
  cases abi <;> rfl

theorem syscallRegisters_arguments_distinct (abi : SyscallAbi) : (syscallRegisters abi).2.1.Nodup := by
  cases abi <;> decide

/-- The syscall number register never doubles as an argument register. -/
theorem syscallRegisters_number_not_argument (abi : SyscallAbi) :
    (syscallRegisters abi).1 ∉ (syscallRegisters abi).2.1 := by
  cases abi <;> decide

theorem callAbi_arguments_distinct (abi : SyscallAbi) : (callAbi abi).1.Nodup := by
  cases abi <;> decide

/-- Only x86-64 passes the return address on the stack. -/
theorem callAbi_stack_return_iff (abi : SyscallAbi) : (callAbi abi).2.2.2 = true ↔ abi = .x86_64 := by
  cases abi <;> simp [callAbi]

theorem mipsWord_none_iff (code : ByteArray) (address : Nat) :
    mipsWord code address = none ↔ address + 4 > code.size := by
  simp only [mipsWord]
  split <;> simp_all

/-- A decoded instruction word is big-endian. -/
theorem mipsWord_value {code : ByteArray} {address word : Nat} (h : mipsWord code address = some word) :
    word = code[address]!.toNat * 2 ^ 24 + code[address + 1]!.toNat * 2 ^ 16 +
      code[address + 2]!.toNat * 2 ^ 8 + code[address + 3]!.toNat := by
  simp only [mipsWord] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [List.range, List.range.loop]
    omega

theorem mipsWord_bound {code : ByteArray} {address word : Nat} (h : mipsWord code address = some word) :
    word < 2 ^ 32 := by
  have hv := mipsWord_value h
  have h0 := (code[address]!).toNat_lt
  have h1 := (code[address + 1]!).toNat_lt
  have h2 := (code[address + 2]!).toNat_lt
  have h3 := (code[address + 3]!).toNat_lt
  omega

/-- A branch-likely instruction always has a delay slot. -/
theorem mipsLikely_implies_delayed (release6 : Bool) (word : Nat) (h : mipsLikely release6 word = true) :
    mipsDelayed release6 word = true := by
  simp only [mipsLikely, mipsDelayed] at h ⊢
  generalize (word / 2 ^ 26) % 64 = op at h ⊢
  generalize (word / 2 ^ 21) % 32 = rs at h ⊢
  generalize (word / 2 ^ 16) % 32 = rt at h ⊢
  cases release6 with
  | true => simp at h
  | false =>
    simp only [Bool.not_false, Bool.true_and] at h
    split at h
    · simp
    · simp
    · simp
    · simp
    · simp at h ⊢
      omega
    · simp at h ⊢
      omega
    · simp at h

/-- Release 6 removed branch-likely encodings. -/
theorem mipsLikely_release6 (word : Nat) : mipsLikely true word = false := by
  simp [mipsLikely]

/-- On Release 6 an instruction with a forbidden slot never also has a delay slot. -/
theorem mipsCompact_not_delayed (word : Nat) (h : mipsCompact word = true) : mipsDelayed true word = false := by
  simp only [mipsCompact, mipsDelayed] at h ⊢
  generalize (word / 2 ^ 26) % 64 = op at h ⊢
  generalize (word / 2 ^ 21) % 32 = rs at h ⊢
  generalize (word / 2 ^ 16) % 32 = rt at h ⊢
  split at h <;> simp_all

/-- Jumps and register jumps always have delay slots, on every release. -/
theorem mipsDelayed_jump (release6 : Bool) (word : Nat) (h : (word / 2 ^ 26) % 64 = 0x02 ∨ (word / 2 ^ 26) % 64 = 0x03) :
    mipsDelayed release6 word = true := by
  simp only [mipsDelayed]
  generalize (word / 2 ^ 26) % 64 = op at h ⊢
  rcases h with rfl | rfl <;> rfl

end Regions

/-! ### Address space, protection and fetch -/

section Audit

open_private Bap.Emu Bap.Emu overlaps lookupRegion memoryWidth initializeMemory regionPiece persistentRegionData
  coversRange.loop fetchSpan.extend

/-- A region past the end of the address space is refused at construction. -/
theorem initializeMemory_rejects_out_of_space (config : Config) (regions : List Bap.Emu.Region)
    (region : Bap.Emu.Region) (width : Nat) (hw : memoryWidth config = .ok width) (hr : region ∈ regions)
    (hs : regionInSpace width region = false) : ∃ e, initializeMemory config regions = .error e := by
  have hall : regions.all (regionInSpace width) = false :=
    List.all_eq_false.2 ⟨region, hr, by simp [hs]⟩
  simp only [initializeMemory, hw, bind, Except.bind]
  split
  · exact ⟨_, rfl⟩
  · simp [hall, pure, Except.pure]

/-- Every address of a region accepted by the check is representable in `width` bits, so none aliases. -/
theorem regionInSpace_contains {width : Nat} {region : Bap.Emu.Region} (h : regionInSpace width region = true)
    {address : Nat} (hc : region.contains address = true) : address < 2 ^ width := by
  have hb : region.address + region.data.size ≤ 2 ^ width := by simpa [regionInSpace] using h
  have := ((region_contains_iff _ _).1 hc).2
  omega

/-- An accepted overlay only ever replaces a same-sized region at its own address. -/
theorem overlayConflict_false {mapped : List Bap.Emu.Region} {region current : Bap.Emu.Region}
    (h : overlayConflict mapped region = false) (hm : current ∈ mapped) :
    (current.address = region.address ∧ current.data.size = region.data.size) ∨
      (current.address ≠ region.address ∧ overlaps current region = false) := by
  have := List.any_eq_false.1 h current hm
  by_cases he : current.address = region.address
  · simp only [he, ↓reduceIte, bne_iff_ne, ne_eq, Decidable.not_not, Bool.not_eq_true] at this
    exact Or.inl ⟨he, by simpa using this⟩
  · simp only [he, ↓reduceIte, Bool.not_eq_true] at this
    exact Or.inr ⟨he, this⟩

/-- An access touches a range iff one of its bytes lies in the range; a straddling access counts. -/
theorem accessTouches_iff (first last address size : Nat) (hr : first ≤ last) :
    accessTouches first last address size = true ↔
      ∃ byte, address ≤ byte ∧ byte < address + max size 1 ∧ first ≤ byte ∧ byte ≤ last := by
  simp only [accessTouches, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨max first address, by omega, by omega, by omega, by omega⟩
  · rintro ⟨b, h1, h2, h3, h4⟩
    exact ⟨by omega, by omega⟩

theorem stackAfterPush_of_room (sp : Nat) (h : 8 ≤ sp) (hb : sp < 2 ^ 64) : stackAfterPush sp = sp - 8 := by
  simp only [stackAfterPush]
  rw [show sp + 2 ^ 64 - 8 = (sp - 8) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Pushing near zero wraps like the hardware instead of sticking at zero. -/
theorem stackAfterPush_wraps (sp : Nat) (h : sp < 8) : stackAfterPush sp = 2 ^ 64 + sp - 8 := by
  simp only [stackAfterPush]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem joinWorkers_all_ok {ε : Type} (steps : List Nat) :
    joinWorkers (steps.map (.ok : Nat → Except ε Nat)) = .ok steps.sum := by
  induction steps with
  | nil => rfl
  | cons head rest ih => simp [joinWorkers, ih]

/-- A failed worker fails the round with the error of the first failure in thread order. -/
theorem joinWorkers_first_error {ε : Type} (steps : List Nat) (error : ε) (rest : List (Except ε Nat)) :
    joinWorkers (steps.map (.ok : Nat → Except ε Nat) ++ .error error :: rest) = .error error := by
  induction steps with
  | nil => rfl
  | cons head tail ih => simp [joinWorkers, ih]

/-- Rebuilding a region from a memory dump always yields a region of the same size. -/
theorem persistentRegionData_size (cells : List (Nat × UInt8)) (address size : Nat) (output : Array UInt8)
    (h : output.size ≤ size) : (persistentRegionData cells address size output).size = size := by
  induction hm : cells.length + (size - output.size) using Nat.strongRecOn generalizing cells output with
  | ind measure ih =>
    rw [persistentRegionData]
    by_cases hg : output.size ≥ size
    · simp only [hg, ↓reduceDIte]
      omega
    · simp only [hg, ↓reduceDIte]
      cases cells with
      | nil =>
        simp only [Array.size_append, Array.size_replicate]
        omega
      | cons cell rest =>
        obtain ⟨current, value⟩ := cell
        simp only [List.length_cons] at hm
        simp only
        split
        · exact ih _ (by omega) _ _ h rfl
        · split
          · exact ih _ (by simp only [Array.size_push]; omega) _ _ (by simp only [Array.size_push]; omega) rfl
          · exact ih _ (by simp only [List.length_cons, Array.size_push]; omega) _ _
              (by simp only [Array.size_push]; omega) rfl

/-! `mprotect` splitting. -/

private theorem piece_mem {region piece : Bap.Emu.Region} {first last : Nat} {p : Primus.Protection}
    (h : piece ∈ regionPiece region first last p) :
    first < last ∧ piece = ⟨first, region.data.extract (first - region.address) (last - region.address), p⟩ := by
  simp only [regionPiece] at h
  split at h
  · exact ⟨by assumption, by simpa using h⟩
  · simp at h

/-- A piece holds the same bytes as the region it was cut from. -/
private theorem piece_contains {region piece : Bap.Emu.Region} {first last address : Nat} {p : Primus.Protection}
    (h : piece ∈ regionPiece region first last p) (hl : region.address ≤ first)
    (hu : last ≤ region.address + region.data.size) (hc : piece.contains address = true) :
    first ≤ address ∧ address < last ∧ piece.protection = p ∧
      piece.data[address - piece.address]? = region.data[address - region.address]? := by
  obtain ⟨hlt, rfl⟩ := piece_mem h
  generalize hd : region.data.extract (first - region.address) (last - region.address) = data at hc
  have hsize : data.size = last - first := by
    rw [← hd, ByteArray.size_extract]
    omega
  obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
  have h1' : first ≤ address := h1
  have h2' : address < first + data.size := h2
  refine ⟨h1', by omega, rfl, ?_⟩
  subst hd
  have hi : address - first < (region.data.extract (first - region.address) (last - region.address)).size := by
    omega
  have hj : address - region.address < region.data.size := by omega
  show (region.data.extract (first - region.address) (last - region.address))[address - first]? = _
  rw [getElem?_pos (region.data.extract (first - region.address) (last - region.address)) _ hi,
    getElem?_pos region.data _ hj, ByteArray.getElem_extract]
  simp only [Option.some.injEq]
  congr 1
  omega

private theorem piece_has {region : Bap.Emu.Region} {first last address : Nat} {p : Primus.Protection}
    (hl : region.address ≤ first) (hu : last ≤ region.address + region.data.size) (h1 : first ≤ address) (h2 : address < last) :
    ∃ piece ∈ regionPiece region first last p, piece.contains address = true := by
  have hlt : first < last := Nat.lt_of_le_of_lt h1 h2
  refine ⟨⟨first, region.data.extract (first - region.address) (last - region.address), p⟩, ?_, ?_⟩
  · simp [regionPiece, hlt]
  · refine (region_contains_iff _ _).2 ⟨h1, ?_⟩
    show address < first + (region.data.extract _ _).size
    rw [ByteArray.size_extract]
    omega

private theorem split_spec (lower upper : Nat) (p : Primus.Protection) (region : Bap.Emu.Region) (address : Nat) :
    (∀ piece ∈ splitRegion lower upper p region, piece.contains address = true →
        region.contains address = true ∧ piece.protection = (if lower ≤ address ∧ address < upper then p else region.protection) ∧
        piece.data[address - piece.address]? = region.data[address - region.address]?) ∧
      (region.contains address = true → ∃ piece ∈ splitRegion lower upper p region, piece.contains address = true) := by
  simp only [splitRegion]
  by_cases hempty : min upper (region.address + region.data.size) ≤ max lower region.address
  · simp only [hempty, ↓reduceIte, List.mem_singleton, forall_eq]
    refine ⟨fun hc => ?_, fun hc => ⟨region, by simp, hc⟩⟩
    obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
    refine ⟨hc, ?_, trivial⟩
    have : ¬ (lower ≤ address ∧ address < upper) := by omega
    simp [this]
  · simp only [hempty, ↓reduceIte]
    by_cases hwhole : (max lower region.address = region.address ∧
        min upper (region.address + region.data.size) = region.address + region.data.size)
    · have hb : (decide (max lower region.address = region.address) &&
          decide (min upper (region.address + region.data.size) = region.address + region.data.size)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact hwhole
      simp only [hb, ↓reduceIte, List.mem_singleton, forall_eq]
      have hsame : ({ region with protection := p } : Bap.Emu.Region).contains address = region.contains address := rfl
      refine ⟨fun hc => ?_, fun hc => ⟨{ region with protection := p }, rfl, by rwa [hsame]⟩⟩
      rw [hsame] at hc
      obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
      have : lower ≤ address ∧ address < upper := by omega
      exact ⟨hc, by simp [this], trivial⟩
    · have hb : (decide (max lower region.address = region.address) &&
          decide (min upper (region.address + region.data.size) = region.address + region.data.size)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro piece hp hc
        simp only [List.mem_append] at hp
        rcases hp with (hp | hp) | hp
        · obtain ⟨h1, h2, h3, h4⟩ := piece_contains hp (by omega) (by omega) hc
          refine ⟨(region_contains_iff _ _).2 ⟨h1, by omega⟩, ?_, h4⟩
          have : ¬ (lower ≤ address ∧ address < upper) := by omega
          simp [this, h3]
        · obtain ⟨h1, h2, h3, h4⟩ := piece_contains hp (by omega) (by omega) hc
          refine ⟨(region_contains_iff _ _).2 ⟨by omega, by omega⟩, ?_, h4⟩
          have : lower ≤ address ∧ address < upper := by omega
          simp [this, h3]
        · obtain ⟨h1, h2, h3, h4⟩ := piece_contains hp (by omega) (Nat.le_refl _) hc
          refine ⟨(region_contains_iff _ _).2 ⟨by omega, by omega⟩, ?_, h4⟩
          have : ¬ (lower ≤ address ∧ address < upper) := by omega
          simp [this, h3]
      · intro hc
        obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
        by_cases hs : address < max lower region.address
        · obtain ⟨q, hq, hqc⟩ := piece_has (p := region.protection) (region := region) (first := region.address)
            (last := max lower region.address) (Nat.le_refl _) (by omega) h1 hs
          exact ⟨q, by simp only [List.mem_append]; exact Or.inl (Or.inl hq), hqc⟩
        · by_cases ht : address < min upper (region.address + region.data.size)
          · obtain ⟨q, hq, hqc⟩ := piece_has (p := p) (region := region) (first := max lower region.address)
              (last := min upper (region.address + region.data.size)) (by omega) (by omega) (by omega) ht
            exact ⟨q, by simp only [List.mem_append]; exact Or.inl (Or.inr hq), hqc⟩
          · obtain ⟨q, hq, hqc⟩ := piece_has (p := region.protection) (region := region)
              (first := min upper (region.address + region.data.size)) (last := region.address + region.data.size)
              (by omega) (Nat.le_refl _) (by omega) h2
            exact ⟨q, by simp only [List.mem_append]; exact Or.inr hq, hqc⟩

private theorem lookup_flatMap (lower upper : Nat) (p : Primus.Protection) (regions : List Bap.Emu.Region) (address : Nat) :
    lookupRegion (regions.flatMap (splitRegion lower upper p)) address =
      (lookupRegion regions address).bind fun region => lookupRegion (splitRegion lower upper p region) address := by
  simp only [lookupRegion]
  induction regions with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.flatMap_cons, List.find?_append, List.find?_cons]
    cases hc : head.contains address with
    | true => 
      obtain ⟨piece, hp, hpc⟩ := (split_spec lower upper p head address).2 hc
      have : (splitRegion lower upper p head).find? (fun region => region.contains address) ≠ none := by
        intro hn
        have := List.find?_eq_none.1 hn piece hp
        simp [hpc] at this
      obtain ⟨found, hf⟩ := Option.ne_none_iff_exists'.1 this
      simp [hf]
    | false =>
      have : (splitRegion lower upper p head).find? (fun region => region.contains address) = none := by
        apply List.find?_eq_none.2
        intro piece hp hpc
        have := ((split_spec lower upper p head address).1 piece hp (by simpa using hpc)).1
        simp [hc] at this
      simp [this, ih]

/-- `protect` is exact: bytes in the range get the new protection, all others keep theirs, every byte keeps
its value, and no address becomes mapped or unmapped. -/
theorem protectRegions_spec {regions result : List Bap.Emu.Region} {address size : Nat} {p : Primus.Protection}
    (h : protectRegions regions address size p = some result) (query : Nat) :
    match lookupRegion regions query with
    | none => lookupRegion result query = none
    | some region =>
      ∃ piece, lookupRegion result query = some piece ∧
        piece.protection = (if address ≤ query ∧ query < address + size then p else region.protection) ∧
        piece.data[query - piece.address]? = region.data[query - region.address]? := by
  simp only [protectRegions] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [lookup_flatMap]
    cases hl : lookupRegion regions query with
    | none => rfl
    | some region =>
      obtain ⟨_, hc⟩ := lookupRegion_sound hl
      simp only [Option.bind_some]
      obtain ⟨hall, hex⟩ := split_spec address (address + size) p region query
      obtain ⟨piece, hp, hpc⟩ := hex hc
      have : (splitRegion address (address + size) p region).find? (fun r => r.contains query) ≠ none := by
        intro hn
        have := List.find?_eq_none.1 hn piece hp
        simp [hpc] at this
      obtain ⟨found, hf⟩ := Option.ne_none_iff_exists'.1 this
      have hfm := List.mem_of_find?_eq_some hf
      have hfc := List.find?_some hf
      obtain ⟨_, h2, h3⟩ := hall found hfm hfc
      exact ⟨found, hf, h2, h3⟩
  · simp at h

private theorem covers_loop {regions : List Bap.Emu.Region} {upper : Nat} {fuel position : Nat}
    (h : coversRange.loop regions upper fuel position = true) (query : Nat) (h1 : position ≤ query) (h2 : query < upper) :
    (lookupRegion regions query).isSome = true := by
  induction fuel generalizing position with
  | zero =>
    unfold coversRange.loop at h
    split at h
    · omega
    · simp at h
  | succ fuel ih =>
    unfold coversRange.loop at h
    split at h
    · omega
    · simp only at h
      split at h
      · rename_i region hl
        obtain ⟨hm, hc⟩ := lookupRegion_sound hl
        by_cases hq : query < region.address + region.data.size
        · have : region.contains query = true := by
            have := (region_contains_iff _ _).1 hc
            exact (region_contains_iff _ _).2 ⟨by omega, hq⟩
          cases hq' : lookupRegion regions query with
          | some _ => rfl
          | none =>
            have := (lookupRegion_none_iff _ _).1 hq' region hm
            simp_all
        · exact ih h (by omega)
      · simp at h

/-- A protected range is entirely mapped: protection never silently skips a hole. -/
theorem protectRegions_covered {regions result : List Bap.Emu.Region} {address size : Nat} {p : Primus.Protection}
    (h : protectRegions regions address size p = some result) (query : Nat) (h1 : address ≤ query)
    (h2 : query < address + size) : (lookupRegion regions query).isSome = true := by
  simp only [protectRegions] at h
  split at h
  · rename_i hc
    exact covers_loop hc query h1 h2
  · simp at h

/-! Instruction fetch. -/

private theorem extend_spec {regions : List Bap.Emu.Region} {address limit : Nat}
    (hd : regions.Pairwise fun l r => ∀ a, ¬ (l.contains a = true ∧ r.contains a = true)) (fuel position : Nat)
    (hp : address ≤ position)
    (hprefix : ∀ a, address ≤ a → a < position →
      ∃ r, lookupRegion regions a = some r ∧ r.protection.executable = true) :
    let span := fetchSpan.extend regions address limit fuel position
    span ≤ limit ∧ min limit (position - address) ≤ span ∧ ∀ offset, offset < span →
      ∃ r, lookupRegion regions (address + offset) = some r ∧ r.protection.executable = true := by
  intro span
  induction fuel generalizing position with
  | zero =>
    simp only [span]
    unfold fetchSpan.extend
    split
    · exact ⟨Nat.le_refl _, by omega, fun o ho => hprefix _ (by omega) (by omega)⟩
    · cases lookupRegion regions position <;> dsimp only <;>
        exact ⟨by omega, by omega, fun o ho => hprefix _ (by omega) (by omega)⟩
  | succ fuel ih =>
    simp only [span]
    unfold fetchSpan.extend
    split
    · exact ⟨Nat.le_refl _, by omega, fun o ho => hprefix _ (by omega) (by omega)⟩
    · cases hl : lookupRegion regions position with
      | none =>
        dsimp only
        exact ⟨by omega, by omega, fun o ho => hprefix _ (by omega) (by omega)⟩
      | some region =>
        dsimp only
        split
        · rename_i hx
          obtain ⟨hm, hc⟩ := lookupRegion_sound hl
          obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
          obtain ⟨r1, r2, r3⟩ := ih (region.address + region.data.size) (by omega) (by
            intro a ha hb
            by_cases hq : a < position
            · exact hprefix a ha hq
            · refine ⟨region, lookupRegion_disjoint hd hm ((region_contains_iff _ _).2 ⟨by omega, hb⟩), hx⟩)
          exact ⟨r1, by omega, r3⟩
        · exact ⟨by omega, by omega, fun o ho => hprefix _ (by omega) (by omega)⟩

/-- Fetch is sound: every fetched byte is in an executable region, whatever its other permissions. -/
theorem fetchSpan_sound {regions : List Bap.Emu.Region} {address limit span : Nat}
    (hd : regions.Pairwise fun l r => ∀ a, ¬ (l.contains a = true ∧ r.contains a = true))
    (h : fetchSpan regions address limit = .ok span) :
    span ≤ limit ∧ ∀ offset, offset < span →
      ∃ r, lookupRegion regions (address + offset) = some r ∧ r.protection.executable = true := by
  simp only [fetchSpan] at h
  split at h
  · simp at h
  · rename_i region hl
    split at h
    · simp at h
    · rename_i hx
      simp only [Except.ok.injEq] at h
      subst h
      have hxe : region.protection.executable = true := by simpa using hx
      obtain ⟨hm, hc⟩ := lookupRegion_sound hl
      obtain ⟨h1, _⟩ := (region_contains_iff _ _).1 hc
      obtain ⟨r1, _, r3⟩ := extend_spec (limit := limit) (address := address) hd regions.length
        (region.address + region.data.size) (by omega) (fun a ha hb =>
          ⟨region, lookupRegion_disjoint hd hm ((region_contains_iff _ _).2 ⟨by omega, hb⟩), hxe⟩)
      exact ⟨r1, r3⟩

/-- Execute permission alone is enough: `readable` plays no part, and the whole window inside the region
is fetched. -/
theorem fetchSpan_executable {regions : List Bap.Emu.Region} {region : Bap.Emu.Region} {address : Nat} (limit : Nat)
    (hd : regions.Pairwise fun l r => ∀ a, ¬ (l.contains a = true ∧ r.contains a = true))
    (hl : lookupRegion regions address = some region) (hx : region.protection.executable = true) :
    ∃ span, fetchSpan regions address limit = .ok span ∧
      min limit (region.address + region.data.size - address) ≤ span := by
  obtain ⟨hm, hc⟩ := lookupRegion_sound hl
  obtain ⟨h1, _⟩ := (region_contains_iff _ _).1 hc
  obtain ⟨_, r2, _⟩ := extend_spec (limit := limit) (address := address) hd regions.length
    (region.address + region.data.size) (by omega) (fun a ha hb =>
      ⟨region, lookupRegion_disjoint hd hm ((region_contains_iff _ _).2 ⟨by omega, hb⟩), hx⟩)
  exact ⟨_, by simp [fetchSpan, hl, hx], r2⟩

/-- A non-executable region is never fetched. -/
theorem fetchSpan_not_executable {regions : List Bap.Emu.Region} {region : Bap.Emu.Region} {address limit : Nat}
    (hl : lookupRegion regions address = some region) (hx : region.protection.executable = false) :
    ∃ e, fetchSpan regions address limit = .error e :=
  ⟨s!"non-executable Emu instruction address {address}", by simp [fetchSpan, hl, hx]⟩

end Audit

/-! ### Memory isolation -/

section Isolation

/-- Combined isolation: threads share an address space iff neither side owns a private one. -/
theorem selectMemory_iff {β : Type} (processes : Std.HashMap Nat β) (current next : Nat) {α : Type}
    (currentMemory targetMemory : α) :
    (processes.contains current = false ∧ processes.contains next = false ∧
        selectMemory processes current next currentMemory targetMemory = currentMemory) ∨
      ((processes.contains current = true ∨ processes.contains next = true) ∧
        selectMemory processes current next currentMemory targetMemory = targetMemory) := by
  cases hc : processes.contains current <;> cases hn : processes.contains next
  · exact Or.inl ⟨rfl, rfl, selectMemory_shared _ _ _ _ _ hc hn⟩
  · exact Or.inr ⟨Or.inr rfl, selectMemory_private_next _ _ _ _ _ hn⟩
  · exact Or.inr ⟨Or.inl rfl, selectMemory_private_current _ _ _ _ _ hc⟩
  · exact Or.inr ⟨Or.inl rfl, selectMemory_private_current _ _ _ _ _ hc⟩

/-- Sharing is an equivalence on threads: transitive and reflexive for threads without private memory. -/
theorem shouldShareMemory_trans {α : Type} (processes : Std.HashMap Nat α) (a b c : Nat)
    (hab : shouldShareMemory processes a b = true) (hbc : shouldShareMemory processes b c = true) :
    shouldShareMemory processes a c = true := by
  simp only [shouldShareMemory, Bool.not_eq_true', Bool.or_eq_false_iff] at *
  exact ⟨hab.1, hbc.2⟩

theorem shouldShareMemory_self {α : Type} (processes : Std.HashMap Nat α) (a : Nat) :
    shouldShareMemory processes a a = !processes.contains a := by
  simp [shouldShareMemory]

/-- After a fork registers a child's memory, the child never runs on the current memory. -/
theorem selectMemory_after_fork {β α : Type} (processes : Std.HashMap Nat β) (child current : Nat) (memory : β)
    (currentMemory targetMemory : α) :
    selectMemory (processes.insert child memory) current child currentMemory targetMemory = targetMemory := by
  apply selectMemory_private_next
  simp

/-- A fork does not disturb a pair of threads that share memory and are unrelated to the child. -/
theorem selectMemory_fork_frame {β α : Type} (processes : Std.HashMap Nat β) (child current next : Nat) (memory : β)
    (currentMemory targetMemory : α) (hc : child ≠ current) (hn : child ≠ next) :
    selectMemory (processes.insert child memory) current next currentMemory targetMemory =
      selectMemory processes current next currentMemory targetMemory := by
  have h1 : (processes.insert child memory).contains current = processes.contains current := by
    simp [Std.HashMap.contains_insert, hc]
  have h2 : (processes.insert child memory).contains next = processes.contains next := by
    simp [Std.HashMap.contains_insert, hn]
  simp [selectMemory, shouldShareMemory, h1, h2]

theorem controlledStopped_insert_same (control : Std.HashMap Nat Bool) (id : Nat) (value fallback : Bool) :
    controlledStopped (control.insert id value) id fallback = value := by
  simp [controlledStopped]

theorem controlledStopped_insert_other (control : Std.HashMap Nat Bool) (id other : Nat) (value fallback : Bool)
    (h : id ≠ other) :
    controlledStopped (control.insert id value) other fallback = controlledStopped control other fallback := by
  simp [controlledStopped, Std.HashMap.getElem?_insert, h]

end Isolation

/-! ### Snapshot diffing -/

section Diff

open_private Bap.Emu.Diff Bap.Emu byteAt coalesce

theorem byteAt_some_iff (regions : List Bap.Emu.Region) (address : Nat) :
    (byteAt regions address).isSome = true ↔ ∃ region ∈ regions, region.contains address = true := by
  simp only [byteAt, bind, Option.bind_eq_bind]
  cases hf : regions.find? (fun region => region.contains address) with
  | none =>
    simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨r, hr, hc⟩
    have := List.find?_eq_none.1 hf r hr
    simp [hc] at this
  | some region =>
    have hc := List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
    have hlt : address - region.address < region.data.size := by omega
    simp only [Option.bind_some]
    have hsome : (region.data[address - region.address]?).isSome = true := by
      rw [getElem?_pos region.data _ hlt]
      rfl
    exact ⟨fun _ => ⟨region, hm, hc⟩, fun _ => hsome⟩

/-- `byteAt` reads the owning region at the right offset. -/
theorem byteAt_region {regions : List Bap.Emu.Region} {region : Bap.Emu.Region} {address : Nat}
    (hd : regions.Pairwise fun l r => ∀ a, ¬ (l.contains a = true ∧ r.contains a = true))
    (hm : region ∈ regions) (hc : region.contains address = true) :
    byteAt regions address = region.data[address - region.address]? := by
  have hl : regions.find? (fun region => region.contains address) = some region := lookupRegion_disjoint hd hm hc
  simp [byteAt, hl]

private def coalesceStep (ranges : List (Nat × Nat)) (address : Nat) : List (Nat × Nat) :=
  match ranges with
  | (start, size) :: rest =>
    if start + size = address then (start, size + 1) :: rest
    else if start ≤ address && address < start + size then ranges
    else (address, 1) :: ranges
  | _ => (address, 1) :: ranges

private theorem coalesce_eq (changes : List Nat) :
    coalesce changes = ((changes.mergeSort (· ≤ ·)).foldl coalesceStep []).reverse := rfl

/-- `range` covers `address`. -/
def RangeHas (range : Nat × Nat) (address : Nat) : Prop := range.1 ≤ address ∧ address < range.1 + range.2

private theorem step_mem (ranges : List (Nat × Nat)) (address query : Nat) :
    (∃ range ∈ coalesceStep ranges address, RangeHas range query) ↔
      query = address ∨ ∃ range ∈ ranges, RangeHas range query := by
  unfold coalesceStep
  split
  · rename_i start size rest
    split
    · rename_i he
      simp only [List.mem_cons, exists_eq_or_imp, RangeHas]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · by_cases hq : query = address
          · exact Or.inl hq
          · exact Or.inr (Or.inl ⟨h1, by omega⟩)
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨h1, h2⟩ | h)
        · exact Or.inl (by omega)
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr h
    · split
      · rename_i hin
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
        simp only [List.mem_cons, exists_eq_or_imp, RangeHas]
        constructor
        · exact Or.inr
        · rintro (h | h)
          · exact Or.inl (by omega)
          · exact h
      · simp only [List.mem_cons, exists_eq_or_imp, RangeHas]
        constructor
        · rintro (⟨h1, h2⟩ | h)
          · exact Or.inl (by omega)
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (by omega)
          · exact Or.inr h
  · simp only [List.mem_cons, exists_eq_or_imp, RangeHas]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h

private theorem foldl_mem (addresses : List Nat) (init : List (Nat × Nat)) (query : Nat) :
    (∃ range ∈ addresses.foldl coalesceStep init, RangeHas range query) ↔
      query ∈ addresses ∨ ∃ range ∈ init, RangeHas range query := by
  induction addresses generalizing init with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, step_mem, List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Coverage: the coalesced ranges cover exactly the changed addresses. -/
theorem coalesce_covers (changes : List Nat) (query : Nat) :
    (∃ range ∈ coalesce changes, RangeHas range query) ↔ query ∈ changes := by
  rw [coalesce_eq]
  simp only [List.mem_reverse, foldl_mem]
  simp only [List.not_mem_nil, false_and, exists_false, or_false]
  exact (List.mergeSort_perm _ _).mem_iff

private theorem step_positive (ranges : List (Nat × Nat)) (address : Nat) (h : ∀ r ∈ ranges, 0 < r.2) :
    ∀ r ∈ coalesceStep ranges address, 0 < r.2 := by
  unfold coalesceStep
  split
  · rename_i start size rest
    split
    · simp only [List.mem_cons, forall_eq_or_imp] at h ⊢
      exact ⟨by omega, h.2⟩
    · split
      · exact h
      · simp only [List.mem_cons, forall_eq_or_imp] at h ⊢
        exact ⟨by omega, h⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨by omega, h⟩

/-- Every reported range is nonempty. -/
theorem coalesce_nonempty (changes : List Nat) (range : Nat × Nat) (h : range ∈ coalesce changes) : 0 < range.2 := by
  rw [coalesce_eq] at h
  have key : ∀ (addresses : List Nat) (init : List (Nat × Nat)), (∀ r ∈ init, 0 < r.2) →
      ∀ r ∈ addresses.foldl coalesceStep init, 0 < r.2 := by
    intro addresses
    induction addresses with
    | nil => simp
    | cons head rest ih =>
      intro init hi
      exact ih _ (step_positive _ _ hi)
  exact key _ [] (by simp) range (List.mem_reverse.1 h)

private theorem foldl_separated (addresses : List Nat) (init : List (Nat × Nat))
    (hs : addresses.Pairwise (· ≤ ·))
    (hi : init.Pairwise fun newer older => older.1 + older.2 < newer.1)
    (hp : ∀ r ∈ init, 0 < r.2)
    (hh : ∀ head tail, init = head :: tail → ∀ a ∈ addresses, head.1 + head.2 ≤ a + 1) :
    (addresses.foldl coalesceStep init).Pairwise fun newer older => older.1 + older.2 < newer.1 := by
  induction addresses generalizing init with
  | nil => exact hi
  | cons address rest ih =>
    obtain ⟨hlt, hrest⟩ := List.pairwise_cons.1 hs
    simp only [List.foldl_cons]
    apply ih _ hrest
    · unfold coalesceStep
      split
      · rename_i start size tail
        split
        · obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hi
          exact List.pairwise_cons.2 ⟨fun older ho => hhead older ho, htail⟩
        · split
          · exact hi
          · rename_i hne hout
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt] at hout
            have hle := hh _ _ rfl address (by simp)
            have hpos := hp (start, size) (by simp)
            simp only at hle hpos
            refine List.pairwise_cons.2 ⟨?_, hi⟩
            intro older ho
            rcases List.mem_cons.1 ho with rfl | ho'
            · simp only
              have := hout (by omega)
              omega
            · have := (List.pairwise_cons.1 hi).1 older ho'
              have := hout (by omega)
              simp only at *
              omega
      · rename_i hne
        cases init with
        | nil => simp
        | cons h t => exact (hne h.1 h.2 t rfl).elim
    · exact step_positive _ _ hp
    · intro head tail he a ha
      have hal := hlt a ha
      revert he
      unfold coalesceStep
      split
      · rename_i start size _
        split
        · intro heq
          simp only [List.cons.injEq] at heq
          obtain ⟨rfl, _⟩ := heq
          simp only
          omega
        · split
          · intro heq
            have hle := hh head tail heq a (List.mem_cons_of_mem _ ha)
            exact hle
          · intro heq
            simp only [List.cons.injEq] at heq
            obtain ⟨rfl, _⟩ := heq
            simp only
            omega
      · intro heq
        simp only [List.cons.injEq] at heq
        obtain ⟨rfl, _⟩ := heq
        simp only
        omega

/-- The ranges are ascending and maximal for every input, duplicates included: consecutive ranges are
not even adjacent. -/
theorem coalesce_separated (changes : List Nat) :
    (coalesce changes).Pairwise fun left right => left.1 + left.2 < right.1 := by
  rw [coalesce_eq, List.pairwise_reverse]
  have hsorted : (changes.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have hle := List.pairwise_mergeSort (l := changes) (le := fun a b : Nat => decide (a ≤ b))
      (by intro a b c; simp; omega) (by intro a b; simp; omega)
    exact hle.imp (by simp)
  exact foldl_separated _ [] hsorted List.Pairwise.nil (by simp) (by simp)

private theorem separated_unique {ranges : List (Nat × Nat)}
    (h : ranges.Pairwise fun left right => left.1 + left.2 < right.1) {left right : Nat × Nat} {address : Nat}
    (hl : left ∈ ranges) (hr : right ∈ ranges) (ha : RangeHas left address) (hb : RangeHas right address) :
    left = right := by
  induction ranges with
  | nil => simp at hl
  | cons head rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.1 h
    unfold RangeHas at ha hb
    rcases List.mem_cons.1 hl with rfl | hl' <;> rcases List.mem_cons.1 hr with rfl | hr'
    · rfl
    · have := hhead _ hr'
      omega
    · have := hhead _ hl'
      omega
    · exact ih hrest hl' hr'

/-- A repeated address is reported once. -/
theorem coalesce_duplicate (address : Nat) : coalesce [address, address] = [(address, 1)] := by
  simp [coalesce_eq, coalesceStep, List.mergeSort_pair]

/-! Candidate selection and the whole diff. -/

private def candidateStep (candidates : List (Nat × Nat)) (region : Bap.Emu.Region) : List (Nat × Nat) :=
  if candidates.any fun current => current.1 = region.address then
    candidates.map fun current =>
      if current.1 = region.address then (current.1, max current.2 region.data.size) else current
  else candidates ++ [(region.address, region.data.size)]

private theorem candidateStep_grows (candidates : List (Nat × Nat)) (region : Bap.Emu.Region) (c : Nat × Nat)
    (h : c ∈ candidates) : ∃ c' ∈ candidateStep candidates region, c'.1 = c.1 ∧ c.2 ≤ c'.2 := by
  unfold candidateStep
  split
  · by_cases he : c.1 = region.address
    · exact ⟨(c.1, max c.2 region.data.size), List.mem_map.2 ⟨c, h, by simp [he]⟩, rfl, by simp; omega⟩
    · exact ⟨c, List.mem_map.2 ⟨c, h, by simp [he]⟩, rfl, Nat.le_refl _⟩
  · exact ⟨c, List.mem_append_left _ h, rfl, Nat.le_refl _⟩

private theorem candidateStep_region (candidates : List (Nat × Nat)) (region : Bap.Emu.Region) :
    ∃ c' ∈ candidateStep candidates region, c'.1 = region.address ∧ region.data.size ≤ c'.2 := by
  unfold candidateStep
  split
  · rename_i hany
    obtain ⟨c, hc, he⟩ := List.any_eq_true.1 hany
    have he' : c.1 = region.address := by simpa using he
    exact ⟨(c.1, max c.2 region.data.size), List.mem_map.2 ⟨c, hc, by simp [he']⟩, he', by simp; omega⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl, Nat.le_refl _⟩

private theorem candidates_foldl (regions : List Bap.Emu.Region) (init : List (Nat × Nat)) :
    (∀ c ∈ init, ∃ c' ∈ regions.foldl candidateStep init, c'.1 = c.1 ∧ c.2 ≤ c'.2) ∧
      ∀ region ∈ regions, ∃ c' ∈ regions.foldl candidateStep init, c'.1 = region.address ∧ region.data.size ≤ c'.2 := by
  induction regions generalizing init with
  | nil => exact ⟨fun c hc => ⟨c, hc, rfl, Nat.le_refl _⟩, by simp⟩
  | cons head rest ih =>
    obtain ⟨h1, h2⟩ := ih (candidateStep init head)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨c', hc', he, hle⟩ := candidateStep_grows init head c hc
      obtain ⟨c'', hc'', he', hle'⟩ := h1 c' hc'
      exact ⟨c'', hc'', he'.trans he, by omega⟩
    · intro region hr
      rcases List.mem_cons.1 hr with rfl | hr'
      · obtain ⟨c', hc', he, hle⟩ := candidateStep_region init region
        obtain ⟨c'', hc'', he', hle'⟩ := h1 c' hc'
        exact ⟨c'', hc'', he'.trans he, by omega⟩
      · exact h2 region hr'

/-- Grown regions are not skipped: candidates span every byte of every region, whichever table it came from. -/
theorem diffCandidates_cover (regions : List Bap.Emu.Region) (region : Bap.Emu.Region) (hr : region ∈ regions)
    (address : Nat) (hc : region.contains address = true) :
    ∃ c ∈ diffCandidates regions, RangeHas c address := by
  obtain ⟨c, hm, he, hle⟩ := (candidates_foldl regions []).2 region hr
  obtain ⟨h1, h2⟩ := (region_contains_iff _ _).1 hc
  exact ⟨c, hm, by omega, by omega⟩

private theorem changed_inner (saved live : List Bap.Emu.Region) (base : Nat) (offsets : List Nat) (changes : List Nat)
    (query : Nat) :
    query ∈ offsets.foldl (init := changes) (fun changes offset =>
      if byteAt live (base + offset) != byteAt saved (base + offset) then (base + offset) :: changes else changes) ↔
      query ∈ changes ∨ ∃ offset ∈ offsets, query = base + offset ∧ byteAt live query ≠ byteAt saved query := by
  induction offsets generalizing changes with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih]
    by_cases hd : byteAt live (base + head) = byteAt saved (base + head)
    · simp only [hd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨rfl, hq⟩ | h)
        · exact Or.inl h
        · exact absurd hd hq
        · exact Or.inr h
    · have hb : (byteAt live (base + head) != byteAt saved (base + head)) = true := by simpa using hd
      simp only [hb, ↓reduceIte, List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl ⟨h, h ▸ hd⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨rfl, _⟩ | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h

private theorem changed_outer (saved live : List Bap.Emu.Region) (candidates : List (Nat × Nat)) (changes : List Nat)
    (query : Nat) :
    query ∈ candidates.foldl (init := changes) (fun changes candidate =>
      (List.range candidate.2).foldl (init := changes) fun changes offset =>
        let address := candidate.1 + offset
        if byteAt live address != byteAt saved address then address :: changes else changes) ↔
      query ∈ changes ∨ ∃ c ∈ candidates, RangeHas c query ∧ byteAt live query ≠ byteAt saved query := by
  induction candidates generalizing changes with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons, ih]
    have hinner := changed_inner saved live head.1 (List.range head.2) changes query
    have hmem : (∃ offset ∈ List.range head.2, query = head.1 + offset ∧ byteAt live query ≠ byteAt saved query) ↔
        (RangeHas head query ∧ byteAt live query ≠ byteAt saved query) := by
      unfold RangeHas
      constructor
      · rintro ⟨o, ho, rfl, hd⟩
        have := List.mem_range.1 ho
        exact ⟨⟨by omega, by omega⟩, hd⟩
      · rintro ⟨⟨h1, h2⟩, hd⟩
        exact ⟨query - head.1, List.mem_range.2 (by omega), by omega, hd⟩
    rw [hmem] at hinner
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · rcases hinner.1 h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (hinner.2 (Or.inl h))
      · exact Or.inl (hinner.2 (Or.inr h))
      · exact Or.inr h

/-- An address is listed iff its byte differs between the two tables. Mapped against unmapped counts as different. -/
theorem changedAddresses_mem (saved live : List Bap.Emu.Region) (address : Nat) :
    address ∈ changedAddresses saved live ↔ byteAt live address ≠ byteAt saved address := by
  have key := changed_outer saved live (diffCandidates (saved ++ live)) [] address
  simp only [List.not_mem_nil, false_or] at key
  refine key.trans ⟨fun ⟨_, _, _, hd⟩ => hd, fun hd => ?_⟩
  have : (byteAt live address).isSome = true ∨ (byteAt saved address).isSome = true := by
    cases hl : byteAt live address <;> cases hs : byteAt saved address <;> simp_all
  obtain ⟨region, hr, hc⟩ : ∃ region ∈ saved ++ live, region.contains address = true := by
    rcases this with h | h
    · obtain ⟨r, hr, hc⟩ := (byteAt_some_iff _ _).1 h
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · obtain ⟨r, hr, hc⟩ := (byteAt_some_iff _ _).1 h
      exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain ⟨c, hm, hrange⟩ := diffCandidates_cover _ region hr address hc
  exact ⟨c, hm, hrange, hd⟩

/-- Diff correctness: the reported ranges cover exactly the bytes that differ, including bytes of grown,
shrunk, new and removed regions. -/
theorem diffRanges_covers (saved live : List Bap.Emu.Region) (address : Nat) :
    (∃ range ∈ diffRanges saved live, RangeHas range address) ↔ byteAt live address ≠ byteAt saved address :=
  (coalesce_covers _ _).trans (changedAddresses_mem saved live address)

/-- Ranges are ascending and never touch. -/
theorem diffRanges_separated (saved live : List Bap.Emu.Region) :
    (diffRanges saved live).Pairwise fun left right => left.1 + left.2 < right.1 :=
  coalesce_separated _

/-- Each changed byte is reported exactly once: it lies in a single range. -/
theorem diffRanges_exactly_once (saved live : List Bap.Emu.Region) (address : Nat)
    (h : byteAt live address ≠ byteAt saved address) :
    ∃ range ∈ diffRanges saved live, RangeHas range address ∧
      ∀ other ∈ diffRanges saved live, RangeHas other address → other = range := by
  obtain ⟨range, hm, hr⟩ := (diffRanges_covers saved live address).2 h
  exact ⟨range, hm, hr, fun other ho hrr => separated_unique (diffRanges_separated saved live) ho hm hrr hr⟩

/-- Identical tables have an empty diff. -/
theorem diffRanges_self (regions : List Bap.Emu.Region) : diffRanges regions regions = [] := by
  cases hd : diffRanges regions regions with
  | nil => rfl
  | cons head rest =>
    have hpos := coalesce_nonempty _ head (by
      show head ∈ diffRanges regions regions
      simp [hd])
    have := (diffRanges_covers regions regions head.1).1 ⟨head, by simp [hd], Nat.le_refl _, by omega⟩
    exact absurd rfl this

end Diff

/-! ### Text checkpoints -/

section TextCheckpoint

open_private Bap.Bil.Wire Bap.Bil.Wire hexDigit parseHexLoop
open_private Bap.Emu.Checkpoint Bap.Emu nat bool hex boolValue encodeTyp decodeTyp encodeValue decodeValue decodeCells
  encodeBinding decodeBinding encodeBytes decodeHex decodeHex.loop decodeRegionBytes encodeRegion decodeRegion encodePending
  decodePending encodeThread decodeThread encodeProcess decodeProcess

theorem toNat?_toString (n : Nat) : (toString n).toNat? = some n := by
  have hdig : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun c hc =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  rw [Nat.toString_eq_ofList_toDigits, ← String.toNat?_toSlice]
  have hnat : (String.ofList (Nat.toDigits 10 n)).toSlice.isNat = true := by
    apply String.Slice.isNat_of_isDigit
    · simp [Nat.toDigits_ne_nil]
    · intro c hc
      apply hdig
      simpa using hc
  rw [String.Slice.toNat?_eq_some_ofDigitChars hnat]
  have hf : (Nat.toDigits 10 n).filter (· != '_') = Nat.toDigits 10 n := by
    apply List.filter_eq_self.2
    intro c hc
    have := Nat.underscore_not_in_toDigits (n := n)
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact this hc
  simp [hf, Nat.ofDigitChars_ten_toDigits]

theorem sexp_nat_roundtrip (n : Nat) : Sexp.nat (nat n) = .ok n := by
  simp [Sexp.nat, nat, Sexp.asAtom, toNat?_toString, bind, Except.bind]

theorem boolValue_roundtrip (value : Bool) : boolValue (bool value) = .ok value := by
  cases value <;> rfl

private theorem hexDigit_digitChar_fin : ∀ d : Fin 16, hexDigit (Nat.digitChar d) = some d := by decide

private theorem hexDigit_digitChar (d : Nat) (h : d < 16) : hexDigit (Nat.digitChar d) = some d :=
  hexDigit_digitChar_fin ⟨d, h⟩

private theorem parseHexLoop_append {chars more : List Char} {start value : Nat}
    (h : parseHexLoop chars start = .ok value) :
    parseHexLoop (chars ++ more) start = parseHexLoop more value := by
  induction chars generalizing start with
  | nil =>
    simp only [parseHexLoop, Except.ok.injEq] at h
    subst h
    rfl
  | cons c rest ih =>
    simp only [parseHexLoop] at h
    simp only [List.cons_append, parseHexLoop]
    cases hd : hexDigit c with
    | none => simp [hd] at h
    | some d =>
      simp only [hd] at h ⊢
      exact ih h

private theorem parseHexLoop_toDigits (n : Nat) : parseHexLoop (Nat.toDigits 16 n) 0 = .ok n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · rename_i hlt
      simp [parseHexLoop, hexDigit_digitChar n hlt]
    · rename_i hge
      have hdiv : n / 16 < n := Nat.div_lt_self (by omega) (by decide)
      rw [parseHexLoop_append (ih _ hdiv)]
      have hmod : n % 16 < 16 := Nat.mod_lt _ (by decide)
      simp only [parseHexLoop, hexDigit_digitChar _ hmod]
      congr 1
      omega

/-- Printing a number in hex and parsing it back is the identity. -/
theorem parseHex_toDigits (n : Nat) : Bil.Wire.parseHex (String.ofList (Nat.toDigits 16 n)) = .ok n := by
  simp only [Bil.Wire.parseHex, String.toList_ofList]
  have : (String.ofList (Nat.toDigits 16 n)).isEmpty = false := by
    simp [Nat.toDigits_ne_nil]
  rw [this]
  exact parseHexLoop_toDigits n

theorem typ_roundtrip (typ : Typ) : decodeTyp (encodeTyp typ) = .ok typ := by
  cases typ with
  | unknown => rfl
  | unit => rfl
  | imm width =>
    simp only [encodeTyp, Sexp.tagged, decodeTyp, sexp_nat_roundtrip, bind, Except.bind]
  | mem address value =>
    simp only [encodeTyp, Sexp.tagged, decodeTyp, sexp_nat_roundtrip, bind, Except.bind]

/-- Decoding a memory value rebuilds it from its sparse cells. -/
def normalizeValue : Value → Value
  | .memory memory => .memory (Bap.Memory.ofCells (Bap.Memory.cells memory))
  | value => value

private theorem mapM_map_ok {α β γ ε : Type} {f : α → β} {g : β → Except ε γ} {n : α → γ} {items : List α}
    (h : ∀ x ∈ items, g (f x) = .ok (n x)) : (items.map f).mapM g = .ok (items.map n) := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons, List.mapM_cons, h head (by simp), bind, Except.bind]
    simp only [ih fun x hx => h x (List.mem_cons_of_mem _ hx), pure, Except.pure]

private theorem mapM_map_self {α β ε : Type} {f : α → β} {g : β → Except ε α} {items : List α}
    (h : ∀ x ∈ items, g (f x) = .ok x) : (items.map f).mapM g = .ok items := by
  have := mapM_map_ok (n := id) h
  simpa using this

theorem value_roundtrip (value : Value) : decodeValue (encodeValue value) = .ok (normalizeValue value) := by
  cases value with
  | undefined => rfl
  | bits value =>
    simp only [encodeValue, Sexp.tagged, decodeValue, sexp_nat_roundtrip, bind, Except.bind, hex, Sexp.asAtom,
      parseHex_toDigits]
    simp [normalizeValue, pure, Except.pure, value.isLt]
  | @memory width memory =>
    have hcells : decodeCells width (.list ((Bap.Memory.cells memory).map fun cell =>
        Sexp.tagged "cell" [hex cell.1.toNat, nat cell.2.toNat])) = .ok (Bap.Memory.cells memory) := by
      simp only [decodeCells, Sexp.asList, bind, Except.bind]
      apply mapM_map_self
      intro cell _
      obtain ⟨a, b⟩ := cell
      have hb := b.toNat_lt
      simp [Sexp.expectTagged, Sexp.tagged, Sexp.asList, Sexp.asAtom, hex, parseHex_toDigits, sexp_nat_roundtrip,
        bind, Except.bind, pure, Except.pure]
      exact hb
    simp only [encodeValue, decodeValue, Sexp.tagged, sexp_nat_roundtrip, bind, Except.bind]
    simp only [Sexp.tagged] at hcells
    rw [hcells]
    rfl

/-- Normalising a well-formed memory value preserves every byte it holds. -/
theorem readByte_normalizeValue {width : Nat} {memory : Bap.Memory width} (wf : PagesWF memory) (address : BitVec width) :
    Bap.Memory.readByte (Bap.Memory.ofCells (Bap.Memory.cells memory)) address = Bap.Memory.readByte memory address :=
  readByte_ofCells_cells wf address

/-- Bindings survive up to memory normalisation. -/
def normalizeBinding (binding : Bap.Var × Value) : Bap.Var × Value := (binding.1, normalizeValue binding.2)

theorem binding_roundtrip (binding : Bap.Var × Value) :
    decodeBinding (encodeBinding binding) = .ok (normalizeBinding binding) := by
  obtain ⟨var, value⟩ := binding
  obtain ⟨name, typ, index, isVirtual⟩ := var
  simp only [encodeBinding, decodeBinding, Sexp.tagged, Sexp.expectTagged, Sexp.asList, Sexp.asAtom, bind, Except.bind,
    typ_roundtrip, sexp_nat_roundtrip, boolValue_roundtrip, value_roundtrip, normalizeBinding]
  simp [typ_roundtrip, sexp_nat_roundtrip, boolValue_roundtrip, value_roundtrip, pure, Except.pure]

/-! Region bytes. -/

private theorem byteArray_toList_loop (data : ByteArray) (index : Nat) (acc : List UInt8) (h : index ≤ data.size) :
    ByteArray.toList.loop data index acc = acc.reverse ++ data.data.toList.drop index := by
  have hlen : data.data.toList.length = data.size := Array.length_toList
  induction hd : data.size - index generalizing index acc with
  | zero =>
    have he : index = data.size := by omega
    subst he
    rw [ByteArray.toList.loop, ite_eq_right (by omega), List.drop_eq_nil_of_le (by omega)]
    simp
  | succ k ih =>
    have hlt : index < data.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left hlt, ih (index + 1) _ hlt (by omega)]
    rw [List.drop_eq_getElem_cons (by omega : index < data.data.toList.length)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    congr 2
    cases data with | mk bytes =>
    simp only [ByteArray.get!]
    simp [Array.get!Internal_eq_getElem!, getElem!_pos, show index < bytes.size from hlt]

theorem byteArray_toList (data : ByteArray) : data.toList = data.data.toList :=
  (byteArray_toList_loop data 0 [] (Nat.zero_le _)).trans (by simp)

private def byteDigits (byte : UInt8) : List Char :=
  let digits := Nat.toDigits 16 byte.toNat
  if digits.length = 1 then ['0'] ++ digits else digits

private theorem byteDigits_pair (byte : UInt8) :
    ∃ high low, byteDigits byte = [high, low] ∧ parseHexLoop [high, low] 0 = .ok byte.toNat := by
  have hb : byte.toNat < 256 := byte.toNat_lt
  by_cases hs : byte.toNat < 16
  · refine ⟨'0', Nat.digitChar byte.toNat, ?_, ?_⟩
    · simp [byteDigits, Nat.toDigits_of_lt_base hs]
    · have h0 : hexDigit '0' = some 0 := by decide
      simp [parseHexLoop, h0, hexDigit_digitChar _ hs]
  · have hdiv : byte.toNat / 16 < 16 := by omega
    have hmod : byte.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hd : Nat.toDigits 16 byte.toNat = [Nat.digitChar (byte.toNat / 16), Nat.digitChar (byte.toNat % 16)] := by
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_right hs, Nat.toDigits_of_lt_base hdiv]
      rfl
    refine ⟨Nat.digitChar (byte.toNat / 16), Nat.digitChar (byte.toNat % 16), by simp [byteDigits, hd], ?_⟩
    simp only [parseHexLoop, hexDigit_digitChar _ hdiv, hexDigit_digitChar _ hmod]
    congr 1
    omega

private theorem encodeBytes_toList (data : ByteArray) :
    (encodeBytes data).toList = data.data.toList.flatMap byteDigits := by
  simp only [encodeBytes, String.toList_intercalate, byteArray_toList]
  generalize data.data.toList = bytes
  induction bytes with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.map_cons, List.flatMap_cons]
    cases rest with
    | nil => simp [List.intercalate, byteDigits]
    | cons second tail =>
      rw [List.intercalate_cons_of_ne_nil (by simp), ih]
      simp [byteDigits]

private theorem decodeHex_loop (bytes : List UInt8) (acc : List UInt8) :
    decodeHex.loop (bytes.flatMap byteDigits) acc = .ok (ByteArray.mk (acc.reverse ++ bytes).toArray) := by
  induction bytes generalizing acc with
  | nil => simp [decodeHex.loop, pure, Except.pure]
  | cons head rest ih =>
    obtain ⟨high, low, hd, hp⟩ := byteDigits_pair head
    have hparse : Bil.Wire.parseHex (String.ofList [high, low]) = .ok head.toNat := by
      simp only [Bil.Wire.parseHex, String.toList_ofList]
      have : (String.ofList [high, low]).isEmpty = false := by simp
      rw [this]
      exact hp
    have hb : ¬ head.toNat ≥ 256 := by
      have := head.toNat_lt
      omega
    simp only [List.flatMap_cons, hd, List.cons_append, List.nil_append, decodeHex.loop, hparse, bind, Except.bind, hb,
      ↓reduceIte, ih]
    simp

/-- The text encoding of region bytes is lossless. -/
theorem decodeHex_encodeBytes (data : ByteArray) : decodeHex (encodeBytes data) = .ok data := by
  simp only [decodeHex, encodeBytes_toList, decodeHex_loop]
  simp

/-! Whole-record round trips. -/

theorem region_roundtrip (region : Bap.Emu.Region) : decodeRegion (encodeRegion region) = .ok region := by
  obtain ⟨address, data, ⟨r, w, x⟩⟩ := region
  simp only [encodeRegion, decodeRegion, Sexp.tagged, Sexp.expectTagged, Sexp.asList, bind, Except.bind]
  simp [sexp_nat_roundtrip, boolValue_roundtrip, decodeRegionBytes, decodeHex_encodeBytes, pure, Except.pure]

theorem pending_roundtrip (pending : Option PendingBranch) : decodePending (encodePending pending) = .ok pending := by
  cases pending with
  | none => rfl
  | some pending =>
    obtain ⟨branch, target⟩ := pending
    simp only [encodePending, decodePending, Sexp.tagged, Sexp.expectTagged, Sexp.asList, bind, Except.bind]
    simp [sexp_nat_roundtrip, pure, Except.pure]

/-- A thread with its memory values normalised. -/
def normalizeThread (context : ThreadContext) : ThreadContext :=
  { context with state := { env := context.state.env.map normalizeBinding } }

theorem thread_roundtrip (context : ThreadContext) :
    decodeThread (encodeThread context) = .ok (normalizeThread context) := by
  obtain ⟨id, ⟨env⟩, pc, stopped, pending⟩ := context
  simp only [encodeThread, decodeThread, Sexp.tagged, Sexp.expectTagged, Sexp.asList, bind, Except.bind]
  simp [sexp_nat_roundtrip, boolValue_roundtrip, pending_roundtrip, mapM_map_ok (fun x _ => binding_roundtrip x),
    normalizeThread, pure, Except.pure]

theorem process_roundtrip (process : ThreadId × List Bap.Emu.Region) :
    decodeProcess (encodeProcess process) = .ok process := by
  obtain ⟨id, regions⟩ := process
  simp only [encodeProcess, decodeProcess, Sexp.tagged, Sexp.expectTagged, Sexp.asList, bind, Except.bind]
  simp [sexp_nat_roundtrip, mapM_map_self (fun x _ => region_roundtrip x), pure, Except.pure]

/-- A snapshot with its memory values normalised. -/
def normalizeSnapshot (snapshot : Snapshot) : Snapshot :=
  { snapshot with
    state := { env := snapshot.state.env.map normalizeBinding }
    threads := snapshot.threads.map normalizeThread }

/-- The text checkpoint format is lossless: decoding an encoded snapshot returns it, with memory values
rebuilt from their sparse cells (see `readByte_normalizeValue`). -/
theorem snapshot_roundtrip (snapshot : Snapshot) :
    decodeSnapshot (encodeSnapshot snapshot) = .ok (normalizeSnapshot snapshot) := by
  obtain ⟨⟨env⟩, pc, regions, stopped, threads, current, next, pending, processes⟩ := snapshot
  simp only [encodeSnapshot, decodeSnapshot, Sexp.tagged, Sexp.asList, bind, Except.bind]
  simp [sexp_nat_roundtrip, boolValue_roundtrip, pending_roundtrip, mapM_map_ok (fun x _ => binding_roundtrip x),
    mapM_map_ok (fun x _ => thread_roundtrip x), mapM_map_self (fun x _ => region_roundtrip x),
    mapM_map_self (fun x _ => process_roundtrip x), normalizeSnapshot, pure, Except.pure]

end TextCheckpoint

/-! ### Binary checkpoints -/

section BinaryCheckpoint

open_private Bap.Emu.Checkpoint Bap.Emu encodeBinaryUnchecked fitsWord pendingFits typFits valueFits bindingFits regionFits
  threadFits processFits Writer Writer.mk Writer.data Reader Reader.mk Reader.data Reader.offset
  putBytes putByte natBytes putNat putBool putText putPendingBin putTypBin putCellsBin putValueBin putBindingBin
  putRegionBin putThreadBin putProcessBin takeBytes getByte getNat getBool getText getList getList.loop getPendingBin
  getTypBin getValueBin getBindingBin getRegionBin getThreadBin getProcessBin binaryMagic

/-- `encoded` sits in `data` at `offset`. -/
def At (data : ByteArray) (offset : Nat) (encoded : ByteArray) : Prop :=
  offset + encoded.size ≤ data.size ∧ data.extract offset (offset + encoded.size) = encoded

theorem At.split {data : ByteArray} {offset : Nat} {left right : ByteArray} (h : At data offset (left ++ right)) :
    At data offset left ∧ At data (offset + left.size) right := by
  obtain ⟨hs, he⟩ := h
  rw [ByteArray.size_append] at hs he
  constructor
  · refine ⟨by omega, ?_⟩
    have key : (data.extract offset (offset + (left.size + right.size))).extract 0 left.size = left := by
      rw [he]
      exact ByteArray.extract_append_eq_left rfl
    rw [ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left (by omega)] at key
    exact key
  · refine ⟨by omega, ?_⟩
    have key : (data.extract offset (offset + (left.size + right.size))).extract left.size (left.size + right.size) = right := by
      rw [he]
      exact ByteArray.extract_append_eq_right rfl rfl
    rw [ByteArray.extract_extract, Nat.min_self] at key
    rw [show offset + left.size + right.size = offset + (left.size + right.size) by omega]
    exact key

/-- `decode` reads back `value` from any occurrence of `encoded`, stopping right after it. -/
def Decodes {α : Type} (decode : Reader → Except String (α × Reader)) (encoded : ByteArray) (value : α) : Prop :=
  ∀ data offset, At data offset encoded →
    decode (Reader.mk data offset) = .ok (value, Reader.mk data (offset + encoded.size))

theorem takeBytes_at {data encoded : ByteArray} {offset : Nat} (h : At data offset encoded) :
    takeBytes (Reader.mk data offset) encoded.size = .ok (encoded, Reader.mk data (offset + encoded.size)) := by
  obtain ⟨hs, he⟩ := h
  have hn : ¬ offset + encoded.size > data.size := by omega
  simp only [takeBytes, bind, Except.bind, Reader.offset, Reader.data, hn, ↓reduceIte, he]

private def byteEnc (value : Nat) : ByteArray := ByteArray.mk #[UInt8.ofNat value]

private theorem byteEnc_size (value : Nat) : (byteEnc value).size = 1 := rfl

theorem getByte_decodes (value : Nat) (h : value < 256) : Decodes getByte (byteEnc value) value := by
  intro data offset hat
  have ht := takeBytes_at hat
  rw [byteEnc_size] at ht
  simp only [getByte, bind, Except.bind, ht]
  congr 3
  rw [byteGet_eq]
  show (#[UInt8.ofNat value] : Array UInt8)[0]!.toNat = value
  simpa using Nat.mod_eq_of_lt h

/-- The little-endian byte image of the low `count` bytes of `value`. -/
private def bytesOf (count value : Nat) : ByteArray :=
  ByteArray.mk ((List.range count).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray

private theorem bytesOf_size (count value : Nat) : (bytesOf count value).size = count := by
  show ((List.range count).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray.size = count
  simp

private theorem bytesOf_get (count value index : Nat) (h : index < count) :
    (bytesOf count value)[index]!.toNat = value / 256 ^ index % 256 := by
  rw [byteGet_eq]
  show ((List.range count).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray[index]!.toNat = _
  simp [getElem!_pos, h]

private theorem sum_bytesOf (count value steps : Nat) (h : steps ≤ count) :
    (List.range steps).foldl (init := 0) (fun acc index => acc + (bytesOf count value)[index]!.toNat * 256 ^ index) =
      value % 256 ^ steps := by
  induction steps with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [bytesOf_get _ _ _ (by omega), Nat.mod_pow_succ, Nat.mul_comm]

/-- Round trip of the fixed-width integer encoding, modulo its width. -/
theorem natBytes_decodes (value : Nat) (h : value < 2 ^ 64) : Decodes getNat (natBytes value) value := by
  intro data offset hat
  have hnb : natBytes value = bytesOf 8 value := rfl
  have ht := takeBytes_at hat
  rw [hnb, bytesOf_size] at ht
  simp only [getNat, bind, Except.bind, ht]
  rw [hnb, bytesOf_size, sum_bytesOf 8 value 8 (by omega), Nat.mod_eq_of_lt (by simpa using h)]

theorem getBool_decodes (value : Bool) : Decodes getBool (byteEnc (if value then 1 else 0)) value := by
  intro data offset hat
  have ht := getByte_decodes (if value then 1 else 0) (by split <;> decide) data offset hat
  simp only [getBool, bind, Except.bind, ht]
  cases value <;> rfl

private theorem fromUTF8_toUTF8 (text : String) : String.fromUTF8! text.toUTF8 = text := by
  have hv : text.toByteArray.IsValidUTF8 := text.isValidUTF8
  simp only [String.fromUTF8!, String.toUTF8_eq_toByteArray, hv, ↓reduceDIte]
  rw [← String.toByteArray_inj]
  rfl

theorem getText_decodes (text : String) (h : text.utf8ByteSize < 2 ^ 64) :
    Decodes getText (natBytes text.utf8ByteSize ++ text.toUTF8) text := by
  intro data offset hat
  obtain ⟨h1, h2⟩ := hat.split
  have hn := natBytes_decodes _ h data offset h1
  have hsize : text.toUTF8.size = text.utf8ByteSize := rfl
  have ht := takeBytes_at h2
  rw [hsize] at ht
  simp only [getText, bind, Except.bind, hn, ht, fromUTF8_toUTF8]
  simp only [ByteArray.size_append, hsize, Nat.add_assoc]

/-! Sequencing byte images. -/

private def body {α : Type} (f : α → ByteArray) : List α → ByteArray
  | [] => ByteArray.empty
  | head :: rest => f head ++ body f rest

private theorem foldl_writer {α : Type} (put : Writer → α → Writer) (f : α → ByteArray)
    (hput : ∀ writer item, Writer.data (put writer item) = Writer.data writer ++ f item) (items : List α) (writer : Writer) :
    Writer.data (items.foldl put writer) = Writer.data writer ++ body f items := by
  induction items generalizing writer with
  | nil => simp [body]
  | cons head rest ih =>
    simp only [List.foldl_cons, ih, hput, body, ByteArray.append_assoc]

private theorem natBytes_size (value : Nat) : (natBytes value).size = 8 := rfl

private theorem getList_loop {α β : Type} (decode : Reader → Except String (β × Reader)) (f : α → ByteArray) (n : α → β)
    (items : List α) (data : ByteArray) (offset : Nat) (acc : List β) (hat : At data offset (body f items))
    (hdec : ∀ item ∈ items, Decodes decode (f item) (n item)) :
    getList.loop decode items.length (Reader.mk data offset) acc =
      .ok (acc.reverse ++ items.map n, Reader.mk data (offset + (body f items).size)) := by
  induction items generalizing offset acc with
  | nil => simp [getList.loop, body, pure, Except.pure, ByteArray.size_empty]
  | cons head rest ih =>
    obtain ⟨h1, h2⟩ := At.split (left := f head) (right := body f rest) hat
    have hd := hdec head (by simp) data offset h1
    simp only [List.length_cons, getList.loop, bind, Except.bind, hd]
    rw [ih _ _ h2 fun item hi => hdec item (List.mem_cons_of_mem _ hi)]
    simp [body, ByteArray.size_append, Nat.add_assoc]

/-- Lists: a count followed by the elements. -/
theorem getList_decodes {α β : Type} {decode : Reader → Except String (β × Reader)} (f : α → ByteArray) (n : α → β)
    (items : List α) {data : ByteArray} {offset : Nat} (hlen : items.length < 2 ^ 64)
    (hat : At data offset (natBytes items.length ++ body f items))
    (hdec : ∀ item ∈ items, Decodes decode (f item) (n item)) :
    getList (Reader.mk data offset) decode =
      .ok (items.map n, Reader.mk data (offset + (natBytes items.length ++ body f items).size)) := by
  obtain ⟨h1, h2⟩ := hat.split
  have hn := natBytes_decodes _ hlen data offset h1
  simp only [getList, bind, Except.bind, hn]
  rw [getList_loop decode f n items data _ [] h2 hdec]
  simp [ByteArray.size_append, Nat.add_assoc]

/-! Records. -/

private def encPending : Option PendingBranch → ByteArray
  | none => byteEnc 0
  | some pending => byteEnc 1 ++ natBytes pending.branch ++ natBytes pending.target

private def PendingSafe : Option PendingBranch → Prop
  | none => True
  | some pending => pending.branch < 2 ^ 64 ∧ pending.target < 2 ^ 64

private theorem data_putBytes (writer : Writer) (bytes : ByteArray) :
    Writer.data (putBytes writer bytes) = Writer.data writer ++ bytes := rfl

private theorem data_putByte (writer : Writer) (value : Nat) :
    Writer.data (putByte writer value) = Writer.data writer ++ byteEnc value := rfl

private theorem data_putNat (writer : Writer) (value : Nat) :
    Writer.data (putNat writer value) = Writer.data writer ++ natBytes value := rfl

private theorem data_putBool (writer : Writer) (value : Bool) :
    Writer.data (putBool writer value) = Writer.data writer ++ byteEnc (if value then 1 else 0) := rfl

private theorem data_putPending (writer : Writer) (pending : Option PendingBranch) :
    Writer.data (putPendingBin writer pending) = Writer.data writer ++ encPending pending := by
  cases pending with
  | none => rfl
  | some pending =>
    simp only [putPendingBin, data_putNat, data_putByte, encPending, ByteArray.append_assoc]

theorem getPending_decodes (pending : Option PendingBranch) (h : PendingSafe pending) :
    Decodes getPendingBin (encPending pending) pending := by
  intro data offset hat
  cases pending with
  | none =>
    have hd := getByte_decodes 0 (by decide) data offset hat
    simp only [getPendingBin, bind, Except.bind, hd]
    rfl
  | some pending =>
    obtain ⟨branch, target⟩ := pending
    obtain ⟨hb, ht⟩ := h
    obtain ⟨h12, h3⟩ := At.split hat
    obtain ⟨h1, h2⟩ := At.split h12
    have d1 := getByte_decodes 1 (by decide) data offset h1
    have d2 := natBytes_decodes _ hb data _ h2
    have d3 := natBytes_decodes _ ht data _ h3
    simp only [ByteArray.size_append, byteEnc_size, natBytes_size, Nat.add_assoc] at d1 d2 d3
    simp only [getPendingBin, bind, Except.bind, d1, d2, d3, encPending, ByteArray.size_append, byteEnc_size, natBytes_size,
      Nat.add_assoc]

private def encTyp : Typ → ByteArray
  | .unknown => byteEnc 0
  | .unit => byteEnc 1
  | .mem address value => byteEnc 2 ++ natBytes address ++ natBytes value
  | .imm width => byteEnc 3 ++ natBytes width

private def TypSafe : Typ → Prop
  | .mem address value => address < 2 ^ 64 ∧ value < 2 ^ 64
  | .imm width => width < 2 ^ 64
  | _ => True

private theorem data_putTyp (writer : Writer) (typ : Typ) :
    Writer.data (putTypBin writer typ) = Writer.data writer ++ encTyp typ := by
  cases typ <;> first | rfl | simp only [putTypBin, data_putNat, data_putByte, encTyp, ByteArray.append_assoc]

theorem getTyp_decodes (typ : Typ) (h : TypSafe typ) : Decodes getTypBin (encTyp typ) typ := by
  intro data offset hat
  cases typ with
  | unknown =>
    have hd := getByte_decodes 0 (by decide) data offset hat
    simp only [getTypBin, bind, Except.bind, hd]
    rfl
  | unit =>
    have hd := getByte_decodes 1 (by decide) data offset hat
    simp only [getTypBin, bind, Except.bind, hd]
    rfl
  | mem address value =>
    obtain ⟨ha, hv⟩ := h
    obtain ⟨h12, h3⟩ := At.split hat
    obtain ⟨h1, h2⟩ := At.split h12
    have d1 := getByte_decodes 2 (by decide) data offset h1
    have d2 := natBytes_decodes _ ha data _ h2
    have d3 := natBytes_decodes _ hv data _ h3
    simp only [ByteArray.size_append, byteEnc_size, natBytes_size, Nat.add_assoc] at d1 d2 d3
    simp only [getTypBin, bind, Except.bind, d1, d2, d3, encTyp, ByteArray.size_append, byteEnc_size, natBytes_size,
      Nat.add_assoc]
  | imm width =>
    obtain ⟨h1, h2⟩ := At.split hat
    have d1 := getByte_decodes 3 (by decide) data offset h1
    have d2 := natBytes_decodes _ h data _ h2
    simp only [ByteArray.size_append, byteEnc_size, natBytes_size, Nat.add_assoc] at d1 d2
    simp only [getTypBin, bind, Except.bind, d1, d2, encTyp, ByteArray.size_append, byteEnc_size, natBytes_size,
      Nat.add_assoc]

/-! Values and bindings. -/

private def encCell {width : Nat} (cell : BitVec width × UInt8) : ByteArray := natBytes cell.1.toNat ++ byteEnc cell.2.toNat

private def encValue : Value → ByteArray
  | .undefined => byteEnc 0
  | @Value.bits width value => byteEnc 1 ++ natBytes width ++ bytesOf 32 value.toNat
  | @Value.memory width memory => byteEnc 2 ++ natBytes width ++
      (natBytes (Bap.Memory.cells memory).length ++ body encCell (Bap.Memory.cells memory))

/-- A value the binary format can represent: at most 256 bits, or memory with 64-bit addresses. -/
private def ValueSafe : Value → Prop
  | .undefined => True
  | @Value.bits width _ => width ≤ 256
  | @Value.memory width memory => width ≤ 64 ∧ (Bap.Memory.cells memory).length < 2 ^ 64

private theorem foldl_push_bytesOf (count value : Nat) :
    (List.range count).foldl (init := ByteArray.empty) (fun bytes index =>
      bytes.push (UInt8.ofNat (value / 256 ^ index % 256))) = bytesOf count value := by
  induction count with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    apply ByteArray.ext
    simp [bytesOf, List.range_succ, ByteArray.data_push]

private theorem data_putCells {width : Nat} (writer : Writer) (cells : List (BitVec width × UInt8)) :
    Writer.data (putCellsBin writer cells) = Writer.data writer ++ (natBytes cells.length ++ body encCell cells) := by
  simp only [putCellsBin]
  rw [foldl_writer _ encCell (fun _ _ => by
    simp only [data_putByte, data_putNat, encCell, ByteArray.append_assoc])]
  simp only [data_putNat, ByteArray.append_assoc]

private theorem data_putValue (writer : Writer) (value : Value) :
    Writer.data (putValueBin writer value) = Writer.data writer ++ encValue value := by
  cases value with
  | undefined => rfl
  | bits value =>
    simp only [putValueBin, data_putBytes, data_putNat, data_putByte, encValue, ByteArray.append_assoc]
    rw [foldl_push_bytesOf]
  | memory memory =>
    simp only [putValueBin, data_putCells, data_putNat, data_putByte, encValue, ByteArray.append_assoc]

theorem getValue_decodes (value : Value) (h : ValueSafe value) :
    Decodes getValueBin (encValue value) (normalizeValue value) := by
  intro data offset hat
  cases value with
  | undefined =>
    have hd := getByte_decodes 0 (by decide) data offset hat
    simp only [getValueBin, bind, Except.bind, hd]
    rfl
  | @bits width value =>
    have hw : width ≤ 256 := h
    obtain ⟨h12, h3⟩ := At.split hat
    obtain ⟨h1, h2⟩ := At.split h12
    have d1 := getByte_decodes 1 (by decide) data offset h1
    have d2 := natBytes_decodes _ (by omega : width < 2 ^ 64) data _ h2
    have d3 := takeBytes_at h3
    rw [bytesOf_size] at d3
    simp only [ByteArray.size_append, byteEnc_size, natBytes_size, Nat.add_assoc] at d1 d2 d3
    simp only [getValueBin, bind, Except.bind, d1, d2, d3, encValue, ByteArray.size_append, byteEnc_size, natBytes_size,
      bytesOf_size, Nat.add_assoc]
    rw [sum_bytesOf 32 _ 32 (by omega)]
    have hlt : value.toNat < 256 ^ 32 := by
      have h1 := value.isLt
      have h2 : 2 ^ width ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) hw
      have h3 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
      omega
    rw [Nat.mod_eq_of_lt hlt]
    simp [normalizeValue, pure, Except.pure]
  | @memory width memory =>
    obtain ⟨hw, hlen⟩ := h
    obtain ⟨h12, h3⟩ := At.split hat
    obtain ⟨h1, h2⟩ := At.split h12
    have d1 := getByte_decodes 2 (by decide) data offset h1
    have d2 := natBytes_decodes _ (by omega : width < 2 ^ 64) data _ h2
    simp only [ByteArray.size_append, byteEnc_size, natBytes_size, Nat.add_assoc] at d1 d2 h3
    simp only [getValueBin, bind, Except.bind, d1, d2, encValue, ByteArray.size_append, byteEnc_size, natBytes_size,
      Nat.add_assoc]
    rw [getList_decodes encCell id (Bap.Memory.cells memory) hlen h3]
    · simp [normalizeValue, pure, Except.pure, ByteArray.size_append, natBytes_size]
      omega
    · rintro ⟨a, b⟩ _ dt ot hc
      obtain ⟨c1, c2⟩ := At.split hc
      have hlt : a.toNat < 2 ^ 64 := by
        have h1 := a.isLt
        have h2 : 2 ^ width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
        omega
      have e1 := natBytes_decodes _ hlt dt ot c1
      have e2 := getByte_decodes b.toNat b.toNat_lt dt _ c2
      simp only [e1, e2, bind, Except.bind, pure, Except.pure, encCell, ByteArray.size_append, byteEnc_size]
      simp [id]
      omega

private def encBinding (binding : Bap.Var × Value) : ByteArray :=
  natBytes binding.1.name.utf8ByteSize ++ binding.1.name.toUTF8 ++ encTyp binding.1.typ ++ natBytes binding.1.index ++
    byteEnc (if binding.1.isVirtual then 1 else 0) ++ encValue binding.2

/-- A binding representable in the binary format. -/
def BindingSafe (binding : Bap.Var × Value) : Prop :=
  binding.1.name.utf8ByteSize < 2 ^ 64 ∧ TypSafe binding.1.typ ∧ binding.1.index < 2 ^ 64 ∧ ValueSafe binding.2

private theorem data_putBinding (writer : Writer) (binding : Bap.Var × Value) :
    Writer.data (putBindingBin writer binding) = Writer.data writer ++ encBinding binding := by
  obtain ⟨var, value⟩ := binding
  simp only [putBindingBin, data_putValue, data_putBool, data_putNat, data_putTyp, putText, data_putBytes, encBinding,
    ByteArray.append_assoc]

theorem getBinding_decodes (binding : Bap.Var × Value) (h : BindingSafe binding) :
    Decodes getBindingBin (encBinding binding) (normalizeBinding binding) := by
  intro data offset hat
  obtain ⟨⟨name, typ, index, isVirtual⟩, value⟩ := binding
  obtain ⟨hn, ht, hi, hv⟩ := h
  simp only [encBinding] at hat
  obtain ⟨h5, h6⟩ := At.split hat
  obtain ⟨h4, h45⟩ := At.split h5
  obtain ⟨h3, h34⟩ := At.split h4
  obtain ⟨h2, h23⟩ := At.split h3
  have d1 := getText_decodes name hn data offset h2
  have d2 := getTyp_decodes typ ht data _ h23
  have d3 := natBytes_decodes index hi data _ h34
  have d4 := getBool_decodes isVirtual data _ h45
  have d5 := getValue_decodes value hv data _ h6
  simp only [ByteArray.size_append, Nat.add_assoc] at d1 d2 d3 d4 d5
  simp only [getBindingBin, bind, Except.bind, d1, d2, d3, d4, d5, encBinding, ByteArray.size_append, Nat.add_assoc,
    normalizeBinding]

private def encRegion (region : Bap.Emu.Region) : ByteArray :=
  natBytes region.address ++ byteEnc (if region.protection.readable then 1 else 0) ++
    byteEnc (if region.protection.writable then 1 else 0) ++ byteEnc (if region.protection.executable then 1 else 0) ++
    natBytes region.data.size ++ region.data

/-- A region representable in the binary format. -/
def RegionSafe (region : Bap.Emu.Region) : Prop := region.address < 2 ^ 64 ∧ region.data.size < 2 ^ 64

private theorem data_putRegion (writer : Writer) (region : Bap.Emu.Region) :
    Writer.data (putRegionBin writer region) = Writer.data writer ++ encRegion region := by
  simp only [putRegionBin, data_putBytes, data_putBool, data_putNat, encRegion, ByteArray.append_assoc]

theorem getRegion_decodes (region : Bap.Emu.Region) (h : RegionSafe region) :
    Decodes getRegionBin (encRegion region) region := by
  intro data offset hat
  obtain ⟨address, bytes, ⟨r, w, x⟩⟩ := region
  obtain ⟨ha, hs⟩ := h
  simp only [encRegion] at hat
  obtain ⟨h5, h6⟩ := At.split hat
  obtain ⟨h4, h45⟩ := At.split h5
  obtain ⟨h3, h34⟩ := At.split h4
  obtain ⟨h2, h23⟩ := At.split h3
  obtain ⟨h1, h12⟩ := At.split h2
  have d1 := natBytes_decodes address ha data offset h1
  have d2 := getBool_decodes r data _ h12
  have d3 := getBool_decodes w data _ h23
  have d4 := getBool_decodes x data _ h34
  have d5 := natBytes_decodes _ hs data _ h45
  have d6 := takeBytes_at h6
  simp only [ByteArray.size_append, Nat.add_assoc] at d1 d2 d3 d4 d5 d6
  simp only [getRegionBin, bind, Except.bind, d1, d2, d3, d4, d5, d6, encRegion, ByteArray.size_append, Nat.add_assoc]

private def encThread (context : ThreadContext) : ByteArray :=
  natBytes context.id ++ natBytes context.pc ++ byteEnc (if context.stopped then 1 else 0) ++
    (natBytes context.state.env.length ++ body encBinding context.state.env) ++ encPending context.pending

/-- A thread representable in the binary format. -/
def ThreadSafe (context : ThreadContext) : Prop :=
  context.id < 2 ^ 64 ∧ context.pc < 2 ^ 64 ∧ context.state.env.length < 2 ^ 64 ∧
    (∀ binding ∈ context.state.env, BindingSafe binding) ∧ PendingSafe context.pending

private theorem data_putThread (writer : Writer) (context : ThreadContext) :
    Writer.data (putThreadBin writer context) = Writer.data writer ++ encThread context := by
  simp only [putThreadBin, data_putPending, data_putBool, data_putNat, encThread, ByteArray.append_assoc]
  rw [foldl_writer _ encBinding data_putBinding]
  simp only [data_putBool, data_putNat, ByteArray.append_assoc]

theorem getThread_decodes (context : ThreadContext) (h : ThreadSafe context) :
    Decodes getThreadBin (encThread context) (normalizeThread context) := by
  intro data offset hat
  obtain ⟨id, ⟨env⟩, pc, stopped, pending⟩ := context
  obtain ⟨hi, hp, hl, hb, hq⟩ := h
  simp only [encThread] at hat
  obtain ⟨h4, h5⟩ := At.split hat
  obtain ⟨h3, h34⟩ := At.split h4
  obtain ⟨h2, h23⟩ := At.split h3
  obtain ⟨h1, h12⟩ := At.split h2
  have d1 := natBytes_decodes id hi data offset h1
  have d2 := natBytes_decodes pc hp data _ h12
  have d3 := getBool_decodes stopped data _ h23
  have d4 := getList_decodes (decode := getBindingBin) encBinding normalizeBinding env hl h34
    fun b hb' => getBinding_decodes b (hb b hb')
  have d5 := getPending_decodes pending hq data _ h5
  simp only [ByteArray.size_append, Nat.add_assoc] at d1 d2 d3 d4 d5
  simp only [getThreadBin, bind, Except.bind, d1, d2, d3, d4, d5, encThread, ByteArray.size_append, Nat.add_assoc,
    normalizeThread]

private def encProcess (process : ThreadId × List Bap.Emu.Region) : ByteArray :=
  natBytes process.1 ++ (natBytes process.2.length ++ body encRegion process.2)

/-- A process entry representable in the binary format. -/
def ProcessSafe (process : ThreadId × List Bap.Emu.Region) : Prop :=
  process.1 < 2 ^ 64 ∧ process.2.length < 2 ^ 64 ∧ ∀ region ∈ process.2, RegionSafe region

private theorem data_putProcess (writer : Writer) (process : ThreadId × List Bap.Emu.Region) :
    Writer.data (putProcessBin writer process) = Writer.data writer ++ encProcess process := by
  simp only [putProcessBin, encProcess]
  rw [foldl_writer _ encRegion data_putRegion]
  simp only [data_putNat, ByteArray.append_assoc]

theorem getProcess_decodes (process : ThreadId × List Bap.Emu.Region) (h : ProcessSafe process) :
    Decodes getProcessBin (encProcess process) process := by
  intro data offset hat
  obtain ⟨pid, regions⟩ := process
  obtain ⟨hi, hl, hr⟩ := h
  obtain ⟨h1, h2⟩ := At.split hat
  have d1 := natBytes_decodes pid hi data offset h1
  have d2 := getList_decodes (decode := getRegionBin) encRegion id regions hl h2 fun r hr' => getRegion_decodes r (hr r hr')
  simp only [ByteArray.size_append, Nat.add_assoc, List.map_id] at d1 d2
  simp only [getProcessBin, bind, Except.bind, d1, d2, encProcess, ByteArray.size_append, Nat.add_assoc]

/-- A snapshot representable in the binary format: 64-bit counters, at most 256-bit values, 64-bit addresses. -/
structure SnapshotSafe (snapshot : Snapshot) : Prop where
  pc : snapshot.pc < 2 ^ 64
  regionsLength : snapshot.regions.length < 2 ^ 64
  regions : ∀ region ∈ snapshot.regions, RegionSafe region
  envLength : snapshot.state.env.length < 2 ^ 64
  env : ∀ binding ∈ snapshot.state.env, BindingSafe binding
  threadsLength : snapshot.threads.length < 2 ^ 64
  threads : ∀ thread ∈ snapshot.threads, ThreadSafe thread
  current : snapshot.currentThread < 2 ^ 64
  next : snapshot.nextThread < 2 ^ 64
  pending : PendingSafe snapshot.pending
  processesLength : snapshot.processMemory.length < 2 ^ 64
  processes : ∀ process ∈ snapshot.processMemory, ProcessSafe process

private def encBody (snapshot : Snapshot) : ByteArray :=
  natBytes snapshot.pc ++ byteEnc (if snapshot.stopped then 1 else 0) ++
    (natBytes snapshot.regions.length ++ body encRegion snapshot.regions) ++
    (natBytes snapshot.state.env.length ++ body encBinding snapshot.state.env) ++
    (natBytes snapshot.threads.length ++ body encThread snapshot.threads) ++
    natBytes snapshot.currentThread ++ natBytes snapshot.nextThread ++ encPending snapshot.pending ++
    (natBytes snapshot.processMemory.length ++ body encProcess snapshot.processMemory)

private theorem encodeBinary_eq (snapshot : Snapshot) :
    encodeBinaryUnchecked snapshot = binaryMagic ++ encBody snapshot := by
  simp only [encodeBinaryUnchecked, encBody]
  rw [foldl_writer _ encProcess data_putProcess]
  simp only [data_putPending, data_putNat]
  rw [foldl_writer _ encThread data_putThread]
  simp only [data_putNat]
  rw [foldl_writer _ encBinding data_putBinding]
  simp only [data_putNat]
  rw [foldl_writer _ encRegion data_putRegion]
  simp only [data_putNat, data_putBool, data_putBytes, ByteArray.append_assoc]

private theorem bind_ok_eq {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {v : α} (h : x = .ok v) :
    (x >>= f) = f v := by
  rw [h]
  rfl

private theorem unchecked_roundtrip (snapshot : Snapshot) (h : SnapshotSafe snapshot) :
    decodeBinarySnapshot (encodeBinaryUnchecked snapshot) = .ok (normalizeSnapshot snapshot) := by
  rw [encodeBinary_eq]
  generalize hdata : binaryMagic ++ encBody snapshot = data
  have hmagic : data.extract 0 binaryMagic.size = binaryMagic := by
    rw [← hdata]
    exact ByteArray.extract_append_eq_left rfl
  have hat : At data binaryMagic.size (encBody snapshot) := by
    rw [← hdata]
    refine ⟨by simp [ByteArray.size_append], ?_⟩
    exact ByteArray.extract_append_eq_right rfl rfl
  have hsize : data.size = binaryMagic.size + (encBody snapshot).size := by
    rw [← hdata, ByteArray.size_append]
  have hne : (binaryMagic != binaryMagic) = false := by decide +kernel
  simp only [decodeBinarySnapshot, hmagic, hne, Bool.false_eq_true, ↓reduceIte]
  clear hmagic hdata hne
  generalize binaryMagic.size = start at hat hsize ⊢
  obtain ⟨⟨env⟩, pc, regions, stopped, threads, current, next, pending, processes⟩ := snapshot
  simp only [encBody] at hat hsize
  obtain ⟨h8, h9⟩ := At.split hat
  obtain ⟨h7, h78⟩ := At.split h8
  obtain ⟨h6, h67⟩ := At.split h7
  obtain ⟨h5, h56⟩ := At.split h6
  obtain ⟨h4, h45⟩ := At.split h5
  obtain ⟨h3, h34⟩ := At.split h4
  obtain ⟨h2, h23⟩ := At.split h3
  obtain ⟨h1, h12⟩ := At.split h2
  have d1 := natBytes_decodes pc h.pc data _ h1
  have d2 := getBool_decodes stopped data _ h12
  have d3 := getList_decodes (decode := getRegionBin) encRegion id regions h.regionsLength h23
    fun r hr => getRegion_decodes r (h.regions r hr)
  have d4 := getList_decodes (decode := getBindingBin) encBinding normalizeBinding env h.envLength h34
    fun b hb => getBinding_decodes b (h.env b hb)
  have d5 := getList_decodes (decode := getThreadBin) encThread normalizeThread threads h.threadsLength h45
    fun t ht => getThread_decodes t (h.threads t ht)
  have d6 := natBytes_decodes current h.current data _ h56
  have d7 := natBytes_decodes next h.next data _ h67
  have d8 := getPending_decodes pending h.pending data _ h78
  have d9 := getList_decodes (decode := getProcessBin) encProcess id processes h.processesLength h9
    fun p hp => getProcess_decodes p (h.processes p hp)
  simp only [ByteArray.size_append, natBytes_size, byteEnc_size, Nat.add_assoc, List.map_id] at d1 d2 d3 d4 d5 d6 d7 d8 d9 hsize
  rw [bind_ok_eq d1]
  dsimp only
  rw [bind_ok_eq d2]
  dsimp only
  rw [bind_ok_eq d3]
  dsimp only
  rw [bind_ok_eq d4]
  dsimp only
  rw [bind_ok_eq d5]
  dsimp only
  rw [bind_ok_eq d6]
  dsimp only
  rw [bind_ok_eq d7]
  dsimp only
  rw [bind_ok_eq d8]
  dsimp only
  rw [bind_ok_eq d9]
  dsimp only
  simp only [hsize, Reader.offset, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem fits_pending {pending : Option PendingBranch} (h : pendingFits pending = true) : PendingSafe pending := by
  cases pending with
  | none => trivial
  | some p => simpa [pendingFits, fitsWord, PendingSafe] using h

private theorem fits_typ {typ : Typ} (h : typFits typ = true) : TypSafe typ := by
  cases typ <;> first | trivial | simpa [typFits, fitsWord, TypSafe] using h

private theorem fits_value {value : Value} (h : valueFits value = true) : ValueSafe value := by
  cases value <;> first | trivial | simpa [valueFits, fitsWord, ValueSafe] using h

private theorem fits_binding {binding : Bap.Var × Value} (h : bindingFits binding = true) : BindingSafe binding := by
  simp only [bindingFits, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨by simpa [fitsWord] using h1, fits_typ h2, by simpa [fitsWord] using h3, fits_value h4⟩

private theorem fits_region {region : Bap.Emu.Region} (h : regionFits region = true) : RegionSafe region := by
  simp only [regionFits, Bool.and_eq_true] at h
  exact ⟨by simpa [fitsWord] using h.1, by simpa [fitsWord] using h.2⟩

private theorem fits_thread {context : ThreadContext} (h : threadFits context = true) : ThreadSafe context := by
  simp only [threadFits, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨by simpa [fitsWord] using h1, by simpa [fitsWord] using h2, by simpa [fitsWord] using h3,
    fun b hb => fits_binding (h4 b hb), fits_pending h5⟩

private theorem fits_process {process : ThreadId × List Bap.Emu.Region} (h : processFits process = true) :
    ProcessSafe process := by
  simp only [processFits, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨by simpa [fitsWord] using h1, by simpa [fitsWord] using h2, fun r hr => fits_region (h3 r hr)⟩

private theorem fits_snapshot {snapshot : Snapshot} (h : binaryFits snapshot = true) : SnapshotSafe snapshot := by
  simp only [binaryFits, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨by simpa [fitsWord] using h1, by simpa [fitsWord] using h2, fun r hr => fits_region (h3 r hr),
    by simpa [fitsWord] using h4, fun b hb => fits_binding (h5 b hb), by simpa [fitsWord] using h6,
    fun t ht => fits_thread (h7 t ht), by simpa [fitsWord] using h8, by simpa [fitsWord] using h9, fits_pending h10,
    by simpa [fitsWord] using h11, fun p hp => fits_process (h12 p hp)⟩

private theorem encode_rejects {snapshot : Snapshot} (h : binaryFits snapshot = false) :
    ∃ error, encodeBinarySnapshot snapshot = .error error :=
  ⟨"snapshot has a value too wide for the binary checkpoint format", by simp [encodeBinarySnapshot, h]⟩

/-- Binary checkpoints never truncate: for every snapshot the encoder either refuses it, or its output
decodes back to the snapshot with memory values rebuilt from their sparse cells. This is the codec
`save` and `loadSnapshot` use. -/
theorem binary_lossless_or_rejecting (snapshot : Snapshot) :
    (binaryFits snapshot = false ∧ ∃ error, encodeBinarySnapshot snapshot = .error error) ∨
      ∃ data, encodeBinarySnapshot snapshot = .ok data ∧ decodeBinarySnapshot data = .ok (normalizeSnapshot snapshot) := by
  cases h : binaryFits snapshot with
  | false => exact Or.inl ⟨rfl, encode_rejects h⟩
  | true => exact Or.inr ⟨_, by simp [encodeBinarySnapshot, h], unchecked_roundtrip snapshot (fits_snapshot h)⟩

/-- Values wider than the format's 256-bit slot are refused, not cut down. -/
theorem binary_rejects_wide_bits (snapshot : Snapshot) (var : Bap.Var) {width : Nat} (value : BitVec width)
    (hm : (var, Value.bits value) ∈ snapshot.state.env) (hw : 256 < width) :
    ∃ error, encodeBinarySnapshot snapshot = .error error := by
  have hfits : binaryFits snapshot = false := by
    cases h : binaryFits snapshot with
    | false => rfl
    | true =>
      have := (fits_snapshot h).env _ hm
      have hv : ValueSafe (Value.bits value) := this.2.2.2
      have : width ≤ 256 := hv
      omega
  exact encode_rejects hfits

/-- Fixed-width fields past 64 bits are refused, not wrapped. -/
theorem binary_rejects_wide_pc (snapshot : Snapshot) (hp : 2 ^ 64 ≤ snapshot.pc) :
    ∃ error, encodeBinarySnapshot snapshot = .error error := by
  have hfits : binaryFits snapshot = false := by
    cases h : binaryFits snapshot with
    | false => rfl
    | true =>
      have := (fits_snapshot h).pc
      omega
  exact encode_rejects hfits

end BinaryCheckpoint

/-! ### Shell formatting -/

section Shell

open_private Bap.Emu.Shell Bap.Emu hex byteHex formatValue
open_private Bap.Bil.Wire Bap.Bil.Wire parseHexLoop hexDigit

theorem shell_hex_roundtrip (value : Nat) : Bil.Wire.parseHex (hex value) = .ok value :=
  parseHex_toDigits value

/-- Byte dumps are always exactly two hex digits. -/
theorem byteHex_length (value : UInt8) : (byteHex value).length = 2 := by
  have hb : value.toNat < 256 := value.toNat_lt
  simp only [byteHex, hex]
  by_cases hs : value.toNat < 16
  · have : String.length (String.ofList (Nat.toDigits 16 value.toNat)) < 2 := by
      simp [Nat.toDigits_of_lt_base hs]
    have h0 : "0".length = 1 := by decide
    simp [this, Nat.toDigits_of_lt_base hs, h0]
  · have hdiv : value.toNat / 16 < 16 := by omega
    have hd : Nat.toDigits 16 value.toNat = [Nat.digitChar (value.toNat / 16), Nat.digitChar (value.toNat % 16)] := by
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_right hs, Nat.toDigits_of_lt_base hdiv]
      rfl
    simp [hd]

/-- Byte dumps parse back to the byte. -/
theorem byteHex_roundtrip (value : UInt8) : Bil.Wire.parseHex (byteHex value) = .ok value.toNat := by
  simp only [byteHex, hex]
  by_cases hs : (String.ofList (Nat.toDigits 16 value.toNat)).length < 2
  · simp only [hs, ↓reduceIte]
    have h0 : hexDigit '0' = some 0 := by decide
    have hl : ("0" ++ String.ofList (Nat.toDigits 16 value.toNat)).toList = '0' :: Nat.toDigits 16 value.toNat := by
      simp
    have he : ("0" ++ String.ofList (Nat.toDigits 16 value.toNat)).isEmpty = false := by
      simp
    simp only [Bil.Wire.parseHex, he, Bool.false_eq_true, ↓reduceIte, hl, parseHexLoop, h0]
    simpa using parseHexLoop_toDigits value.toNat
  · simp only [hs, ↓reduceIte]
    exact parseHex_toDigits _

theorem formatValue_bits {width : Nat} (value : BitVec width) :
    formatValue (.bits value) = s!"{width}:0x{hex value.toNat}" := rfl

end Shell

/-! ### Live project merging -/

section Project

open_private Bap.Emu.Project Bap.Emu imageArch imageWidth mergeInstructions mergeEdges mergeDisasm

theorem imageArch_injective (left right : SyscallAbi) (h : imageArch left = imageArch right) : left = right := by
  cases left <;> cases right <;> first | rfl | (simp [imageArch] at h)

theorem imageWidth_ok_iff (config : Config) (width : Nat) :
    imageWidth config = .ok width ↔ config.memory.typ = .mem width 8 := by
  simp only [imageWidth]
  split
  · rename_i w hw
    simp [hw]
  · rename_i hn
    simp only [reduceCtorEq, false_iff]
    exact hn width

/-- A merge step only appends instructions at unseen addresses. -/
private theorem mergeInstructions_foldl (right : List Disasm.Insn) (init : List Disasm.Insn) :
    let result := right.foldl (init := init) fun instructions insn =>
      if instructions.any fun current => current.address == insn.address then instructions
      else instructions ++ [insn]
    init <+: result ∧ (∀ insn ∈ result, insn ∈ init ∨ insn ∈ right) ∧
      (∀ insn ∈ right, ∃ kept ∈ result, kept.address = insn.address) ∧
      ((init.map Disasm.Insn.address).Nodup → (result.map Disasm.Insn.address).Nodup) := by
  induction right generalizing init with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hany
      obtain ⟨h1, h2, h3, h4⟩ := ih init
      refine ⟨h1, ?_, ?_, h4⟩
      · intro insn hi
        rcases h2 insn hi with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro insn hi
        rcases List.mem_cons.1 hi with rfl | hr
        · obtain ⟨k, hk, he⟩ := List.any_eq_true.1 hany
          exact ⟨k, h1.subset hk, by simpa using he⟩
        · exact h3 insn hr
    · rename_i hany
      obtain ⟨h1, h2, h3, h4⟩ := ih (init ++ [head])
      refine ⟨List.IsPrefix.trans (List.prefix_append _ _) h1, ?_, ?_, ?_⟩
      · intro insn hi
        rcases h2 insn hi with h | h
        · rcases List.mem_append.1 h with h' | h'
          · exact Or.inl h'
          · simp only [List.mem_singleton] at h'
            exact Or.inr (by simp [h'])
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro insn hi
        rcases List.mem_cons.1 hi with rfl | hr
        · exact ⟨insn, h1.subset (by simp), rfl⟩
        · exact h3 insn hr
      · intro hnd
        apply h4
        simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.pairwise_append.2 ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ha
        intro he
        apply hany
        exact List.any_eq_true.2 ⟨k, hk, by simpa using he⟩

/-- Merging is left-biased, loses no address, invents no instruction, and keeps addresses unique. -/
theorem mergeInstructions_spec (left right : List Disasm.Insn) :
    left <+: mergeInstructions left right ∧
      (∀ insn ∈ mergeInstructions left right, insn ∈ left ∨ insn ∈ right) ∧
      (∀ insn ∈ right, ∃ kept ∈ mergeInstructions left right, kept.address = insn.address) ∧
      ((left.map Disasm.Insn.address).Nodup → ((mergeInstructions left right).map Disasm.Insn.address).Nodup) :=
  mergeInstructions_foldl right left

private theorem mergeEdges_foldl (right init : List (Nat × Nat)) :
    let result := right.foldl (init := init) fun edges edge =>
      if edges.contains edge then edges else edges ++ [edge]
    (∀ edge, edge ∈ result ↔ edge ∈ init ∨ edge ∈ right) ∧ (init.Nodup → result.Nodup) := by
  induction right generalizing init with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hc
      obtain ⟨h1, h2⟩ := ih init
      refine ⟨?_, h2⟩
      intro edge
      rw [h1, List.mem_cons]
      have hm : head ∈ init := by simpa using hc
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hm
        · exact Or.inr h
    · rename_i hc
      obtain ⟨h1, h2⟩ := ih (init ++ [head])
      refine ⟨?_, ?_⟩
      · intro edge
        rw [h1, List.mem_append, List.mem_singleton, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      · intro hnd
        apply h2
        refine List.pairwise_append.2 ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hc (by simpa using ha)

/-- Edge merging computes the set union without creating duplicates. -/
theorem mergeEdges_spec (left right : List (Nat × Nat)) :
    (∀ edge, edge ∈ mergeEdges left right ↔ edge ∈ left ∨ edge ∈ right) ∧
      (left.Nodup → (mergeEdges left right).Nodup) :=
  mergeEdges_foldl right left

theorem mergeDisasm_entry (left right : Disasm.Disasm) : (mergeDisasm left right).entry = left.entry := rfl

theorem mergeDisasm_errors (left right : Disasm.Disasm) :
    (mergeDisasm left right).errors = left.errors ++ right.errors := rfl

end Project

/-! ### JNI helpers -/

section Jni

open Bap.Emu.Jni
open_private Bap.Emu.Jni Bap.Emu.Jni word branch

theorem arg_in_range (call : Call) (index : Nat) (h : index < call.args.size) : arg call index = call.args[index] := by
  simp [arg, Array.getD, h]

theorem arg_out_of_range (call : Call) (index : Nat) (h : call.args.size ≤ index) : arg call index = 0 := by
  simp [arg, Array.getD, Nat.not_lt.2 h]

theorem word_size (value : Nat) : (word value).size = 8 := rfl

/-- `word` is the little-endian image of the low 64 bits. -/
theorem word_little_endian (value index : Nat) (h : index < 8) :
    (word value)[index]!.toNat = value / 256 ^ index % 256 :=
  bytesOf_get 8 value index h

/-- A branch is always an AArch64 `B` instruction: its top six bits are `000101`. -/
theorem branch_opcode (source target : Nat) : branch source target / 2 ^ 26 = 5 := by
  simp only [branch]
  omega

/-- For an aligned displacement within ±128 MiB the encoded `B` reaches exactly the target. -/
theorem branch_reaches_target (source target : Nat) (aligned : ((target : Int) - source) % 4 = 0)
    (low : -(2 ^ 27 : Int) ≤ (target : Int) - source) (high : (target : Int) - source < 2 ^ 27) :
    let imm : Nat := branch source target % 2 ^ 26
    (if imm ≥ 2 ^ 25 then (imm : Int) - 2 ^ 26 else (imm : Int)) * 4 + (source : Int) = (target : Int) := by
  intro imm
  have himm : imm = (0x14000000 + (((target : Int) - source) / 4 % 0x4000000).toNat) % 2 ^ 26 := rfl
  by_cases hc : imm ≥ 2 ^ 25
  · simp only [hc, ↓reduceIte]
    omega
  · simp only [hc, ↓reduceIte]
    omega

end Jni

end Bap.Proofs.Emu
