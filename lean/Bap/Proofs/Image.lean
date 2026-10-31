import Lean
import Bap.Image.Loader
import Bap.Image.Coff
import Bap.Proofs.Core

namespace Bap.Proofs.Image

open Bap.Image

open Lean in
/-- `open_private Mod Ns x y` makes the private constants `Ns.x`, `Ns.y` of module `Mod` nameable here. -/
local elab "open_private " mod:ident ns:ident names:ident* : command => do
  for name in names do
    let target := mkPrivateNameCore mod.getId (ns.getId ++ name.getId)
    let alias := (← getCurrNamespace) ++ name.getId
    modifyEnv (addAlias · alias target)

open_private Bap.IO.Reader Bap.IO.Reader readLoop

abbrev byteAt (data : ByteArray) (i : Nat) : Nat := (data.get! i).toNat

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} :
    (x >>= f) = .ok v ↔ ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

/-! ## Regions -/

namespace Region

theorem contains_iff {region : MemRegion} {address : Nat} :
    region.contains address = true ↔ region.addr ≤ address ∧ address < region.addr + region.size := by
  simp only [MemRegion.contains, Bool.and_eq_true, decide_eq_true_eq]
  rfl

theorem readByte_of_contains {region : MemRegion} {address : Nat} (h : region.contains address = true) :
    region.readByte address = some (region.data.get! (address - region.addr)) := by
  simp [MemRegion.readByte, h]

theorem readByte_of_not_contains {region : MemRegion} {address : Nat} (h : region.contains address = false) :
    region.readByte address = none := by
  simp [MemRegion.readByte, h]

theorem readByte_isSome_iff {region : MemRegion} {address : Nat} :
    (region.readByte address).isSome = region.contains address := by
  cases h : region.contains address
  · simp [readByte_of_not_contains h]
  · simp [readByte_of_contains h]

/-- Every offset within a region reads the byte at that offset of its contents. -/
theorem readByte_offset (region : MemRegion) {offset : Nat} (h : offset < region.size) :
    region.readByte (region.addr + offset) = some (region.data.get! offset) := by
  rw [readByte_of_contains (MemRegion.contains_offset region offset h), Nat.add_sub_cancel_left]

theorem readByte_below {region : MemRegion} {address : Nat} (h : address < region.addr) :
    region.readByte address = none :=
  readByte_of_not_contains (by simp [MemRegion.contains]; omega)

theorem readByte_above {region : MemRegion} {address : Nat} (h : region.maxAddr ≤ address) :
    region.readByte address = none :=
  readByte_of_not_contains (by simp [MemRegion.contains]; omega)

end Region

/-- Section numbers are 1-based: 0 means no section, and `n + 1` is the entry at position `n`. -/
theorem sectionOfNumber_spec (sections : List Section) (number : Nat) :
    sectionOfNumber sections 0 = none ∧ sectionOfNumber sections (number + 1) = sections[number]? :=
  ⟨rfl, rfl⟩

/-! ## Memory maps -/

namespace Map

theorem mem_lookup {map : MemoryMap α} {address : Nat} {entry : MemRegion × α} :
    entry ∈ map.lookup address ↔ entry ∈ map.entries ∧ entry.1.contains address = true := by
  simp [MemoryMap.lookup]

theorem contains_iff {map : MemoryMap α} {address : Nat} :
    map.contains address = true ↔ ∃ entry ∈ map.entries, entry.1.contains address = true := by
  simp only [MemoryMap.contains, MemoryMap.lookup, Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem,
    List.mem_filter]

/-- `readByte` hits exactly when some region contains the address. -/
theorem readByte_isSome_iff {map : MemoryMap α} {address : Nat} :
    (map.readByte address).isSome = map.contains address := by
  unfold MemoryMap.readByte MemoryMap.contains
  cases h : map.lookup address with
  | nil => simp
  | cons head tail =>
    have hm : head ∈ map.lookup address := by simp [h]
    simp [Region.readByte_isSome_iff, (mem_lookup.mp hm).2]

theorem readByte_eq_none_iff {map : MemoryMap α} {address : Nat} :
    map.readByte address = none ↔ ∀ entry ∈ map.entries, entry.1.contains address = false := by
  rw [← Option.not_isSome_iff_eq_none, readByte_isSome_iff]
  simp [contains_iff]

/-- A read returns the right offset of the first region containing the address. -/
theorem readByte_some {map : MemoryMap α} {address : Nat} {byte : UInt8}
    (h : map.readByte address = some byte) :
    ∃ entry ∈ map.entries, entry.1.contains address = true ∧
      byte = entry.1.data.get! (address - entry.1.addr) := by
  unfold MemoryMap.readByte at h
  cases hl : map.lookup address with
  | nil => simp [hl] at h
  | cons head tail =>
    have hm : head ∈ map.lookup address := by simp [hl]
    have ⟨hmem, hc⟩ := mem_lookup.mp hm
    rw [hl] at h
    simp only [Region.readByte_of_contains hc, Option.some.injEq] at h
    exact ⟨head, hmem, hc, h.symm⟩

/-- A newly added region shadows older ones on its own addresses. -/
theorem readByte_add_hit {region : MemRegion} {value : α} {map : MemoryMap α} {address : Nat}
    (h : region.contains address = true) :
    (map.add region value).readByte address = some (region.data.get! (address - region.addr)) := by
  simp [MemoryMap.readByte, MemoryMap.add, MemoryMap.lookup, h, Region.readByte_of_contains h]

/-- Adding a region leaves every address outside it unchanged. -/
theorem readByte_add_miss {region : MemRegion} {value : α} {map : MemoryMap α} {address : Nat}
    (h : region.contains address = false) :
    (map.add region value).readByte address = map.readByte address := by
  simp [MemoryMap.readByte, MemoryMap.add, MemoryMap.lookup, h]

theorem readByte_empty (address : Nat) : (MemoryMap.empty : MemoryMap α).readByte address = none := rfl

theorem contains_add {region : MemRegion} {value : α} {map : MemoryMap α} {address : Nat} :
    (map.add region value).contains address = (region.contains address || map.contains address) := by
  cases h : region.contains address <;> simp [MemoryMap.contains, MemoryMap.add, MemoryMap.lookup, h]

/-- Folding `add` over regions is how every format decoder builds its map. -/
theorem foldl_add_entries (regions : List MemRegion) (map : MemoryMap Unit) :
    (regions.foldl (fun memory region => MemoryMap.add region () memory) map).entries =
      (regions.reverse.map fun region => (region, ())) ++ map.entries := by
  induction regions generalizing map with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih]
    simp [MemoryMap.add]

/-- For non-empty regions, the `intersections` test is exactly sharing an address. -/
theorem overlap_iff {left right : MemRegion} (hl : 0 < left.size) (hr : 0 < right.size) :
    (left.addr < right.maxAddr ∧ right.addr < left.maxAddr) ↔
      ∃ address, left.contains address = true ∧ right.contains address = true := by
  simp only [Region.contains_iff, MemRegion.maxAddr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨max left.addr right.addr, ?_⟩
    omega
  · rintro ⟨address, h1, h2⟩
    omega

/-- `intersections` and `removeIntersections` partition the map. -/
theorem mem_removeIntersections {map : MemoryMap α} {region : MemRegion} {entry : MemRegion × α} :
    entry ∈ (map.removeIntersections region).entries ↔
      entry ∈ map.entries ∧ entry ∉ map.intersections region := by
  simp only [MemoryMap.removeIntersections, MemoryMap.intersections, List.mem_filter, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, not_and]
  constructor
  · rintro ⟨hm, hd⟩
    exact ⟨hm, fun _ => by omega⟩
  · rintro ⟨hm, hd⟩
    have := hd hm
    exact ⟨hm, by omega⟩

/-- After removal, no remaining region contains any address of the removed span. -/
theorem removeIntersections_disjoint {map : MemoryMap α} {region : MemRegion} {address : Nat}
    (h : region.contains address = true) : (map.removeIntersections region).contains address = false := by
  rw [Bool.eq_false_iff, ne_eq, contains_iff]
  rintro ⟨entry, hm, hc⟩
  simp only [MemoryMap.removeIntersections, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq] at hm
  have h1 := Region.contains_iff.mp h
  have h2 := Region.contains_iff.mp hc
  simp only [MemRegion.maxAddr] at hm
  omega

/-- Addresses outside the removed span read as before only if no intersecting region held them. -/
theorem removeIntersections_preserves {map : MemoryMap α} {region : MemRegion} {entry : MemRegion × α}
    (hm : entry ∈ map.entries) (hd : entry.1.maxAddr ≤ region.addr ∨ region.maxAddr ≤ entry.1.addr) :
    entry ∈ (map.removeIntersections region).entries := by
  simp only [MemoryMap.removeIntersections, List.mem_filter, Bool.or_eq_true, decide_eq_true_eq]
  exact ⟨hm, hd⟩

theorem lookup_mapValues (f : α → β) (map : MemoryMap α) (address : Nat) :
    (map.mapValues f).lookup address = (map.lookup address).map fun entry => (entry.1, f entry.2) := by
  simp [MemoryMap.mapValues, MemoryMap.lookup, List.filter_map, Function.comp_def]

/-- Reads do not observe the region annotations. -/
theorem readByte_mapValues (f : α → β) (map : MemoryMap α) (address : Nat) :
    (map.mapValues f).readByte address = map.readByte address := by
  simp only [MemoryMap.readByte, lookup_mapValues]
  cases map.lookup address <;> simp

theorem contains_mapValues (f : α → β) (map : MemoryMap α) (address : Nat) :
    (map.mapValues f).contains address = map.contains address := by
  simp [MemoryMap.contains, lookup_mapValues]

end Map

/-! ## Raw images -/

namespace RawImage

/-- A raw image maps every input byte at `base + offset`. -/
theorem readByte_offset (data : ByteArray) (base : Nat) (endian : Endian) (width : Nat) {offset : Nat}
    (h : offset < data.size) :
    (Raw.load data base endian width).memory.readByte (base + offset) = some (data.get! offset) := by
  have hc : MemRegion.contains ⟨base, data, true, false, true⟩ (base + offset) = true :=
    MemRegion.contains_offset ⟨base, data, true, false, true⟩ offset h
  simp only [Raw.load]
  rw [Map.readByte_add_hit hc, Nat.add_sub_cancel_left]

/-- A raw image maps nothing outside `[base, base + size)`. -/
theorem readByte_outside (data : ByteArray) (base : Nat) (endian : Endian) (width : Nat) {address : Nat}
    (h : address < base ∨ base + data.size ≤ address) :
    (Raw.load data base endian width).memory.readByte address = none := by
  have hc : MemRegion.contains ⟨base, data, true, false, true⟩ address = false := by
    rw [Bool.eq_false_iff, ne_eq, Region.contains_iff]
    simp only [MemRegion.size]
    omega
  simp only [Raw.load]
  rw [Map.readByte_add_miss hc]
  rfl

theorem contains_iff (data : ByteArray) (base : Nat) (endian : Endian) (width address : Nat) :
    (Raw.load data base endian width).memory.contains address = true ↔
      base ≤ address ∧ address < base + data.size := by
  have hempty : (MemoryMap.empty : MemoryMap Unit).contains address = false := rfl
  simp only [Raw.load, Map.contains_add, hempty, Bool.or_false, Region.contains_iff, MemRegion.size]

/-- The raw segment describes the same span as the mapped region, and the entry is its start. -/
theorem layout (data : ByteArray) (base : Nat) (endian : Endian) (width : Nat) :
    let image := Raw.load data base endian width
    image.entryPoint = base ∧ image.data = data ∧ image.endian = endian ∧ image.addrWidth = width ∧
      image.segments = [⟨"raw", base, data.size, true, false, true⟩] ∧ image.sections = [] ∧
      image.symbols = [] := by
  simp [Raw.load]

/-- Every byte of the input is reachable through its segment. -/
theorem segment_covers_memory (data : ByteArray) (base : Nat) (endian : Endian) (width address : Nat) :
    (Raw.load data base endian width).memory.contains address = true ↔
      ∃ segment ∈ (Raw.load data base endian width).segments,
        segment.addr ≤ address ∧ address < segment.addr + segment.size := by
  rw [contains_iff]
  simp [Raw.load]

end RawImage

/-! ## Reader facts used by the parsers -/

namespace Reader

theorem read_bound {data : ByteArray} {endian : Endian} {offset count value : Nat}
    (h : IO.Reader.read data endian offset count = .ok value) : offset + count ≤ data.size := by
  simp only [IO.Reader.read] at h
  by_cases hb : offset + count > data.size
  · rw [ite_eq_left hb] at h; cases h
  · omega

theorem read_oob {data : ByteArray} {endian : Endian} {offset count : Nat} (h : data.size < offset + count) :
    IO.Reader.read data endian offset count =
      .error s!"{count}-byte read past end of input at {offset}" := by
  simp only [IO.Reader.read]
  rw [ite_eq_left h]

theorem get8_ok {data : ByteArray} {offset value : Nat} (h : IO.Reader.get8 data offset = .ok value) :
    offset < data.size ∧ value = byteAt data offset := by
  simp only [IO.Reader.get8] at h
  by_cases hb : offset ≥ data.size
  · rw [ite_eq_left hb] at h; cases h
  · rw [ite_eq_right hb] at h; cases h; exact ⟨by omega, rfl⟩

theorem get8_of_lt {data : ByteArray} {offset : Nat} (h : offset < data.size) :
    IO.Reader.get8 data offset = .ok (byteAt data offset) := by
  simp only [IO.Reader.get8]
  rw [ite_eq_right (by omega)]

private theorem get8_step {data : ByteArray} {endian : Endian} {offset count index result : Nat}
    (h : offset + index < data.size) :
    readLoop data endian offset count (index + 1) result =
      readLoop data endian offset count index
        (match endian with
         | .little => result + byteAt data (offset + index) * 256 ^ index
         | .big => result + byteAt data (offset + index) * 256 ^ (count - index - 1)) := by
  rw [readLoop, get8_of_lt h]
  rfl

/-- The four-byte big-endian read that detects every magic number here. -/
theorem read_big_four {data : ByteArray} {offset : Nat} (h : offset + 4 ≤ data.size) :
    IO.Reader.read data .big offset 4 =
      .ok (byteAt data (offset + 3) + byteAt data (offset + 2) * 256 + byteAt data (offset + 1) * 65536 +
        byteAt data offset * 16777216) := by
  simp only [IO.Reader.read]
  rw [ite_eq_right (by omega), get8_step (by omega), get8_step (by omega), get8_step (by omega),
    get8_step (by omega)]
  simp only [readLoop, Nat.add_zero]
  congr 1
  omega

theorem read_little_two {data : ByteArray} {offset : Nat} (h : offset + 2 ≤ data.size) :
    IO.Reader.read data .little offset 2 = .ok (byteAt data (offset + 1) * 256 + byteAt data offset) := by
  simp only [IO.Reader.read]
  rw [ite_eq_right (by omega), get8_step (by omega), get8_step (by omega)]
  simp only [readLoop]
  congr 1
  simp

theorem slice_ok {data out : ByteArray} {offset size : Nat} (h : IO.Reader.slice data offset size = .ok out) :
    offset + size ≤ data.size ∧ out = data.extract offset (offset + size) := by
  simp only [IO.Reader.slice] at h
  by_cases hb : offset + size > data.size
  · rw [ite_eq_left hb] at h; cases h
  · rw [ite_eq_right hb] at h; cases h; exact ⟨by omega, rfl⟩

theorem get!_eq_getElem {data : ByteArray} {i : Nat} (h : i < data.size) : data.get! i = data[i] := by
  cases data with
  | mk bytes =>
    show bytes[i]! = bytes[i]
    exact getElem!_pos bytes i h

theorem get!_extract {data : ByteArray} {offset size i : Nat} (h : offset + size ≤ data.size) (hi : i < size) :
    (data.extract offset (offset + size)).get! i = data.get! (offset + i) := by
  have hs : i < (data.extract offset (offset + size)).size := by
    simp only [ByteArray.size_extract]; omega
  rw [get!_eq_getElem hs, get!_eq_getElem (by omega), ByteArray.getElem_extract]

theorem size_extract {data : ByteArray} {offset size : Nat} (h : offset + size ≤ data.size) :
    (data.extract offset (offset + size)).size = size := by
  simp only [ByteArray.size_extract]; omega

theorem size_zeroFilled (file : ByteArray) (extra : Nat) :
    (file.append (ByteArray.mk (Array.replicate extra 0))).size = file.size + extra := by
  show (file ++ ByteArray.mk (Array.replicate extra 0)).size = _
  rw [ByteArray.size_append]
  congr 1
  exact Array.size_replicate

/-- Past the file bytes, a loaded segment reads as zero. -/
theorem get!_zeroFilled_right {file : ByteArray} {extra i : Nat} (h1 : file.size ≤ i) (h2 : i < file.size + extra) :
    (file.append (ByteArray.mk (Array.replicate extra 0))).get! i = 0 := by
  have hs : i < (file ++ ByteArray.mk (Array.replicate extra 0)).size := by
    have := size_zeroFilled file extra
    exact this ▸ h2
  show (file ++ ByteArray.mk (Array.replicate extra 0)).get! i = 0
  rw [get!_eq_getElem hs, ByteArray.getElem_append_right h1]
  simp [ByteArray.getElem_eq_getElem_data]

theorem get!_zeroFilled_left {file : ByteArray} {extra i : Nat} (h : i < file.size) :
    (file.append (ByteArray.mk (Array.replicate extra 0))).get! i = file.get! i := by
  have hs : i < (file ++ ByteArray.mk (Array.replicate extra 0)).size := by
    have := size_zeroFilled file extra
    have : i < file.size + extra := by omega
    rwa [← size_zeroFilled] at this
  show (file ++ ByteArray.mk (Array.replicate extra 0)).get! i = file.get! i
  rw [get!_eq_getElem hs, ByteArray.getElem_append_left h, get!_eq_getElem h]

theorem mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ i (h : i < ys.length) (h' : i < xs.length), f xs[i] = .ok ys[i]
  | [], ys, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun i h => by simp at h⟩
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, bind_ok_iff] at h
    rcases h with ⟨y, hy, zs, hzs, h⟩
    cases h
    have ⟨hl, hi⟩ := mapM_ok hzs
    refine ⟨by simp [hl], ?_⟩
    intro i h h'
    cases i with
    | zero => exact hy
    | succ i => exact hi i (by simpa using h) (by simpa using h')

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl

/-- `bytes` holds `data[offset, offset + fileSize)` followed by zeros, up to `memorySize` in total. -/
def Loaded (bytes data : ByteArray) (offset fileSize memorySize : Nat) : Prop :=
  bytes.size = memorySize ∧ fileSize ≤ memorySize ∧ offset + fileSize ≤ data.size ∧
    (∀ i, i < fileSize → bytes.get! i = data.get! (offset + i)) ∧
    (∀ i, fileSize ≤ i → i < memorySize → bytes.get! i = 0)

theorem loaded_of_slice {data file : ByteArray} {offset fileSize memorySize : Nat}
    (h : IO.Reader.slice data offset fileSize = .ok file) (hm : fileSize ≤ memorySize) :
    Loaded (file.append (ByteArray.mk (Array.replicate (memorySize - fileSize) 0))) data offset fileSize memorySize := by
  have ⟨hb, he⟩ := slice_ok h
  have hs : file.size = fileSize := by rw [he]; exact size_extract hb
  refine ⟨by rw [size_zeroFilled]; omega, hm, hb, ?_, ?_⟩
  · intro i hi
    rw [get!_zeroFilled_left (by omega), he, get!_extract hb hi]
  · intro i h1 h2
    exact get!_zeroFilled_right (by omega) (by omega)

/-- Mapped file bytes read back at their loaded addresses. -/
theorem Loaded.readByte_file {region : MemRegion} {data : ByteArray} {offset fileSize memorySize i : Nat}
    (h : Loaded region.data data offset fileSize memorySize) (hi : i < fileSize) :
    region.readByte (region.addr + i) = some (data.get! (offset + i)) := by
  have ⟨hs, hm, _, hf, _⟩ := h
  rw [Region.readByte_offset region (by simp only [MemRegion.size]; omega), hf i hi]

/-- Memory beyond the file bytes reads as zero. -/
theorem Loaded.readByte_zero {region : MemRegion} {data : ByteArray} {offset fileSize memorySize i : Nat}
    (h : Loaded region.data data offset fileSize memorySize) (h1 : fileSize ≤ i) (h2 : i < memorySize) :
    region.readByte (region.addr + i) = some 0 := by
  have ⟨hs, _, _, _, hz⟩ := h
  rw [Region.readByte_offset region (by simp only [MemRegion.size]; omega), hz i h1 h2]

end Reader

/-! ## Loader dispatch -/

namespace Dispatch

/-- ELF magic selects the ELF decoder. -/
theorem decode_elf {data : ByteArray} (hs : 4 ≤ data.size) (h0 : data.get! 0 = 0x7f) (h1 : data.get! 1 = 0x45)
    (h2 : data.get! 2 = 0x4c) (h3 : data.get! 3 = 0x46) : decode data = Elf.decode data := by
  simp [decode, hs, h0, h1, h2, h3]

/-- `MZ` selects the PE decoder, when the input is not ELF. -/
theorem decode_pe {data : ByteArray} (hs : 2 ≤ data.size) (h0 : data.get! 0 = 0x4d) (h1 : data.get! 1 = 0x5a) :
    decode data = Pe.decode data := by
  simp [decode, hs, h0, h1]

/-- Either byte order of the 64-bit Mach-O magic selects the Mach-O decoder. -/
theorem decode_macho {data : ByteArray} (hs : 4 ≤ data.size)
    (h : (data.get! 0 = 0xcf ∧ data.get! 1 = 0xfa ∧ data.get! 2 = 0xed ∧ data.get! 3 = 0xfe) ∨
      (data.get! 0 = 0xfe ∧ data.get! 1 = 0xed ∧ data.get! 2 = 0xfa ∧ data.get! 3 = 0xcf)) :
    decode data = Macho.decode data := by
  rcases h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> simp [decode, hs, h0, h1, h2, h3]

/-- The dispatcher is exhaustive: every other input is rejected without parsing. -/
theorem decode_unknown {data : ByteArray}
    (helf : ¬ (4 ≤ data.size ∧ data.get! 0 = 0x7f ∧ data.get! 1 = 0x45 ∧ data.get! 2 = 0x4c ∧ data.get! 3 = 0x46))
    (hpe : ¬ (2 ≤ data.size ∧ data.get! 0 = 0x4d ∧ data.get! 1 = 0x5a))
    (hmacho : ¬ (4 ≤ data.size ∧
      ((data.get! 0 = 0xcf ∧ data.get! 1 = 0xfa ∧ data.get! 2 = 0xed ∧ data.get! 3 = 0xfe) ∨
       (data.get! 0 = 0xfe ∧ data.get! 1 = 0xed ∧ data.get! 2 = 0xfa ∧ data.get! 3 = 0xcf)))) :
    decode data = .error "unsupported executable format" := by
  simp only [decode, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, and_assoc]
  rw [ite_eq_right helf, ite_eq_right hpe, ite_eq_right hmacho]

/-- Anything `decode` accepts carries one of the recognized magic numbers. -/
theorem decode_ok_has_magic {data : ByteArray} {image : Image} (h : decode data = .ok image) :
    (4 ≤ data.size ∧ data.get! 0 = 0x7f ∧ data.get! 1 = 0x45 ∧ data.get! 2 = 0x4c ∧ data.get! 3 = 0x46) ∨
      (2 ≤ data.size ∧ data.get! 0 = 0x4d ∧ data.get! 1 = 0x5a) ∨
      (4 ≤ data.size ∧
        ((data.get! 0 = 0xcf ∧ data.get! 1 = 0xfa ∧ data.get! 2 = 0xed ∧ data.get! 3 = 0xfe) ∨
         (data.get! 0 = 0xfe ∧ data.get! 1 = 0xed ∧ data.get! 2 = 0xfa ∧ data.get! 3 = 0xcf))) := by
  by_cases helf : 4 ≤ data.size ∧ data.get! 0 = 0x7f ∧ data.get! 1 = 0x45 ∧ data.get! 2 = 0x4c ∧ data.get! 3 = 0x46
  · exact .inl helf
  by_cases hpe : 2 ≤ data.size ∧ data.get! 0 = 0x4d ∧ data.get! 1 = 0x5a
  · exact .inr (.inl hpe)
  by_cases hmacho : 4 ≤ data.size ∧
      ((data.get! 0 = 0xcf ∧ data.get! 1 = 0xfa ∧ data.get! 2 = 0xed ∧ data.get! 3 = 0xfe) ∨
       (data.get! 0 = 0xfe ∧ data.get! 1 = 0xed ∧ data.get! 2 = 0xfa ∧ data.get! 3 = 0xcf))
  · exact .inr (.inr hmacho)
  rw [decode_unknown helf hpe hmacho] at h
  cases h

theorem decode_short (data : ByteArray) (h : data.size < 2) :
    decode data = .error "unsupported executable format" :=
  decode_unknown (by omega) (by omega) (by omega)

end Dispatch

/-! ## The linker of relocatable ELF files -/

namespace LinkerLaws

open ElfLinker Reader

theorem alignUp_ge (value alignment : Nat) : value ≤ alignUp value alignment := by
  unfold alignUp
  split
  · exact Nat.le_refl _
  · rename_i ha
    have hpos : 0 < alignment := by omega
    have hdiv := Nat.div_add_mod (value + alignment - 1) alignment
    have hmod := Nat.mod_lt (value + alignment - 1) hpos
    have hcomm : (value + alignment - 1) / alignment * alignment = alignment * ((value + alignment - 1) / alignment) :=
      Nat.mul_comm ..
    omega

/-- A region ends before the next one starts. -/
def Before (left right : Region) : Prop := left.addr + left.size ≤ right.addr

/-- The layout so far: regions in reverse, inside `[base, cursor)`, in order and coming from the sections. -/
def LayoutOk (sections : List ElfLinker.Section) (base : Nat) (layout : Layout) : Prop :=
  base ≤ layout.cursor ∧ layout.addrs.size = sections.length ∧
    layout.regions.reverse.Pairwise Before ∧
    (∀ region ∈ layout.regions, base ≤ region.addr ∧ region.addr + region.size ≤ layout.cursor ∧ 0 < region.size ∧
      region.isSection = true) ∧
    ∀ region ∈ layout.regions, ∃ sec ∈ sections, region.name = sec.name ∧ region.size = sec.size ∧
      hasFlag sec.flags shfAlloc = true ∧ region.addr = alignUp region.addr sec.align

theorem alignUp_idempotent (value alignment : Nat) : alignUp (alignUp value alignment) alignment = alignUp value alignment := by
  unfold alignUp
  split
  · rfl
  · rename_i ha
    have hpos : 0 < alignment := by omega
    generalize (value + alignment - 1) / alignment = q
    have hstep : q * alignment + alignment - 1 = (alignment - 1) + alignment * q := by
      rw [Nat.mul_comm q alignment]; omega
    rw [hstep, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega)]
    simp

theorem placeSection_ok {sections : List ElfLinker.Section} {base : Nat} {layout : Layout} (sec : ElfLinker.Section)
    (h : LayoutOk sections base layout) : LayoutOk (sections ++ [sec]) base (placeSection layout sec) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold placeSection
  split
  · rename_i halloc
    have hge := alignUp_ge layout.cursor sec.align
    have hbefore : ∀ region ∈ layout.regions, region.addr + region.size ≤ alignUp layout.cursor sec.align :=
      fun region hr => by have := (h4 region hr).2.1; omega
    refine ⟨by simp only; omega, by simp [h2], ?_, ?_, ?_⟩
    · simp only
      split
      · rw [List.reverse_cons, List.pairwise_append]
        refine ⟨h3, by simp, ?_⟩
        intro left hl right hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact hbefore left (by simpa using hl)
      · exact h3
    · intro region hr
      simp only at hr ⊢
      split at hr
      · rename_i hsize
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨by simp only; omega, by simp, hsize, rfl⟩
        · have ⟨a, b, c, d⟩ := h4 region hr
          exact ⟨a, by omega, c, d⟩
      · have ⟨a, b, c, d⟩ := h4 region hr
        exact ⟨a, by omega, c, d⟩
    · intro region hr
      simp only at hr
      split at hr
      · simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact ⟨sec, by simp, rfl, rfl, halloc, (alignUp_idempotent _ _).symm⟩
        · have ⟨other, ho, a, b, c, d⟩ := h5 region hr
          exact ⟨other, by simp [ho], a, b, c, d⟩
      · have ⟨other, ho, a, b, c, d⟩ := h5 region hr
        exact ⟨other, by simp [ho], a, b, c, d⟩
  · refine ⟨h1, by simp [h2], h3, h4, ?_⟩
    intro region hr
    have ⟨other, ho, a, b, c, d⟩ := h5 region hr
    exact ⟨other, by simp [ho], a, b, c, d⟩

/-- The layout assigns an entry to every section, and allocated sections to regions in order, without overlap. -/
theorem layoutSections_ok (sections : List ElfLinker.Section) (base : Nat) :
    LayoutOk sections base (layoutSections sections base) := by
  have step : ∀ (rest done : List ElfLinker.Section) (layout : Layout), LayoutOk done base layout →
      LayoutOk (done ++ rest) base (rest.foldl placeSection layout) := by
    intro rest
    induction rest with
    | nil => intro done layout h; simpa using h
    | cons sec rest ih =>
      intro done layout h
      have := ih (done ++ [sec]) _ (placeSection_ok sec h)
      simpa using this
  have := step sections [] { cursor := base } ⟨Nat.le_refl _, rfl, by simp, by simp, by simp⟩
  simpa [layoutSections] using this

theorem synthetic_spec {name : String} {start cursor : Nat} {off : Option Nat} {w : Bool} :
    ∀ region ∈ synthetic name start cursor off w, region.addr = start ∧ region.addr + region.size = cursor ∧
      start < cursor := by
  intro region hr
  unfold synthetic at hr
  split at hr
  · rename_i hlt
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨rfl, by simp only; omega, hlt⟩
  · cases hr

theorem placeCommons_mono : ∀ (symbols : List Sym) (commons : Array (Option Nat)) (cursor : Nat),
    cursor ≤ (symbols.foldl (init := (commons, cursor)) fun (commons, cursor) sym =>
      if special sym shnCommon then
        let addr := alignUp cursor sym.value
        (commons.push (some addr), addr + sym.size)
      else
        (commons.push none, cursor)).2
  | [], _, _ => Nat.le_refl _
  | sym :: rest, commons, cursor => by
    simp only [List.foldl_cons]
    split
    · have := placeCommons_mono rest (commons.push (some (alignUp cursor sym.value))) (alignUp cursor sym.value + sym.size)
      have := alignUp_ge cursor sym.value
      simp only at *
      omega
    · exact placeCommons_mono rest _ _

theorem placeExternals_mono {machine word : Nat} : ∀ (symbols : List Sym) (externals : Std.HashMap String Nat) (cursor : Nat),
    cursor ≤ (symbols.foldl (init := (externals, cursor)) fun (externals, cursor) sym =>
      if isExternal machine sym && !externals.contains sym.name then
        let addr := alignUp cursor word
        (externals.insert sym.name addr, addr + word)
      else
        (externals, cursor)).2
  | [], _, _ => Nat.le_refl _
  | sym :: rest, externals, cursor => by
    simp only [List.foldl_cons]
    split
    · have := placeExternals_mono (machine := machine) (word := word) rest
        (externals.insert sym.name (alignUp cursor word)) (alignUp cursor word + word)
      have := alignUp_ge cursor word
      simp only at *
      omega
    · exact placeExternals_mono rest _ _

private theorem pairwise_append_before {left right : List Region} {middle : Nat} (hl : left.Pairwise Before)
    (hr : right.Pairwise Before) (h1 : ∀ region ∈ left, region.addr + region.size ≤ middle)
    (h2 : ∀ region ∈ right, middle ≤ region.addr) : (left ++ right).Pairwise Before := by
  rw [List.pairwise_append]
  refine ⟨hl, hr, ?_⟩
  intro a ha b hb
  have := h1 a ha
  have := h2 b hb
  unfold Before
  omega

private theorem synthetic_pairwise {name : String} {start cursor : Nat} {off : Option Nat} {w : Bool} :
    (synthetic name start cursor off w).Pairwise Before := by
  unfold synthetic
  split <;> simp

/-- The regions of a linked file do not overlap: sections, then commons, externals, and the GOT, in that order. -/
theorem link_regions_disjoint (input : Input) : (link input).regions.Pairwise Before := by
  have hl := layoutSections_ok input.sections.toList input.base
  simp only [link]
  generalize hlayout : layoutSections input.sections.toList input.base = layout at hl
  obtain ⟨_, _, h3, h4, _⟩ := hl
  have hc0 := alignUp_ge layout.cursor (input.width / 8)
  have hc1 := placeCommons_mono input.symbols.toList #[] (alignUp layout.cursor (input.width / 8))
  generalize hcommons : placeCommons input.symbols.toList (alignUp layout.cursor (input.width / 8)) = commons
  have hc1' : alignUp layout.cursor (input.width / 8) ≤ commons.2 := by
    rw [← hcommons]; exact hc1
  have hc2 := alignUp_ge commons.2 (input.width / 8)
  have hc3 := placeExternals_mono (machine := input.machine) (word := input.width / 8) input.symbols.toList {}
    (alignUp commons.2 (input.width / 8))
  generalize hexternals : placeExternals input.machine (input.width / 8) input.symbols.toList
    (alignUp commons.2 (input.width / 8)) = externals
  have hc3' : alignUp commons.2 (input.width / 8) ≤ externals.2 := by
    rw [← hexternals]; exact hc3
  have hc4 := alignUp_ge externals.2 (input.width / 8)
  generalize alignUp externals.2 (input.width / 8) + _ = gotEnd
  have hsections : ∀ region ∈ layout.regions.reverse, region.addr + region.size ≤ alignUp layout.cursor (input.width / 8) := by
    intro region hr
    have := (h4 region (by simpa using hr)).2.1
    omega
  refine pairwise_append_before (middle := alignUp externals.2 (input.width / 8))
    (pairwise_append_before (middle := alignUp commons.2 (input.width / 8))
      (pairwise_append_before (middle := alignUp layout.cursor (input.width / 8)) h3 synthetic_pairwise hsections ?_)
      synthetic_pairwise ?_ ?_) synthetic_pairwise ?_ ?_
  · intro region hr
    exact Nat.le_of_eq (synthetic_spec region hr).1.symm
  · intro region hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hsections region hr
      omega
    · have := (synthetic_spec region hr).2.1
      omega
  · intro region hr
    exact Nat.le_of_eq (synthetic_spec region hr).1.symm
  · intro region hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · have := hsections region hr
        omega
      · have := (synthetic_spec region hr).2.1
        omega
    · have := (synthetic_spec region hr).2.1
      omega
  · intro region hr
    exact Nat.le_of_eq (synthetic_spec region hr).1.symm

/-- The contents of a region are always of its size, whatever the file holds. -/
theorem regionBytes_size (memory : ByteArray) (fileSize : Nat) (region : Region) :
    (regionBytes memory fileSize region).size = region.size := by
  unfold regionBytes
  split
  · show (Array.replicate region.size 0).size = _
    simp
  · rename_i off _
    simp only
    rw [size_zeroFilled]
    simp only [ByteArray.size_extract]
    generalize hl : (if region.isSection = true then min fileSize memory.size else memory.size) = limit
    have hlimit : limit ≤ memory.size := by
      rw [← hl]; split <;> omega
    have hb : min (off + min region.size (limit - off)) memory.size - off = min region.size (limit - off) := by omega
    rw [hb]
    omega

/-- A region reads as its bytes in memory, as far as they go, then as zeros. -/
theorem regionBytes_get {memory : ByteArray} {fileSize off : Nat} {region : Region} (ho : region.off = some off) {i : Nat}
    (hi : i < region.size) :
    let limit := if region.isSection = true then min fileSize memory.size else memory.size
    (i < limit - off → (regionBytes memory fileSize region).get! i = memory.get! (off + i)) ∧
      (limit - off ≤ i → (regionBytes memory fileSize region).get! i = 0) := by
  intro limit
  have hlimit : limit ≤ memory.size := by
    show (if region.isSection = true then min fileSize memory.size else memory.size) ≤ _
    split <;> omega
  have hdef : regionBytes memory fileSize region =
      (memory.extract off (off + min region.size (limit - off))).append
        (ByteArray.mk (Array.replicate (region.size - min region.size (limit - off)) 0)) := by
    unfold regionBytes
    simp only [ho]
    rfl
  have hfile : (memory.extract off (off + min region.size (limit - off))).size = min region.size (limit - off) := by
    simp only [ByteArray.size_extract]
    omega
  rw [hdef]
  constructor
  · intro hl
    have hin : i < min region.size (limit - off) := by omega
    rw [get!_zeroFilled_left (by omega), get!_extract (by omega) hin]
  · intro hl
    exact get!_zeroFilled_right (by omega) (by omega)

theorem regionBytes_unmapped {memory : ByteArray} {fileSize : Nat} {region : Region} (ho : region.off = none) {i : Nat}
    (hi : i < region.size) : (regionBytes memory fileSize region).get! i = 0 := by
  have hdef : regionBytes memory fileSize region = ByteArray.mk (Array.replicate region.size 0) := by
    unfold regionBytes
    simp only [ho]
  rw [hdef]
  show (Array.replicate region.size (0 : UInt8))[i]! = 0
  rw [getElem!_pos (Array.replicate region.size (0 : UInt8)) i (by simpa using hi)]
  simp

/-- A linked segment and its mapped region describe the same memory. -/
theorem toSegment_toMemRegion (memory : ByteArray) (fileSize : Nat) (region : Region) :
    (toSegment region).addr = (toMemRegion memory fileSize region).addr ∧
      (toSegment region).size = (toMemRegion memory fileSize region).size ∧
      (toSegment region).readable = (toMemRegion memory fileSize region).readable ∧
      (toSegment region).writable = (toMemRegion memory fileSize region).writable ∧
      (toSegment region).executable = (toMemRegion memory fileSize region).executable :=
  ⟨rfl, (regionBytes_size memory fileSize region).symm, rfl, rfl, rfl⟩

/-! ### Fields -/

theorem field_lt (value : Int) (lo n : Nat) : field value lo n < 2 ^ n := by
  unfold field
  have hpos : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.pow_pos (by decide)
  have h1 := Int.emod_lt_of_pos (value >>> lo) hpos
  have h2 := Int.emod_nonneg (value >>> lo) (Int.ne_of_gt hpos)
  omega

/-- The low `m + 8` bits of a value are its low `m` bits and the byte above them. -/
theorem field_succ (value : Int) (m : Nat) :
    field value 0 (m + 8) = field value 0 m + field value m 8 * 2 ^ m := by
  have hP : (0 : Int) < ((2 ^ m : Nat) : Int) := by exact_mod_cast Nat.pow_pos (by decide)
  have hQ : (0 : Int) < ((2 ^ 8 : Nat) : Int) := by decide
  have hcast : ((2 ^ (m + 8) : Nat) : Int) = ((2 ^ m : Nat) : Int) * ((2 ^ 8 : Nat) : Int) := by
    rw [Nat.pow_add]; simp
  have hshift : value >>> m = value / ((2 ^ m : Nat) : Int) := by
    rw [Int.shiftRight_eq_div_pow]
  have hzero : value >>> 0 = value := by
    rw [Int.shiftRight_eq_div_pow]; simp
  unfold field
  rw [hzero, hshift, hcast]
  generalize hPdef : ((2 ^ m : Nat) : Int) = P at *
  generalize hQdef : ((2 ^ 8 : Nat) : Int) = Q at *
  have h1 := Int.emod_add_mul_ediv value P
  have h2 := Int.emod_add_mul_ediv (value / P) Q
  have ha0 := Int.emod_nonneg value (Int.ne_of_gt hP)
  have ha1 := Int.emod_lt_of_pos value hP
  have hb0 := Int.emod_nonneg (value / P) (Int.ne_of_gt hQ)
  have hb1 := Int.emod_lt_of_pos (value / P) hQ
  generalize ha : value % P = a at *
  generalize hb : (value / P) % Q = b at *
  generalize hc : (value / P) / Q = c at *
  generalize hq : value / P = q at *
  have hvalue : value = (a + P * b) + P * Q * c := by
    rw [← h1, ← h2, Int.mul_add, Int.mul_assoc, Int.add_assoc]
  have hbound : P * b ≤ P * (Q - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hb0' : 0 ≤ P * b := Int.mul_nonneg (by omega) hb0
  rw [Int.mul_sub, Int.mul_one] at hbound
  have hmod : value % (P * Q) = a + P * b := by
    rw [hvalue, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hmod]
  have e1 : ((a.toNat : Nat) : Int) = a := Int.toNat_of_nonneg ha0
  have e2 : ((b.toNat : Nat) : Int) = b := Int.toNat_of_nonneg hb0
  have hcast2 : ((a + P * b).toNat : Int) = ((a.toNat + b.toNat * 2 ^ m : Nat) : Int) := by
    rw [Int.toNat_of_nonneg (by omega), Int.natCast_add, Int.natCast_mul, e1, e2, hPdef, Int.mul_comm b P]
  exact Int.ofNat.inj hcast2

/-! ### Stores -/

theorem get!_set! (bytes : ByteArray) (i j : Nat) (value : UInt8) (hi : i < bytes.size) :
    (bytes.set! i value).get! j = if i = j then value else bytes.get! j := by
  cases bytes with
  | mk array =>
    have hi : i < array.size := hi
    show (array.setIfInBounds i value)[j]! = if i = j then value else array[j]!
    by_cases hj : j < array.size
    · have hj' : j < (array.setIfInBounds i value).size := by simpa using hj
      rw [getElem!_pos (array.setIfInBounds i value) j hj', getElem!_pos array j hj,
        Array.getElem_setIfInBounds hj]
    · have hne : ¬ i = j := by omega
      rw [ite_eq_right hne, getElem!_neg (array.setIfInBounds i value) j (by simpa using hj),
        getElem!_neg array j hj]

theorem size_set! (bytes : ByteArray) (i : Nat) (value : UInt8) : (bytes.set! i value).size = bytes.size := by
  cases bytes
  show (Array.setIfInBounds _ _ _).size = _
  simp
  rfl

/-- The position of byte `index` of an `n`-byte number. -/
def bytePosition (little : Bool) (n index : Nat) : Nat := if little then index else n - index - 1

private def writesUpTo (memory : ByteArray) (little : Bool) (off n : Nat) (value : Int) (k : Nat) : ByteArray :=
  (List.range k).foldl (init := memory) fun result index =>
    result.set! (off + index) (UInt8.ofNat (field value (8 * if little then index else n - index - 1) 8))

private theorem writesUpTo_succ (memory : ByteArray) (little : Bool) (off n : Nat) (value : Int) (k : Nat) :
    writesUpTo memory little off n value (k + 1) =
      (writesUpTo memory little off n value k).set! (off + k)
        (UInt8.ofNat (field value (8 * if little then k else n - k - 1) 8)) := by
  simp [writesUpTo, List.range_succ, List.foldl_append]

private theorem writesUpTo_spec {memory : ByteArray} {little : Bool} {off n : Nat} {value : Int} :
    ∀ k, off + k ≤ memory.size →
      (writesUpTo memory little off n value k).size = memory.size ∧
      (∀ j, j < off ∨ off + k ≤ j → (writesUpTo memory little off n value k).get! j = memory.get! j) ∧
      ∀ i, i < k → ((writesUpTo memory little off n value k).get! (off + i)).toNat =
        field value (8 * bytePosition little n i) 8
  | 0, _ => ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  | k + 1, hb => by
    have ⟨hs, hf, hw⟩ := writesUpTo_spec (memory := memory) (little := little) (off := off) (n := n) (value := value) k
      (by omega)
    rw [writesUpTo_succ]
    have hlt : off + k < (writesUpTo memory little off n value k).size := by omega
    refine ⟨by rw [size_set!, hs], ?_, ?_⟩
    · intro j hj
      rw [get!_set! _ _ _ _ hlt, ite_eq_right (by omega), hf j (by omega)]
    · intro i hi
      rw [get!_set! _ _ _ _ hlt]
      by_cases hik : i = k
      · subst hik
        simp only [↓reduceIte]
        have hu := field_lt value (8 * if little then i else n - i - 1) 8
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hu]
        rfl
      · rw [ite_eq_right (by omega), hw i (by omega)]

/-- A store of `n` in-range bytes changes exactly those, to the bytes of the value in the file's order. -/
theorem writeNat_spec {memory : ByteArray} {little : Bool} {off n : Nat} {value : Int} (h : off + n ≤ memory.size) :
    (writeNat memory little off n value).size = memory.size ∧
      (∀ j, j < off ∨ off + n ≤ j → (writeNat memory little off n value).get! j = memory.get! j) ∧
      ∀ i, i < n → ((writeNat memory little off n value).get! (off + i)).toNat =
        field value (8 * bytePosition little n i) 8 :=
  writesUpTo_spec n h

def foldWrites (memory : ByteArray) (writes : List Write) : ByteArray :=
  writes.foldl (init := memory) fun memory write =>
    writeNat memory write.little write.off write.n write.value

theorem commit_run (site : Site) (writes : List Write) (state : LinkState) :
    (commit site writes).run state =
      if writes.all (fun write => site.off ≤ write.off && write.off + write.n ≤ site.limit &&
          write.off + write.n ≤ state.memory.size) = true then
        .ok () { state with memory := foldWrites state.memory writes, applied := (site, writes) :: state.applied }
      else .error (outside site) state := by
  show commit site writes state = _
  simp only [commit, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  split <;> rfl

theorem commit_fold : ∀ (writes : List Write) (memory : ByteArray),
    (∀ write ∈ writes, write.off + write.n ≤ memory.size) →
    let result := writes.foldl (init := memory) fun memory write =>
      writeNat memory write.little write.off write.n write.value
    result.size = memory.size ∧
      ∀ j, (∀ write ∈ writes, j < write.off ∨ write.off + write.n ≤ j) → result.get! j = memory.get! j
  | [], _, _ => ⟨rfl, fun _ _ => rfl⟩
  | write :: rest, memory, h => by
    have ⟨s1, f1, _⟩ := writeNat_spec (little := write.little) (value := write.value) (h write (by simp))
    have ⟨s2, f2⟩ := commit_fold rest (writeNat memory write.little write.off write.n write.value) (by
      intro other ho
      rw [s1]
      exact h other (by simp [ho]))
    refine ⟨s2.trans s1, ?_⟩
    intro j hj
    rw [List.foldl_cons, f2 j (fun other ho => hj other (by simp [ho])), f1 j (hj write (by simp))]

/-- All the stores of a committed site stay in its section, and everything else in memory is left alone. -/
theorem commit_ok {site : Site} {writes : List Write} {state after : LinkState} {result : Unit}
    (h : (commit site writes).run state = .ok result after) :
    after.memory.size = state.memory.size ∧
      (∀ j, (∀ write ∈ writes, j < write.off ∨ write.off + write.n ≤ j) → after.memory.get! j = state.memory.get! j) ∧
      ∀ write ∈ writes, site.off ≤ write.off ∧ write.off + write.n ≤ site.limit := by
  rw [commit_run] at h
  split at h
  · rename_i hall
    cases h
    have hb : ∀ write ∈ writes, site.off ≤ write.off ∧ write.off + write.n ≤ site.limit ∧
        write.off + write.n ≤ state.memory.size := by
      intro write hw
      have := List.all_eq_true.mp hall write hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have ⟨s, f⟩ := commit_fold writes state.memory fun write hw => (hb write hw).2.2
    exact ⟨s, f, fun write hw => ⟨(hb write hw).1, (hb write hw).2.1⟩⟩
  · cases h

/-- A site out of its section stores nothing. -/
theorem commit_outside {site : Site} {writes : List Write} {state : LinkState} {write : Write} (hw : write ∈ writes)
    (hout : site.limit < write.off + write.n) :
    (commit site writes).run state = .error (outside site) state := by
  rw [commit_run, ite_eq_right]
  intro hall
  have := List.all_eq_true.mp hall write hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

private theorem readNat_little_fold {memory : ByteArray} {off : Nat} {value : Int} :
    ∀ k, (∀ i, i < k → (memory.get! (off + i)).toNat = field value (8 * i) 8) →
      (List.range k).foldl (init := 0) (fun sum index => sum + (memory.get! (off + index)).toNat * 256 ^ index) =
        field value 0 (8 * k)
  | 0, _ => by
    simp [field]
  | k + 1, h => by
    rw [List.range_succ, List.foldl_append, readNat_little_fold k (fun i hi => h i (by omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h k (by omega), show 8 * (k + 1) = 8 * k + 8 by omega, field_succ, Nat.pow_mul]

/-- A little-endian store reads back as the value, cut to its width. -/
theorem readNat_writeNat_little {memory : ByteArray} {off n : Nat} {value : Int} (h : off + n ≤ memory.size) :
    readNat (writeNat memory true off n value) true off n = field value 0 (8 * n) := by
  have ⟨_, _, hw⟩ := writeNat_spec (little := true) (value := value) h
  simp only [readNat, ↓reduceIte]
  exact readNat_little_fold n fun i hi => by
    rw [hw i hi]
    simp [bytePosition]

/-- `value` and its two's complement field agree modulo the width, and it is back in range. -/
theorem sext_range (value : Int) {n : Nat} (hn : 0 < n) :
    -((2 ^ (n - 1) : Nat) : Int) ≤ sext value n ∧ sext value n < ((2 ^ (n - 1) : Nat) : Int) := by
  have hl := field_lt value 0 n
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  unfold sext
  simp only
  split <;> omega

/-! ### Handlers -/

/-- `R_X86_64_PC32`: S + A - P in 4 bytes. -/
theorem x86_64_pc32 {env : Env} {site : Site} (ht : site.rel.typ = 2) (state : LinkState) :
    (x86_64 env site).run state = .ok (some [stAt env site 0 4 (site.s + site.a - site.p)]) state := by
  simp only [x86_64, ht]
  rfl

/-- `R_X86_64_PC32` end to end: once committed, the place holds S + A - P, cut to 32 bits. -/
theorem x86_64_pc32_resolves {env : Env} {site : Site} {state after : LinkState} {result : Unit}
    (hl : env.little = true) (hb : site.off + 4 ≤ state.memory.size)
    (h : (commit site [stAt env site 0 4 (site.s + site.a - site.p)]).run state = .ok result after) :
    readNat after.memory true site.off 4 = field (site.s + site.a - site.p) 0 32 := by
  rw [commit_run] at h
  split at h
  · cases h
    change readNat (writeNat state.memory env.little (site.off + 0) 4 (site.s + site.a - site.p)) true site.off 4 = _
    rw [hl]
    exact readNat_writeNat_little (off := site.off) (n := 4) hb
  · cases h

/-- Loads are in the section or not at all. -/
theorem load_run (site : Site) (at' n : Nat) (little : Bool) (state : LinkState) :
    (load site at' n little).run state =
      if inSection site at' n state.memory.size = true then
        .ok (readNat state.memory little (site.off + at') n) state
      else .error (outside site) state := by
  show load site at' n little state = _
  simp only [ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  split <;> rfl

/-- The same value always shares its GOT entry. -/
theorem gotEntry_hit {env : Env} {value : Int} {state : LinkState} {slot : Nat}
    (h : state.got[field value 0 64]? = some slot) :
    (gotEntry env value).run state = .ok (slot : Int) state := by
  show gotEntry env value state = _
  simp only [gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h]
  rfl

/-- A new GOT entry is the next word after the entries so far. -/
theorem gotEntry_new {env : Env} {value : Int} {state after : LinkState} {slot : Int}
    (h : state.got[field value 0 64]? = none) (hr : (gotEntry env value).run state = .ok slot after) :
    slot = (env.gotBase + state.gotCount * (env.width / 8) : Nat) ∧ after.gotCount = state.gotCount + 1 := by
  change gotEntry env value state = _ at hr
  simp only [gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h] at hr
  cases hr
  exact ⟨rfl, rfl⟩

/-! ### Fields as bits

`field` and `setBits` are what the handlers cut values and patch instructions with. The theorems about instructions below
all come from what they say of bits: a field holds what was put in it, and the rest of the word is left alone. -/

theorem shiftRight_toDiv (v : Int) (lo : Nat) : v >>> lo = v / ((2 ^ lo : Nat) : Int) := by
  rw [Int.shiftRight_eq_div_pow]

theorem field_natCast (x lo n : Nat) : field (x : Int) lo n = x / 2 ^ lo % 2 ^ n := by
  unfold field
  rw [shiftRight_toDiv]
  have : ((x : Int) / ((2 ^ lo : Nat) : Int)) % ((2 ^ n : Nat) : Int) = ((x / 2 ^ lo % 2 ^ n : Nat) : Int) := by
    rw [Int.natCast_emod, Int.natCast_ediv]
  rw [this, Int.toNat_natCast]

theorem testBit_field (x j m i : Nat) :
    (field (x : Int) j m).testBit i = (decide (i < m) && x.testBit (j + i)) := by
  rw [field_natCast, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i j]

/-- A number below `2 ^ n` is its own low `n` bits. -/
theorem field_of_lt {x n : Nat} (h : x < 2 ^ n) : field (x : Int) 0 n = x := by
  rw [field_natCast]
  simp [Nat.mod_eq_of_lt h]

/-- Replacing the bits leaves the bits below and above them, as a sum of its parts. -/
theorem setBits_eq (w lo n : Nat) (v : Int) :
    setBits w lo n v = 2 ^ lo * (2 ^ n * (w / 2 ^ lo / 2 ^ n) + field v 0 n) + w % 2 ^ lo := by
  unfold setBits
  rw [field_natCast]
  have h1 := Nat.div_add_mod w (2 ^ lo)
  have h2 := Nat.div_add_mod (w / 2 ^ lo) (2 ^ n)
  generalize w / 2 ^ lo % 2 ^ n = m at *
  generalize w / 2 ^ lo / 2 ^ n = t at *
  generalize w % 2 ^ lo = r at *
  generalize w / 2 ^ lo = d at *
  subst h2
  subst h1
  simp only [Nat.mul_add, Nat.mul_comm m, Nat.mul_comm (field v 0 n)]
  omega

theorem testBit_setBits (w lo n : Nat) (v : Int) (i : Nat) :
    (setBits w lo n v).testBit i =
      if i < lo then w.testBit i else if i < lo + n then (field v 0 n).testBit (i - lo) else w.testBit i := by
  rw [setBits_eq, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos lo)),
    Nat.testBit_two_pow_mul_add _ (field_lt v 0 n), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow]
  by_cases h : i < lo
  · simp [h]
  · simp only [h, ite_false]
    by_cases h2 : i < lo + n
    · have : i - lo < n := by omega
      simp [h2, this]
    · have : ¬ i - lo < n := by omega
      simp only [h2, this, ite_false]
      congr 1
      omega

/-- A replaced field holds the low bits of the value. -/
theorem field_setBits_self (w lo n : Nat) (v : Int) : field (setBits w lo n v : Nat) lo n = field v 0 n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_field, testBit_setBits]
  by_cases h : i < n
  · have h1 : ¬ lo + i < lo := by omega
    have h2 : lo + i < lo + n := by omega
    simp [h, h1, h2]
  · simp only [h, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (field_lt v 0 n) (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- The other bits stay: a field that does not overlap the replaced one. -/
theorem field_setBits_other (w lo n : Nat) (v : Int) (j m : Nat) (h : j + m ≤ lo ∨ lo + n ≤ j) :
    field (setBits w lo n v : Nat) j m = field (w : Int) j m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_field, testBit_field, testBit_setBits]
  by_cases hi : i < m
  · have : ¬ (j + i < lo) → ¬ (j + i < lo + n) := by omega
    by_cases h1 : j + i < lo
    · simp [h1]
    · simp [h1, this h1]
  · simp [hi]

/-- Patching a word never makes it wider than its field reach. -/
theorem setBits_lt {w lo n k : Nat} (v : Int) (hw : w < 2 ^ k) (h : lo + n ≤ k) : setBits w lo n v < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_setBits]
  have h1 : ¬ j < lo := by omega
  have h2 : ¬ j < lo + n := by omega
  simp only [h1, h2, ite_false]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) hj))

/-- A shift only moves the bits a field reads. -/
theorem field_shiftRight (v : Int) (k lo n : Nat) : field (v >>> k) lo n = field v (k + lo) n := by
  unfold field
  rw [Int.shiftRight_add]

/-- Fields split: the bits of a run are those of its low part and those above them. -/
theorem field_split (value : Int) (a n m : Nat) :
    field value a (n + m) = field value a n + field value (a + n) m * 2 ^ n := by
  have hP : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.pow_pos (by decide)
  have hQ : (0 : Int) < ((2 ^ m : Nat) : Int) := by exact_mod_cast Nat.pow_pos (by decide)
  have hcast : ((2 ^ (n + m) : Nat) : Int) = ((2 ^ n : Nat) : Int) * ((2 ^ m : Nat) : Int) := by
    rw [Nat.pow_add]; simp
  have hshift : value >>> (a + n) = (value >>> a) / ((2 ^ n : Nat) : Int) := by
    rw [Int.shiftRight_add, shiftRight_toDiv]
  unfold field
  rw [hshift, hcast]
  generalize value >>> a = u
  generalize hPdef : ((2 ^ n : Nat) : Int) = P at *
  generalize hQdef : ((2 ^ m : Nat) : Int) = Q at *
  have h1 := Int.emod_add_mul_ediv u P
  have h2 := Int.emod_add_mul_ediv (u / P) Q
  have ha0 := Int.emod_nonneg u (Int.ne_of_gt hP)
  have ha1 := Int.emod_lt_of_pos u hP
  have hb0 := Int.emod_nonneg (u / P) (Int.ne_of_gt hQ)
  have hb1 := Int.emod_lt_of_pos (u / P) hQ
  generalize ha : u % P = a' at *
  generalize hb : (u / P) % Q = b at *
  generalize hc : (u / P) / Q = c at *
  generalize hq : u / P = q at *
  have hvalue : u = (a' + P * b) + P * Q * c := by
    rw [← h1, ← h2, Int.mul_add, Int.mul_assoc, Int.add_assoc]
  have hbound : P * b ≤ P * (Q - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have hb0' : 0 ≤ P * b := Int.mul_nonneg (by omega) hb0
  rw [Int.mul_sub, Int.mul_one] at hbound
  have hmod : u % (P * Q) = a' + P * b := by
    rw [hvalue, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [hmod]
  have e1 : ((a'.toNat : Nat) : Int) = a' := Int.toNat_of_nonneg ha0
  have e2 : ((b.toNat : Nat) : Int) = b := Int.toNat_of_nonneg hb0
  have hcast2 : ((a' + P * b).toNat : Int) = ((a'.toNat + b.toNat * 2 ^ n : Nat) : Int) := by
    rw [Int.toNat_of_nonneg (by omega), Int.natCast_add, Int.natCast_mul, e1, e2, hPdef, Int.mul_comm b P]
  exact Int.ofNat.inj hcast2

/-- The low bits of a value, shifted down, are the middle bits of the value. -/
theorem field_low_shift (value : Int) (s m : Nat) : field value 0 (s + m) >>> s = field value s m := by
  rw [Nat.shiftRight_eq_div_pow, field_split, Nat.zero_add]
  have hlt := field_lt value 0 s
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos s), Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- What `sext` of a value says, in the arithmetic of integers. -/
theorem sext_eq (value : Int) {n : Nat} (hn : 0 < n) :
    sext value n = (value + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) - ((2 ^ (n - 1) : Nat) : Int) := by
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hzero : value >>> 0 = value := by rw [Int.shiftRight_eq_div_pow]; simp
  have hHalf : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos (n - 1)
  have hP : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by rw [hp]; simp
  have hfield : field value 0 n = (value % ((2 ^ n : Nat) : Int)).toNat := by
    unfold field
    rw [hzero]
  unfold sext
  rw [hfield]
  dsimp only
  rw [hP] at hfield ⊢
  have hnat : (2 ^ n : Nat) = 2 ^ n := rfl
  generalize hH : ((2 ^ (n - 1) : Nat) : Int) = H at *
  have h0 := Int.emod_nonneg value (by omega : 2 * H ≠ 0)
  have h1 := Int.emod_lt_of_pos value (by omega : 0 < 2 * H)
  have hto : ((value % (2 * H)).toNat : Int) = value % (2 * H) := Int.toNat_of_nonneg h0
  have hdiv := Int.emod_add_mul_ediv value (2 * H)
  have hmodAdd : (value + H) % (2 * H) = if value % (2 * H) < H then value % (2 * H) + H else value % (2 * H) - H := by
    generalize value % (2 * H) = r at *
    generalize value / (2 * H) = q at *
    have hv : value + H = (if r < H then r + H else r - H) + (2 * H) * (if r < H then q else q + 1) := by
      split
      · rw [← hdiv]; omega
      · rw [← hdiv, Int.mul_add, Int.mul_one]; omega
    rw [hv, Int.add_mul_emod_self_left]
    split <;> exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmodAdd]
  have hcast : ((2 ^ n : Nat) : Int) = 2 * H := hP
  split
  · rename_i hc
    have hc' : ((2 ^ n : Nat) : Int) ≤ 2 * ((value % (2 * H)).toNat : Int) := by exact_mod_cast hc
    rw [hcast, hto] at hc'
    have hr : ¬ value % (2 * H) < H := by omega
    simp only [hr, ite_false, hto]
    omega
  · rename_i hc
    have hc' : ¬ ((2 ^ n : Nat) : Int) ≤ 2 * ((value % (2 * H)).toNat : Int) := by
      intro h
      exact hc (by exact_mod_cast h)
    rw [hcast, hto] at hc'
    have hr : value % (2 * H) < H := by omega
    simp only [hr, ite_true, hto]
    omega


/-! ### Reading back -/

private theorem readNat_big_fold {memory : ByteArray} {off n : Nat} {value : Int} :
    ∀ k, k ≤ n → (∀ i, i < k → (memory.get! (off + i)).toNat = field value (8 * (n - i - 1)) 8) →
      (List.range k).foldl (init := 0)
          (fun sum index => sum + (memory.get! (off + index)).toNat * 256 ^ (n - index - 1)) =
        field value (8 * (n - k)) (8 * k) * 256 ^ (n - k)
  | 0, _, _ => by
    simp [field]
  | k + 1, hk, h => by
    rw [List.range_succ, List.foldl_append, readNat_big_fold k (by omega) (fun i hi => h i (by omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [h k (by omega)]
    have hr : n - k = (n - k - 1) + 1 := by omega
    have hr2 : n - (k + 1) = n - k - 1 := by omega
    rw [hr2, hr]
    generalize n - k - 1 = r
    have e1 : 8 * (r + 1) = 8 * r + 8 := by omega
    have e2 : 8 * (k + 1) = 8 + 8 * k := by omega
    have hs : r + 1 - 1 = r := by omega
    rw [e1, e2, field_split, Nat.pow_succ]
    simp only [hs]
    have : (2 : Nat) ^ 8 = 256 := rfl
    rw [this, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ r), ← Nat.mul_assoc, Nat.add_comm]

/-- A store reads back as the value cut to its width, in either byte order. -/
theorem readNat_writeNat {memory : ByteArray} {little : Bool} {off n : Nat} {value : Int} (h : off + n ≤ memory.size) :
    readNat (writeNat memory little off n value) little off n = field value 0 (8 * n) := by
  cases little with
  | true => exact readNat_writeNat_little h
  | false =>
    have ⟨_, _, hw⟩ := writeNat_spec (little := false) (value := value) h
    simp only [readNat, Bool.false_eq_true, ↓reduceIte]
    have hb : ∀ i, i < n → ((writeNat memory false off n value).get! (off + i)).toNat =
        field value (8 * (n - i - 1)) 8 := fun i hi => by rw [hw i hi]; simp [bytePosition]
    rw [readNat_big_fold n (Nat.le_refl n) hb]
    simp

/-- A big-endian store reads back as the value cut to its width. -/
theorem readNat_writeNat_big {memory : ByteArray} {off n : Nat} {value : Int} (h : off + n ≤ memory.size) :
    readNat (writeNat memory false off n value) false off n = field value 0 (8 * n) :=
  readNat_writeNat h

/-- Reads of a range are not affected by what is written outside of it. -/
theorem readNat_congr {a b : ByteArray} {little : Bool} {off n : Nat}
    (h : ∀ i, i < n → a.get! (off + i) = b.get! (off + i)) : readNat a little off n = readNat b little off n := by
  unfold readNat
  have key : ∀ (l : List Nat) (init : Nat), (∀ i ∈ l, i < n) →
      l.foldl (init := init) (fun value index => value + (a.get! (off + index)).toNat * 256 ^ (if little then index else n - index - 1)) =
      l.foldl (init := init) (fun value index => value + (b.get! (off + index)).toNat * 256 ^ (if little then index else n - index - 1)) := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons x xs ih =>
      intro init hl
      simp only [List.foldl_cons]
      rw [h x (hl x (by simp))]
      exact ih _ fun i hi => hl i (by simp [hi])
  exact key _ _ fun i hi => List.mem_range.1 hi

theorem foldWrites_read : ∀ (writes : List Write) (memory : ByteArray) (write : Write),
    write ∈ writes → (∀ w ∈ writes, w.off + w.n ≤ memory.size) →
    writes.Pairwise (fun a b => a.off + a.n ≤ b.off ∨ b.off + b.n ≤ a.off) →
    readNat (writes.foldl (init := memory) fun memory write =>
      writeNat memory write.little write.off write.n write.value) write.little write.off write.n =
        field write.value 0 (8 * write.n)
  | [], _, _, hm, _, _ => by cases hm
  | w :: rest, memory, write, hm, hb, hp => by
    have ⟨s1, f1, _⟩ := writeNat_spec (little := w.little) (value := w.value) (hb w (by simp))
    have hb' : ∀ x ∈ rest, x.off + x.n ≤ (writeNat memory w.little w.off w.n w.value).size := by
      intro x hx
      rw [s1]
      exact hb x (by simp [hx])
    have ⟨hd, hrest⟩ := List.pairwise_cons.1 hp
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hm with rfl | hmem
    · rw [readNat_congr (b := writeNat memory write.little write.off write.n write.value)]
      · exact readNat_writeNat (hb _ (by simp))
      · intro i hi
        have ⟨_, hf⟩ := (commit_fold rest _ hb')
        exact hf _ fun o ho => by
          rcases hd o ho with h | h <;> omega
    · exact foldWrites_read rest _ write hmem hb' hrest

/-- The stores of a site that do not overlap each read back as their values, whatever their byte order. -/
theorem commit_read_back {site : Site} {writes : List Write} {state after : LinkState} {result : Unit} {write : Write}
    (h : (commit site writes).run state = .ok result after) (hw : write ∈ writes)
    (hp : writes.Pairwise (fun a b => a.off + a.n ≤ b.off ∨ b.off + b.n ≤ a.off)) :
    readNat after.memory write.little write.off write.n = field write.value 0 (8 * write.n) := by
  rw [commit_run] at h
  split at h
  · rename_i hall
    cases h
    exact foldWrites_read writes state.memory write hw (fun w hx => by
      have := List.all_eq_true.mp hall w hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2) hp
  · cases h

/-- A value stored at a place, end to end: once committed, the place holds it cut to the width of the store. -/
theorem store_resolves {env : Env} {site : Site} {n : Nat} {value : Int} {state after : LinkState} {result : Unit}
    (h : (commit site [stAt env site 0 n value]).run state = .ok result after) :
    readNat after.memory env.little (site.off + 0) n = field value 0 (8 * n) :=
  commit_read_back (write := stAt env site 0 n value) h (by simp) (by simp)

/-- The same of an instruction word, in the byte order of instructions. -/
theorem code_resolves {env : Env} {site : Site} {n : Nat} {value : Int} {state after : LinkState} {result : Unit}
    (h : (commit site [stiAt env site 0 n value]).run state = .ok result after) :
    readNat after.memory env.codeLittle (site.off + 0) n = field value 0 (8 * n) :=
  commit_read_back (write := stiAt env site 0 n value) h (by simp) (by simp)

/-- A new entry of the GOT is written at the end of what the file and the GOT so far take up, and holds its value. -/
theorem gotEntry_new_holds {env : Env} {value : Int} {state after : LinkState} {slot : Int}
    (h : state.got[field value 0 64]? = none) (hr : (gotEntry env value).run state = .ok slot after) :
    readNat after.memory env.little (env.gotOff + state.gotCount * (env.width / 8)) (env.width / 8) =
      field value 0 (8 * (env.width / 8)) := by
  change gotEntry env value state = _ at hr
  simp only [gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h] at hr
  cases hr
  apply readNat_writeNat
  have key : ∀ (l : List Nat) (m : ByteArray), (l.foldl (init := m) fun memory _ => memory.push 0).size = m.size + l.length := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons x xs ih =>
      intro m
      simp only [List.foldl_cons]
      rw [ih]
      simp [ByteArray.size_push]
      omega
  rw [key]
  simp only [List.length_range]
  omega

/-! ### What the relocations store

The tables are the calculation columns of each psABI, with `S`, `A`, `P` and `GOT`. A handler does what its table says. -/

/-- Running a load inside of the section gives the bytes that are there, and changes nothing. -/
theorem ld_ok {env : Env} {site : Site} {at' n : Nat} {state : LinkState}
    (h : inSection site at' n state.memory.size = true) :
    ld env site at' n state = .ok (readNat state.memory env.little (site.off + at') n) state := by
  simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, h, ite_true]
  rfl

/-- The relocations of x86-64 from the psABI, `Z` being the size of the symbol, that need no entry in the GOT. -/
def x86_64Abi (s a p got z : Int) : Nat → Option (Nat × Int)
  | 1 => some (8, s + a)
  | 2 | 4 => some (4, s + a - p)
  | 10 | 11 => some (4, s + a)
  | 12 => some (2, s + a)
  | 13 => some (2, s + a - p)
  | 14 => some (1, s + a)
  | 15 => some (1, s + a - p)
  | 24 => some (8, s + a - p)
  | 25 | 31 => some (8, s + a - got)
  | 26 => some (4, got + a - p)
  | 29 => some (8, got + a - p)
  | 32 => some (4, z + a)
  | 33 => some (8, z + a)
  | _ => none

theorem x86_64_abi {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState)
    (h : x86_64Abi site.s site.a site.p env.gotBase site.sym.size site.rel.typ = some (n, value)) :
    (x86_64 env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold x86_64Abi at h
  split at h <;> cases h <;> (simp only [x86_64, ht]; try rfl)

/-- The relocations of x86-64 through the GOT: `G + GOT` is the address `slot` of the entry of the symbol. -/
def x86_64GotAbi (slot a p got : Int) : Nat → Option (Nat × Int)
  | 3 => some (4, slot - got + a)
  | 9 | 41 | 42 | 43 => some (4, slot + a - p)
  | 27 | 30 => some (8, slot - got + a)
  | 28 => some (8, slot + a - p)
  | _ => none

theorem x86_64_got {env : Env} {site : Site} {n : Nat} {value slot : Int} {state after : LinkState}
    (hg : gotEntry env site.s state = .ok slot after)
    (h : x86_64GotAbi slot site.a site.p env.gotBase site.rel.typ = some (n, value)) :
    (x86_64 env site).run state = .ok (some [stAt env site 0 n value]) after := by
  generalize ht : site.rel.typ = t at h
  unfold x86_64GotAbi at h
  split at h <;> cases h <;> (simp only [x86_64, ht, EStateM.run, bind, EStateM.bind, hg, done, pure, EStateM.pure]; try rfl)

/-- The relocations of i386 from the psABI, as a function of the addend. -/
def i386Abi (s p got : Int) : Nat → Option (Nat × (Int → Int))
  | 1 => some (4, fun a => s + a)
  | 2 | 4 => some (4, fun a => s + a - p)
  | 9 => some (4, fun a => s + a - got)
  | 10 => some (4, fun a => got + a - p)
  | 20 => some (2, fun a => s + a)
  | 21 => some (2, fun a => s + a - p)
  | 22 => some (1, fun a => s + a)
  | 23 => some (1, fun a => s + a - p)
  | _ => none

/-- The addend of a place in `n` bytes: of the record, or sign-extended from the place. -/
def placeAddend (env : Env) (site : Site) (state : LinkState) (n : Nat) : Int :=
  if site.rel.isExplicit then site.a else sext (readNat state.memory env.little (site.off + 0) n) (8 * n)

theorem i386_abi {env : Env} {site : Site} {n : Nat} {f : Int → Int} {state : LinkState}
    (hb : inSection site 0 n state.memory.size = true)
    (h : i386Abi site.s site.p env.gotBase site.rel.typ = some (n, f)) :
    (i386 env site).run state = .ok (some [stAt env site 0 n (f (placeAddend env site state n))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold i386Abi at h
  split at h <;> cases h <;> (cases he : site.rel.isExplicit <;>
         simp only [i386, ht, EStateM.run, bind, EStateM.bind, he, done, pure, EStateM.pure, placeAddend, ld, ElfLinker.load,
           get, getThe, MonadStateOf.get, EStateM.get, hb, ite_true, ite_false, Bool.false_eq_true] <;> rfl)

/-- `R_386_GOT32`, `R_386_GOT32X`: `G + A - GOT`, the same formula with or without relaxing. -/
theorem i386_got {env : Env} {site : Site} {slot : Int} {state after : LinkState}
    (hg : gotEntry env site.s state = .ok slot after) (ht : site.rel.typ = 3 ∨ site.rel.typ = 43)
    (hb : inSection site 0 4 after.memory.size = true) :
    (i386 env site).run state =
      .ok (some [stAt env site 0 4 (slot + placeAddend env site after 4 - env.gotBase)]) after := by
  rcases ht with ht | ht <;>
    cases he : site.rel.isExplicit <;>
      simp only [i386, ht, EStateM.run, bind, EStateM.bind, he, hg, done, pure, EStateM.pure, placeAddend, ld, ElfLinker.load,
        get, getThe, MonadStateOf.get, EStateM.get, hb, ite_true, ite_false, Bool.false_eq_true] <;> rfl

/-- The data relocations of AArch64, with `X = S + A`. -/
def aarch64Data (x p : Int) : Nat → Option (Nat × Int)
  | 0x101 => some (8, x)
  | 0x102 => some (4, x)
  | 0x103 => some (2, x)
  | 0x104 => some (8, x - p)
  | 0x105 | 0x13a => some (4, x - p)
  | 0x106 => some (2, x - p)
  | _ => none

theorem aarch64_data {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState)
    (h : aarch64Data (site.s + site.a) site.p site.rel.typ = some (n, value)) :
    (aarch64 env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold aarch64Data at h
  split at h <;> cases h <;> (simp only [aarch64, ht]; try rfl)

/-- The instruction relocations of AArch64: `MOVW_UABS_G*` take 16 bits of `X`, the branches and literals the displacement
in words, `ADRP` the distance in pages, and the rest the low bits of `X` scaled by the access. -/
def aarch64Code (x p : Int) : Nat → Option (Nat → Nat)
  | 0x107 | 0x108 => some fun i => setBits i 5 16 (x >>> 0)
  | 0x109 | 0x10a => some fun i => setBits i 5 16 (x >>> 16)
  | 0x10b | 0x10c => some fun i => setBits i 5 16 (x >>> 32)
  | 0x10d => some fun i => setBits i 5 16 (x >>> 48)
  | 0x111 | 0x118 => some fun i => setBits i 5 19 ((x - p) >>> 2)
  | 0x112 => some (aarch64Adr (x - p))
  | 0x113 | 0x114 => some (aarch64Adr ((aarch64Page x - aarch64Page p) >>> 12))
  | 0x115 | 0x116 => some (aarch64Lo12 0 x)
  | 0x117 => some fun i => setBits i 5 14 ((x - p) >>> 2)
  | 0x11a | 0x11b => some fun i => setBits i 0 26 ((x - p) >>> 2)
  | 0x11c => some (aarch64Lo12 1 x)
  | 0x11d => some (aarch64Lo12 2 x)
  | 0x11e => some (aarch64Lo12 3 x)
  | 0x12b => some (aarch64Lo12 4 x)
  | _ => none

theorem aarch64_code {env : Env} {site : Site} {f : Nat → Nat} {state : LinkState}
    (hb : inSection site 0 4 state.memory.size = true)
    (h : aarch64Code (site.s + site.a) site.p site.rel.typ = some f) :
    (aarch64 env site).run state =
      .ok (some [stiAt env site 0 4 (f (readNat state.memory env.codeLittle (site.off + 0) 4))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold aarch64Code at h
  split at h <;> cases h <;> (simp only [aarch64, ht, EStateM.run, ldi, ElfLinker.load, done, bind, EStateM.bind, get, getThe, MonadStateOf.get,
         EStateM.get, hb, ite_true, pure, EStateM.pure]; try rfl)

/-- The relocations of AArch64 through the GOT. The entry holds `X`, as `lld` also has it. -/
def aarch64GotCode (slot p : Int) : Nat → Option (Nat → Nat)
  | 0x135 => some fun i => setBits i 5 19 ((slot - p) >>> 2)
  | 0x137 => some (aarch64Adr ((aarch64Page slot - aarch64Page p) >>> 12))
  | 0x138 => some (aarch64Lo12 3 slot)
  | _ => none

theorem aarch64_got_code {env : Env} {site : Site} {f : Nat → Nat} {slot : Int} {state after : LinkState}
    (hg : gotEntry env (site.s + site.a) state = .ok slot after)
    (hb : inSection site 0 4 after.memory.size = true)
    (h : aarch64GotCode slot site.p site.rel.typ = some f) :
    (aarch64 env site).run state =
      .ok (some [stiAt env site 0 4 (f (readNat after.memory env.codeLittle (site.off + 0) 4))]) after := by
  generalize ht : site.rel.typ = t at h
  unfold aarch64GotCode at h
  split at h <;> cases h <;> (simp only [aarch64, ht, EStateM.run, ldi, ElfLinker.load, done, bind, EStateM.bind, get, getThe, MonadStateOf.get,
         EStateM.get, hg, hb, ite_true, pure, EStateM.pure]; try rfl)

/-- `R_AARCH64_GOTPCREL32`: the entry of `S` from the place, plus `A`. -/
theorem aarch64_gotpcrel32 {env : Env} {site : Site} {slot : Int} {state after : LinkState}
    (hg : gotEntry env site.s state = .ok slot after) (ht : site.rel.typ = 0x13b) :
    (aarch64 env site).run state = .ok (some [stAt env site 0 4 (slot + site.a - site.p)]) after := by
  simp only [aarch64, ht, EStateM.run, bind, EStateM.bind, hg, done, pure, EStateM.pure]

/-! ### The instructions they patch -/

/-- `ADR` and `ADRP` hold a value in `immhi:immlo`, and the rest of the instruction stays. -/
theorem aarch64Adr_spec (value : Int) (insn : Nat) :
    field (aarch64Adr value insn : Nat) 5 19 * 4 + field (aarch64Adr value insn : Nat) 29 2 = field value 0 21 ∧
      ∀ j m, (j + m ≤ 5 ∨ (24 ≤ j ∧ j + m ≤ 29) ∨ 31 ≤ j) →
        field (aarch64Adr value insn : Nat) j m = field (insn : Int) j m := by
  unfold aarch64Adr
  constructor
  · rw [field_setBits_self, field_setBits_other _ _ _ _ _ _ (by omega), field_setBits_self, field_shiftRight,
      Nat.add_zero]
    have h : field value 0 21 = field value 0 2 + field value 2 19 * 2 ^ 2 := field_split value 0 2 19
    omega
  · intro j m h
    rw [field_setBits_other _ _ _ _ _ _ (by omega), field_setBits_other _ _ _ _ _ _ (by omega)]

/-- The offset of an `ADD` or a load is the bits of the low 12 of a value that the scale of the access does not drop,
and the rest of the instruction stays. -/
theorem aarch64Lo12_spec (shift m : Nat) (hm : shift + m = 12) (value : Int) (insn : Nat) :
    field (aarch64Lo12 shift value insn : Nat) 10 12 = field value shift m ∧
      ∀ j k, (j + k ≤ 10 ∨ 22 ≤ j) → field (aarch64Lo12 shift value insn : Nat) j k = field (insn : Int) j k := by
  unfold aarch64Lo12
  have h12 : field value 0 12 = field value 0 (shift + m) := by rw [hm]
  constructor
  · rw [field_setBits_self, h12, field_low_shift]
    apply field_of_lt
    exact Nat.lt_of_lt_of_le (field_lt value shift m) (Nat.pow_le_pow_right (by decide) (by omega))
  · intro j k h
    exact field_setBits_other _ _ _ _ _ _ (by omega)

/-- A page is its value with the low bits clear, so the distance of `ADRP` and the low 12 bits rebuild the address. -/
theorem aarch64_page_rebuild (x p : Int) :
    ∃ q : Int, aarch64Page p + (aarch64Page x - aarch64Page p) + field x 0 12 = x ∧ aarch64Page x = 4096 * q := by
  have hf : (field x 0 12 : Int) = x % 4096 := by
    unfold field
    have hzero : x >>> 0 = x := by rw [Int.shiftRight_eq_div_pow]; simp
    rw [hzero]
    have h0 : (0 : Int) ≤ x % ((2 ^ 12 : Nat) : Int) := Int.emod_nonneg _ (by decide)
    rw [Int.toNat_of_nonneg h0]
    rfl
  refine ⟨x / 4096, ?_, ?_⟩
  · unfold aarch64Page
    omega
  · unfold aarch64Page
    omega


/-! ### ARM and Thumb -/

/-- Rewrites the fields of patched words to what they hold. -/
local macro "bits_step" : tactic =>
  `(tactic| first
    | rw [field_setBits_self]
    | rw [field_setBits_other _ _ _ _ _ _ (by omega)]
    | rw [field_shiftRight])

local macro "bits" : tactic =>
  `(tactic| ((repeat bits_step); (try simp only [Nat.add_zero, Nat.reduceAdd, Nat.zero_add])))

/-- Runs a handler, in terms of what it loads. -/
local macro "link_run" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [EStateM.run, ldi, ld, ldInt, ElfLinker.load, done, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, ite_true, ite_false, Bool.false_eq_true, $ts,*])

/-- A branch's immediate, doubled or more, holds an even value of its range. -/
theorem sext_natCast_field (value : Int) (n : Nat) : sext (field value 0 n : Nat) n = sext value n := by
  unfold sext
  simp only []
  rw [field_of_lt (field_lt value 0 n)]

theorem sext_of_range {value : Int} {n : Nat} (hn : 0 < n)
    (h1 : -((2 ^ (n - 1) : Nat) : Int) ≤ value) (h2 : value < ((2 ^ (n - 1) : Nat) : Int)) : sext value n = value := by
  rw [sext_eq value hn]
  have hp : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [this]
    simp
  rw [hp, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- What a branch or literal decodes to, when its value is aligned and in range, is the value: nothing was lost. -/
theorem sext_scaled_of_range {value : Int} {k m : Nat} (hm : 0 < k + m) (hal : field value 0 k = 0)
    (h1 : -((2 ^ (k + m - 1) : Nat) : Int) ≤ value) (h2 : value < ((2 ^ (k + m - 1) : Nat) : Int)) :
    sext (field value k m * 2 ^ k : Nat) (k + m) = value := by
  have : field value k m * 2 ^ k = field value 0 (k + m) := by
    rw [field_split]
    simp [hal]
  rw [this, sext_natCast_field, sext_of_range hm h1 h2]

private theorem bit_flip_lt (x s : Nat) : 1 - (x ^^^ s) < 2 ^ 1 := by
  omega

private theorem bit_flip_twice {x s : Nat} (hx : x < 2) (hs : s < 2) : 1 - ((1 - (x ^^^ s)) ^^^ s) = x := by
  have h1 : x = 0 ∨ x = 1 := by omega
  have h2 : s = 0 ∨ s = 1 := by omega
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rfl

/-- An A32 `MOVW` or `MOVT` holds 16 bits in `imm4:imm12`, and the rest of the instruction stays. -/
theorem armMovSet_spec (word : Nat) (value : Int) :
    armMovImm (armMovSet word value) = field value 0 16 ∧
      ∀ j m, ((12 ≤ j ∧ j + m ≤ 16) ∨ 20 ≤ j) → field (armMovSet word value : Nat) j m = field (word : Int) j m := by
  unfold armMovImm armMovSet
  constructor
  · bits
    have h : field value 0 16 = field value 0 12 + field value 12 4 * 2 ^ 12 := field_split value 0 12 4
    omega
  · intro j m h
    bits

/-- A T32 `MOVW` or `MOVT` holds 16 bits in `imm4:i:imm3:imm8`, and the rest of the instructions stay. -/
theorem thumbMovSet_spec (hw1 hw2 : Nat) (value : Int) :
    thumbMovImm (thumbMovSet1 hw1 value) (thumbMovSet2 hw2 value) = field value 0 16 ∧
      (∀ j m, ((4 ≤ j ∧ j + m ≤ 10) ∨ 11 ≤ j) → field (thumbMovSet1 hw1 value : Nat) j m = field (hw1 : Int) j m) ∧
      (∀ j m, ((8 ≤ j ∧ j + m ≤ 12) ∨ 15 ≤ j) → field (thumbMovSet2 hw2 value : Nat) j m = field (hw2 : Int) j m) := by
  unfold thumbMovImm thumbMovSet1 thumbMovSet2
  refine ⟨?_, ?_, ?_⟩
  · bits
    have h1 : field value 0 16 = field value 0 8 + field value 8 8 * 2 ^ 8 := field_split value 0 8 8
    have h2 : field value 8 8 = field value 8 3 + field value 11 5 * 2 ^ 3 := field_split value 8 3 5
    have h3 : field value 11 5 = field value 11 1 + field value 12 4 * 2 ^ 1 := field_split value 11 1 4
    omega
  · intro j m h
    bits
  · intro j m h
    bits

/-- An A32 branch holds a value in words, and its condition and opcode stay. -/
theorem armBranchSet_spec (word : Nat) (value : Int) :
    armBranchImm (armBranchSet word value) = sext (field value 2 24 * 2 ^ 2 : Nat) 26 ∧
      ∀ j m, 24 ≤ j → field (armBranchSet word value : Nat) j m = field (word : Int) j m := by
  unfold armBranchImm armBranchSet
  constructor
  · bits
  · intro j m h
    bits

/-- The offset of a T32 `BL` or `B.W`, undoing the `I = NOT(J XOR S)` of the encoding, and the opcode bits stay. -/
theorem thumbBranchSet_spec (hw1 hw2 : Nat) (value : Int) :
    thumbBranchImm (thumbBranchSet1 hw1 value) (thumbBranchSet2 hw2 value) = sext (field value 1 24 * 2 ^ 1 : Nat) (1 + 24) ∧
      (∀ j m, 11 ≤ j → field (thumbBranchSet1 hw1 value : Nat) j m = field (hw1 : Int) j m) ∧
      (∀ j m, (j = 12 ∧ m ≤ 1 ∨ 14 ≤ j) → field (thumbBranchSet2 hw2 value : Nat) j m = field (hw2 : Int) j m) := by
  unfold thumbBranchImm thumbBranchSet1 thumbBranchSet2
  refine ⟨?_, ?_, ?_⟩
  · simp only []
    bits
    rw [field_of_lt (bit_flip_lt _ _), field_of_lt (bit_flip_lt _ _),
      bit_flip_twice (field_lt value 23 1) (field_lt value 24 1), bit_flip_twice (field_lt value 22 1) (field_lt value 24 1)]
    have h1 : field value 1 24 = field value 1 11 + field value 12 13 * 2 ^ 11 := field_split value 1 11 13
    have h2 : field value 12 13 = field value 12 10 + field value 22 3 * 2 ^ 10 := field_split value 12 10 3
    have h3 : field value 22 3 = field value 22 1 + field value 23 2 * 2 ^ 1 := field_split value 22 1 2
    have h4 : field value 23 2 = field value 23 1 + field value 24 1 * 2 ^ 1 := field_split value 23 1 1
    congr 2
    omega
  · intro j m h
    bits
  · intro j m h
    simp only []
    bits

/-- The offset of a T32 conditional `B.W`, and the condition and opcode bits stay. -/
theorem thumbJump19Set_spec (hw1 hw2 : Nat) (value : Int) :
    thumbJump19Imm (thumbJump19Set1 hw1 value) (thumbJump19Set2 hw2 value) = sext (field value 1 20 * 2 ^ 1 : Nat) (1 + 20) ∧
      (∀ j m, ((6 ≤ j ∧ j + m ≤ 10) ∨ 11 ≤ j) → field (thumbJump19Set1 hw1 value : Nat) j m = field (hw1 : Int) j m) ∧
      (∀ j m, (j = 12 ∧ m ≤ 1 ∨ 14 ≤ j) → field (thumbJump19Set2 hw2 value : Nat) j m = field (hw2 : Int) j m) := by
  unfold thumbJump19Imm thumbJump19Set1 thumbJump19Set2
  refine ⟨?_, ?_, ?_⟩
  · bits
    have h1 : field value 1 20 = field value 1 11 + field value 12 9 * 2 ^ 11 := field_split value 1 11 9
    have h2 : field value 12 9 = field value 12 6 + field value 18 3 * 2 ^ 6 := field_split value 12 6 3
    have h3 : field value 18 3 = field value 18 1 + field value 19 2 * 2 ^ 1 := field_split value 18 1 2
    have h4 : field value 19 2 = field value 19 1 + field value 20 1 * 2 ^ 1 := field_split value 19 1 1
    congr 2
    omega
  · intro j m h
    bits
  · intro j m h
    bits

/-- The offset of a narrow Thumb branch. -/
theorem thumbShortSet_spec (n word : Nat) (value : Int) :
    thumbShortImm n (thumbShortSet n word value) = sext (field value 1 n * 2 : Nat) (n + 1) ∧
      ∀ j m, n ≤ j → field (thumbShortSet n word value : Nat) j m = field (word : Int) j m := by
  unfold thumbShortImm thumbShortSet
  constructor
  · rw [field_setBits_self, field_shiftRight, Nat.add_zero]
  · intro j m h
    exact field_setBits_other _ _ _ _ _ _ (by omega)

/-- `(S + A) | T`. The Thumb bit is set if the symbol is Thumb code, and the value is otherwise as it was. -/
theorem armWithT_spec (site : Site) (value : Int) :
    armWithT site value = if isThumb site.sym = true && value % 2 == 0 then value + 1 else value := rfl

/-- The relocations of ARM that store a value, from the ABI for the Arm architecture, as functions of the addend. -/
def armData (site : Site) (got : Int) : Nat → Option (Nat × (Int → Int))
  | 2 | 0x26 => some (4, fun a => armWithT site (armS site + a))
  | 3 => some (4, fun a => armWithT site (armS site + a) - site.p)
  | 5 => some (2, fun a => armS site + a)
  | 8 => some (1, fun a => armS site + a)
  | 0x18 => some (4, fun a => armS site + a - got)
  | 0x19 => some (4, fun a => got + a - site.p)
  | _ => none

theorem arm_data {env : Env} {site : Site} {n : Nat} {f : Int → Int} {state : LinkState}
    (hb : inSection site 0 n state.memory.size = true)
    (h : armData site env.gotBase site.rel.typ = some (n, f)) :
    (arm env site).run state = .ok (some [stAt env site 0 n
      (f (addendOf site (sext (readNat state.memory env.little (site.off + 0) n) (8 * n))))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold armData at h
  split at h <;> cases h <;> (link_run [arm, ht, hb]; try rfl)

/-- `R_ARM_GOT_BREL`: `GOT(S) + A - GOT_ORG`. -/
theorem arm_got_brel {env : Env} {site : Site} {slot : Int} {state after : LinkState}
    (hg : gotEntry env (armWithT site (armS site)) state = .ok slot after) (ht : site.rel.typ = 0x1a)
    (hb : inSection site 0 4 after.memory.size = true) :
    (arm env site).run state = .ok (some [stAt env site 0 4
      (slot + addendOf site (sext (readNat after.memory env.little (site.off + 0) 4) 32) - env.gotBase)]) after := by
  link_run [arm, ht, hb, hg]

/-- `R_ARM_GOT_PREL`, and `R_ARM_TARGET2` that means it on Linux: `GOT(S) + A - P`. -/
theorem arm_got_prel {env : Env} {site : Site} {slot : Int} {state after : LinkState}
    (hg : gotEntry env (armWithT site (armS site)) state = .ok slot after) (ht : site.rel.typ = 0x60 ∨ site.rel.typ = 0x29)
    (hb : inSection site 0 4 after.memory.size = true) :
    (arm env site).run state = .ok (some [stAt env site 0 4
      (slot + addendOf site (sext (readNat after.memory env.little (site.off + 0) 4) 32) - site.p)]) after := by
  rcases ht with ht | ht <;> link_run [arm, ht, hb, hg]

/-- `R_ARM_PREL31`: `((S + A) | T) - P` in 31 bits, keeping the top bit. -/
theorem arm_prel31 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 0x2a)
    (hb : inSection site 0 4 state.memory.size = true) :
    (arm env site).run state = .ok (some [stAt env site 0 4 (setBits (readNat state.memory env.little (site.off + 0) 4) 0 31
      (armWithT site (armS site + addendOf site
        (sext (field (readNat state.memory env.little (site.off + 0) 4 : Nat) 0 31) 31)) - site.p) : Nat)]) state := by
  link_run [arm, ht, hb]
  try rfl

/-- The value of each of the `MOVW` and `MOVT` relocations of ARM, `R_ARM_MOVW_ABS_NC` to `R_ARM_MOVT_PREL` in order. -/
def armMovValue (site : Site) (kind : Nat) (a : Int) : Int :=
  match kind with
  | 0 => armWithT site (armS site + a)
  | 1 => (armS site + a) >>> 16
  | 2 => armWithT site (armS site + a) - site.p
  | _ => (armS site + a - site.p) >>> 16

theorem arm_mov {env : Env} {site : Site} {state : LinkState} {kind : Nat} (hk : kind < 4)
    (ht : site.rel.typ = 0x2b + kind) (hb : inSection site 0 4 state.memory.size = true) :
    (arm env site).run state = .ok (some [stAt env site 0 4 (armMovSet (readNat state.memory env.little (site.off + 0) 4)
      (armMovValue site kind (addendOf site (sext (armMovImm (readNat state.memory env.little (site.off + 0) 4)) 16))) : Nat)])
      state := by
  have : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> (link_run [arm, ht, hb]; try rfl)

theorem arm_thumb_mov {env : Env} {site : Site} {state : LinkState} {kind : Nat} (hk : kind < 4)
    (ht : site.rel.typ = 0x2f + kind) (hb1 : inSection site 0 2 state.memory.size = true)
    (hb2 : inSection site 2 2 state.memory.size = true) :
    let hw1 := readNat state.memory env.little (site.off + 0) 2
    let hw2 := readNat state.memory env.little (site.off + 2) 2
    let value := armMovValue site kind (addendOf site (sext (thumbMovImm hw1 hw2) 16))
    (arm env site).run state = .ok (some [stAt env site 0 2 (thumbMovSet1 hw1 value : Nat),
      stAt env site 2 2 (thumbMovSet2 hw2 value : Nat)]) state := by
  have : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> (link_run [arm, ht, hb1, hb2]; try rfl)

/-- `R_ARM_PC24`, `R_ARM_CALL`, `R_ARM_JUMP24`: `S + A - P` in words. A `BL` to Thumb code becomes `BLX`, with its halfword
in the H bit, and a `BLX` to ARM code becomes `BL`. -/
theorem arm_branch {env : Env} {site : Site} {state : LinkState}
    (ht : site.rel.typ = 1 ∨ site.rel.typ = 0x1c ∨ site.rel.typ = 0x1d)
    (hb : inSection site 0 4 state.memory.size = true) :
    let insn := readNat state.memory env.little (site.off + 0) 4
    let value := armS site + addendOf site (armBranchImm insn) - site.p
    (arm env site).run state = .ok (some [stAt env site 0 4
      (if site.rel.typ == 0x1c && isThumb site.sym then setBits (armBranchSet 0xfa000000 value) 24 1 (value >>> 1)
       else if site.rel.typ == 0x1c && isFunctionSym site.sym && field insn 28 4 == 0xf then armBranchSet 0xeb000000 value
       else armBranchSet insn value : Nat)]) state := by
  rcases ht with ht | ht | ht <;> (link_run [arm, ht, hb]; try rfl) <;>
    (try simp only [ht]) <;> (split <;> (try split) <;> rfl)

/-- `R_ARM_THM_PC22`, `R_ARM_THM_JUMP24`: `S + A - P`. A call goes to the aligned pc when it is a `BLX`, to ARM code, and
its H bit says so; a jump has none. -/
theorem arm_thumb_branch {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 0xa ∨ site.rel.typ = 0x1e)
    (hb1 : inSection site 0 2 state.memory.size = true) (hb2 : inSection site 2 2 state.memory.size = true) :
    let hw1 := readNat state.memory env.little (site.off + 0) 2
    let hw2 := readNat state.memory env.little (site.off + 2) 2
    let a := addendOf site (thumbBranchImm hw1 hw2)
    let call := site.rel.typ == 0xa
    let blx := call && (if isFunctionSym site.sym then !isThumb site.sym else field hw2 12 1 == 0)
    let value := if blx then armS site + a - (site.p - site.p % 4) else armS site + a - site.p
    let hw2' := if !call then hw2 else setBits hw2 12 1 (if blx then 0 else 1)
    (arm env site).run state = .ok (some [stAt env site 0 2 (thumbBranchSet1 hw1 value : Nat),
      stAt env site 2 2 (thumbBranchSet2 hw2' value : Nat)]) state := by
  rcases ht with ht | ht <;> (link_run [arm, ht, hb1, hb2]; try rfl)

/-- `R_ARM_THM_JUMP19`: `S + A - P`. -/
theorem arm_thumb_jump19 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 0x33)
    (hb1 : inSection site 0 2 state.memory.size = true) (hb2 : inSection site 2 2 state.memory.size = true) :
    let hw1 := readNat state.memory env.little (site.off + 0) 2
    let hw2 := readNat state.memory env.little (site.off + 2) 2
    let value := armS site + addendOf site (thumbJump19Imm hw1 hw2) - site.p
    (arm env site).run state = .ok (some [stAt env site 0 2 (thumbJump19Set1 hw1 value : Nat),
      stAt env site 2 2 (thumbJump19Set2 hw2 value : Nat)]) state := by
  link_run [arm, ht, hb1, hb2]
  try rfl

/-- `R_ARM_THM_JUMP11` and `R_ARM_THM_JUMP8`: `S + A - P` in halfwords. -/
theorem arm_thumb_short {env : Env} {site : Site} {state : LinkState} {n : Nat}
    (ht : (site.rel.typ = 0x66 ∧ n = 11) ∨ (site.rel.typ = 0x67 ∧ n = 8))
    (hb : inSection site 0 2 state.memory.size = true) :
    let hw := readNat state.memory env.little (site.off + 0) 2
    (arm env site).run state = .ok (some [stAt env site 0 2
      (thumbShortSet n hw (armS site + addendOf site (thumbShortImm n hw) - site.p) : Nat)]) state := by
  rcases ht with ⟨ht, rfl⟩ | ⟨ht, rfl⟩ <;> (link_run [arm, ht, hb]; try rfl)


/-! ### MIPS -/

private theorem field16_int (value : Int) : (field value 0 16 : Int) = value % 65536 := by
  unfold field
  have hzero : value >>> 0 = value := by rw [Int.shiftRight_eq_div_pow]; simp
  rw [hzero, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  rfl

private theorem sext16_eq (value : Int) : sext value 16 = (value + 32768) % 65536 - 32768 :=
  sext_eq value (n := 16) (by decide)

/-- `HI16` and `LO16` in a pair rebuild the value: `HI16 << 16` plus the sign-extended `LO16`. -/
theorem mips_hi_lo (value : Int) : mipsHi value * 65536 + sext value 16 = value := by
  rw [sext16_eq]
  unfold mipsHi
  rw [shiftRight_toDiv]
  have : ((2 ^ 16 : Nat) : Int) = 65536 := rfl
  rw [this]
  omega

/-- The sequence `lui %highest; daddiu %higher; dsll 16; daddiu %hi; dsll 16; daddiu %lo` rebuilds a 64-bit constant, every
`daddiu` sign-extending its halfword, which is what each of the upper halves carries for. -/
theorem mips_four_halves (value : Int) :
    ((sext (mipsHighest value) 16 * 65536 + sext (mipsHigher value) 16) * 4294967296 +
        sext (mipsHi value) 16 * 65536 + sext value 16) % 18446744073709551616 = value % 18446744073709551616 := by
  simp only [sext16_eq, mipsHighest, mipsHigher, mipsHi, shiftRight_toDiv]
  have e1 : ((2 ^ 48 : Nat) : Int) = 281474976710656 := rfl
  have e2 : ((2 ^ 32 : Nat) : Int) = 4294967296 := rfl
  have e3 : ((2 ^ 16 : Nat) : Int) = 65536 := rfl
  rw [e1, e2, e3]
  omega

/-- A 16-bit immediate of an instruction takes the low bits of a value, and the opcode and registers stay. -/
theorem setLo16_spec (insn : Nat) (value : Int) :
    field (setLo16 insn value) 0 16 = field value 0 16 ∧
      ∀ j m, 16 ≤ j → field (setLo16 insn value) j m = field (insn : Int) j m := by
  unfold setLo16
  exact ⟨field_setBits_self .., fun j m h => field_setBits_other _ _ _ _ _ _ (.inr (by omega))⟩

/-- The relocations of MIPS that store a word, with the addend that is in the record or in the place. -/
def mipsData (s p gp gp0 : Int) : Nat → Option (Int → Int)
  | 2 => some fun a => s + a
  | 12 => some fun a => s + a + gp0 - gp
  | 248 => some fun a => s + a - p
  | _ => none

/-- The addend of a word: of the record, or the word in the place. -/
def mipsA32 (env : Env) (site : Site) (state : LinkState) : Int :=
  if site.rel.isExplicit then site.a else readNat state.memory env.little (site.off + 0) 4

/-- The addend of an instruction's immediate: of the record, or sign-extended from the low half. -/
def mipsA16 (env : Env) (site : Site) (state : LinkState) : Int :=
  if site.rel.isExplicit then site.a else sext (readNat state.memory env.little (site.off + 0) 4 &&& 0xffff : Nat) 16

theorem mips_data {env : Env} {site : Site} {f : Int → Int} {state : LinkState}
    (hb : inSection site 0 4 state.memory.size = true)
    (h : mipsData site.s site.p (mipsGp env) (mipsGp0 env site.sym) site.rel.typ = some f) :
    (mips env site).run state = .ok (some [stAt env site 0 4 (f (mipsA32 env site state))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold mipsData at h
  split at h <;> cases h <;> cases he : site.rel.isExplicit <;> (link_run [mips, ht, hb, he, mipsA32]; try rfl)

/-- `R_MIPS_64`: `S + A` in eight bytes, of a 64-bit file. -/
theorem mips_64 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 18) (hw : env.width = 64)
    (hb : inSection site 0 4 state.memory.size = true) :
    (mips env site).run state = .ok (some [stAt env site 0 8 (site.s + mipsA32 env site state)]) state := by
  cases he : site.rel.isExplicit <;> (link_run [mips, ht, hb, he, mipsA32, hw, beq_self_eq_true]; try rfl)

/-- The relocations of MIPS that take the immediate of an instruction, and need no entry of the GOT: `GPREL16` and the two
highest halves of a 64-bit constant. -/
def mipsCode (s gp gp0 : Int) : Nat → Option (Int → Int)
  | 7 | 8 => some fun a => s + a + gp0 - gp
  | 28 => some fun a => mipsHigher (s + a)
  | 29 => some fun a => mipsHighest (s + a)
  | _ => none

theorem mips_code {env : Env} {site : Site} {f : Int → Int} {state : LinkState}
    (hb : inSection site 0 4 state.memory.size = true)
    (h : mipsCode site.s (mipsGp env) (mipsGp0 env site.sym) site.rel.typ = some f) :
    (mips env site).run state = .ok (some [stAt env site 0 4
      (setLo16 (readNat state.memory env.little (site.off + 0) 4) (f (mipsA16 env site state)))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold mipsCode at h
  split at h <;> cases h <;> cases he : site.rel.isExplicit <;> (link_run [mips, ht, hb, he, mipsA16]; try rfl)

/-- The offset of an entry of the GOT from the global pointer, by the relocations that hold it whole or in halves. -/
def mipsGotCode (offset : Int) : Nat → Option Int
  | 19 | 23 | 31 => some offset
  | 22 | 30 => some (mipsHi offset)
  | _ => none

/-- `R_MIPS_GOT_DISP`, `R_MIPS_GOT_HI16`, `R_MIPS_GOT_LO16`, `R_MIPS_CALL_HI16` and `R_MIPS_CALL_LO16`: the entry of `S + A`,
from the global pointer. -/
theorem mips_got_code {env : Env} {site : Site} {slot value : Int} {state after : LinkState}
    (hb : inSection site 0 4 state.memory.size = true)
    (hg : gotEntry env (site.s + mipsA16 env site state) state = .ok slot after)
    (h : mipsGotCode (slot - mipsGp env) site.rel.typ = some value) :
    (mips env site).run state = .ok (some [stAt env site 0 4
      (setLo16 (readNat state.memory env.little (site.off + 0) 4) value)]) after := by
  generalize ht : site.rel.typ = t at h
  unfold mipsGotCode at h
  split at h <;> cases h <;> cases he : site.rel.isExplicit <;>
    (simp only [mipsA16, he, ite_true, ite_false, Bool.false_eq_true] at hg; link_run [mips, ht, hb, he, hg]; try rfl)

/-- `R_MIPS_CALL16` and the `R_MIPS_GOT16` of a global symbol: the entry of `S` from the global pointer. -/
theorem mips_got16 {env : Env} {site : Site} {slot : Int} {state after : LinkState}
    (ht : site.rel.typ = 11 ∨ (site.rel.typ = 9 ∧ site.sym.bind ≠ stbLocal))
    (hb : inSection site 0 4 state.memory.size = true)
    (hg : gotEntry env site.s state = .ok slot after) :
    (mips env site).run state = .ok (some [stAt env site 0 4
      (setLo16 (readNat state.memory env.little (site.off + 0) 4) (slot - mipsGp env))]) after := by
  rcases ht with ht | ⟨ht, hl⟩
  · link_run [mips, ht, hb, hg]
  · have hl' : (site.sym.bind == stbLocal) = false := by simpa using hl
    link_run [mips, ht, hb, hg, hl']

/-- `R_MIPS_PC16`: `S + A - P` in words, the addend being in the instruction. -/
theorem mips_pc16 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 10)
    (hb : inSection site 0 4 state.memory.size = true) :
    let insn := readNat state.memory env.little (site.off + 0) 4
    (mips env site).run state = .ok (some [stAt env site 0 4 (setLo16 insn
      ((site.s + sext ((insn &&& 0xffff) <<< 2 : Nat) 18 - site.p) >>> 2))]) state := by
  link_run [mips, ht, hb]
  try rfl

/-- `R_MIPS_26`: a local symbol stays in the 256 MiB region of the delay slot, and the target of the others is sign-extended. -/
theorem mips_26 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 4)
    (hb : inSection site 0 4 state.memory.size = true) :
    let insn := readNat state.memory env.little (site.off + 0) 4
    let a : Int := if site.rel.isExplicit then site.a else ((insn &&& 0x3ffffff) <<< 2 : Nat)
    let target := if site.sym.bind == stbLocal then
        (field a 0 28 + (field (site.p + 4) 28 36) * 2 ^ 28 : Nat) + site.s
      else sext a 28 + site.s
    (mips env site).run state = .ok (some [stAt env site 0 4 (setBits insn 0 26 (target >>> 2) : Nat)]) state := by
  link_run [mips, ht, hb]
  try rfl

/-- `R_MIPS_HI16` when the pair is complete, with `AHL = (AHI << 16) + ALO`: `(AHL + S + 0x8000) >> 16`, and `_gp_disp` is
`GP - P` for `S`. -/
theorem mipsApplyHi_hi16 {env : Env} {site : Site} {ahl : Int} {state : LinkState} (ht : site.rel.typ = 5)
    (hb : inSection site 0 4 state.memory.size = true) :
    let insn := readNat state.memory env.little (site.off + 0) 4
    let s := if site.sym.name == "_gp_disp" then mipsGp env - site.p else site.s
    (mipsApplyHi env site ahl).run state =
      (commit site [stAt env site 0 4 (setLo16 insn ((ahl + s + 0x8000) >>> 16))]).run state := by
  link_run [mipsApplyHi, ht, hb]
  try rfl

/-- The `R_MIPS_GOT16` of a local symbol when the pair is complete: the entry of the page of `S + AHL`. -/
theorem mipsApplyHi_got16 {env : Env} {site : Site} {ahl slot : Int} {state after : LinkState} (ht : site.rel.typ ≠ 5)
    (hb : inSection site 0 4 state.memory.size = true)
    (hg : gotEntry env ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) state = .ok slot after) :
    (mipsApplyHi env site ahl).run state =
      (commit site [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4) (slot - mipsGp env))]).run after := by
  have ht' : (site.rel.typ == 5) = false := by simpa using ht
  link_run [mipsApplyHi, ht', hb, hg]
  try rfl

/-- `R_MIPS_LO16`: after the pending halves of its symbol are done, `S + A`, and for `_gp_disp` the `GP - P + 4` of the pair. -/
theorem mips_lo16 {env : Env} {site : Site} {state after : LinkState} {result : Unit} (ht : site.rel.typ = 6)
    (hb : inSection site 0 4 state.memory.size = true)
    (hf : mipsFlush env (mipsA16 env site state) site.rel.symbol state = .ok result after) :
    (mips env site).run state = .ok (some [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4)
      ((if site.sym.name == "_gp_disp" then mipsGp env - site.p + 4 else site.s) + mipsA16 env site state))]) after := by
  cases he : site.rel.isExplicit <;>
    (simp only [mipsA16, he, ite_true, ite_false, Bool.false_eq_true] at hf ⊢; link_run [mips, ht, hb, he, hf]; try rfl)

/-- The middle of a compound record, on the special symbol: `R_MIPS_SUB` is `S - A`, `R_MIPS_64` is `S + A`, and `R_MIPS_NONE`
leaves the value. -/
theorem mipsCompoundStep_spec (s value : Int) :
    mipsCompoundStep s value 24 = some (s - value) ∧ mipsCompoundStep s value 18 = some (s + value) ∧
      mipsCompoundStep s value 0 = some value := ⟨rfl, rfl, rfl⟩

/-- What the last of a compound record does with its result: 16-bit halves of it, or all of it. -/
theorem mipsCompoundField_spec (insn : Nat) (s value : Int) :
    mipsCompoundField insn s value 5 = some (4, setLo16 insn (mipsHi (s + value))) ∧
      mipsCompoundField insn s value 6 = some (4, setLo16 insn (s + value)) ∧
      mipsCompoundField insn s value 28 = some (4, setLo16 insn (mipsHigher (s + value))) ∧
      mipsCompoundField insn s value 29 = some (4, setLo16 insn (mipsHighest (s + value))) ∧
      mipsCompoundField insn s value 18 = some (8, s + value) ∧ mipsCompoundField insn s value 2 = some (4, s + value) ∧
      mipsCompoundField insn s value 24 = some (8, s - value) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The special symbols of the N64 ABI. -/
theorem mipsSpecial_spec (env : Env) (site : Site) :
    mipsSpecial env site 0 = some 0 ∧ mipsSpecial env site 1 = some (mipsGp env) ∧ mipsSpecial env site 2 = some env.gp0 ∧
      mipsSpecial env site 3 = some site.p := ⟨rfl, rfl, rfl, rfl⟩

/-- A compound record, in general: the first relocation's value goes through the middle one, on the special symbol, and the
last one stores it. -/
theorem mipsCompound_spec {env : Env} {site : Site} {special base value : Int} {n : Nat} {stored : Int} {state after : LinkState}
    (hs : mipsSpecial env site (site.rel.typ >>> 24) = some special)
    (hbase : mipsCompoundBase env site (site.rel.typ % 256) state = .ok (some base) after)
    (hm : (if (site.rel.typ >>> 16) % 256 != 0 then mipsCompoundStep special base ((site.rel.typ >>> 8) % 256) else some base) = some value)
    (hb : inSection site 0 4 after.memory.size = true)
    (hl : mipsCompoundField (readNat after.memory env.little (site.off + 0) 4) (if (site.rel.typ >>> 16) % 256 != 0 then 0 else special) value
      (if (site.rel.typ >>> 16) % 256 != 0 then (site.rel.typ >>> 16) % 256 else (site.rel.typ >>> 8) % 256) = some (n, stored)) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 n stored]) after := by
  link_run [mipsCompound, hs, hbase, hm, hb, hl, bne_self_eq_false]

/-- The value of the first of a compound record: `GPREL16` and `GPREL32` count from the global pointer, as in a record of
their own, and the others are as their formulas say. -/
theorem mipsCompoundBase_spec (env : Env) (site : Site) (state : LinkState) :
    mipsCompoundBase env site 7 state = .ok (some (site.s + site.a + mipsGp0 env site.sym - mipsGp env)) state ∧
      mipsCompoundBase env site 12 state = .ok (some (site.s + site.a + mipsGp0 env site.sym - mipsGp env)) state ∧
      mipsCompoundBase env site 248 state = .ok (some (site.s + site.a - site.p)) state ∧
      mipsCompoundBase env site 18 state = .ok (some (site.s + site.a)) state ∧
      mipsCompoundBase env site 2 state = .ok (some (site.s + site.a)) state := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The relocations of a record with the special symbol `RSS_UNDEF`, with a middle one of `R_MIPS_SUB`, of `GPREL16`, as
`.cpsetup` has them: `%hi` or `%lo` of `GP - (S + A)`, with the first one's global pointer. -/
private theorem compound_gp_rel_neg {env : Env} {site : Site} {state : LinkState} {last : Nat} {stored : Int}
    (ht : site.rel.typ = 7 + 24 * 2 ^ 8 + last * 2 ^ 16) (hlast : 0 < last) (hl : last < 256) (hb : inSection site 0 4 state.memory.size = true)
    (hf : mipsCompoundField (readNat state.memory env.little (site.off + 0) 4) 0 (0 - (site.s + site.a + mipsGp0 env site.sym - mipsGp env)) last =
      some (4, stored)) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 4 stored]) state := by
  have h1 : site.rel.typ >>> 24 = 0 := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h2 : (site.rel.typ >>> 16) % 256 = last := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h3 : (site.rel.typ >>> 8) % 256 = 24 := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h4 : site.rel.typ % 256 = 7 := by rw [ht]; omega
  have hne : (last != 0) = true := by simp; omega
  apply mipsCompound_spec (special := 0) (base := site.s + site.a + mipsGp0 env site.sym - mipsGp env)
    (value := 0 - (site.s + site.a + mipsGp0 env site.sym - mipsGp env))
  · rw [h1]; rfl
  · rw [h4]; rfl
  · simp only [h2, h3, hne, ↓reduceIte]; rfl
  · exact hb
  · simp only [h2, hne, ↓reduceIte]; exact hf

/-- `%hi(%neg(%gp_rel(S + A)))`, as `R_MIPS_GPREL16 / R_MIPS_SUB / R_MIPS_HI16` of `.cpsetup`: the high half of `GP - (S + A)`. -/
theorem mips_gp_rel_neg_hi {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 7 + 24 * 2 ^ 8 + 5 * 2 ^ 16)
    (hb : inSection site 0 4 state.memory.size = true) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4)
      (mipsHi (-(site.s + site.a + mipsGp0 env site.sym - mipsGp env))))]) state := by
  apply compound_gp_rel_neg ht (by decide) (by decide) hb
  simp only [mipsCompoundField, Int.zero_add, Int.zero_sub]

/-- `%lo(%neg(%gp_rel(S + A)))`: the low half of `GP - (S + A)`. -/
theorem mips_gp_rel_neg_lo {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 7 + 24 * 2 ^ 8 + 6 * 2 ^ 16)
    (hb : inSection site 0 4 state.memory.size = true) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4)
      (-(site.s + site.a + mipsGp0 env site.sym - mipsGp env)))]) state := by
  apply compound_gp_rel_neg ht (by decide) (by decide) hb
  simp only [mipsCompoundField, Int.zero_add, Int.zero_sub]

/-- The second relocation is on the special symbol: with `RSS_GP`, `R_MIPS_GPREL16 / R_MIPS_SUB` is a value measured back from
the global pointer. lld knows only `RSS_UNDEF`, so this is by the N64 ABI alone. -/
theorem mips_special_gp {env : Env} {site : Site} {state : LinkState} {last : Nat}
    (ht : site.rel.typ = 7 + 24 * 2 ^ 8 + last * 2 ^ 16 + 1 * 2 ^ 24) (hlast : 0 < last) (hl : last < 256)
    (hb : inSection site 0 4 state.memory.size = true) {stored : Int}
    (hf : mipsCompoundField (readNat state.memory env.little (site.off + 0) 4) 0
      (mipsGp env - (site.s + site.a + mipsGp0 env site.sym - mipsGp env)) last = some (4, stored)) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 4 stored]) state := by
  have h1 : site.rel.typ >>> 24 = 1 := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h2 : (site.rel.typ >>> 16) % 256 = last := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h3 : (site.rel.typ >>> 8) % 256 = 24 := by rw [ht, Nat.shiftRight_eq_div_pow]; omega
  have h4 : site.rel.typ % 256 = 7 := by rw [ht]; omega
  have hne : (last != 0) = true := by simp; omega
  apply mipsCompound_spec (special := mipsGp env) (base := site.s + site.a + mipsGp0 env site.sym - mipsGp env)
    (value := mipsGp env - (site.s + site.a + mipsGp0 env site.sym - mipsGp env))
  · rw [h1]; rfl
  · rw [h4]; rfl
  · simp only [h2, h3, hne, ↓reduceIte]; rfl
  · exact hb
  · simp only [h2, hne, ↓reduceIte]; exact hf

/-- `R_MIPS_PC32 / R_MIPS_64`: `S + A - P` in eight bytes, as in the `.eh_frame` of N64. -/
theorem mips_pc32_64 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 248 + 18 * 2 ^ 8)
    (hb : inSection site 0 4 state.memory.size = true) :
    (mipsCompound env site).run state = .ok (some [stAt env site 0 8 (site.s + site.a - site.p)]) state := by
  have : (mipsCompoundField (readNat state.memory env.little (site.off + 0) 4) 0 (site.s + site.a - site.p) 18) =
      some (8, site.s + site.a - site.p) := by simp only [mipsCompoundField, Int.zero_add]
  apply mipsCompound_spec (special := 0) (base := site.s + site.a - site.p) (value := site.s + site.a - site.p)
  · rw [ht]; rfl
  · rw [ht]; rfl
  · rw [ht]; rfl
  · exact hb
  · rw [ht]; exact this

/-- A record's type above 8 bits goes to the compound rule. -/
theorem mips_of_compound {env : Env} {site : Site} (ht : 256 ≤ site.rel.typ) :
    mips env site = mipsCompound env site := by
  unfold mips
  dsimp only
  split <;> first
    | omega
    | (rename_i hk; rw [ite_eq_right (by omega)])


/-! ### RISC-V -/

/-- A field as integers, for arithmetic with literals. -/
theorem field_int (value : Int) (lo n : Nat) :
    (field value lo n : Int) = (value / ((2 ^ lo : Nat) : Int)) % ((2 ^ n : Nat) : Int) := by
  unfold field
  rw [shiftRight_toDiv, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
    have : (0 : Int) < ((2 ^ n : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos n
    omega))]

/-- `AUIPC` or `LUI` and the 12-bit immediate that follows rebuild the value, which is what the high part is rounded for. -/
theorem riscv_hi_lo (value : Int) (first second : Nat) :
    ((field (riscvU value first) 12 20 : Int) * 4096 + sext (field (riscvI value second) 20 12 : Nat) 12) % 4294967296 =
      value % 4294967296 := by
  unfold riscvU riscvI
  rw [field_setBits_self, field_setBits_self, field_shiftRight, sext_natCast_field, sext_eq value (n := 12) (by decide),
    field_int]
  have e1 : ((2 ^ (12 + 0) : Nat) : Int) = 4096 := rfl
  have e2 : ((2 ^ 20 : Nat) : Int) = 1048576 := rfl
  have e3 : ((2 ^ (12 - 1) : Nat) : Int) = 2048 := rfl
  rw [e1, e2, e3]
  omega

/-- A U-type instruction keeps its opcode and register, an I-type also its other register and function. -/
theorem riscvU_frame (value : Int) (insn j m : Nat) (h : j + m ≤ 12) : field (riscvU value insn) j m = field (insn : Int) j m :=
  field_setBits_other _ _ _ _ _ _ (.inl h)

theorem riscvI_frame (value : Int) (insn j m : Nat) (h : j + m ≤ 20) : field (riscvI value insn) j m = field (insn : Int) j m :=
  field_setBits_other _ _ _ _ _ _ (.inl h)

/-- An S-type instruction has its offset in two parts, and the rest stays. -/
theorem riscvS_spec (value : Int) (insn : Nat) :
    field (riscvS value insn) 25 7 * 2 ^ 5 + field (riscvS value insn) 7 5 = field value 0 12 ∧
      ∀ j m, ((j + m ≤ 7) ∨ (12 ≤ j ∧ j + m ≤ 25)) → field (riscvS value insn) j m = field (insn : Int) j m := by
  unfold riscvS
  constructor
  · bits
    have h : field value 0 12 = field value 0 5 + field value 5 7 * 2 ^ 5 := field_split value 0 5 7
    omega
  · intro j m h
    bits

/-- A branch has `imm[12|10:5]` and `imm[4:1|11]` in two parts, and the rest stays. -/
theorem riscvB_spec (value : Int) (insn : Nat) :
    field (riscvB value insn) 31 1 * 2 ^ 12 + field (riscvB value insn) 7 1 * 2 ^ 11 + field (riscvB value insn) 25 6 * 2 ^ 5 +
        field (riscvB value insn) 8 4 * 2 = field value 1 12 * 2 ∧
      ∀ j m, ((j + m ≤ 7) ∨ (12 ≤ j ∧ j + m ≤ 25)) → field (riscvB value insn) j m = field (insn : Int) j m := by
  unfold riscvB
  constructor
  · bits
    have h1 : field value 1 12 = field value 1 4 + field value 5 8 * 2 ^ 4 := field_split value 1 4 8
    have h2 : field value 5 8 = field value 5 6 + field value 11 2 * 2 ^ 6 := field_split value 5 6 2
    have h3 : field value 11 2 = field value 11 1 + field value 12 1 * 2 ^ 1 := field_split value 11 1 1
    omega
  · intro j m h
    bits

/-- `JAL` has `imm[20|10:1|11|19:12]`, and the rest stays. -/
theorem riscvJ_spec (value : Int) (insn : Nat) :
    field (riscvJ value insn) 31 1 * 2 ^ 20 + field (riscvJ value insn) 12 8 * 2 ^ 12 + field (riscvJ value insn) 20 1 * 2 ^ 11 +
        field (riscvJ value insn) 21 10 * 2 = field value 1 20 * 2 ∧
      ∀ j m, j + m ≤ 12 → field (riscvJ value insn) j m = field (insn : Int) j m := by
  unfold riscvJ
  constructor
  · bits
    have h1 : field value 1 20 = field value 1 10 + field value 11 10 * 2 ^ 10 := field_split value 1 10 10
    have h2 : field value 11 10 = field value 11 1 + field value 12 9 * 2 ^ 1 := field_split value 11 1 9
    have h3 : field value 12 9 = field value 12 8 + field value 20 1 * 2 ^ 8 := field_split value 12 8 1
    omega
  · intro j m h
    bits

/-- `C.BEQZ` and `C.BNEZ` have `offset[8|4:3]` and `offset[7:6|2:1|5]`, and the rest stays. -/
theorem riscvCB_spec (value : Int) (insn : Nat) :
    field (riscvCB value insn) 12 1 * 2 ^ 8 + field (riscvCB value insn) 5 2 * 2 ^ 6 + field (riscvCB value insn) 2 1 * 2 ^ 5 +
        field (riscvCB value insn) 10 2 * 2 ^ 3 + field (riscvCB value insn) 3 2 * 2 = field value 1 8 * 2 ∧
      ∀ j m, (j + m ≤ 2 ∨ (7 ≤ j ∧ j + m ≤ 10) ∨ 13 ≤ j) → field (riscvCB value insn) j m = field (insn : Int) j m := by
  unfold riscvCB
  constructor
  · bits
    have h1 : field value 1 8 = field value 1 2 + field value 3 6 * 2 ^ 2 := field_split value 1 2 6
    have h2 : field value 3 6 = field value 3 2 + field value 5 4 * 2 ^ 2 := field_split value 3 2 4
    have h3 : field value 5 4 = field value 5 1 + field value 6 3 * 2 ^ 1 := field_split value 5 1 3
    have h4 : field value 6 3 = field value 6 2 + field value 8 1 * 2 ^ 2 := field_split value 6 2 1
    omega
  · intro j m h
    bits

/-- `C.J` has `offset[11|4|9:8|10|6|7|3:1|5]`, and the rest stays. -/
theorem riscvCJ_spec (value : Int) (insn : Nat) :
    field (riscvCJ value insn) 12 1 * 2 ^ 11 + field (riscvCJ value insn) 8 1 * 2 ^ 10 + field (riscvCJ value insn) 9 2 * 2 ^ 8 +
        field (riscvCJ value insn) 6 1 * 2 ^ 7 + field (riscvCJ value insn) 7 1 * 2 ^ 6 + field (riscvCJ value insn) 2 1 * 2 ^ 5 +
        field (riscvCJ value insn) 11 1 * 2 ^ 4 + field (riscvCJ value insn) 3 3 * 2 = field value 1 11 * 2 ∧
      ∀ j m, (j + m ≤ 2 ∨ 13 ≤ j) → field (riscvCJ value insn) j m = field (insn : Int) j m := by
  unfold riscvCJ
  constructor
  · bits
    have h1 : field value 1 11 = field value 1 3 + field value 4 8 * 2 ^ 3 := field_split value 1 3 8
    have h2 : field value 4 8 = field value 4 1 + field value 5 7 * 2 ^ 1 := field_split value 4 1 7
    have h3 : field value 5 7 = field value 5 1 + field value 6 6 * 2 ^ 1 := field_split value 5 1 6
    have h4 : field value 6 6 = field value 6 1 + field value 7 5 * 2 ^ 1 := field_split value 6 1 5
    have h5 : field value 7 5 = field value 7 1 + field value 8 4 * 2 ^ 1 := field_split value 7 1 4
    have h6 : field value 8 4 = field value 8 2 + field value 10 2 * 2 ^ 2 := field_split value 8 2 2
    have h7 : field value 10 2 = field value 10 1 + field value 11 1 * 2 ^ 1 := field_split value 10 1 1
    omega
  · intro j m h
    bits

/-- The relocations of RISC-V that store a value, with `X = S + A`. -/
def riscvData (x p : Int) : Nat → Option (Nat × Int)
  | 1 | 56 => some (4, x)
  | 2 => some (8, x)
  | 54 => some (1, x)
  | 55 => some (2, x)
  | 57 | 59 => some (4, x - p)
  | _ => none

theorem riscv_data {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState)
    (h : riscvData (site.s + site.a) site.p site.rel.typ = some (n, value)) :
    (riscv env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold riscvData at h
  split at h <;> cases h <;> (link_run [riscv, ht]; try rfl)

/-- The relocations of RISC-V that patch an instruction word. -/
def riscvCode (x p : Int) : Nat → Option (Nat × (Nat → Int))
  | 16 => some (4, riscvB (x - p))
  | 17 => some (4, riscvJ (x - p))
  | 26 => some (4, riscvU x)
  | 27 => some (4, riscvI x)
  | 28 => some (4, riscvS x)
  | 44 => some (2, riscvCB (x - p))
  | 45 => some (2, riscvCJ (x - p))
  | _ => none

theorem riscv_code {env : Env} {site : Site} {n : Nat} {f : Nat → Int} {state : LinkState}
    (hb : inSection site 0 n state.memory.size = true)
    (h : riscvCode (site.s + site.a) site.p site.rel.typ = some (n, f)) :
    (riscv env site).run state =
      .ok (some [stiAt env site 0 n (f (readNat state.memory env.codeLittle (site.off + 0) n))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold riscvCode at h
  split at h <;> cases h <;> (link_run [riscv, ht, hb]; try rfl)

/-- `R_RISCV_CALL` and `R_RISCV_CALL_PLT`: `S + A - P` in the `AUIPC` and the `JALR` after it. -/
theorem riscv_call {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 18 ∨ site.rel.typ = 19)
    (hb1 : inSection site 0 4 state.memory.size = true) (hb2 : inSection site 4 4 state.memory.size = true) :
    let v := site.s + site.a - site.p
    (riscv env site).run state = .ok (some [
      stiAt env site 0 4 (riscvU v (readNat state.memory env.codeLittle (site.off + 0) 4)),
      stiAt env site 4 4 (riscvI v (readNat state.memory env.codeLittle (site.off + 4) 4))]) state := by
  rcases ht with ht | ht <;> (link_run [riscv, ht, hb1, hb2]; try rfl)

/-- `R_RISCV_ADD*` and `R_RISCV_SUB*`: a value in the place, plus or minus `S + A`. -/
def riscvArith (x : Int) : Nat → Option (Nat × (Int → Int))
  | 33 => some (1, fun old => old + x)
  | 34 => some (2, fun old => old + x)
  | 35 => some (4, fun old => old + x)
  | 36 => some (8, fun old => old + x)
  | 37 => some (1, fun old => old - x)
  | 38 => some (2, fun old => old - x)
  | 39 => some (4, fun old => old - x)
  | 40 => some (8, fun old => old - x)
  | _ => none

theorem riscv_arith {env : Env} {site : Site} {n : Nat} {f : Int → Int} {state : LinkState}
    (hb : inSection site 0 n state.memory.size = true)
    (h : riscvArith (site.s + site.a) site.rel.typ = some (n, f)) :
    (riscv env site).run state = .ok (some [stAt env site 0 n
      (f (readNat state.memory env.little (site.off + 0) n))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold riscvArith at h
  split at h <;> cases h <;> (link_run [riscv, ht, hb]; try rfl)

/-- `R_RISCV_SUB6` and `R_RISCV_SET6`: the low 6 bits of a byte, and the top two stay. -/
theorem riscv_sub6_set6 {env : Env} {site : Site} {state : LinkState} (hb : inSection site 0 1 state.memory.size = true) :
    let old := readNat state.memory env.little (site.off + 0) 1
    (site.rel.typ = 52 → (riscv env site).run state = .ok (some [stAt env site 0 1
      (setBits old 0 6 ((old : Int) - (site.s + site.a)) : Nat)]) state) ∧
    (site.rel.typ = 53 → (riscv env site).run state = .ok (some [stAt env site 0 1
      (setBits old 0 6 (site.s + site.a) : Nat)]) state) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩ <;> (link_run [riscv, ht, hb]; try rfl)

/-- `R_RISCV_GOT32_PCREL`: the entry of `S` from the place, plus `A`. -/
theorem riscv_got32 {env : Env} {site : Site} {slot : Int} {state after : LinkState} (ht : site.rel.typ = 41)
    (hg : gotEntry env site.s state = .ok slot after) :
    (riscv env site).run state = .ok (some [stAt env site 0 4 (slot + site.a - site.p)]) after := by
  link_run [riscv, ht, hg]

/-- `R_RISCV_PCREL_HI20` and `R_RISCV_GOT_HI20`: the value collected for the instruction before the relocations. -/
theorem riscv_pcrel_hi {env : Env} {site : Site} {state : LinkState} {value : Int} (ht : site.rel.typ = 20 ∨ site.rel.typ = 23)
    (hv : state.riscvHi[site.p]? = some value) (hb : inSection site 0 4 state.memory.size = true) :
    (riscv env site).run state = .ok (some [stiAt env site 0 4
      (riscvU value (readNat state.memory env.codeLittle (site.off + 0) 4))]) state := by
  rcases ht with ht | ht <;> (link_run [riscv, ht, hb, hv]; try rfl)

/-- `R_RISCV_PCREL_LO12_I` and `_S`: the symbol is the label of the `AUIPC`, and the value is the one of that instruction,
so a pair adds up to what it should even though the two are at different places. -/
theorem riscv_pcrel_lo {env : Env} {site : Site} {state : LinkState} {value : Int}
    (hv : state.riscvHi[site.s]? = some value) (hb : inSection site 0 4 state.memory.size = true) :
    let insn := readNat state.memory env.codeLittle (site.off + 0) 4
    (site.rel.typ = 24 → (riscv env site).run state = .ok (some [stiAt env site 0 4 (riscvI value insn)]) state) ∧
      (site.rel.typ = 25 → (riscv env site).run state = .ok (some [stiAt env site 0 4 (riscvS value insn)]) state) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩ <;> (link_run [riscv, ht, hb, hv]; try rfl)

/-- A `PCREL_HI20` is collected as `S + A - P`, and `GOT_HI20` through the entry of `S`. -/
theorem riscvPrescan_pcrel {env : Env} {site : Site} (ht : site.rel.typ = 23) (state : LinkState) :
    riscvPrescan env site state =
      .ok () { state with riscvHi := state.riscvHi.insert site.p (site.s + site.a - site.p) } := by
  link_run [riscvPrescan, ht, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  try rfl

theorem riscvPrescan_got {env : Env} {site : Site} {slot : Int} {state after : LinkState} (ht : site.rel.typ = 20)
    (hg : gotEntry env site.s state = .ok slot after) :
    riscvPrescan env site state =
      .ok () { after with riscvHi := after.riscvHi.insert site.p (slot + site.a - site.p) } := by
  link_run [riscvPrescan, ht, hg, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  try rfl

/-- The bytes of a ULEB128 number rewritten in its length: 7 bits each from the low end, and each but the last says that
another one follows. -/
def ulebBytes (value : Int) (n : Nat) : List Nat :=
  (List.range n).map fun i => field value (7 * i) 7 + (if i + 1 < n then 0x80 else 0)

/-- The continuation bit does not disturb the digit. -/
theorem ulebBytes_getElem (value : Int) (n i : Nat) (h : i < n) :
    (ulebBytes value n)[i]'(by simpa [ulebBytes] using h) % 128 = field value (7 * i) 7 ∧
      ((ulebBytes value n)[i]'(by simpa [ulebBytes] using h) / 128 = 1 ↔ i + 1 < n) := by
  have hl : field value (7 * i) 7 < 2 ^ 7 := field_lt ..
  have e : (2 : Nat) ^ 7 = 128 := rfl
  rw [e] at hl
  simp only [ulebBytes, List.getElem_map, List.getElem_range]
  split <;> simp_all <;> omega

/-- Digit by digit they add up to the low `7 * n` bits of the value, so the number reads back as it was stored. -/
theorem ulebBytes_value (value : Int) : ∀ k, (List.range k).foldl (init := 0)
    (fun sum i => sum + field value (7 * i) 7 * 128 ^ i) = field value 0 (7 * k)
  | 0 => by simp [field]
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, ulebBytes_value value k]
    simp only [List.foldl_cons, List.foldl_nil]
    have e : 7 * (k + 1) = 7 * k + 7 := by omega
    have e2 : (128 : Nat) = 2 ^ 7 := rfl
    rw [e, field_split, Nat.zero_add, e2, ← Nat.pow_mul]

theorem uleb_read_loop {env : Env} {site : Site} {state : LinkState} :
    ∀ (l : List Nat) (init : Nat), (∀ i ∈ l, inSection site i 1 state.memory.size = true) →
      (forIn l init (fun i (r : Nat) =>
        (do
          let r' := r + ((← ld env site i 1) &&& 0x7f) * 2 ^ (7 * i)
          pure PUnit.unit
          pure (ForInStep.yield r') : LinkM (ForInStep Nat)))) state =
        .ok (l.foldl (init := init) fun r i =>
          r + (readNat state.memory env.little (site.off + i) 1 &&& 0x7f) * 2 ^ (7 * i)) state
  | [], _, _ => rfl
  | i :: rest, init, h => by
    simp only [List.forIn_cons, List.foldl_cons]
    have hi := ld_ok (env := env) (h i (by simp))
    simp only [bind, EStateM.bind, hi, pure, EStateM.pure]
    exact uleb_read_loop rest _ fun j hj => h j (by simp [hj])

/-- What a ULEB128 relocation stores, as `R_RISCV_SET_ULEB128` and `R_RISCV_SUB_ULEB128` use it. -/
theorem rewriteUleb_spec {env : Env} {site : Site} {state : LinkState} {f : Nat → Int} {n : Nat}
    (hlen : ulebLength env site 9 0 state = .ok n state)
    (hb : ∀ i, i < n → inSection site i 1 state.memory.size = true) :
    let old := (List.range n).foldl (init := 0) fun r i =>
      r + (readNat state.memory env.little (site.off + i) 1 &&& 0x7f) * 2 ^ (7 * i)
    (rewriteUleb env site f).run state = .ok (some ((List.range n).map fun i =>
      stAt env site i 1 ((field (f old) (7 * i) 7 + (if i + 1 < n then 0x80 else 0) : Nat) : Int))) state := by
  intro old
  have hloop := uleb_read_loop (env := env) (site := site) (state := state) (List.range n) 0
    (fun i hi => hb i (List.mem_range.1 hi))
  simp only [bind, pure] at hloop
  simp only [rewriteUleb, EStateM.run, bind, EStateM.bind, hlen, done, pure, EStateM.pure]
  rw [hloop]


/-! ### PowerPC -/

/-- `@ha` and `@l` in a pair rebuild the value: `addis` and a sign-extended offset. -/
theorem ppc_ha_lo (value : Int) : ppcHa value * 65536 + sext value 16 = value := by
  rw [sext16_eq]
  unfold ppcHa
  rw [shiftRight_toDiv]
  have : ((2 ^ 16 : Nat) : Int) = 65536 := rfl
  rw [this]
  omega

/-- The halves of the three 16-bit `@ha`, `@highera` and `@highesta` of a value carry only for the offset below them, that
is the low half, as `lis`, `ori` and `rldicr` sequences of the ABI want. -/
theorem ppc_high_halves (value : Int) :
    ppcHigher value = value >>> 32 ∧ ppcHighest value = value >>> 48 ∧ ppcHi value = value >>> 16 ∧
      ppcHighera value = (value + 0x8000) >>> 32 ∧ ppcHighesta value = (value + 0x8000) >>> 48 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A DS-form offset keeps the two bits of the opcode extension, and a DQ-form offset the four of its own. -/
theorem ppcDsHalf_spec (old : Nat) (value : Int) :
    (field (ppcDsHalf false old value : Nat) 2 14 = field value 2 14 ∧
        field (ppcDsHalf false old value : Nat) 0 2 = field (old : Int) 0 2) ∧
      (field (ppcDsHalf true old value : Nat) 4 12 = field value 4 12 ∧
        field (ppcDsHalf true old value : Nat) 0 4 = field (old : Int) 0 4) := by
  unfold ppcDsHalf
  simp only [Bool.false_eq_true, ite_false, ite_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> bits

/-- `lq`, `lxvp` and `stxvp` are DQ-form, and `lxv` and `stxv` among primary opcode 61 by their low bits. -/
theorem ppcIsDq_spec (insn : Nat) :
    ppcIsDq insn = (field (insn : Int) 26 6 == 6 || field (insn : Int) 26 6 == 56 ||
      (field (insn : Int) 26 6 == 61 && field (insn : Int) 0 2 == 1)) := rfl

/-- The relocations that PowerPC and PowerPC64 share, with `X = S + A`. -/
def ppcData (x p : Int) : Nat → Option (Nat × Int)
  | 1 => some (4, x)
  | 3 | 4 => some (2, x)
  | 5 => some (2, ppcHi x)
  | 6 => some (2, ppcHa x)
  | 26 => some (4, x - p)
  | 38 => some (8, x)
  | 44 => some (8, x - p)
  | _ => none

theorem ppc_data {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState)
    (h : ppcData (site.s + site.a) site.p site.rel.typ = some (n, value)) :
    (powerpc env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold ppcData at h
  split at h <;> cases h <;> (link_run [powerpc, ht]; try rfl)

/-- The branches: `LI` and `BD`, in words, keeping `AA` and `LK`. -/
def ppcCode (x p : Int) : Nat → Option (Nat → Nat)
  | 2 => some fun i => setBits i 2 24 (x >>> 2)
  | 7 => some fun i => setBits i 2 14 (x >>> 2)
  | 10 | 18 => some fun i => setBits i 2 24 ((x - p) >>> 2)
  | 11 => some fun i => setBits i 2 14 ((x - p) >>> 2)
  | _ => none

theorem ppc_code {env : Env} {site : Site} {f : Nat → Nat} {state : LinkState}
    (hb : inSection site 0 4 state.memory.size = true)
    (h : ppcCode (site.s + site.a) site.p site.rel.typ = some f) :
    (powerpc env site).run state =
      .ok (some [stiAt env site 0 4 (f (readNat state.memory env.codeLittle (site.off + 0) 4))]) state := by
  generalize ht : site.rel.typ = t at h
  unfold ppcCode at h
  split at h <;> cases h <;> (link_run [powerpc, ht, hb]; try rfl)

/-- The relocations of the ELFv1 and ELFv2 ABIs of PowerPC64 that need no entry of the GOT, `.TOC.` being the TOC pointer. -/
def ppc64Data (x p toc a : Int) : Nat → Option (Nat × Int)
  | 39 => some (2, ppcHigher x)
  | 40 => some (2, ppcHighera x)
  | 41 => some (2, ppcHighest x)
  | 42 => some (2, ppcHighesta x)
  | 47 | 48 => some (2, x - toc)
  | 49 => some (2, ppcHi (x - toc))
  | 50 => some (2, ppcHa (x - toc))
  | 51 => some (8, toc + a)
  | 249 | 250 => some (2, x - p)
  | 251 => some (2, ppcHi (x - p))
  | 252 => some (2, ppcHa (x - p))
  | _ => none

theorem ppc64_data {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState) (hm : env.machine = emPpc64)
    (h : ppc64Data (site.s + site.a) site.p (ppcToc env) site.a site.rel.typ = some (n, value)) :
    (powerpc env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold ppc64Data at h
  split at h <;> cases h <;> (link_run [powerpc, ht, hm, bne_self_eq_false]; try rfl)

/-- The TOC relocations only exist on PowerPC64: on 32 bits the numbers mean other things and are left alone. -/
theorem ppc32_no_toc {env : Env} {site : Site} (state : LinkState) (hm : env.machine ≠ emPpc64)
    (ht : site.rel.typ = 47 ∨ site.rel.typ = 48 ∨ site.rel.typ = 49 ∨ site.rel.typ = 50 ∨ site.rel.typ = 51) :
    (powerpc env site).run state = .ok none state := by
  have hm' : (env.machine != emPpc64) = true := by simpa using hm
  rcases ht with ht | ht | ht | ht | ht <;> (link_run [powerpc, ht, hm']; try rfl)

/-- The relocations of PowerPC64 through the GOT. -/
theorem ppc64_got {env : Env} {site : Site} {slot : Int} {state after : LinkState} (hm : env.machine = emPpc64)
    (hg : gotEntry env (site.s + site.a) state = .ok slot after) :
    ((site.rel.typ = 14 ∨ site.rel.typ = 15) →
      (powerpc env site).run state = .ok (some [stAt env site 0 2 (slot - ppcToc env)]) after) ∧
    (site.rel.typ = 16 →
      (powerpc env site).run state = .ok (some [stAt env site 0 2 (ppcHi (slot - ppcToc env))]) after) ∧
    (site.rel.typ = 17 →
      (powerpc env site).run state = .ok (some [stAt env site 0 2 (ppcHa (slot - ppcToc env))]) after) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · rcases ht with ht | ht <;> link_run [powerpc, ht, hm, hg, bne_self_eq_false]
  · link_run [powerpc, ht, hm, hg, bne_self_eq_false]
  · link_run [powerpc, ht, hm, hg, bne_self_eq_false]

/-- The word of the instruction a little-endian halfword belongs to, for telling DS-form from DQ-form. -/
theorem ppcInsnOfHalf_little {env : Env} {site : Site} {state : LinkState} (hl : env.little = true) (hc : env.codeLittle = true)
    (hb : inSection site 0 4 state.memory.size = true) :
    ppcInsnOfHalf env site state = .ok (readNat state.memory true (site.off + 0) 4) state := by
  simp only [ppcInsnOfHalf, hl, ite_true, ldi, hc, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, hb]
  rfl

/-- On big-endian, the halfword is the second half of the word. -/
theorem ppcInsnOfHalf_big {env : Env} {site : Site} {state : LinkState} (hl : env.little = false) (ho : 2 ≤ site.off)
    (hb : inSection { site with off := site.off - 2 } 0 4 state.memory.size = true) :
    ppcInsnOfHalf env site state = .ok (readNat state.memory false (site.off - 2 + 0) 4) state := by
  have hn : ¬ site.off < 2 := by omega
  simp only [ppcInsnOfHalf, hl, Bool.false_eq_true, ite_false, hn, ElfLinker.load, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, hb, ite_true]
  rfl

/-- `R_PPC64_ADDR16_DS`, `R_PPC64_TOC16_DS` and `R_PPC64_TOC16_LO_DS`: the value goes in the offset of a DS-form or DQ-form
instruction. -/
theorem ppc64_ds {env : Env} {site : Site} {state : LinkState} {insn : Nat} (hm : env.machine = emPpc64)
    (hi : ppcInsnOfHalf env site state = .ok insn state) (hb : inSection site 0 2 state.memory.size = true) :
    let old := readNat state.memory env.little (site.off + 0) 2
    let x := site.s + site.a
    ((site.rel.typ = 56 ∨ site.rel.typ = 57) → (powerpc env site).run state =
      .ok (some [stAt env site 0 2 (ppcDsHalf (ppcIsDq insn) old x : Nat)]) state) ∧
    ((site.rel.typ = 63 ∨ site.rel.typ = 64) → (powerpc env site).run state =
      .ok (some [stAt env site 0 2 (ppcDsHalf (ppcIsDq insn) old (x - ppcToc env) : Nat)]) state) := by
  refine ⟨fun ht => ?_, fun ht => ?_⟩ <;> rcases ht with ht | ht <;>
    (link_run [powerpc, ht, hm, hi, hb, bne_self_eq_false]; try rfl)

/-- `R_PPC64_GOT16_DS` and `R_PPC64_GOT16_LO_DS`. -/
theorem ppc64_got_ds {env : Env} {site : Site} {state after : LinkState} {slot : Int} {insn : Nat} (hm : env.machine = emPpc64)
    (ht : site.rel.typ = 58 ∨ site.rel.typ = 59) (hg : gotEntry env (site.s + site.a) state = .ok slot after)
    (hi : ppcInsnOfHalf env site after = .ok insn after) (hb : inSection site 0 2 after.memory.size = true) :
    (powerpc env site).run state = .ok (some [stAt env site 0 2 (ppcDsHalf (ppcIsDq insn)
      (readNat after.memory env.little (site.off + 0) 2) (slot - ppcToc env) : Nat)]) after := by
  rcases ht with ht | ht <;> (link_run [powerpc, ht, hm, hg, hi, hb, bne_self_eq_false]; try rfl)

/-- The local entry of a function of ELFv2: none, or `1 << v` bytes for the three top bits `v` of `st_other`. -/
theorem ppcLocalEntry_spec (other : Nat) :
    let v := (other >>> 5) % 8
    (v ≤ 1 ∨ v = 7 → ppcLocalEntry other = 0) ∧ (2 ≤ v → v ≤ 6 → ppcLocalEntry other = 2 ^ v) := by
  intro v
  have hv : v = (other >>> 5) % 8 := rfl
  have hlt : v < 8 := Nat.mod_lt _ (by decide)
  unfold ppcLocalEntry
  rw [← hv]
  constructor
  · intro h
    have : v = 0 ∨ v = 1 ∨ v = 7 := by omega
    rcases this with h | h | h <;> rw [h] <;> rfl
  · intro h1 h2
    have : v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 := by omega
    rcases this with h | h | h | h | h <;> rw [h] <;> rfl

/-! ### SystemZ -/

/-- The relocations of SystemZ, with `X = S + A` and halfword-scaled displacements for the `DBL` ones. -/
def systemzData (x p : Int) : Nat → Option (Nat × Int)
  | 1 => some (1, x)
  | 3 => some (2, x)
  | 4 => some (4, x)
  | 5 | 8 => some (4, x - p)
  | 16 => some (2, x - p)
  | 17 | 18 => some (2, (x - p) >>> 1)
  | 19 | 20 => some (4, (x - p) >>> 1)
  | 22 => some (8, x)
  | 23 | 25 => some (8, x - p)
  | _ => none

theorem systemz_data {env : Env} {site : Site} {n : Nat} {value : Int} (state : LinkState)
    (h : systemzData (site.s + site.a) site.p site.rel.typ = some (n, value)) :
    (systemz env site).run state = .ok (some [stAt env site 0 n value]) state := by
  generalize ht : site.rel.typ = t at h
  unfold systemzData at h
  split at h <;> cases h <;> (link_run [systemz, ht]; try rfl)

/-- `R_390_12`: `S + A` in the low 12 bits, keeping the base register. -/
theorem systemz_12 {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 2)
    (hb : inSection site 0 2 state.memory.size = true) :
    (systemz env site).run state = .ok (some [stAt env site 0 2
      (setBits (readNat state.memory env.little (site.off + 0) 2) 0 12 (site.s + site.a) : Nat)]) state := by
  link_run [systemz, ht, hb]
  try rfl

/-! ### The rest of MIPS and the relocations that store nothing -/

/-- `R_MIPS_GOT_PAGE` of a 64-bit file: a local symbol in 32 bits needs no page entry, and the instruction becomes the `LUI` of
its page; the others take the entry of their page, from the global pointer. -/
theorem mips_got_page {env : Env} {site : Site} {slot : Int} {state after : LinkState} (ht : site.rel.typ = 20)
    (hw : env.width = 64) (hb : inSection site 0 4 state.memory.size = true) :
    let x := site.s + mipsA16 env site state
    let insn := readNat state.memory env.little (site.off + 0) 4
    ((site.sym.bind == stbLocal && sext x 32 == x) = true → (mips env site).run state = .ok (some [stAt env site 0 4
      ((0x3c000000 ||| (field (insn : Int) 16 5 <<< 16) ||| field (x + 0x8000) 16 16 : Nat) : Int)]) state) ∧
    ((site.sym.bind == stbLocal && sext x 32 == x) = false →
      gotEntry env ((x + 0x8000) - (x + 0x8000) % 65536) state = .ok slot after →
      (mips env site).run state = .ok (some [stAt env site 0 4 (setLo16 insn (slot - mipsGp env))]) after) := by
  intro x insn
  refine ⟨fun hl => ?_, fun hl hg => ?_⟩ <;>
    cases he : site.rel.isExplicit <;>
    simp only [x, mipsA16, he, ite_true, ite_false, Bool.false_eq_true] at hl ⊢ <;>
    (try simp only [x, mipsA16, he, ite_true, ite_false, Bool.false_eq_true] at hg) <;>
    (link_run [mips, ht, hb, he, hw, hl, beq_self_eq_true]; try simp_all <;> try rfl)

/-- `R_MIPS_GOT_OFST` of a 64-bit file: the offset from the page of `R_MIPS_GOT_PAGE`, or all of it where that was a `LUI`. -/
theorem mips_got_ofst {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 21) (hw : env.width = 64)
    (hb : inSection site 0 4 state.memory.size = true) :
    let x := site.s + mipsA16 env site state
    (mips env site).run state = .ok (some [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4)
      (if (site.sym.bind == stbLocal && sext x 32 == x) = true then x else x - ((x + 0x8000) - (x + 0x8000) % 65536)))]) state := by
  intro x
  cases he : site.rel.isExplicit <;>
    simp only [x, mipsA16, he, ite_true, ite_false, Bool.false_eq_true] <;>
    (link_run [mips, ht, hb, he, hw, beq_self_eq_true]; try rfl)

/-- `R_MIPS_HI16` of a record with its addend is done at once, and the `R_MIPS_GOT16` of a local symbol likewise. -/
theorem mips_hi16_explicit {env : Env} {site : Site} {state after : LinkState} {result : Unit}
    (ht : site.rel.typ = 5 ∨ (site.rel.typ = 9 ∧ site.sym.bind = stbLocal)) (he : site.rel.isExplicit = true)
    (ha : mipsApplyHi env site site.a state = .ok result after) :
    (mips env site).run state = .ok (some []) after := by
  rcases ht with ht | ⟨ht, hl⟩
  · link_run [mips, ht, he, ha]
  · have hl' : (site.sym.bind == stbLocal) = true := by simpa using hl
    link_run [mips, ht, he, ha, hl']

/-- Without an addend in the record, the half waits for its `R_MIPS_LO16`, with what it holds of the addend. -/
theorem mips_hi16_pending {env : Env} {site : Site} {state : LinkState}
    (ht : site.rel.typ = 5 ∨ (site.rel.typ = 9 ∧ site.sym.bind = stbLocal)) (he : site.rel.isExplicit = false)
    (hb : inSection site 0 4 state.memory.size = true) :
    (mips env site).run state = .ok (some []) { state with mipsPending :=
      (site, readNat state.memory env.little (site.off + 0) 4 &&& 0xffff) :: state.mipsPending } := by
  rcases ht with ht | ⟨ht, hl⟩
  · link_run [mips, ht, he, hb, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    try rfl
  · have hl' : (site.sym.bind == stbLocal) = true := by simpa using hl
    link_run [mips, ht, he, hb, hl', modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    try rfl

/-- The relocations that store nothing: `NONE`, and the markers of `R_ARM_V4BX`, `R_MIPS_JALR`, `R_RISCV_ALIGN` and
`R_RISCV_RELAX`. -/
theorem relocations_of_nothing (env : Env) (site : Site) (state : LinkState) :
    (site.rel.typ = 0 → (x86_64 env site).run state = .ok (some []) state) ∧
      (site.rel.typ = 0 → (i386 env site).run state = .ok (some []) state) ∧
      (site.rel.typ = 0 → (aarch64 env site).run state = .ok (some []) state) ∧
      ((site.rel.typ = 0 ∨ site.rel.typ = 0x28) → (arm env site).run state = .ok (some []) state) ∧
      ((site.rel.typ = 0 ∨ site.rel.typ = 37) → (mips env site).run state = .ok (some []) state) ∧
      ((site.rel.typ = 0 ∨ site.rel.typ = 43 ∨ site.rel.typ = 51) → (riscv env site).run state = .ok (some []) state) ∧
      (site.rel.typ = 0 → (powerpc env site).run state = .ok (some []) state) ∧
      (site.rel.typ = 0 → (systemz env site).run state = .ok (some []) state) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · simp only [x86_64, ht]; rfl
  · simp only [i386, ht]; rfl
  · simp only [aarch64, ht]; rfl
  · rcases ht with ht | ht <;> (simp only [arm, ht]; rfl)
  · rcases ht with ht | ht <;> (simp only [mips, ht]; rfl)
  · rcases ht with ht | ht | ht <;> (simp only [riscv, ht]; rfl)
  · simp only [powerpc, ht]; rfl
  · simp only [systemz, ht]; rfl

/-! ### The machines -/

/-- Each machine has its handler. -/
theorem handler_spec (env : Env) :
    (env.machine = 62 → handler env = some (x86_64 env)) ∧ (env.machine = 3 → handler env = some (i386 env)) ∧
      (env.machine = 183 → handler env = some (aarch64 env)) ∧ (env.machine = 40 → handler env = some (arm env)) ∧
      (env.machine = 8 → handler env = some (mips env)) ∧ (env.machine = 243 → handler env = some (riscv env)) ∧
      (env.machine = 20 → handler env = some (powerpc env)) ∧ (env.machine = 21 → handler env = some (powerpc env)) ∧
      (env.machine = 22 → handler env = some (systemz env)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp only [handler, h])


/-! ### The instructions of ARM and AArch64 objects

`lld-link` has the same instruction formats as ELF, and these patched words are built from the same encoders. -/

open Coff in
/-- The numbers of the relocations of ARM and AArch64, against `llvm/BinaryFormat/COFF.h`. -/
theorem relocationKind_instructions :
    relocationKind 0xaa64 0 = some .ignored ∧ relocationKind 0xaa64 1 = some (.absolute 4) ∧
      relocationKind 0xaa64 2 = some (.absolute 4) ∧ relocationKind 0xaa64 3 = some (.arm64Branch 0 26) ∧
      relocationKind 0xaa64 4 = some (.arm64Adr 12) ∧ relocationKind 0xaa64 5 = some (.arm64Adr 0) ∧
      relocationKind 0xaa64 6 = some (.arm64Add false) ∧ relocationKind 0xaa64 7 = some (.arm64Load false) ∧
      relocationKind 0xaa64 8 = some .sectionRelative ∧ relocationKind 0xaa64 9 = some (.arm64Add true) ∧
      relocationKind 0xaa64 0xa = some .arm64AddHigh ∧ relocationKind 0xaa64 0xb = some (.arm64Load true) ∧
      relocationKind 0xaa64 0xd = some .section ∧ relocationKind 0xaa64 0xe = some (.absolute 8) ∧
      relocationKind 0xaa64 0xf = some (.arm64Branch 5 19) ∧ relocationKind 0xaa64 0x10 = some (.arm64Branch 5 14) ∧
      relocationKind 0xaa64 0x11 = some (.relative 4) ∧
      relocationKind 0x01c4 0 = some .ignored ∧ relocationKind 0x01c4 1 = some (.absolute 4) ∧
      relocationKind 0x01c4 2 = some (.absolute 4) ∧ relocationKind 0x01c4 0xa = some (.relative 4) ∧
      relocationKind 0x01c4 0xe = some .section ∧ relocationKind 0x01c4 0xf = some .sectionRelative ∧
      relocationKind 0x01c4 0x10 = some .armMov32A ∧ relocationKind 0x01c4 0x11 = some .armMov32T ∧
      relocationKind 0x01c4 0x12 = some .armBranch20T ∧ relocationKind 0x01c4 0x14 = some .armBranch24T ∧
      relocationKind 0x01c4 0x15 = some .armBranch24T := by
  decide

open Coff in
/-- `ADR` and `ADRP`: the address with the addend in the instruction, from the place, in the immediate; and the rest stays. -/
theorem patched_adr (shift symbol place sectionAddr old : Nat) :
    let imm := sext (field (old : Int) 5 19 * 4 + field (old : Int) 29 2 : Nat) 21
    let value := ((symbol + imm) >>> shift) - ((place : Int) >>> shift)
    let word := patchedInstruction (.arm64Adr shift) symbol place sectionAddr old
    field (word : Int) 5 19 * 4 + field (word : Int) 29 2 = field value 0 21 ∧
      ∀ j m, (j + m ≤ 5 ∨ (24 ≤ j ∧ j + m ≤ 29) ∨ 31 ≤ j) → field (word : Int) j m = field (old : Int) j m :=
  aarch64Adr_spec _ _

open Coff in
/-- `ADD`: the page offset of the address, or of its offset in its section, plus the addend in the immediate. -/
theorem patched_add (within : Bool) (symbol place sectionAddr old : Nat) :
    let base := if within then symbol - sectionAddr else symbol
    let word := patchedInstruction (.arm64Add within) symbol place sectionAddr old
    field (word : Int) 10 12 = (field (old : Int) 10 12 + base % 4096) % 4096 ∧
      ∀ j m, (j + m ≤ 10 ∨ 22 ≤ j) → field (word : Int) j m = field (old : Int) j m := by
  refine ⟨?_, fun j m h => field_setBits_other _ _ _ _ _ _ (by omega)⟩
  show field (setBits old 10 12 _ : Nat) 10 12 = _
  rw [field_setBits_self, field_natCast]
  simp

open Coff in
/-- `ADD` of `SECREL_HIGH12A`: the bits above the page offset, of the offset in the section with the addend. -/
theorem patched_add_high (symbol place sectionAddr old : Nat) :
    let word := patchedInstruction .arm64AddHigh symbol place sectionAddr old
    field (word : Int) 10 12 = ((symbol - sectionAddr + field (old : Int) 10 12) / 4096) % 4096 ∧
      ∀ j m, (j + m ≤ 10 ∨ 22 ≤ j) → field (word : Int) j m = field (old : Int) j m := by
  refine ⟨?_, fun j m h => field_setBits_other _ _ _ _ _ _ (by omega)⟩
  show field (setBits old 10 12 _ : Nat) 10 12 = _
  rw [field_setBits_self, field_natCast, Nat.shiftRight_eq_div_pow]
  simp

open Coff in
/-- Loads and stores: the page offset scaled by the size of the access, plus the addend in the immediate, cut to the range
that the scale leaves in a page. -/
theorem patched_load (within : Bool) (symbol place sectionAddr old : Nat) :
    let base := if within then symbol - sectionAddr else symbol
    let scale := arm64LoadScale old
    let word := patchedInstruction (.arm64Load within) symbol place sectionAddr old
    field (word : Int) 10 12 % 2 ^ (12 - scale) = (field (old : Int) 10 12 + (base % 4096) >>> scale) % 2 ^ (12 - scale) ∧
      ∀ j m, (j + m ≤ 10 ∨ 22 ≤ j) → field (word : Int) j m = field (old : Int) j m := by
  refine ⟨?_, fun j m h => field_setBits_other _ _ _ _ _ _ (by omega)⟩
  show field (setBits old 10 12 _ : Nat) 10 12 % _ = _
  rw [field_setBits_self]
  simp only [field_natCast]
  simp only [Nat.pow_zero, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)) |>.trans (Nat.mod_mod _ _)

open Coff in
/-- The scale of a load: the size bits, or 4 for a 128-bit access of the SIMD registers. -/
theorem arm64LoadScale_spec (word : Nat) :
    arm64LoadScale word = if field (word : Int) 26 1 == 1 && field (word : Int) 23 1 == 1 then field (word : Int) 30 2 + 4
      else field (word : Int) 30 2 := rfl

open Coff in
/-- Branches: `S + A - P` in words, the addend being in the immediate, and the rest stays. -/
theorem patched_branch (lo n symbol place sectionAddr old : Nat) :
    let value := symbol + sext (field (old : Int) lo n * 4 : Nat) (n + 2) - (place : Int)
    let word := patchedInstruction (.arm64Branch lo n) symbol place sectionAddr old
    field (word : Int) lo n = field value 2 n ∧
      ∀ j m, (j + m ≤ lo ∨ lo + n ≤ j) → field (word : Int) j m = field (old : Int) j m := by
  refine ⟨?_, fun j m h => field_setBits_other _ _ _ _ _ _ h⟩
  show field (setBits old lo n _ : Nat) lo n = _
  rw [field_setBits_self, field_shiftRight, Nat.add_zero]

/-- Halfwords put together give themselves back. -/
theorem halves_spec {a b : Nat} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    field ((a + b * 2 ^ 16 : Nat) : Int) 0 16 = a ∧ field ((a + b * 2 ^ 16 : Nat) : Int) 16 16 = b := by
  simp only [field_natCast]
  omega

open Coff in
/-- Thumb conditional branches: `S + A - (P + 4)`, the addend being in the immediate. -/
theorem patched_branch20T (symbol place sectionAddr old : Nat) :
    let hw1 := field (old : Int) 0 16
    let hw2 := field (old : Int) 16 16
    let value := symbol + thumbJump19Imm hw1 hw2 - ((place : Int) + 4)
    let word := patchedInstruction .armBranch20T symbol place sectionAddr old
    thumbJump19Imm (field (word : Int) 0 16) (field (word : Int) 16 16) = sext (field value 1 20 * 2 ^ 1 : Nat) (1 + 20) := by
  intro hw1 hw2 value word
  have h1 : thumbJump19Set1 hw1 value < 2 ^ 16 :=
    setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have h2 : thumbJump19Set2 hw2 value < 2 ^ 16 :=
    setBits_lt _ (setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)) (by omega)
  have ⟨e1, e2⟩ := halves_spec h1 h2
  have hw : word = thumbJump19Set1 hw1 value + thumbJump19Set2 hw2 value * 2 ^ 16 := rfl
  rw [hw, e1, e2]
  exact (thumbJump19Set_spec hw1 hw2 value).1

open Coff in
/-- Thumb `B.W`, `BL` and `BLX`: `S + A - pc`, from the pc aligned to a word for a `BLX`, and the opcode bit stays. -/
theorem patched_branch24T (symbol place sectionAddr old : Nat) :
    let hw1 := field (old : Int) 0 16
    let hw2 := field (old : Int) 16 16
    let pc := (place : Int) + 4
    let value := symbol + thumbBranchImm hw1 hw2 - (if field (hw2 : Int) 12 1 == 0 then pc - pc % 4 else pc)
    let word := patchedInstruction .armBranch24T symbol place sectionAddr old
    thumbBranchImm (field (word : Int) 0 16) (field (word : Int) 16 16) = sext (field value 1 24 * 2 ^ 1 : Nat) (1 + 24) ∧
      field (field (word : Int) 16 16 : Int) 12 1 = field (hw2 : Int) 12 1 := by
  intro hw1 hw2 pc value word
  have h1 : thumbBranchSet1 hw1 value < 2 ^ 16 := setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have h2 : thumbBranchSet2 hw2 value < 2 ^ 16 :=
    setBits_lt _ (setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)) (by omega)
  have ⟨e1, e2⟩ := halves_spec h1 h2
  have hw : word = thumbBranchSet1 hw1 value + thumbBranchSet2 hw2 value * 2 ^ 16 := rfl
  rw [hw, e1, e2]
  exact ⟨(thumbBranchSet_spec hw1 hw2 value).1, (thumbBranchSet_spec hw1 hw2 value).2.2 12 1 (by omega)⟩

open Coff in
/-- Thumb `MOVW` and `MOVT` in a row: `S + A`, whose addend is in their immediates, split between them. -/
theorem patched_mov32T (symbol place sectionAddr old : Nat) :
    let hw1 := field (old : Int) 0 16
    let hw2 := field (old : Int) 16 16
    let hw3 := field (old : Int) 32 16
    let hw4 := field (old : Int) 48 16
    let value : Int := symbol + (thumbMovImm hw1 hw2 + thumbMovImm hw3 hw4 * 2 ^ 16 : Nat)
    let word := patchedInstruction .armMov32T symbol place sectionAddr old
    thumbMovImm (field (word : Int) 0 16) (field (word : Int) 16 16) = field value 0 16 ∧
      thumbMovImm (field (word : Int) 32 16) (field (word : Int) 48 16) = field value 16 16 := by
  intro hw1 hw2 hw3 hw4 value word
  have h1 : thumbMovSet1 hw1 value < 2 ^ 16 := setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have h2 : thumbMovSet2 hw2 value < 2 ^ 16 := setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have h3 : thumbMovSet1 hw3 (value >>> 16) < 2 ^ 16 := setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have h4 : thumbMovSet2 hw4 (value >>> 16) < 2 ^ 16 := setBits_lt _ (setBits_lt _ (field_lt ..) (by omega)) (by omega)
  have hw : word = (thumbMovSet1 hw1 value + thumbMovSet2 hw2 value * 2 ^ 16) +
      (thumbMovSet1 hw3 (value >>> 16) + thumbMovSet2 hw4 (value >>> 16) * 2 ^ 16) * 2 ^ 32 := rfl
  rw [hw]
  simp only [field_natCast]
  have ha := (thumbMovSet_spec hw1 hw2 value).1
  have hb := (thumbMovSet_spec hw3 hw4 (value >>> 16)).1
  rw [field_shiftRight] at hb
  simp only [Nat.add_zero] at hb
  have r1 : (thumbMovSet1 hw1 value + thumbMovSet2 hw2 value * 2 ^ 16 +
      (thumbMovSet1 hw3 (value >>> 16) + thumbMovSet2 hw4 (value >>> 16) * 2 ^ 16) * 2 ^ 32) / 2 ^ 0 % 2 ^ 16 = thumbMovSet1 hw1 value := by omega
  have r2 : (thumbMovSet1 hw1 value + thumbMovSet2 hw2 value * 2 ^ 16 +
      (thumbMovSet1 hw3 (value >>> 16) + thumbMovSet2 hw4 (value >>> 16) * 2 ^ 16) * 2 ^ 32) / 2 ^ 16 % 2 ^ 16 = thumbMovSet2 hw2 value := by omega
  have r3 : (thumbMovSet1 hw1 value + thumbMovSet2 hw2 value * 2 ^ 16 +
      (thumbMovSet1 hw3 (value >>> 16) + thumbMovSet2 hw4 (value >>> 16) * 2 ^ 16) * 2 ^ 32) / 2 ^ 32 % 2 ^ 16 = thumbMovSet1 hw3 (value >>> 16) := by omega
  have r4 : (thumbMovSet1 hw1 value + thumbMovSet2 hw2 value * 2 ^ 16 +
      (thumbMovSet1 hw3 (value >>> 16) + thumbMovSet2 hw4 (value >>> 16) * 2 ^ 16) * 2 ^ 32) / 2 ^ 48 % 2 ^ 16 = thumbMovSet2 hw4 (value >>> 16) := by omega
  rw [r1, r2, r3, r4]
  exact ⟨ha, hb⟩

open Coff in
/-- A pointer to Thumb code has the low bit set unless it is an offset, as `lld-link` also does it. Elsewhere nothing changes. -/
theorem withThumbBit_spec (machine flags symbol : Nat) (kind : RelocationKind) :
    (machine ≠ 0x01c0 → machine ≠ 0x01c2 → machine ≠ 0x01c4 → withThumbBit machine kind flags symbol = symbol) ∧
      withThumbBit machine .sectionRelative flags symbol = symbol ∧
      (flags &&& 0x20000000 = 0 → withThumbBit machine kind flags symbol = symbol) ∧
      (symbol % 2 = 1 → withThumbBit machine kind flags symbol = symbol) := by
  unfold withThumbBit
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2 h3
    simp [h1, h2, h3]
  · simp
  · intro h
    simp [h]
  · intro h
    simp [h]

/-! ### The driver

The theorems above are about one relocation. These are about `relocate` and `link`: the two passes go through all of the
relocations in their order, what fails is a warning and doesn't stop them, and in the end the bytes of the input that no
relocation is in are as they were. -/

/-- The state an action leaves behind, whether it failed or not. -/
def stateOf : EStateM.Result String LinkState α → LinkState
  | .ok _ state => state
  | .error _ state => state

/-- What fails under `guard` is a warning, and `guard` itself never fails. -/
theorem guard_run (action : LinkM Unit) (state : LinkState) :
    guard action state = .ok () (match action state with
      | .ok _ after => after
      | .error message after => { after with warnings := message :: after.warnings }) := by
  show EStateM.tryCatch action warn state = _
  simp only [EStateM.tryCatch]
  cases action state <;> rfl

theorem guard_ok (action : LinkM Unit) (state : LinkState) :
    guard action state = .ok () (stateOf (guard action state)) := by
  rw [guard_run]; rfl

theorem bind_ok {m : LinkM α} {f : α → LinkM β} {state after : LinkState} {result : α} (h : m state = .ok result after) :
    (m >>= f) state = f result after := by
  simp [bind, EStateM.bind, h]

/-- A loop whose body doesn't fail is a fold. -/
theorem forIn_fold (f : β → LinkM Unit) (hf : ∀ b state, f b state = .ok () (stateOf (f b state))) (list : List β)
    (state : LinkState) :
    (forIn list PUnit.unit fun b _ => do f b; pure (ForInStep.yield PUnit.unit) : LinkM PUnit) state =
      .ok PUnit.unit (list.foldl (fun state b => stateOf (f b state)) state) := by
  induction list generalizing state with
  | nil => rfl
  | cons b rest ih =>
    rw [List.forIn_cons]
    have hb : (do f b; pure (ForInStep.yield PUnit.unit) : LinkM _) state = .ok (ForInStep.yield PUnit.unit) (stateOf (f b state)) :=
      bind_ok (hf b state)
    exact (bind_ok hb).trans (ih _)

/-- **The relocations of a machine with a handler**: both passes go through all of them in their order, whatever becomes of
each, and then MIPS finishes what is pending. -/
theorem relocate_run {tables : Tables} {apply : Site → Outcome} (h : handler tables.env = some apply) (state : LinkState) :
    relocate tables state = .ok () (
      let prescanned := tables.input.relocations.foldl (fun state rel => stateOf (prescanOne tables rel state)) state
      let applied := tables.input.relocations.foldl (fun state rel => stateOf (applyOne tables apply rel state)) prescanned
      if tables.env.machine == emMips then stateOf (guard (mipsFinish tables.env) applied) else applied) := by
  simp only [relocate, h]
  refine (bind_ok (forIn_fold (prescanOne tables) (fun _ _ => guard_ok _ _) _ state)).trans ?_
  refine (bind_ok (forIn_fold (applyOne tables apply) (fun _ _ => guard_ok _ _) _ _)).trans ?_
  split
  · exact guard_ok _ _
  · rfl

theorem applyOne_ok (tables : Tables) (apply : Site → Outcome) (rel : Rel) (state : LinkState) :
    applyOne tables apply rel state = .ok () (stateOf (applyOne tables apply rel state)) := guard_ok _ _

/-! Memory: a byte can change only where some action may write. -/

/-- An action that keeps the pending sites good, doesn't shrink the memory, and changes only bytes that `P` allows. -/
def Frame (P : Nat → Prop) (S : Site → Prop) (m : LinkM α) : Prop :=
  ∀ state : LinkState, (∀ entry ∈ state.mipsPending, S entry.1) →
    let after := stateOf (m state)
    (∀ entry ∈ after.mipsPending, S entry.1) ∧ state.memory.size ≤ after.memory.size ∧
      ∀ o, o < state.memory.size → ¬ P o → after.memory.get! o = state.memory.get! o

namespace Frame

variable {P : Nat → Prop} {S : Site → Prop}

theorem pure (a : α) : Frame P S (Pure.pure a : LinkM α) := fun _ h => ⟨h, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem throw (e : String) : Frame P S (MonadExcept.throw e : LinkM α) := fun _ h => ⟨h, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem get : Frame P S (MonadState.get : LinkM LinkState) := fun _ h => ⟨h, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem bind {m : LinkM α} {f : α → LinkM β} (hm : Frame P S m) (hf : ∀ a, Frame P S (f a)) : Frame P S (m >>= f) := by
  intro state hp
  have h1 := hm state hp
  dsimp only at h1 ⊢
  cases hr : m state with
  | error e after =>
    have he : (m >>= f) state = .error e after := by simp [Bind.bind, EStateM.bind, hr]
    rw [he]
    rw [hr] at h1
    exact h1
  | ok a after =>
    rw [bind_ok hr]
    rw [hr] at h1
    obtain ⟨p1, s1, f1⟩ := h1
    obtain ⟨p2, s2, f2⟩ := hf a after p1
    refine ⟨p2, Nat.le_trans s1 s2, fun o ho hn => ?_⟩
    exact (f2 o (Nat.lt_of_lt_of_le ho s1) hn).trans (f1 o ho hn)

theorem modify {f : LinkState → LinkState} (hp : ∀ state : LinkState, (∀ entry ∈ state.mipsPending, S entry.1) →
      ∀ entry ∈ (f state).mipsPending, S entry.1) (hm : ∀ state, (f state).memory = state.memory) :
    Frame P S (_root_.modify f : LinkM PUnit) := fun state h =>
  ⟨hp state h, by
    show state.memory.size ≤ (f state).memory.size
    rw [hm]
    exact Nat.le_refl _, fun o _ _ => by
    show (f state).memory.get! o = _
    rw [hm]⟩

theorem forIn {list : List β} {init : γ} {f : β → γ → LinkM (ForInStep γ)} (hf : ∀ b ∈ list, ∀ c, Frame P S (f b c)) :
    Frame P S (ForIn.forIn list init f) := by
  induction list generalizing init with
  | nil => exact pure _
  | cons b rest ih =>
    rw [List.forIn_cons]
    refine bind (hf b (by simp) init) fun step => ?_
    cases step with
    | done c => exact pure _
    | yield c => exact ih fun b hb => hf b (by simp [hb])

/-- An action that starts by looking at the state knows what the state is. -/
theorem get_bind {f : LinkState → LinkM α} (h : ∀ state : LinkState, (∀ entry ∈ state.mipsPending, S entry.1) →
      let after := stateOf (f state state)
      (∀ entry ∈ after.mipsPending, S entry.1) ∧ state.memory.size ≤ after.memory.size ∧
        ∀ o, o < state.memory.size → ¬ P o → after.memory.get! o = state.memory.get! o) :
    Frame P S (MonadState.get >>= f) := fun state hp => h state hp

end Frame

variable {P : Nat → Prop} {S : Site → Prop}

/-- The sites whose bytes `P` allows to change. -/
def SiteIn (P : Nat → Prop) (site : Site) : Prop := ∀ o, site.off ≤ o → o < site.limit → P o

theorem frame_load (site : Site) (at' n : Nat) (little : Bool) : Frame P S (load site at' n little) := by
  unfold ElfLinker.load
  refine Frame.bind Frame.get fun state => ?_
  split
  · exact Frame.pure _
  · exact Frame.throw _

theorem frame_commit {site : Site} (hs : SiteIn P site) (writes : List Write) : Frame P S (commit site writes) := by
  unfold commit
  refine Frame.get_bind fun state hp => ?_
  split
  · next hall =>
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hall
    obtain ⟨hsize, hkeep⟩ := commit_fold writes state.memory fun w hw => (hall w hw).2
    refine ⟨hp, Nat.le_of_eq hsize.symm, fun o _ hn => hkeep o fun w hw => ?_⟩
    have := hall w hw
    by_cases h1 : o < w.off
    · exact .inl h1
    · refine .inr (Classical.byContradiction fun h2 => hn (hs o ?_ ?_)) <;> omega
  · exact ⟨hp, Nat.le_refl _, fun _ _ _ => rfl⟩

theorem pushes_spec (memory : ByteArray) (list : List Nat) :
    let padded := list.foldl (init := memory) fun memory _ => memory.push 0
    padded.size = memory.size + list.length ∧ ∀ o, o < memory.size → padded.get! o = memory.get! o := by
  induction list generalizing memory with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons x rest ih =>
    have hs : (memory.push 0).size = memory.size + 1 := by simp
    obtain ⟨h1, h2⟩ := ih (memory.push 0)
    refine ⟨by simp only [List.foldl_cons, List.length_cons]; rw [h1, hs]; omega, fun o ho => ?_⟩
    simp only [List.foldl_cons]
    rw [h2 o (by omega)]
    show (memory.data.push (0 : UInt8))[o]! = memory.data[o]!
    have ho' : o < memory.data.size := ho
    rw [getElem!_pos (memory.data.push (0 : UInt8)) o (by simp; omega), getElem!_pos memory.data o ho', Array.getElem_push_lt]

theorem frame_gotEntry {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (value : Int) : Frame P S (gotEntry env value) := by
  unfold gotEntry
  refine Frame.get_bind fun state hp => ?_
  cases hc : state.got[field value 0 64]? with
  | some slot =>
    dsimp only
    exact ⟨hp, Nat.le_refl _, fun _ _ _ => rfl⟩
  | none =>
    dsimp only
    obtain ⟨hs, hk⟩ := pushes_spec state.memory (List.range (env.gotOff + state.gotCount * (env.width / 8) + env.width / 8 - state.memory.size))
    simp only [List.length_range] at hs
    generalize hp' : (List.range (env.gotOff + state.gotCount * (env.width / 8) + env.width / 8 - state.memory.size)).foldl (init := state.memory)
      (fun memory _ => memory.push 0) = padded at hs hk
    obtain ⟨w1, w2, _⟩ := writeNat_spec (memory := padded) (off := env.gotOff + state.gotCount * (env.width / 8)) (n := env.width / 8)
      (little := env.little) (value := value) (by omega)
    subst hp'
    refine ⟨hp, by show _ ≤ (writeNat _ _ _ _ _).size; rw [w1]; omega, fun o ho hn => ?_⟩
    show (writeNat _ _ _ _ _).get! o = _
    have hlt : o < env.gotOff := Nat.lt_of_not_le fun h => hn (hg o h)
    rw [w2 o (.inl (by omega)), hk o ho]

theorem frame_ld (env : Env) (site : Site) (at' n : Nat) : Frame P S (ld env site at' n) := frame_load _ _ _ _

theorem frame_ldInt (env : Env) (site : Site) (at' n : Nat) : Frame P S (ldInt env site at' n) :=
  Frame.bind (frame_ld _ _ _ _) fun _ => Frame.pure _

theorem frame_ldi (env : Env) (site : Site) (at' n : Nat) : Frame P S (ldi env site at' n) := frame_load _ _ _ _

theorem frame_done (writes : List Write) : Frame P S (done writes) := Frame.pure _

/-- What every handler is made of. Only reducible unification: a failing `exact` at default transparency unfolds all of
`EStateM`, which is what this took a minute for. -/
local macro "frame_auto" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible apply Frame.bind
    | with_reducible apply Frame.forIn
    | with_reducible exact Frame.pure _
    | with_reducible exact Frame.throw _
    | with_reducible exact Frame.get
    | with_reducible exact frame_done _
    | with_reducible exact frame_ld _ _ _ _
    | with_reducible exact frame_ldInt _ _ _ _
    | with_reducible exact frame_ldi _ _ _ _
    | with_reducible exact frame_load _ _ _ _
    | with_reducible exact frame_gotEntry ‹_› _
    | split
    | intro _)

theorem frame_x86_64 {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (x86_64 env site) := by
  unfold x86_64
  dsimp only
  split <;> frame_auto

theorem frame_i386 {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (i386 env site) := by
  unfold i386
  dsimp only
  split <;> frame_auto

theorem frame_aarch64 {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (aarch64 env site) := by
  unfold aarch64
  dsimp only
  split <;> frame_auto

theorem frame_arm {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (arm env site) := by
  unfold arm
  dsimp only
  split <;> frame_auto

theorem frame_systemz {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (systemz env site) := by
  unfold systemz
  dsimp only
  split <;> frame_auto

theorem frame_ppcInsnOfHalf {env : Env} {site : Site} : Frame P S (ppcInsnOfHalf env site) := by
  unfold ppcInsnOfHalf
  frame_auto

theorem frame_powerpc {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (powerpc env site) := by
  unfold powerpc
  dsimp only
  have := @frame_ppcInsnOfHalf P S env site
  split <;> frame_auto

theorem frame_ulebLength {env : Env} {site : Site} (fuel n : Nat) : Frame P S (ulebLength env site fuel n) := by
  induction fuel generalizing n with
  | zero => exact Frame.pure _
  | succ fuel ih =>
    unfold ulebLength
    refine Frame.bind (frame_load _ _ _ _) fun _ => ?_
    split
    · exact Frame.pure _
    · exact ih _

theorem frame_rewriteUleb {env : Env} {site : Site} (f : Nat → Int) : Frame P S (rewriteUleb env site f) := by
  unfold rewriteUleb
  refine Frame.bind (frame_ulebLength _ _) fun _ => ?_
  frame_auto

theorem frame_riscv {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (riscv env site) := by
  unfold riscv
  dsimp only
  split <;> first
    | with_reducible exact frame_rewriteUleb _
    | frame_auto

/-- A deferred half is resolved at its own site. -/
theorem frame_mipsApplyHi {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) {site : Site} (hs : SiteIn P site) (ahl : Int) :
    Frame P S (mipsApplyHi env site ahl) := by
  unfold mipsApplyHi
  refine Frame.bind (frame_load _ _ _ _) fun _ => ?_
  dsimp only
  split
  · exact frame_commit hs _
  · exact Frame.bind (frame_gotEntry hg _) fun _ => frame_commit hs _

theorem frame_mipsFlush {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (lo : Int) (symbol : Nat) :
    Frame P (SiteIn P) (mipsFlush env lo symbol) := by
  unfold mipsFlush
  refine Frame.get_bind fun state hp => ?_
  dsimp only
  generalize hpart : state.mipsPending.partition (fun entry => entry.1.rel.symbol == symbol) = parts
  obtain ⟨matched, rest⟩ := parts
  have hboth : (∀ entry ∈ matched, entry ∈ state.mipsPending) ∧ ∀ entry ∈ rest, entry ∈ state.mipsPending := by
    rw [List.partition_eq_filter_filter] at hpart
    simp only [Prod.mk.injEq] at hpart
    rw [← hpart.1, ← hpart.2]
    exact ⟨fun _ h => (List.mem_filter.mp h).1, fun _ h => (List.mem_filter.mp h).1⟩
  have hloop : Frame P (SiteIn P) (forIn matched.reverse PUnit.unit
      fun entry _ => do
        mipsApplyHi env entry.1 ((entry.2 : Int) * 65536 + lo)
        pure (ForInStep.yield PUnit.unit)) := by
    apply Frame.forIn
    intro entry hentry c
    exact Frame.bind (frame_mipsApplyHi hg (hp entry (hboth.1 entry (List.mem_reverse.mp hentry))) _) fun _ => Frame.pure _
  have hset : ∀ entry ∈ ({ state with mipsPending := rest } : LinkState).mipsPending, SiteIn P entry.1 :=
    fun entry hentry => hp entry (hboth.2 entry hentry)
  exact (Frame.bind hloop fun _ => Frame.pure _) _ hset

theorem frame_mipsCompound {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (mipsCompound env site) := by
  unfold mipsCompound mipsCompoundBase
  dsimp only
  frame_auto

theorem frame_pending {site : Site} (hs : SiteIn P site) (stored : Nat) :
    Frame P (SiteIn P) (modify fun state : LinkState => { state with mipsPending := (site, stored) :: state.mipsPending } : LinkM PUnit) :=
  Frame.modify (fun _ hp entry hentry => by
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact hs
    · exact hp _ hentry) (fun _ => rfl)

theorem frame_mips {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) {site : Site} (hs : SiteIn P site) :
    Frame P (SiteIn P) (mips env site) := by
  unfold mips
  dsimp only
  have hflush := fun lo symbol => frame_mipsFlush (P := P) hg lo symbol
  have happly := fun ahl => frame_mipsApplyHi (P := P) (S := SiteIn P) hg hs ahl
  have hcompound := frame_mipsCompound (P := P) (S := SiteIn P) hg site
  have hpend := frame_pending (P := P) hs
  split <;> repeat' first
    | with_reducible apply Frame.bind
    | with_reducible exact Frame.pure _
    | with_reducible exact hflush _ _
    | with_reducible exact happly _
    | with_reducible exact hcompound
    | with_reducible exact hpend _
    | with_reducible exact Frame.throw _
    | with_reducible exact Frame.get
    | with_reducible exact frame_done _
    | with_reducible exact frame_ld _ _ _ _
    | with_reducible exact frame_ldInt _ _ _ _
    | with_reducible exact frame_load _ _ _ _
    | with_reducible exact frame_gotEntry ‹_› _
    | split
    | intro _

theorem frame_handler {env : Env} {apply : Site → Outcome} (hh : handler env = some apply) (hg : ∀ o, env.gotOff ≤ o → P o)
    {site : Site} (hs : SiteIn P site) : Frame P (SiteIn P) (apply site) := by
  unfold handler at hh
  split at hh <;> cases hh
  · exact frame_x86_64 hg site
  · exact frame_i386 hg site
  · exact frame_aarch64 hg site
  · exact frame_arm hg site
  · exact frame_mips hg hs
  · exact frame_riscv hg site
  · exact frame_powerpc hg site
  · exact frame_powerpc hg site
  · exact frame_systemz hg site

theorem frame_warn (message : String) : Frame P S (warn message) :=
  Frame.modify (fun _ hp => hp) (fun _ => rfl)

theorem frame_checkField (env : Env) (site : Site) : Frame P S (checkField env site) := by
  unfold checkField
  refine Frame.bind Frame.get fun _ => ?_
  split
  · exact frame_warn _
  · exact Frame.pure _

theorem frame_applySite {env : Env} {apply : Site → Outcome} (hh : handler env = some apply) (hg : ∀ o, env.gotOff ≤ o → P o)
    {site : Site} (hs : SiteIn P site) : Frame P (SiteIn P) (applySite env apply site) := by
  unfold applySite
  refine Frame.bind (frame_handler hh hg hs) fun outcome => ?_
  cases outcome with
  | some writes => exact Frame.bind (frame_checkField _ _) fun _ => frame_commit hs _
  | none => exact frame_warn _

theorem frame_guard {action : LinkM Unit} (h : Frame P S action) : Frame P S (guard action) := by
  intro state hp
  have := h state hp
  dsimp only at this ⊢
  rw [guard_run]
  cases hr : action state with
  | ok _ after => rw [hr] at this; exact this
  | error message after => rw [hr] at this; exact this

theorem frame_siteOf (tables : Tables) (report : Bool) (rel : Rel) : Frame P S (siteOf tables report rel) := by
  unfold siteOf
  dsimp only
  repeat' first
    | exact Frame.pure _
    | exact frame_warn _
    | exact Frame.modify (fun _ hp => hp) (fun _ => rfl)
    | apply Frame.bind
    | split
    | intro _

/-- The bytes a link may change: its GOT, and the sections with a relocation. -/
def MayChange (tables : Tables) (o : Nat) : Prop :=
  tables.env.gotOff ≤ o ∨ ∃ rel ∈ tables.input.relocations, ∃ sec, tables.input.sections[rel.target]? = some sec ∧
    sec.off ≤ o ∧ o < sec.off + sec.size

/-- A site of a relocation is in the section of the relocation. -/
theorem relocatedSection_some {tables : Tables} {index : Nat} {sec : ElfLinker.Section} {addr : Nat}
    (h : relocatedSection tables index = some (sec, addr)) : tables.input.sections[index]? = some sec := by
  unfold relocatedSection at h
  cases hs : tables.input.sections[index]? with
  | none => simp [hs] at h
  | some found =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    cases ha : (tables.addrs[index]?).join with
    | none => simp [ha] at h
    | some addr' =>
      simp only [ha, Option.bind_some] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [h.1]
      · cases h

/-- What a site of a relocation is: its place and the bounds of the section of its relocation, whose file bytes stop at the GOT. -/
theorem siteOf_some {tables : Tables} {report : Bool} {rel : Rel} {state after : LinkState} {site : Site}
    (h : siteOf tables report rel state = .ok (some site) after) :
    ∃ sec base s, relocatedSection tables rel.target = some (sec, base) ∧ rel.offset < sec.size ∧
      resolveBranchTarget tables rel ((tables.input.symbols[rel.symbol]?).getD nullSym) = some s ∧
      site = ⟨rel, (tables.input.symbols[rel.symbol]?).getD nullSym, sec.name, base + rel.offset, s,
        if rel.isExplicit then rel.addend else 0, sec.off + rel.offset, min (sec.off + sec.size) tables.env.gotOff⟩ := by
  unfold siteOf at h
  dsimp only at h
  cases hsec : relocatedSection tables rel.target with
  | none =>
    rw [hsec] at h
    cases h
  | some found =>
    obtain ⟨sec, base⟩ := found
    rw [hsec] at h
    dsimp only at h
    by_cases hoff : rel.offset ≥ sec.size
    · rw [ite_eq_left hoff] at h
      exfalso
      revert h
      cases report <;> simp [bind, EStateM.bind, pure, EStateM.pure, warn, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    · rw [ite_eq_right hoff] at h
      cases hs : resolveBranchTarget tables rel ((tables.input.symbols[rel.symbol]?).getD nullSym) with
      | none =>
        rw [hs] at h
        exfalso
        revert h
        cases report <;> simp [bind, EStateM.bind, pure, EStateM.pure, warn, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      | some s =>
        rw [hs] at h
        refine ⟨sec, base, s, rfl, by omega, rfl, ?_⟩
        revert h
        cases report <;> (try cases isExternal tables.input.machine ((tables.input.symbols[rel.symbol]?).getD nullSym)) <;>
          simp [bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] <;>
          (intro h _; exact h.symm)

/-- A site of a relocation is in the section of the relocation. -/
theorem siteOf_in {tables : Tables} {report : Bool} {rel : Rel} (hrel : rel ∈ tables.input.relocations) {state after : LinkState}
    {site : Site} (h : siteOf tables report rel state = .ok (some site) after) : SiteIn (MayChange tables) site := by
  obtain ⟨sec, base, s, hsec, _, _, rfl⟩ := siteOf_some h
  intro o hlo hhi
  simp only at hlo hhi
  exact .inr ⟨rel, hrel, sec, relocatedSection_some hsec, by omega, by omega⟩

theorem Frame.bind_some {m : LinkM (Option α)} {f : Option α → LinkM β} {Q : α → Prop} (hm : Frame P S m)
    (hspec : ∀ state after a, m state = .ok (some a) after → Q a) (hnone : Frame P S (f none)) (hf : ∀ a, Q a → Frame P S (f (some a))) :
    Frame P S (m >>= f) := by
  intro state hp
  have h1 := hm state hp
  dsimp only at h1 ⊢
  cases hr : m state with
  | error e after =>
    have he : (m >>= f) state = .error e after := by simp [Bind.bind, EStateM.bind, hr]
    rw [he]
    rw [hr] at h1
    exact h1
  | ok a after =>
    rw [bind_ok hr]
    rw [hr] at h1
    obtain ⟨p1, s1, f1⟩ := h1
    have hf' : Frame P S (f a) := by
      cases a with
      | none => exact hnone
      | some a => exact hf a (hspec _ _ _ hr)
    obtain ⟨p2, s2, f2⟩ := hf' after p1
    exact ⟨p2, Nat.le_trans s1 s2, fun o ho hn => (f2 o (Nat.lt_of_lt_of_le ho s1) hn).trans (f1 o ho hn)⟩

theorem gotOff_may (tables : Tables) : ∀ o, tables.env.gotOff ≤ o → MayChange tables o := fun _ h => .inl h

theorem frame_riscvPrescan {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) (site : Site) : Frame P S (riscvPrescan env site) := by
  unfold riscvPrescan
  split <;> repeat' first
    | exact Frame.pure _
    | exact frame_gotEntry hg _
    | exact Frame.modify (fun _ hp => hp) (fun _ => rfl)
    | apply Frame.bind
    | intro _

theorem frame_prescanOne (tables : Tables) (rel : Rel) (hrel : rel ∈ tables.input.relocations) :
    Frame (MayChange tables) (SiteIn (MayChange tables)) (prescanOne tables rel) := by
  unfold prescanOne
  refine frame_guard (Frame.bind_some (frame_siteOf _ _ _) (fun _ _ _ h => siteOf_in hrel h) (Frame.pure _) fun site _ => ?_)
  dsimp only
  split
  · exact frame_riscvPrescan (gotOff_may tables) site
  · exact Frame.pure _

theorem frame_applyOne {tables : Tables} {apply : Site → Outcome} (hh : handler tables.env = some apply) (rel : Rel)
    (hrel : rel ∈ tables.input.relocations) :
    Frame (MayChange tables) (SiteIn (MayChange tables)) (applyOne tables apply rel) := by
  unfold applyOne
  exact frame_guard (Frame.bind_some (frame_siteOf _ _ _) (fun _ _ _ h => siteOf_in hrel h) (Frame.pure _)
    fun _ hs => frame_applySite hh (gotOff_may tables) hs)

theorem frame_mipsFinish {env : Env} (hg : ∀ o, env.gotOff ≤ o → P o) : Frame P (SiteIn P) (mipsFinish env) := by
  unfold mipsFinish
  refine Frame.bind Frame.get fun _ => ?_
  dsimp only
  refine Frame.bind ?_ fun _ => Frame.pure _
  apply Frame.forIn
  intro _ _ _
  exact Frame.bind (frame_mipsFlush hg _ _) fun _ => Frame.pure _

/-- **The bytes of a link change only in its GOT and in the sections with a relocation**, for all machines and whatever
becomes of the relocations. -/
theorem relocate_frame (tables : Tables) : Frame (MayChange tables) (SiteIn (MayChange tables)) (relocate tables) := by
  unfold relocate
  dsimp only
  split
  · refine Frame.bind (Frame.forIn fun rel hrel _ => ?_) fun _ => ?_
    · refine Frame.bind (frame_siteOf _ _ _) fun _ => ?_
      split <;> exact Frame.pure _
    · split
      · exact frame_warn _
      · exact Frame.pure _
  · next apply hh =>
    refine Frame.bind (Frame.forIn fun rel hrel _ => ?_) fun _ => ?_
    · exact Frame.bind (frame_prescanOne tables rel hrel) fun _ => Frame.pure _
    · refine Frame.bind (Frame.forIn fun rel hrel _ => ?_) fun _ => ?_
      · exact Frame.bind (frame_applyOne hh rel hrel) fun _ => Frame.pure _
      · split
        · exact frame_guard (frame_mipsFinish (gotOff_may tables))
        · exact Frame.pure _

/-- `link` is `relocate` on the tables of its layout. -/
theorem link_relocate (input : Input) :
    ∃ tables : Tables, tables.input = input ∧ tables.env.gotOff = input.data.size ∧ tables.env.machine = input.machine ∧
      tables.env.width = input.width ∧ tables.env.little = input.little ∧ tables.env.gp0 = input.gp0 ∧
      tables.addrs = (layoutSections input.sections.toList input.base).addrs ∧
      let after := stateOf (relocate tables { memory := input.data })
      (link input).memory = after.memory ∧ (link input).warnings = after.warnings.reverse ∧
        (link input).references = after.references.reverse ∧
        (link input).sectionAddrs = (layoutSections input.sections.toList input.base).addrs ∧
        (link input).applied = after.applied.reverse := by
  generalize hl : layoutSections input.sections.toList input.base = layout
  cases hc : placeCommons input.symbols.toList (alignUp layout.cursor (input.width / 8)) with
  | mk commons commonsEnd =>
    cases he : placeExternals input.machine (input.width / 8) input.symbols.toList (alignUp commonsEnd (input.width / 8)) with
    | mk externals externalsEnd =>
      refine ⟨⟨input, { machine := input.machine, width := input.width, little := input.little
                        codeLittle := input.little || input.machine == 183, gotBase := alignUp externalsEnd (input.width / 8)
                        gotOff := input.data.size, tls := tlsBlock input.sections.toList layout.addrs, gp0 := input.gp0 },
          layout.addrs, commons, externals⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      dsimp only [link]
      rw [hl, hc]
      dsimp only
      rw [he]
      dsimp only [EStateM.run]
      split <;> (rename_i heq; rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- **What a link leaves of the input**: its bytes, but for the sections with a relocation; and the GOT goes after them. -/
theorem link_keeps_bytes (input : Input) {o : Nat} (ho : o < input.data.size)
    (hout : ∀ rel ∈ input.relocations, ∀ sec, input.sections[rel.target]? = some sec → ¬ (sec.off ≤ o ∧ o < sec.off + sec.size)) :
    (link input).memory.get! o = input.data.get! o := by
  obtain ⟨tables, rfl, hg, _, _, _, _, _, hmem, _⟩ := link_relocate input
  obtain ⟨_, _, hkeep⟩ := relocate_frame tables { memory := tables.input.data } (by simp)
  rw [hmem]
  apply hkeep o ho
  rintro (h | ⟨rel, hrel, sec, hsec, h1, h2⟩)
  · omega
  · exact hout rel hrel sec hsec ⟨h1, h2⟩

/-- A link only adds to the bytes of the input. -/
theorem link_memory_size (input : Input) : input.data.size ≤ (link input).memory.size := by
  obtain ⟨tables, rfl, _, _, _, _, _, _, hmem, _⟩ := link_relocate input
  obtain ⟨_, hs, _⟩ := relocate_frame tables { memory := tables.input.data } (by simp)
  rw [hmem]
  exact hs

/-- **The check of a field is what warns, and the only thing that does**: it leaves all but the warnings as they are. -/
theorem checkField_run (env : Env) (site : Site) (state : LinkState) :
    checkField env site state = .ok () (if fieldFits env state site then state else
      { state with warnings := s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field" :: state.warnings }) := by
  have : checkField env site state = (if !fieldFits env state site then
      warn s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field" else (pure () : LinkM Unit)) state := rfl
  rw [this]
  cases fieldFits env state site <;> rfl

/-- **A relocation under the driver**: what its handler returns is stored if it is in bounds, and it warns exactly if it has to
cut what it stores. -/
theorem applySite_store {env : Env} {apply : Site → Outcome} {site : Site} {state after : LinkState} {writes : List Write}
    (h : apply site state = .ok (some writes) after)
    (hall : ∀ w ∈ writes, site.off ≤ w.off ∧ w.off + w.n ≤ site.limit ∧ w.off + w.n ≤ after.memory.size) :
    ∃ final, applySite env apply site state = .ok () final ∧
      final.memory = writes.foldl (init := after.memory) (fun memory w => writeNat memory w.little w.off w.n w.value) ∧
      final.mipsPending = after.mipsPending ∧
      final.warnings = (if fieldFits env after site then after.warnings else
        s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field" :: after.warnings) := by
  unfold applySite
  rw [bind_ok h]
  dsimp only
  rw [bind_ok (checkField_run env site after)]
  have hsize : (if fieldFits env after site then after else
      { after with warnings := s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field" :: after.warnings }).memory = after.memory := by
    split <;> rfl
  generalize hmid : (if fieldFits env after site then after else
      { after with warnings := s!"relocation of type {site.rel.typ} at {site.p} is out of range of its field" :: after.warnings }) = mid at hsize
  have hc := commit_run site writes mid
  rw [ite_eq_left (by
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, hsize]
    exact fun w hw => ⟨⟨(hall w hw).1, (hall w hw).2.1⟩, (hall w hw).2.2⟩)] at hc
  refine ⟨_, hc, by simp only [hsize]; rfl, ?_, ?_⟩
  · show mid.mipsPending = _
    rw [← hmid]
    split <;> rfl
  · show mid.warnings = _
    rw [← hmid]
    split <;> rfl

/-! An end to end theorem, of the commonest relocation of x86-64. -/

/-- The file offset of the place of a relocation. -/
def placeOf (tables : Tables) (rel : Rel) : Nat :=
  ((tables.input.sections[rel.target]?).map (·.off + rel.offset)).getD 0

/-- A relocation with a place of `n` bytes in the bytes of its section in the file, and a symbol with an address. -/
structure Placed (tables : Tables) (rel : Rel) (n : Nat) (sec : ElfLinker.Section) (base s : Nat) : Prop where
  located : relocatedSection tables rel.target = some (sec, base)
  bounds : rel.offset + n ≤ sec.size
  positive : 0 < n
  file : sec.off + sec.size ≤ tables.env.gotOff
  symbol : resolveBranchTarget tables rel ((tables.input.symbols[rel.symbol]?).getD nullSym) = some s

/-- The site of a relocation that is placed. -/
def placedSite (tables : Tables) (rel : Rel) (sec : ElfLinker.Section) (base s : Nat) : Site :=
  ⟨rel, (tables.input.symbols[rel.symbol]?).getD nullSym, sec.name, ((base + rel.offset : Nat) : Int), s,
    if rel.isExplicit then rel.addend else 0, sec.off + rel.offset, min (sec.off + sec.size) tables.env.gotOff⟩

theorem siteOf_placed {tables : Tables} {rel : Rel} {n : Nat} {sec : ElfLinker.Section} {base s : Nat}
    (h : Placed tables rel n sec base s) (state : LinkState) :
    siteOf tables false rel state = .ok (some (placedSite tables rel sec base s)) state := by
  have hb := h.bounds
  have hn := h.positive
  unfold siteOf
  dsimp only
  rw [h.located]
  dsimp only
  rw [ite_eq_right (by omega), h.symbol]
  rfl

/-- The value of `R_X86_64_PC32`, `S + A - P`. -/
def pc32Value (tables : Tables) (rel : Rel) (sec : ElfLinker.Section) (base s : Nat) : Int :=
  let site := placedSite tables rel sec base s
  site.s + site.a - site.p

/-- `R_X86_64_PC32` under the driver: the place gets the value, and a warning if that doesn't fit. -/
private theorem applyOne_pc32 {tables : Tables} {rel : Rel} {sec : ElfLinker.Section} {base s : Nat}
    (ht : rel.typ = 2) (h : Placed tables rel 4 sec base s) (state : LinkState)
    (hsize : tables.env.gotOff ≤ state.memory.size) :
    (stateOf (applyOne tables (x86_64 tables.env) rel state)).memory =
      writeNat state.memory tables.env.little (sec.off + rel.offset) 4 (pc32Value tables rel sec base s) := by
  have hb := h.bounds
  have hf := h.file
  have hst := x86_64_pc32 (env := tables.env) (site := placedSite tables rel sec base s) ht state
  obtain ⟨final, hfinal, hmem, _, _⟩ := applySite_store (env := tables.env) (apply := x86_64 tables.env) hst (by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp only [stAt, placedSite]
    omega)
  rw [applyOne, guard_run, bind_ok (siteOf_placed h state)]
  dsimp only
  rw [hfinal]
  simp only [stateOf]
  rw [hmem]
  rfl

/-- **`R_X86_64_PC32` through all of `relocate`**: when the relocations of a file are all of this type, each with a place
in its section and a symbol with an address, and no two places overlap, each place ends up holding `S + A - P`, cut to its 32
bits. -/
theorem relocate_x86_64_pc32 {tables : Tables} (hm : tables.env.machine = 62) (hl : tables.env.little = true) (state : LinkState)
    (hsize : tables.env.gotOff ≤ state.memory.size)
    (hplaced : ∀ rel ∈ tables.input.relocations, rel.typ = 2 ∧ ∃ sec base s, Placed tables rel 4 sec base s)
    (hdisjoint : tables.input.relocations.Pairwise fun left right =>
      placeOf tables left + 4 ≤ placeOf tables right ∨ placeOf tables right + 4 ≤ placeOf tables left)
    {rel : Rel} (hrel : rel ∈ tables.input.relocations) {sec : ElfLinker.Section} {base s : Nat}
    (hplace : Placed tables rel 4 sec base s) :
    readNat (stateOf (relocate tables state)).memory true (sec.off + rel.offset) 4 =
      field (pc32Value tables rel sec base s) 0 32 := by
  have hhandler : handler tables.env = some (x86_64 tables.env) := by simp only [handler, hm]
  rw [relocate_run hhandler]
  simp only [stateOf, hm]
  rw [show (62 == emMips) = false from rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hunique : ∀ {r : Rel} {sec sec' : ElfLinker.Section} {base base' s s' : Nat}, Placed tables r 4 sec base s →
      Placed tables r 4 sec' base' s' → sec = sec' ∧ base = base' ∧ s = s' := by
    intro r sec sec' base base' s s' h h'
    have h1 := h.located.symm.trans h'.located
    have h2 := h.symbol.symm.trans h'.symbol
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
    exact ⟨h1.1, h1.2, h2⟩
  have hplaceOf : ∀ {r : Rel} {sec : ElfLinker.Section} {base s : Nat}, Placed tables r 4 sec base s →
      placeOf tables r = sec.off + r.offset := by
    intro r sec base s h
    simp only [placeOf, relocatedSection_some h.located, Option.map_some, Option.getD_some]
  -- the first pass leaves the bytes alone on this machine
  have hprescan : ∀ (list : List Rel) (st : LinkState), st.memory.size ≤
      (list.foldl (fun state rel => stateOf (prescanOne tables rel state)) st).memory.size := by
    intro list
    induction list with
    | nil => intro _; exact Nat.le_refl _
    | cons r rest ih =>
      intro st
      refine Nat.le_trans ?_ (ih _)
      have hf : Frame (fun _ => False) (fun _ => True) (prescanOne tables r) := by
        unfold prescanOne
        refine frame_guard (Frame.bind (frame_siteOf _ _ _) fun site => ?_)
        cases site with
        | none => exact Frame.pure _
        | some site =>
          dsimp only
          rw [ite_eq_right (by simp [hm])]
          exact Frame.pure _
      exact (hf st fun _ _ => trivial).2.1
  have key : ∀ (list : List Rel), (∀ r ∈ list, r ∈ tables.input.relocations) →
      list.Pairwise (fun left right => placeOf tables left + 4 ≤ placeOf tables right ∨ placeOf tables right + 4 ≤ placeOf tables left) →
      ∀ st : LinkState, tables.env.gotOff ≤ st.memory.size →
      let after := list.foldl (fun state rel => stateOf (applyOne tables (x86_64 tables.env) rel state)) st
      after.memory.size = st.memory.size ∧
        (∀ o, (∀ r ∈ list, o < placeOf tables r ∨ placeOf tables r + 4 ≤ o) → after.memory.get! o = st.memory.get! o) ∧
        ∀ r ∈ list, ∀ {sec base s}, Placed tables r 4 sec base s →
          readNat after.memory true (sec.off + r.offset) 4 = field (pc32Value tables r sec base s) 0 32 := by
    intro list
    induction list with
    | nil => intro _ _ st _; exact ⟨rfl, fun _ _ => rfl, fun _ hr => by simp at hr⟩
    | cons head rest ih =>
      intro hmem hpair st hst
      obtain ⟨ht, sec, base, s, hp⟩ := hplaced head (hmem head (by simp))
      have hwrite := applyOne_pc32 ht hp st hst
      have hbound : sec.off + head.offset + 4 ≤ st.memory.size := by
        have := hp.bounds
        have := hp.file
        omega
      obtain ⟨w1, w2, _⟩ := writeNat_spec (memory := st.memory) (little := tables.env.little) (off := sec.off + head.offset) (n := 4)
        (value := pc32Value tables head sec base s) hbound
      have hstep : (stateOf (applyOne tables (x86_64 tables.env) head st)).memory.size = st.memory.size := by rw [hwrite, w1]
      obtain ⟨hs, hk, hr⟩ := ih (fun r hr => hmem r (by simp [hr])) (List.pairwise_cons.mp hpair).2
        (stateOf (applyOne tables (x86_64 tables.env) head st)) (by rw [hstep]; exact hst)
      simp only [List.foldl_cons]
      refine ⟨hs.trans hstep, fun o ho => ?_, fun r hmem' {sec' base' s'} hp' => ?_⟩
      · rw [hk o fun r hr => ho r (by simp [hr]), hwrite]
        apply w2
        have := ho head (by simp)
        rw [hplaceOf hp] at this
        exact this
      · rcases List.mem_cons.mp hmem' with rfl | hin
        · obtain ⟨rfl, rfl, rfl⟩ := hunique hp hp'
          have hread := readNat_writeNat_little (memory := st.memory) (off := sec.off + r.offset) (n := 4)
            (value := pc32Value tables r sec base s) hbound
          rw [hl] at hwrite
          rw [readNat_congr (b := writeNat st.memory true (sec.off + r.offset) 4 (pc32Value tables r sec base s)), hread]
          intro i hi
          rw [hk _ (fun other hother => ?_), hwrite]
          have hd := (List.pairwise_cons.mp hpair).1 other hother
          rw [hplaceOf hp] at hd
          omega
        · exact hr r hin hp'
  exact (key _ (fun _ h => h) hdisjoint _ (Nat.le_trans hsize (hprescan _ _))).2.2 rel hrel hplace

/-- The same of `link`: in the linked memory, each place of a file of `R_X86_64_PC32` relocations holds `S + A - P`. -/
theorem link_x86_64_pc32 (input : Input) (hm : input.machine = 62) (hl : input.little = true) :
    ∃ tables : Tables, tables.input = input ∧ tables.addrs = (layoutSections input.sections.toList input.base).addrs ∧
      ((∀ rel ∈ input.relocations, rel.typ = 2 ∧ ∃ sec base s, Placed tables rel 4 sec base s) →
        input.relocations.Pairwise (fun left right =>
          placeOf tables left + 4 ≤ placeOf tables right ∨ placeOf tables right + 4 ≤ placeOf tables left) →
        ∀ rel ∈ input.relocations, ∀ {sec base s}, Placed tables rel 4 sec base s →
          readNat (link input).memory true (sec.off + rel.offset) 4 = field (pc32Value tables rel sec base s) 0 32) := by
  obtain ⟨tables, rfl, hg, hm', _, hl', _, ha, hmem, _⟩ := link_relocate input
  refine ⟨tables, rfl, ha, fun hplaced hdisjoint rel hrel sec base s hplace => ?_⟩
  rw [hmem]
  exact relocate_x86_64_pc32 (hm'.trans hm) (hl'.trans hl) _ (by rw [hg]; exact Nat.le_refl _)
    hplaced hdisjoint hrel hplace

/-! `R_MIPS_LO16` resolves what is pending of its symbol, and that succeeds. -/

theorem commit_bounds {site : Site} {writes : List Write} {state : LinkState}
    (h : ∀ w ∈ writes, site.off ≤ w.off ∧ w.off + w.n ≤ site.limit ∧ w.off + w.n ≤ state.memory.size) :
    ∃ after, commit site writes state = .ok () after ∧ state.memory.size ≤ after.memory.size ∧
      after.mipsPending = state.mipsPending := by
  have hc := commit_run site writes state
  rw [ite_eq_left (by
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact fun w hw => ⟨⟨(h w hw).1, (h w hw).2.1⟩, (h w hw).2.2⟩)] at hc
  exact ⟨_, hc, Nat.le_of_eq (commit_fold writes state.memory fun w hw => (h w hw).2.2).1.symm, rfl⟩

theorem gotEntry_ok (env : Env) (value : Int) (state : LinkState) :
    ∃ slot after, gotEntry env value state = .ok slot after ∧ state.memory.size ≤ after.memory.size ∧
      after.mipsPending = state.mipsPending := by
  have hf := (frame_gotEntry (P := fun o => env.gotOff ≤ o) (S := fun _ => True) (env := env) (fun _ h => h) value state (fun _ _ => trivial)).2.1
  simp only [gotEntry, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at hf ⊢
  cases hc : state.got[field value 0 64]? with
  | some slot => exact ⟨slot, state, rfl, Nat.le_refl _, rfl⟩
  | none =>
    simp only [hc] at hf ⊢
    exact ⟨_, _, rfl, hf, rfl⟩

/-- A deferred half whose place is in bounds is resolved without fail. -/
theorem mipsApplyHi_ok (env : Env) {site : Site} (ahl : Int) {state : LinkState}
    (hb : inSection site 0 4 state.memory.size = true) :
    ∃ after, mipsApplyHi env site ahl state = .ok () after ∧ state.memory.size ≤ after.memory.size ∧
      after.mipsPending = state.mipsPending := by
  have hs : site.off + 0 + 4 ≤ site.limit ∧ site.off + 0 + 4 ≤ state.memory.size := by
    simpa [inSection] using hb
  have hload : ld env site 0 4 state = .ok (readNat state.memory env.little (site.off + 0) 4) state := by
    simp only [ld, ElfLinker.load, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hb, ite_true]
    rfl
  unfold mipsApplyHi
  rw [bind_ok hload]
  dsimp only
  have hcommit : ∀ (st : LinkState) (v : Int), state.memory.size ≤ st.memory.size →
      ∃ after, commit site [stAt env site 0 4 v] st = .ok () after ∧ st.memory.size ≤ after.memory.size ∧
        after.mipsPending = st.mipsPending := fun st v hsize => commit_bounds (by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp only [stAt]
    omega)
  split
  · exact hcommit state _ (Nat.le_refl _)
  · obtain ⟨slot, mid, hg, h1, h2⟩ := gotEntry_ok env ((site.s + ahl + 0x8000) - (site.s + ahl + 0x8000) % 65536) state
    rw [bind_ok hg]
    obtain ⟨after, hc, h3, h4⟩ := hcommit mid (setLo16 (readNat state.memory env.little (site.off + 0) 4) (slot - mipsGp env)) h1
    exact ⟨after, hc, Nat.le_trans h1 h3, h4.trans h2⟩

/-- The sites that are pending can be resolved: their places were read when they were deferred, and memory only grows. -/
def PendingOk (state : LinkState) : Prop := ∀ entry ∈ state.mipsPending, inSection entry.1 0 4 state.memory.size = true

theorem inSection_mono {site : Site} {at' n small large : Nat} (h : inSection site at' n small = true) (hle : small ≤ large) :
    inSection site at' n large = true := by
  simp only [inSection, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, by omega⟩

/-- **The pending halves of a symbol are all resolved**, and only those stop being pending: `mipsFlush` can't fail, so
it isn't a hypothesis of `mips_lo16_resolves`. -/
theorem mipsFlush_ok (env : Env) (lo : Int) (symbol : Nat) {state : LinkState} (h : PendingOk state) :
    ∃ after, mipsFlush env lo symbol state = .ok () after ∧ state.memory.size ≤ after.memory.size ∧
      after.mipsPending = state.mipsPending.filter fun entry => !(entry.1.rel.symbol == symbol) := by
  have key : ∀ (list : List (Site × Nat)) (st : LinkState), (∀ entry ∈ list, inSection entry.1 0 4 st.memory.size = true) →
      ∃ after, (forIn list PUnit.unit fun entry _ => do
          mipsApplyHi env entry.1 ((entry.2 : Int) * 65536 + lo)
          pure (ForInStep.yield PUnit.unit) : LinkM PUnit) st = .ok PUnit.unit after ∧
        st.memory.size ≤ after.memory.size ∧ after.mipsPending = st.mipsPending := by
    intro list
    induction list with
    | nil => exact fun st _ => ⟨st, rfl, Nat.le_refl _, rfl⟩
    | cons entry rest ih =>
      intro st hall
      obtain ⟨mid, hm, h1, h2⟩ := mipsApplyHi_ok env ((entry.2 : Int) * 65536 + lo) (hall entry (by simp))
      obtain ⟨after, ha, h3, h4⟩ := ih mid fun e he => inSection_mono (hall e (by simp [he])) h1
      refine ⟨after, ?_, Nat.le_trans h1 h3, h4.trans h2⟩
      rw [List.forIn_cons]
      have hs : (do mipsApplyHi env entry.1 ((entry.2 : Int) * 65536 + lo); pure (ForInStep.yield PUnit.unit) : LinkM _) st =
          .ok (ForInStep.yield PUnit.unit) mid := bind_ok hm
      exact (bind_ok hs).trans ha
  have hrest : state.mipsPending.partition (fun entry => entry.1.rel.symbol == symbol) =
      (state.mipsPending.filter fun entry => entry.1.rel.symbol == symbol,
        state.mipsPending.filter fun entry => !(entry.1.rel.symbol == symbol)) := by
    rw [List.partition_eq_filter_filter]
    rfl
  obtain ⟨after, ha, h1, h2⟩ := key (state.mipsPending.filter fun entry => entry.1.rel.symbol == symbol).reverse
    { state with mipsPending := state.mipsPending.filter fun entry => !(entry.1.rel.symbol == symbol) } (fun e he =>
      h e (List.mem_filter.mp (List.mem_reverse.mp he)).1)
  refine ⟨after, ?_, h1, h2⟩
  unfold mipsFlush
  have step : ∀ f : LinkState → LinkM Unit, ((get : LinkM LinkState) >>= f) state = f state state := fun _ => rfl
  rw [step]
  simp only [hrest]
  exact Eq.trans rfl ((bind_ok ha).trans rfl)

/-- **`R_MIPS_LO16`**: its place is in bounds and the pending sites are, so what `mips_lo16` assumed holds. It first resolves
the pending halves of its symbol, then stores `S + A`, and for `_gp_disp` the `GP - P + 4` of the pair. -/
theorem mips_lo16_resolves {env : Env} {site : Site} {state : LinkState} (ht : site.rel.typ = 6)
    (hb : inSection site 0 4 state.memory.size = true) (hp : PendingOk state) :
    ∃ after, mipsFlush env (mipsA16 env site state) site.rel.symbol state = .ok () after ∧
      after.mipsPending = (state.mipsPending.filter fun entry => !(entry.1.rel.symbol == site.rel.symbol)) ∧
      (mips env site).run state = .ok (some [stAt env site 0 4 (setLo16 (readNat state.memory env.little (site.off + 0) 4)
        ((if site.sym.name == "_gp_disp" then mipsGp env - site.p + 4 else site.s) + mipsA16 env site state))]) after := by
  obtain ⟨after, hf, _, hpend⟩ := mipsFlush_ok env (mipsA16 env site state) site.rel.symbol hp
  exact ⟨after, hf, hpend, mips_lo16 ht hb hf⟩

/-- What is deferred stays good: the place of `R_MIPS_HI16` was read before it was deferred. -/
theorem PendingOk.push {state : LinkState} (h : PendingOk state) {site : Site} (stored : Nat)
    (hb : inSection site 0 4 state.memory.size = true) :
    PendingOk { state with mipsPending := (site, stored) :: state.mipsPending } := by
  intro entry he
  rcases List.mem_cons.mp he with rfl | he
  · exact hb
  · exact h entry he

/-! The range of a field is exactly when nothing is lost by cutting a value to it. -/

/-- **A signed field**: it keeps a value exactly if the value is in its range. -/
theorem fits_signed_iff {bits : Nat} (hb : 0 < bits) (value : Int) :
    fits .signed bits value = true ↔ sext (field value 0 bits : Nat) bits = value := by
  rw [sext_natCast_field]
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact fun h => sext_of_range hb h.1 h.2
  · intro h
    rw [← h]
    exact sext_range value hb

/-- **An unsigned field**: it keeps a value exactly if the value is in its range. -/
theorem fits_unsigned_iff (bits : Nat) (value : Int) :
    fits .unsigned bits value = true ↔ ((field value 0 bits : Nat) : Int) = value := by
  have hfield : ((field value 0 bits : Nat) : Int) = value % ((2 ^ bits : Nat) : Int) := by
    unfold field
    have hzero : value >>> 0 = value := by rw [Int.shiftRight_eq_div_pow]; simp
    rw [hzero, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have : 0 < 2 ^ bits := Nat.two_pow_pos bits
      omega))]
  have hpos : (0 : Int) < ((2 ^ bits : Nat) : Int) := by
    have : 0 < 2 ^ bits := Nat.two_pow_pos bits
    omega
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq, hfield]
  constructor
  · exact fun h => Int.emod_eq_of_lt h.1 h.2
  · intro h
    rw [← h]
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hpos⟩

/-- **A field that holds both**: it keeps a value exactly if one of the readings of its bits is the value. -/
theorem fits_either_iff {bits : Nat} (hb : 0 < bits) (value : Int) :
    fits .either bits value = true ↔
      sext (field value 0 bits : Nat) bits = value ∨ ((field value 0 bits : Nat) : Int) = value := by
  rw [← fits_signed_iff hb, ← fits_unsigned_iff]
  have hp : ((2 ^ bits : Nat) : Int) = 2 * ((2 ^ (bits - 1) : Nat) : Int) := by
    have : 2 ^ bits = 2 * 2 ^ (bits - 1) := by
      conv => lhs; rw [show bits = (bits - 1) + 1 by omega, Nat.pow_succ']
    omega
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **The checks are of what is stored.** For every checked relocation of x86-64 that stores a value as it is, the check is of
that value, in the bits of the store. -/
theorem x86_64Field_stored {env : Env} {site : Site} {state : LinkState} {check : FieldCheck}
    (ht : site.rel.typ = 2 ∨ site.rel.typ = 4 ∨ site.rel.typ = 10 ∨ site.rel.typ = 11 ∨ site.rel.typ = 12 ∨ site.rel.typ = 13 ∨
      site.rel.typ = 14 ∨ site.rel.typ = 15 ∨ site.rel.typ = 23 ∨ site.rel.typ = 26)
    (hc : x86_64Field env state site = some check) :
    check.bits % 8 = 0 ∧ (x86_64 env site).run state = .ok (some [stAt env site 0 (check.bits / 8) check.value]) state := by
  rcases ht with h | h | h | h | h | h | h | h | h | h <;>
    (simp only [x86_64Field, h, Option.some.injEq] at hc; subst hc; refine ⟨by simp, ?_⟩; simp only [x86_64, h]; rfl)

/-- **The same of i386**, whose addend is in the place unless the record has it. -/
theorem i386Field_stored {env : Env} {site : Site} {state : LinkState} {check : FieldCheck}
    (hb : ∀ n, n ≤ 4 → inSection site 0 n state.memory.size = true)
    (ht : site.rel.typ = 2 ∨ site.rel.typ = 4 ∨ site.rel.typ = 17 ∨ site.rel.typ = 20 ∨ site.rel.typ = 22 ∨ site.rel.typ = 23)
    (hc : i386Field env state site = some check) :
    check.bits % 8 = 0 ∧ (i386 env site).run state = .ok (some [stAt env site 0 (check.bits / 8) check.value]) state := by
  have h4 := hb 4 (by omega)
  have h2 := hb 2 (by omega)
  have h1 := hb 1 (by omega)
  rcases ht with h | h | h | h | h | h <;> (simp only [i386Field, h, Option.some.injEq] at hc; subst hc; refine ⟨by simp, ?_⟩) <;>
    cases he : site.rel.isExplicit <;> (link_run [i386, h, he, h4, h2, h1, addendOf]; try rfl)

/-! The thread pointer of each psABI. -/

/-- Variant II, of x86 and SystemZ: the block ends at the thread pointer, up to its alignment. -/
theorem tpOff_variant2 {env : Env} (hm : env.machine = 62 ∨ env.machine = 3 ∨ env.machine = 22) (s : Int) :
    tpOff env s = s - env.tls.start - (alignUp env.tls.size (max 1 env.tls.align) : Nat) -
      (-(env.tls.start : Int) - (alignUp env.tls.size (max 1 env.tls.align) : Nat)) % (max 1 env.tls.align : Int) := by
  rcases hm with hm | hm | hm <;> simp only [tpOff, hm]

/-- Variant I, of AArch64 and ARM: after a control block of two words, up to its alignment. -/
theorem tpOff_variant1 {env : Env} (hm : env.machine = 183 ∨ env.machine = 40) (s : Int) :
    tpOff env s = s - env.tls.start + (env.width : Int) / 4 +
      ((env.tls.start : Int) - (env.width : Int) / 4) % (max 1 env.tls.align : Int) := by
  rcases hm with hm | hm <;> simp only [tpOff, hm]

private theorem xor_ones {x : Nat} (hx : x < 65536) : x ^^^ 0xffff = 65535 - x := by
  have h1 : (BitVec.ofNat 16 x ^^^ BitVec.allOnes 16).toNat = x ^^^ 65535 := by
    rw [BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat 16 x ^^^ BitVec.allOnes 16).toNat = 65535 - x := by
    rw [BitVec.xor_allOnes, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact h1.symm.trans h2

/-- A signed MOVW is a MOVZ of a value that fits and isn't negative. -/
theorem aarch64SMov_movz {value : Int} {insn : Nat} (h : 0 ≤ value) (hl : value < 65536) :
    field (aarch64SMov value insn) 30 1 = 1 ∧ (field (aarch64SMov value insn) 5 16 : Int) = value := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have hk : k < 65536 := by omega
  have hsign : field (k : Int) 16 1 = 0 := by
    unfold field
    rw [Int.shiftRight_eq_div_pow]
    have : (k : Int) / ((2 ^ 16 : Nat) : Int) = 0 := by omega
    rw [this]
    rfl
  have hmov : aarch64SMov (k : Int) insn = setBits (setBits insn 30 1 1) 5 16 k := by
    simp [aarch64SMov, hsign]
  rw [hmov]
  refine ⟨?_, ?_⟩
  · rw [field_setBits_other _ _ _ _ 30 1 (.inr (by omega)), field_setBits_self]
    rfl
  · rw [field_setBits_self, field_of_lt (show k < 2 ^ 16 from hk)]

/-- A signed MOVW is a MOVN of a value that fits and is negative: the instruction holds the complement. -/
theorem aarch64SMov_movn {value : Int} {insn : Nat} (h : value < 0) (hl : -65536 ≤ value) :
    field (aarch64SMov value insn) 30 1 = 0 ∧ (-1 - (field (aarch64SMov value insn) 5 16 : Nat) : Int) = value := by
  have hsign : field value 16 1 = 1 := by
    unfold field
    rw [Int.shiftRight_eq_div_pow]
    have : value / ((2 ^ 16 : Nat) : Int) = -1 := by omega
    rw [this]
    rfl
  have hlow : (field value 0 16 : Int) = value + 65536 := by
    unfold field
    have hzero : value >>> 0 = value := by rw [Int.shiftRight_eq_div_pow]; simp
    rw [hzero, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
    show value % 65536 = _
    omega
  have hmov : aarch64SMov value insn =
      setBits (setBits insn 30 1 0) 5 16 ((field value 0 16 ^^^ 0xffff : Nat) : Int) := by
    simp [aarch64SMov, hsign]
  have hlt : field value 0 16 < 65536 := field_lt value 0 16
  rw [hmov]
  refine ⟨?_, ?_⟩
  · rw [field_setBits_other _ _ _ _ 30 1 (.inr (by omega)), field_setBits_self]
    rfl
  · rw [field_setBits_self, xor_ones hlt, field_of_lt (show 65535 - field value 0 16 < 2 ^ 16 by
      show 65535 - field value 0 16 < 65536
      omega)]
    omega

/-- A record of N32 at the place of the next one is one record with it: the types are the bytes of the type of the first, and
the symbol and addend are the first one's. -/
theorem packCompound_merge {rel next : Rel} {rest tail : List Rel} (h : Elf.packCompound rest = next :: tail)
    (hsame : next.target = rel.target ∧ next.offset = rel.offset) (ht : next.typ < 2 ^ 16) :
    Elf.packCompound (rel :: rest) = { rel with typ := rel.typ + next.typ * 256 } :: tail := by
  have : Elf.packCompound (rel :: rest) = match Elf.packCompound rest with
      | next :: rest' =>
        if next.target == rel.target && next.offset == rel.offset && next.typ < 2 ^ 16 then
          { rel with typ := rel.typ + next.typ * 256 } :: rest'
        else rel :: Elf.packCompound rest
      | [] => [rel] := rfl
  rw [this, h]
  simp [hsame.1, hsame.2, ht]

/-- A record at another place is a record of its own. -/
theorem packCompound_keep {rel next : Rel} {rest tail : List Rel} (h : Elf.packCompound rest = next :: tail)
    (hother : ¬ (next.target = rel.target ∧ next.offset = rel.offset)) :
    Elf.packCompound (rel :: rest) = rel :: next :: tail := by
  have : Elf.packCompound (rel :: rest) = match Elf.packCompound rest with
      | next :: rest' =>
        if next.target == rel.target && next.offset == rel.offset && next.typ < 2 ^ 16 then
          { rel with typ := rel.typ + next.typ * 256 } :: rest'
        else rel :: Elf.packCompound rest
      | [] => [rel] := rfl
  rw [this, h]
  have hne : ¬ ((next.target == rel.target && next.offset == rel.offset && decide (next.typ < 2 ^ 16)) = true) := by
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact fun h' => hother h'.1
  dsimp only
  rw [ite_eq_right hne]

/-- Without a handler nothing changes in memory, whatever the relocations are. -/
theorem relocate_no_handler {tables : Tables} (h : handler tables.env = none) (state : LinkState) {o : Nat}
    (ho : o < state.memory.size) : (stateOf (relocate tables state)).memory.get! o = state.memory.get! o := by
  have hf : Frame (fun _ => False) (fun _ => True) (relocate tables) := by
    unfold relocate
    dsimp only
    split
    · refine Frame.bind (Frame.forIn fun _ _ _ => ?_) fun _ => ?_
      · refine Frame.bind (frame_siteOf _ _ _) fun _ => ?_
        split <;> exact Frame.pure _
      · split
        · exact frame_warn _
        · exact Frame.pure _
    · next heq => rw [h] at heq; cases heq
  exact (hf state fun _ _ => trivial).2.2 o ho id

end LinkerLaws

/-! ## ELF -/

namespace ElfParser

open_private Bap.Image.Elf Bap.Image.Elf word parseHeader parseProgramHeader parseSections parseSegments
  offsetOf tagValue sleb128 sleb128.loop codeAddress parseSymbol relativeType irelativeType symbolRelocationKind
  isMips64el decodeRelocatable linkInput rawRelocations sectionRelocations relocatesMemory
  AndroidGroup AndroidGroup.is64 AndroidGroup.rela AndroidGroup.byOffset AndroidGroup.offsetDelta AndroidState AndroidState.mk AndroidState.cursor AndroidState.offset
  AndroidState.addend AndroidState.result
  androidField androidEntry androidEntries androidGroupHeader androidGroups decodeAndroid readAndroidRelocations
  relrBits relrDecode readRelrRelocations isRelativeType classifyRelocation storedWord dynamicSymbol
  mipsGotReferences mipsGotReferences.loop collectRelocations

open Reader

theorem word_bound {data : ByteArray} {endian : Endian} {is64 : Bool} {offset value : Nat}
    (h : word data endian is64 offset = .ok value) : offset + (if is64 then 8 else 4) ≤ data.size := by
  cases is64
  · exact read_bound (endian := endian) h
  · exact read_bound (endian := endian) h

/-- The field-reading tail of `parseHeader`, once class and encoding are known. -/
def headerFields (data : ByteArray) (endian : Endian) (is64 : Bool) : Except String Elf.Header := do
  let fileType ← IO.Reader.u16 data endian 16
  let machine ← IO.Reader.u16 data endian 18
  let entryPoint ← word data endian is64 24
  let programOffset ← word data endian is64 (if is64 then 32 else 28)
  let sectionOffset ← word data endian is64 (if is64 then 40 else 32)
  let programEntrySize ← IO.Reader.u16 data endian (if is64 then 54 else 42)
  let programCount ← IO.Reader.u16 data endian (if is64 then 56 else 44)
  let sectionEntrySize ← IO.Reader.u16 data endian (if is64 then 58 else 46)
  let sectionCount ← IO.Reader.u16 data endian (if is64 then 60 else 48)
  let stringSectionIndex ← IO.Reader.u16 data endian (if is64 then 62 else 50)
  .ok {
    is64 := is64
    endian := endian
    machine := machine
    entryPoint := entryPoint
    programOffset := programOffset
    sectionOffset := sectionOffset
    programEntrySize := programEntrySize
    programCount := programCount
    sectionEntrySize := sectionEntrySize
    sectionCount := sectionCount
    stringSectionIndex := stringSectionIndex
    fileType := fileType
  }

/-- An accepted header starts with the magic and valid class and encoding bytes, then reads its fields. -/
theorem parseHeader_spec {data : ByteArray} {header : Elf.Header} (h : parseHeader data = .ok header) :
    IO.Reader.read data .big 0 4 = .ok 0x7f454c46 ∧ 5 < data.size ∧
      (byteAt data 4 = 1 ∨ byteAt data 4 = 2) ∧ (byteAt data 5 = 1 ∨ byteAt data 5 = 2) ∧
      headerFields data (if byteAt data 5 = 1 then .little else .big) (byteAt data 4 = 2) = .ok header := by
  simp only [parseHeader, bind_ok_iff] at h
  rcases h with ⟨magic, hm, h⟩
  by_cases hne : (magic != 0x7f454c46) = true
  · rw [ite_eq_left hne] at h; cases h
  rw [ite_eq_right hne] at h
  have hmagic : magic = 0x7f454c46 := by simpa using hne
  subst hmagic
  simp only [bind_ok_iff] at h
  rcases h with ⟨elfClass, hc, encoding, he, h⟩
  have ⟨hc1, hc2⟩ := get8_ok hc
  have ⟨he1, he2⟩ := get8_ok he
  subst hc2 he2
  refine ⟨hm, he1, ?_⟩
  split at h
  · rename_i hclass
    simp only [ok_bind] at h
    split at h
    · rename_i henc
      refine ⟨.inl hclass, .inl henc, ?_⟩
      simp only [hclass, henc]
      exact h
    · rename_i henc
      refine ⟨.inl hclass, .inr henc, ?_⟩
      simp only [hclass, henc]
      exact h
    · simp only [error_bind] at h; cases h
  · rename_i hclass
    simp only [ok_bind] at h
    split at h
    · rename_i henc
      refine ⟨.inr hclass, .inl henc, ?_⟩
      simp only [hclass, henc]
      exact h
    · rename_i henc
      refine ⟨.inr hclass, .inr henc, ?_⟩
      simp only [hclass, henc]
      exact h
    · simp only [error_bind] at h; cases h
  · simp only [error_bind] at h; cases h

theorem headerFields_ok {data : ByteArray} {endian : Endian} {is64 : Bool} {header : Elf.Header}
    (h : headerFields data endian is64 = .ok header) :
    header.is64 = is64 ∧ header.endian = endian ∧
      IO.Reader.u16 data endian 18 = .ok header.machine ∧
      word data endian is64 24 = .ok header.entryPoint ∧
      word data endian is64 (if is64 then 32 else 28) = .ok header.programOffset ∧
      word data endian is64 (if is64 then 40 else 32) = .ok header.sectionOffset ∧
      IO.Reader.u16 data endian (if is64 then 54 else 42) = .ok header.programEntrySize ∧
      IO.Reader.u16 data endian (if is64 then 56 else 44) = .ok header.programCount ∧
      IO.Reader.u16 data endian (if is64 then 58 else 46) = .ok header.sectionEntrySize ∧
      IO.Reader.u16 data endian (if is64 then 60 else 48) = .ok header.sectionCount ∧
      IO.Reader.u16 data endian (if is64 then 62 else 50) = .ok header.stringSectionIndex ∧
      (if is64 then 64 else 52) ≤ data.size := by
  simp only [headerFields, bind_ok_iff] at h
  rcases h with ⟨t, h0, m, h1, e, h2, po, h3, so, h4, pes, h5, pc, h6, ses, h7, sc, h8, ssi, h9, h⟩
  cases h
  have hb := read_bound h9
  refine ⟨rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  cases is64 <;> simpa using hb

/-- Every field of an accepted header is read at its ELF32 or ELF64 `Ehdr` offset. -/
theorem parseHeader_layout {data : ByteArray} {header : Elf.Header} (h : parseHeader data = .ok header) :
    IO.Reader.u16 data header.endian 18 = .ok header.machine ∧
      word data header.endian header.is64 24 = .ok header.entryPoint ∧
      word data header.endian header.is64 (if header.is64 then 32 else 28) = .ok header.programOffset ∧
      word data header.endian header.is64 (if header.is64 then 40 else 32) = .ok header.sectionOffset ∧
      IO.Reader.u16 data header.endian (if header.is64 then 54 else 42) = .ok header.programEntrySize ∧
      IO.Reader.u16 data header.endian (if header.is64 then 56 else 44) = .ok header.programCount ∧
      IO.Reader.u16 data header.endian (if header.is64 then 58 else 46) = .ok header.sectionEntrySize ∧
      IO.Reader.u16 data header.endian (if header.is64 then 60 else 48) = .ok header.sectionCount ∧
      IO.Reader.u16 data header.endian (if header.is64 then 62 else 50) = .ok header.stringSectionIndex := by
  have ⟨_, _, _, _, hf⟩ := parseHeader_spec h
  have ⟨h64, hend, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := headerFields_ok hf
  rw [h64, hend]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- What an accepted ELF header guarantees about the input. -/
theorem parseHeader_ok {data : ByteArray} {header : Elf.Header} (h : parseHeader data = .ok header) :
    byteAt data 0 = 0x7f ∧ byteAt data 1 = 0x45 ∧ byteAt data 2 = 0x4c ∧ byteAt data 3 = 0x46 ∧
      (header.is64 = true ↔ byteAt data 4 = 2) ∧ (header.is64 = false ↔ byteAt data 4 = 1) ∧
      (header.endian = .little ↔ byteAt data 5 = 1) ∧ (header.endian = .big ↔ byteAt data 5 = 2) ∧
      52 ≤ data.size ∧ (header.is64 = true → 64 ≤ data.size) := by
  have ⟨hm, _, hc, he, hf⟩ := parseHeader_spec h
  have ⟨h64, hend, _, _, _, _, _, _, _, _, _, hsize⟩ := headerFields_ok hf
  have hsize4 : 4 ≤ data.size := read_bound hm
  rw [read_big_four hsize4] at hm
  have hb0 : byteAt data 0 < 256 := (data.get! 0).toNat_lt
  have hb1 : byteAt data 1 < 256 := (data.get! 1).toNat_lt
  have hb2 : byteAt data 2 < 256 := (data.get! 2).toNat_lt
  have hb3 : byteAt data 3 < 256 := (data.get! 3).toNat_lt
  have hval := Except.ok.inj hm
  simp only [Nat.zero_add] at hval
  refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h64]; simp
  · rw [h64]; simp; omega
  · rw [hend]; split <;> simp_all
  · rw [hend]; split <;> simp_all <;> omega
  · split at hsize <;> omega
  · intro h'
    rw [h64] at h'
    simp only [h', ↓reduceIte] at hsize
    exact hsize

theorem parseHeader_rejects_short {data : ByteArray} (h : data.size < 52) :
    (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header => have := (parseHeader_ok hp).2.2.2.2.2.2.2.2.1; omega

theorem parseHeader_rejects_magic {data : ByteArray}
    (h : ¬ (byteAt data 0 = 0x7f ∧ byteAt data 1 = 0x45 ∧ byteAt data 2 = 0x4c ∧ byteAt data 3 = 0x46)) :
    (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header =>
    have ⟨h0, h1, h2, h3, _⟩ := parseHeader_ok hp
    exact absurd ⟨h0, h1, h2, h3⟩ h

/-! ### LOAD segments -/

/-- A LOAD entry is read at its `Phdr` offsets, and produces a segment and region that agree, holding the file
bytes then zeros. -/
theorem parseProgramHeader_layout {data : ByteArray} {header : Elf.Header} {offset : Nat} {segment : Segment}
    {region : MemRegion} (h : parseProgramHeader data header offset = .ok (some (segment, region))) :
    IO.Reader.u32 data header.endian offset = .ok 1 ∧
      word data header.endian header.is64 (offset + if header.is64 then 16 else 8) = .ok segment.addr ∧
      word data header.endian header.is64 (offset + if header.is64 then 40 else 20) = .ok segment.size ∧
      (∃ flags, IO.Reader.u32 data header.endian (offset + if header.is64 then 4 else 24) = .ok flags ∧
        segment.readable = (flags &&& 4 != 0) ∧ segment.writable = (flags &&& 2 != 0) ∧
        segment.executable = (flags &&& 1 != 0)) ∧
      ∃ fileOffset fileSize,
        word data header.endian header.is64 (offset + if header.is64 then 8 else 4) = .ok fileOffset ∧
        word data header.endian header.is64 (offset + if header.is64 then 32 else 16) = .ok fileSize ∧
        Loaded region.data data fileOffset fileSize segment.size := by
  simp only [parseProgramHeader, bind_ok_iff] at h
  rcases h with ⟨kind, hk0, h⟩
  by_cases hk : (kind != 1) = true
  · rw [ite_eq_left hk] at h; cases h
  rw [ite_eq_right hk] at h
  have hk1 : kind = 1 := by simpa using hk
  subst hk1
  simp only [bind_ok_iff] at h
  rcases h with ⟨flags, hfl, fileOffset, hfo, address, ha, fileSize, hfs, memorySize, hms, h⟩
  by_cases hm : fileSize > memorySize
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨file, hslice, h⟩
  cases h
  have hl := loaded_of_slice (memorySize := memorySize) hslice (by omega)
  exact ⟨hk0, ha, hms, ⟨flags, hfl, rfl, rfl, rfl⟩, fileOffset, fileSize, hfo, hfs, hl⟩

/-- A LOAD entry produces a segment and region that agree, holding the file bytes then zeros. -/
theorem parseProgramHeader_load {data : ByteArray} {header : Elf.Header} {offset : Nat} {segment : Segment}
    {region : MemRegion} (h : parseProgramHeader data header offset = .ok (some (segment, region))) :
    segment.addr = region.addr ∧ segment.size = region.size ∧ segment.readable = region.readable ∧
      segment.writable = region.writable ∧ segment.executable = region.executable ∧
      ∃ fileOffset fileSize, Loaded region.data data fileOffset fileSize segment.size := by
  simp only [parseProgramHeader, bind_ok_iff] at h
  rcases h with ⟨kind, _, h⟩
  by_cases hk : (kind != 1) = true
  · rw [ite_eq_left hk] at h; cases h
  rw [ite_eq_right hk] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨flags, _, fileOffset, _, address, _, fileSize, _, memorySize, _, h⟩
  by_cases hm : fileSize > memorySize
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨file, hs, h⟩
  cases h
  have hl := loaded_of_slice (memorySize := memorySize) hs (by omega)
  exact ⟨rfl, hl.1.symm, rfl, rfl, rfl, fileOffset, fileSize, hl⟩

/-- The pairing of loaded segments with their mapped regions. -/
def LoadPair (data : ByteArray) (entry : Segment × MemRegion) : Prop :=
  entry.1.addr = entry.2.addr ∧ entry.1.size = entry.2.size ∧ entry.1.readable = entry.2.readable ∧
    entry.1.writable = entry.2.writable ∧ entry.1.executable = entry.2.executable ∧
    ∃ fileOffset fileSize, Loaded entry.2.data data fileOffset fileSize entry.1.size

theorem parseSegments_ok {data : ByteArray} {header : Elf.Header} {segments : List Segment} {regions : List MemRegion}
    (h : parseSegments data header = .ok (segments, regions)) :
    ∃ entries : List (Segment × MemRegion), segments = entries.map Prod.fst ∧ regions = entries.map Prod.snd ∧
      ∀ entry ∈ entries, LoadPair data entry := by
  simp only [parseSegments] at h
  by_cases h0 : header.programCount = 0
  · rw [ite_eq_left h0] at h
    cases h
    exact ⟨[], rfl, rfl, by simp⟩
  rw [ite_eq_right h0] at h
  by_cases hm : header.programEntrySize < (if header.is64 then 56 else 32)
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨entries, he, h⟩
  have hu := Except.ok.inj h
  refine ⟨entries.filterMap id, ?_, ?_, ?_⟩
  · have := congrArg Prod.fst hu
    simpa using this.symm
  · have := congrArg Prod.snd hu
    simpa using this.symm
  · intro entry hentry
    have ⟨hl, hi⟩ := mapM_ok he
    simp only [List.mem_filterMap, id_eq] at hentry
    rcases hentry with ⟨raw, hraw, hsome⟩
    subst hsome
    have ⟨i, hi1, hi2⟩ := List.getElem_of_mem hraw
    have := hi i hi1 (by omega)
    rw [hi2] at this
    obtain ⟨segment, region⟩ := entry
    exact parseProgramHeader_load this

/-- A file with no program headers has no segments, whatever its `e_phentsize`: relocatable objects load. -/
theorem parseSegments_no_entries {data : ByteArray} {header : Elf.Header} (h : header.programCount = 0) :
    parseSegments data header = .ok ([], []) := by
  simp only [parseSegments]
  rw [ite_eq_left h]

/-- Program headers that are present must be large enough for their class. -/
theorem parseSegments_rejects_small_entry {data : ByteArray} {header : Elf.Header} (h0 : header.programCount ≠ 0)
    (h : header.programEntrySize < (if header.is64 then 56 else 32)) :
    (parseSegments data header).isOk = false := by
  simp only [parseSegments]
  rw [ite_eq_right h0, ite_eq_left h]
  rfl

/-! ### decode -/

/-- Segments and mapped regions correspond one to one, at the same address and of the same size. -/
def SegmentsAgree (image : Image) : Prop :=
  ∃ pairs : List (Segment × MemRegion), image.segments = pairs.map Prod.fst ∧
    image.memory.entries = (pairs.map Prod.snd).reverse.map (fun region => (region, ())) ∧
    ∀ pair ∈ pairs, pair.1.addr = pair.2.addr ∧ pair.1.size = pair.2.size

/-- An executable or shared object: its segments are its LOAD entries, with the bytes of the file. -/
theorem decode_loaded {data : ByteArray} {image : Image} {header : Elf.Header} (h : Elf.decode data = .ok image)
    (hh : parseHeader data = .ok header) (ht : header.fileType ≠ 1) :
    image.data = data ∧ image.addrWidth = (if header.is64 then 64 else 32) ∧ image.endian = header.endian ∧
      image.entryPoint = header.entryPoint ∧
      ∃ entries : List (Segment × MemRegion), image.segments = entries.map Prod.fst ∧
        image.memory.entries = (entries.map Prod.snd).reverse.map (fun region => (region, ())) ∧
        ∀ entry ∈ entries, LoadPair data entry := by
  simp only [Elf.decode, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, h⟩
  cases he
  have hne : ¬ (header.fileType == 1) = true := by simpa using ht
  rw [ite_eq_right hne] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨⟨segments, regions⟩, h2, sh, _, sections, _, symbols, _, h⟩
  cases h
  have ⟨entries, hs, hr, hp⟩ := parseSegments_ok h2
  refine ⟨rfl, rfl, rfl, rfl, entries, hs, ?_, hp⟩
  rw [Map.foldl_add_entries, hr]
  simp

/-- A relocatable file: its segments are the regions that the linker laid out. -/
theorem decode_relocatable {data : ByteArray} {image : Image} {header : Elf.Header} (h : Elf.decode data = .ok image)
    (hh : parseHeader data = .ok header) (ht : header.fileType = 1) :
    image.data = data ∧ image.addrWidth = (if header.is64 then 64 else 32) ∧ image.endian = header.endian ∧
      ∃ sections names, parseSections data header = .ok sections ∧
        let prepared := ElfLinker.prepare (linkInput data header sections names)
        let output := ElfLinker.link prepared
        image.segments = output.regions.map ElfLinker.toSegment ∧
        image.memory.entries = ((output.regions.map (ElfLinker.toMemRegion output.memory prepared.data.size)).reverse.map
          fun region => (region, ())) := by
  simp only [Elf.decode, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, h⟩
  cases he
  have hy : (header.fileType == 1) = true := by simpa using ht
  rw [ite_eq_left hy] at h
  simp only [bind_ok_iff, decodeRelocatable] at h
  rcases h with ⟨sections, h2, names, _, h⟩
  cases h
  refine ⟨rfl, rfl, rfl, sections, names, h2, rfl, ?_⟩
  rw [Map.foldl_add_entries]
  exact List.append_nil _

/-- A file with no program headers that is not relocatable decodes with no segments and no mapped memory. -/
theorem decode_no_program_headers {data : ByteArray} {image : Image} {header : Elf.Header}
    (h : Elf.decode data = .ok image) (hh : parseHeader data = .ok header) (ht : header.fileType ≠ 1)
    (h0 : header.programCount = 0) :
    image.segments = [] ∧ image.memory.entries = [] ∧ Elf.programHeaders data = .ok [] := by
  simp only [Elf.decode, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, h⟩
  cases he
  have hne : ¬ (header.fileType == 1) = true := by simpa using ht
  rw [ite_eq_right hne] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨⟨segments, regions⟩, h2, sh, _, _, _, _, _, h⟩
  rw [parseSegments_no_entries h0] at h2
  cases h2
  cases h
  refine ⟨rfl, rfl, ?_⟩
  simp only [Elf.programHeaders, hh, Reader.ok_bind]
  rw [ite_eq_left h0]

theorem decode_header {data : ByteArray} {image : Image} (h : Elf.decode data = .ok image) :
    ∃ header, parseHeader data = .ok header := by
  simp only [Elf.decode, bind_ok_iff] at h
  rcases h with ⟨header, h1, _⟩
  exact ⟨header, h1⟩

theorem decode_rejects_short {data : ByteArray} (h : data.size < 52) : (Elf.decode data).isOk = false := by
  cases hd : Elf.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp⟩ := decode_header hd
    have := parseHeader_rejects_short (data := data) h
    simp [hp, Except.isOk, Except.toBool] at this

theorem decode_rejects_magic {data : ByteArray}
    (h : ¬ (byteAt data 0 = 0x7f ∧ byteAt data 1 = 0x45 ∧ byteAt data 2 = 0x4c ∧ byteAt data 3 = 0x46)) :
    (Elf.decode data).isOk = false := by
  cases hd : Elf.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp⟩ := decode_header hd
    have := parseHeader_rejects_magic h
    simp [hp, Except.isOk, Except.toBool] at this

/-- Every byte mapped by an image with agreeing segments lies inside one of them. -/
theorem readByte_in_segment {image : Image} {address : Nat} {byte : UInt8} (ha : SegmentsAgree image)
    (hr : image.memory.readByte address = some byte) :
    ∃ segment ∈ image.segments, segment.addr ≤ address ∧ address < segment.addr + segment.size := by
  obtain ⟨pairs, hs, hm, hp⟩ := ha
  have ⟨entry, hentry, hc, _⟩ := Map.readByte_some hr
  rw [hm] at hentry
  simp only [List.mem_map, List.mem_reverse] at hentry
  rcases hentry with ⟨region, ⟨pair, hpair, rfl⟩, rfl⟩
  refine ⟨pair.1, ?_, ?_⟩
  · rw [hs]; exact List.mem_map_of_mem hpair
  · have ⟨h1, h2⟩ := hp pair hpair
    have := Region.contains_iff.mp hc
    simp only at this
    omega

/-! ### Program headers and segment lookup -/

theorem programHeaders_ok {data : ByteArray} {headers : List Elf.ProgramHeader}
    (h : Elf.programHeaders data = .ok headers) :
    ∃ header, parseHeader data = .ok header ∧ headers.length = header.programCount := by
  simp only [Elf.programHeaders, bind_ok_iff] at h
  rcases h with ⟨header, h1, h⟩
  by_cases h0 : header.programCount = 0
  · rw [ite_eq_left h0] at h
    cases h
    exact ⟨header, h1, h0.symm⟩
  rw [ite_eq_right h0] at h
  by_cases hm : header.programEntrySize < (if header.is64 then 56 else 32)
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  exact ⟨header, h1, by simpa using (mapM_ok h).1⟩

/-- Each returned program header is read at its class's `Phdr` offsets from its table slot. -/
theorem programHeaders_layout {data : ByteArray} {headers : List Elf.ProgramHeader}
    (h : Elf.programHeaders data = .ok headers) {header : Elf.Header} (hh : parseHeader data = .ok header)
    (index : Nat) (hi : index < headers.length) :
    let entry := header.programOffset + index * header.programEntrySize
    let program := headers[index]
    IO.Reader.u32 data header.endian entry = .ok program.kind ∧
      IO.Reader.u32 data header.endian (entry + if header.is64 then 4 else 24) = .ok program.flags ∧
      word data header.endian header.is64 (entry + if header.is64 then 8 else 4) = .ok program.offset ∧
      word data header.endian header.is64 (entry + if header.is64 then 16 else 8) = .ok program.addr ∧
      word data header.endian header.is64 (entry + if header.is64 then 32 else 16) = .ok program.fileSize ∧
      word data header.endian header.is64 (entry + if header.is64 then 40 else 20) = .ok program.memorySize := by
  simp only [Elf.programHeaders, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, h⟩
  cases he
  by_cases h0 : header.programCount = 0
  · rw [ite_eq_left h0] at h
    cases h
    simp at hi
  rw [ite_eq_right h0] at h
  by_cases hm : header.programEntrySize < (if header.is64 then 56 else 32)
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  have ⟨hl, hf⟩ := mapM_ok h
  have hlen : index < (List.range header.programCount).length := by rw [← hl]; exact hi
  have hk := hf index hi hlen
  simp only [List.getElem_range, bind_ok_iff] at hk
  rcases hk with ⟨kind, h1, flags, h2, offset, h3, addr, h4, fileSize, h5, memorySize, h6, hk⟩
  have hp := Except.ok.inj hk
  simp only
  rw [← hp]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Virtual-to-file translation stays in a LOAD segment's file bytes and in the input. -/
theorem offsetOf_sound {headers : List Elf.ProgramHeader} {dataSize addr size offset : Nat}
    (h : offsetOf headers dataSize addr size = some offset) :
    offset + size ≤ dataSize ∧ ∃ header ∈ headers, header.kind = 1 ∧ header.addr ≤ addr ∧
      addr - header.addr + size ≤ header.fileSize ∧ offset = header.offset + (addr - header.addr) := by
  have ⟨header, hm, hv⟩ := List.exists_of_findSome?_eq_some h
  dsimp only at hv
  split at hv
  · cases hv
  rename_i h1
  split at hv
  · cases hv
  rename_i h2
  split at hv
  · rename_i h3
    cases hv
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Decidable.not_not] at h1 h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    refine ⟨by omega, header, hm, h1.1, by omega, by omega, rfl⟩
  · cases hv

/-- `tagValue` returns the value of the first matching tag. -/
theorem tagValue_some {tags : List (Nat × Nat)} {tag value : Nat} (h : tagValue tags tag = some value) :
    (tag, value) ∈ tags := by
  simp only [tagValue, Option.map_eq_some_iff] at h
  rcases h with ⟨entry, hf, rfl⟩
  have hm := List.mem_of_find?_eq_some hf
  have ht := List.find?_some hf
  simp only [decide_eq_true_eq] at ht
  rw [← ht]
  exact hm

theorem tagValue_none {tags : List (Nat × Nat)} {tag : Nat} (h : tagValue tags tag = none) :
    ∀ value, (tag, value) ∉ tags := by
  intro value hm
  simp only [tagValue, Option.map_eq_none_iff, List.find?_eq_none] at h
  exact h _ hm (by simp)

/-- The dynamic section walker stops at `DT_NULL`, reads at most `remaining` entries and keeps no null tag. -/
theorem readEntries_ok {data : ByteArray} {is64 : Bool} {endian : Endian} {entrySize : Nat} :
    ∀ {remaining offset : Nat} {tags result : List (Nat × Nat)},
      Elf.dynamicTags.readEntries data is64 endian entrySize remaining offset tags = .ok result →
      result.length ≤ tags.length + remaining ∧
        ∀ entry ∈ result, entry ∈ tags ∨ entry.1 ≠ 0
  | 0, offset, tags, result, h => by
    simp only [Elf.dynamicTags.readEntries] at h
    cases h
    exact ⟨by simp, fun entry hm => .inl (by simpa using hm)⟩
  | n + 1, offset, tags, result, h => by
    simp only [Elf.dynamicTags.readEntries, bind_ok_iff] at h
    rcases h with ⟨tag, _, h⟩
    by_cases ht : tag = 0
    · rw [ite_eq_left ht] at h
      cases h
      exact ⟨by simp, fun entry hm => .inl (by simpa using hm)⟩
    · rw [ite_eq_right ht] at h
      simp only [bind_ok_iff] at h
      rcases h with ⟨value, _, h⟩
      have ⟨hl, hm⟩ := readEntries_ok h
      refine ⟨by simp at hl; omega, fun entry he => ?_⟩
      rcases hm entry he with hc | hc
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact .inr ht
        · exact .inl hc
      · exact .inr hc

/-- Tags read from a dynamic segment never include `DT_NULL`, and the walker is bounded by the segment. -/
theorem dynamicTags_ok {data : ByteArray} {headers : List Elf.ProgramHeader} {is64 : Bool} {endian : Endian}
    {tags : List (Nat × Nat)} (h : Elf.dynamicTags data headers is64 endian = .ok tags) :
    (∀ entry ∈ tags, entry.1 ≠ 0) ∧
      ∀ segment, headers.find? (fun header => header.kind = 2) = some segment →
        tags.length ≤ segment.fileSize / (if is64 then 16 else 8) := by
  simp only [Elf.dynamicTags] at h
  split at h
  · rename_i hf
    cases h
    exact ⟨by simp, fun segment hs => by simp [hs] at hf⟩
  · rename_i segment hf
    by_cases hb : (decide (segment.offset > data.size) ||
        decide (data.size - segment.offset < segment.fileSize)) = true
    · rw [ite_eq_left hb] at h; cases h
    · rw [ite_eq_right hb] at h
      have ⟨hl, hm⟩ := readEntries_ok h
      refine ⟨fun entry he => (hm entry he).elim (by simp) id, ?_⟩
      intro other ho
      rw [hf] at ho
      cases ho
      simpa using hl

/-! ### SLEB128 -/

private theorem sleb128_loop_ok {data : ByteArray} :
    ∀ {fuel offset shift value result next : Nat},
      value < 2 ^ 64 →
      sleb128.loop data fuel offset shift value = some (result, next) →
      offset < next ∧ next ≤ data.size ∧ result < 2 ^ 64
  | 0, _, _, _, _, _, _, h => by simp [sleb128.loop] at h
  | fuel + 1, offset, shift, value, result, next, _, h => by
    simp only [sleb128.loop] at h
    split at h
    · cases h
    rename_i hb
    split at h
    · have ih := sleb128_loop_ok (Nat.mod_lt _ (by decide)) h
      omega
    · cases h
      refine ⟨by omega, by omega, ?_⟩
      split <;> exact Nat.mod_lt _ (by decide)

/-- A decoded SLEB128 consumes at least a byte, stays in the input and yields a 64-bit value. -/
theorem sleb128_ok {data : ByteArray} {offset result next : Nat}
    (h : sleb128 data offset = some (result, next)) :
    offset < next ∧ next ≤ data.size ∧ result < 2 ^ 64 :=
  sleb128_loop_ok (by decide) h

private theorem low_bits : ∀ b : Fin 128,
    b.val &&& 0x7f = b.val ∧ b.val &&& 0x80 = 0 ∧ ((b.val &&& 0x40 != 0) = true ↔ 64 ≤ b.val) := by
  decide

/-- A single-byte SLEB128: values below 64 are themselves, the rest are sign-extended to 64 bits. -/
theorem sleb128_single {data : ByteArray} {offset : Nat} (h : offset < data.size)
    (hb : data[offset]!.toNat < 128) :
    sleb128 data offset =
      some (if 64 ≤ data[offset]!.toNat then 2 ^ 64 + data[offset]!.toNat - 128 else data[offset]!.toNat, offset + 1) := by
  have ⟨h7f, h80, h40⟩ := low_bits ⟨_, hb⟩
  dsimp only at h7f h80 h40
  simp only [sleb128, sleb128.loop]
  rw [ite_eq_right (by omega)]
  simp only [h7f, h80]
  generalize data[offset]!.toNat = byte at *
  by_cases hs : 64 ≤ byte
  · have hd := h40.mpr hs
    simp [hd, hs]
    omega
  · have hd : ¬ (byte &&& 64 != 0) = true := fun e => hs (h40.mp e)
    simp only [Bool.not_eq_true] at hd
    simp [hd, hs]
    omega

/-- `alignUp` returns the least multiple of `alignment` at or above `value`. -/
theorem alignUp_spec {value alignment : Nat} (h : 1 < alignment) :
    value ≤ alignUp value alignment ∧ alignUp value alignment % alignment = 0 ∧
      alignUp value alignment < value + alignment := by
  have hne : ¬ alignment ≤ 1 := by omega
  simp only [alignUp, hne, ↓reduceIte]
  have hpos : 0 < alignment := by omega
  have hdiv := Nat.div_add_mod (value + alignment - 1) alignment
  have hmod := Nat.mod_lt (value + alignment - 1) hpos
  have hcomm : (value + alignment - 1) / alignment * alignment =
      alignment * ((value + alignment - 1) / alignment) := Nat.mul_comm ..
  refine ⟨by omega, Nat.mul_mod_left .., by omega⟩

theorem alignUp_trivial (value : Nat) {alignment : Nat} (h : alignment ≤ 1) : alignUp value alignment = value := by
  simp [alignUp, h]

/-- Import stubs fill whole pages and cover one pointer slot per import. -/
theorem importBytes_spec (image : Image) (count : Nat) :
    let bytes := Elf.importBytes image count
    count * (image.addrWidth / 8) ≤ bytes ∧ bytes % 0x1000 = 0 ∧
      bytes < count * (image.addrWidth / 8) + 0x1000 := by
  exact alignUp_spec (by decide)

/-! ### Symbols and relocations -/

/-- The address of an ARM function drops the Thumb flag; every other symbol's address is its value. -/
theorem codeAddress_spec (machine typ value : Nat) :
    (machine = 40 ∧ typ = 2 → codeAddress machine typ value = value - value % 2 ∧
        codeAddress machine typ value % 2 = 0 ∧ value ≤ codeAddress machine typ value + 1) ∧
      (¬ (machine = 40 ∧ typ = 2) → codeAddress machine typ value = value) := by
  constructor
  · rintro ⟨rfl, rfl⟩
    simp only [codeAddress]
    simp
    omega
  · intro h
    simp only [codeAddress]
    rw [ite_eq_right (by simpa using h)]

/-- A named symbol is read at its class's `Sym` offsets. -/
theorem parseSymbol_layout {data : ByteArray} {header : Elf.Header} {strings : Elf.SectionHeader} {offset : Nat}
    {symbol : Symbol} (h : parseSymbol data header strings offset = .ok (some symbol)) :
    ∃ nameOffset info value,
      IO.Reader.u32 data header.endian offset = .ok nameOffset ∧ nameOffset ≠ 0 ∧
      IO.Reader.get8 data (offset + if header.is64 then 4 else 12) = .ok info ∧
      word data header.endian header.is64 (offset + if header.is64 then 16 else 8) = .ok symbol.size ∧
      word data header.endian header.is64 (offset + if header.is64 then 8 else 4) = .ok value ∧
      symbol.addr = codeAddress header.machine (info &&& 0xf) value ∧
      symbol.isFunction = decide (info &&& 0xf = 2) ∧
      IO.Reader.cstring data (strings.offset + nameOffset) = .ok symbol.name := by
  simp only [parseSymbol, bind_ok_iff] at h
  rcases h with ⟨nameOffset, h1, info, h2, size, h3, value, h4, h⟩
  by_cases h0 : nameOffset = 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨name, h5, h⟩
  cases h
  exact ⟨nameOffset, info, value, h1, h0, h2, h3, h4, rfl, rfl, h5⟩

/-- `r_info` splits exactly into symbol and type: at bit 8 for ELF32 and bit 32 for ELF64. -/
theorem splitInfo_elf32 (info : Nat) :
    (Elf.splitInfo false false info).1 < 0x100 ∧
      info = (Elf.splitInfo false false info).2 * 0x100 + (Elf.splitInfo false false info).1 := by
  simp only [Elf.splitInfo, Bool.false_eq_true, ↓reduceIte]
  omega

theorem splitInfo_elf64 (info : Nat) :
    (Elf.splitInfo true false info).1 < 0x100000000 ∧
      info = (Elf.splitInfo true false info).2 * 0x100000000 + (Elf.splitInfo true false info).1 := by
  simp only [Elf.splitInfo, Bool.false_eq_true, ↓reduceIte]
  omega

/-- mips64el stores `r_sym` in the low word of `r_info` and then `r_ssym, r_type3, r_type2, r_type`, one byte each.
The split reads the same type and symbol as the big-endian layout, `sym:ssym:type3:type2:type`. -/
theorem splitInfo_mips64el {symbol ssym type3 type2 typ : Nat} (hsym : symbol < 4294967296) (h4 : ssym < 256)
    (h3 : type3 < 256) (h2 : type2 < 256) (h1 : typ < 256) :
    Elf.splitInfo true true (symbol + ssym * 4294967296 + type3 * 1099511627776 + type2 * 281474976710656 +
        typ * 72057594037927936) =
      Elf.splitInfo true false (symbol * 4294967296 + ssym * 16777216 + type3 * 65536 + type2 * 256 + typ) := by
  generalize hinfo : symbol + ssym * 4294967296 + type3 * 1099511627776 + type2 * 281474976710656 +
    typ * 72057594037927936 = info
  generalize hbig : symbol * 4294967296 + ssym * 16777216 + type3 * 65536 + type2 * 256 + typ = big
  have little : Elf.splitInfo true true info = ((info >>> 32) % 256 * 2 ^ 24 + (info >>> 40) % 256 * 2 ^ 16 +
      (info >>> 48) % 256 * 2 ^ 8 + (info >>> 56) % 256, info % 0x100000000) := rfl
  have bigEndian : Elf.splitInfo true false big = (big % 0x100000000, big / 0x100000000) := rfl
  have s0 : info >>> 32 = info / 4294967296 := by rw [Nat.shiftRight_eq_div_pow]
  have s1 : info >>> 40 = info / 4294967296 / 256 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  have s2 : info >>> 48 = info / 4294967296 / 256 / 256 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  have s3 : info >>> 56 = info / 4294967296 / 256 / 256 / 256 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  have b6 : info % 4294967296 = symbol := by omega
  have q0 : info / 4294967296 = ssym + type3 * 256 + type2 * 65536 + typ * 16777216 := by omega
  have b0 : info / 4294967296 % 256 = ssym := by omega
  have q1 : info / 4294967296 / 256 = type3 + type2 * 256 + typ * 65536 := by omega
  have b1 : info / 4294967296 / 256 % 256 = type3 := by omega
  have q2 : info / 4294967296 / 256 / 256 = type2 + typ * 256 := by omega
  have b2 : info / 4294967296 / 256 / 256 % 256 = type2 := by omega
  have b3 : info / 4294967296 / 256 / 256 / 256 % 256 = typ := by omega
  have b4 : big % 4294967296 = ssym * 16777216 + type3 * 65536 + type2 * 256 + typ := by omega
  have b5 : big / 4294967296 = symbol := by omega
  rw [little, bigEndian, s0, s1, s2, s3, b0, b1, b2, b3]
  show (ssym * 16777216 + type3 * 65536 + type2 * 256 + typ, info % 4294967296) =
    (big % 4294967296, big / 4294967296)
  rw [b4, b5, b6]

/-- A relocation table holds one record per entry of its class and `REL` or `RELA` kind. Each is read at its own
slot, with `r_info` split at the class's bit, and an addend exactly for `RELA`. -/
theorem readRelocationTable_ok {image : Image} {headers : List Elf.ProgramHeader} {addr size : Nat} {rela : Bool}
    {result : List Elf.DynamicRelocation} {offset : Nat} {header : Elf.Header}
    (hh : parseHeader image.data = .ok header)
    (ho : offsetOf headers image.data.size addr size = some offset)
    (h : Elf.readRelocationTable image headers addr size rela = .ok result) :
    let entrySize := if header.is64 then (if rela then 24 else 16) else (if rela then 12 else 8)
    result.length = size / entrySize ∧
      ∀ index (hi : index < result.length),
        let entry := offset + index * entrySize
        let relocation := result[index]
        word image.data image.endian header.is64 entry = .ok relocation.offset ∧
        relocation.explicitAddend = rela ∧
        ∃ info, word image.data image.endian header.is64 (entry + if header.is64 then 8 else 4) = .ok info ∧
          (relocation.typ, relocation.symbol) = Elf.splitInfo header.is64 (isMips64el header) info ∧
          (rela = true → word image.data image.endian header.is64
            (entry + if header.is64 then 16 else 8) = .ok relocation.addend) ∧
          (rela = false → relocation.addend = 0) := by
  simp only [Elf.readRelocationTable, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, h⟩
  cases he
  simp only [ho] at h
  have ⟨hl, hf⟩ := mapM_ok h
  simp only [List.length_range] at hl
  refine ⟨hl, ?_⟩
  intro index hi
  have hk := hf index hi (by simpa [hl] using hi)
  simp only [List.getElem_range, bind_ok_iff] at hk
  rcases hk with ⟨relOffset, h1, info, h2, hk⟩
  simp only
  rcases hsplit : Elf.splitInfo header.is64 (isMips64el header) info with ⟨typ, symbol⟩
  cases rela with
  | true =>
    simp only [↓reduceIte, bind_ok_iff, hsplit] at hk
    rcases hk with ⟨addend, h3, hk⟩
    rw [← Except.ok.inj hk]
    exact ⟨h1, rfl, info, h2, hsplit.symm, fun _ => h3, fun e => by cases e⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Reader.ok_bind, hsplit] at hk
    rw [← Except.ok.inj hk]
    exact ⟨h1, rfl, info, h2, hsplit.symm, (fun e => by cases e), fun _ => rfl⟩

/-- The relocation numbers against `elf.h` and LLVM's `ELFRelocs`. -/
theorem relocation_numbers :
    relativeType 3 = 8 ∧ relativeType 8 = 3 ∧ relativeType 20 = 22 ∧ relativeType 21 = 22 ∧
      relativeType 40 = 23 ∧ relativeType 62 = 8 ∧ relativeType 183 = 1027 ∧ relativeType 243 = 3 ∧
      irelativeType 3 = 42 ∧ irelativeType 20 = 248 ∧ irelativeType 21 = 248 ∧ irelativeType 40 = 160 ∧
      irelativeType 62 = 37 ∧ irelativeType 183 = 1032 ∧ irelativeType 243 = 58 ∧
      symbolRelocationKind 3 1 false = 1 ∧ symbolRelocationKind 3 6 false = 2 ∧ symbolRelocationKind 3 7 false = 2 ∧
      symbolRelocationKind 3 2 false = 0 ∧
      symbolRelocationKind 20 1 false = 1 ∧ symbolRelocationKind 20 20 false = 2 ∧ symbolRelocationKind 20 21 false = 2 ∧
      symbolRelocationKind 21 38 true = 1 ∧ symbolRelocationKind 21 20 true = 2 ∧ symbolRelocationKind 21 21 true = 2 ∧
      symbolRelocationKind 40 2 false = 1 ∧ symbolRelocationKind 40 21 false = 2 ∧ symbolRelocationKind 40 22 false = 2 ∧
      symbolRelocationKind 243 1 false = 1 ∧ symbolRelocationKind 243 2 true = 1 ∧ symbolRelocationKind 243 5 false = 2 := by
  decide

/-! ### Packed relocations -/

private theorem option_bind_ok {α β : Type} {x : Option α} {f : α → Option β} {v : β} :
    (x >>= f) = some v ↔ ∃ a, x = some a ∧ f a = some v := by
  cases x <;> simp [bind, Option.bind]

/-- A packed relocation advances the offset by its delta in 64 bits, and carries the running addend. -/
theorem androidEntry_ok {bytes : ByteArray} {group : AndroidGroup} {cursor offset addend : Nat}
    {relocation : Elf.DynamicRelocation} {cursor' offset' addend' : Nat} (ha : addend < 2 ^ 64)
    (h : androidEntry bytes group cursor offset addend = some (relocation, cursor', offset', addend')) :
    offset' < 2 ^ 64 ∧ addend' < 2 ^ 64 ∧ relocation.offset = offset' ∧ relocation.addend = addend' ∧
      relocation.explicitAddend = AndroidGroup.rela group ∧
      ∃ delta next, androidField bytes (AndroidGroup.byOffset group) (AndroidGroup.offsetDelta group) cursor =
        some (delta, next) ∧ offset' = (offset + delta) % 0x10000000000000000 := by
  simp only [androidEntry, option_bind_ok] at h
  rcases h with ⟨⟨delta, next⟩, hd, ⟨info, next2⟩, _, h⟩
  have hmod : (offset + delta) % 0x10000000000000000 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  split at h
  · simp only [option_bind_ok, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨addendDelta, next3⟩, _, _, rfl, rfl, _, rfl, rfl⟩ := h
    exact ⟨hmod, Nat.mod_lt _ (by decide), rfl, rfl, rfl, delta, next, hd, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq, option_bind_ok] at h
    obtain ⟨_, rfl, rfl, _, rfl, rfl⟩ := h
    exact ⟨hmod, ha, rfl, rfl, rfl, delta, next, hd, rfl⟩

/-- The relocations that decoding produces: 64-bit offsets and addends, and an addend exactly for `RELA`. -/
def PackedBounds (rela : Bool) (relocation : Elf.DynamicRelocation) : Prop :=
  relocation.offset < 2 ^ 64 ∧ relocation.addend < 2 ^ 64 ∧ relocation.explicitAddend = rela

/-- A group yields exactly its size of relocations unless the input ends in it, when what was read stays. -/
theorem androidEntries_ok {bytes : ByteArray} {group : AndroidGroup} :
    ∀ (left : Nat) (state : AndroidState), AndroidState.addend state < 2 ^ 64 →
      let (complete, next) := androidEntries bytes group left state
      AndroidState.addend next < 2 ^ 64 ∧
        ∃ added, AndroidState.result next = added ++ AndroidState.result state ∧ added.length ≤ left ∧
          (complete = true → added.length = left) ∧ ∀ relocation ∈ added, PackedBounds (AndroidGroup.rela group) relocation
  | 0, state, ha => by
    simp only [androidEntries]
    exact ⟨ha, [], by simp, by simp, by simp, by simp⟩
  | left + 1, state, ha => by
    simp only [androidEntries]
    split
    · exact ⟨ha, [], by simp, by simp, by simp, by simp⟩
    · rename_i relocation cursor offset addend hentry
      have ⟨h1, h2, h3, h4, h5, _⟩ := androidEntry_ok ha hentry
      have hrec := androidEntries_ok (bytes := bytes) (group := group) left
        (AndroidState.mk cursor offset addend (relocation :: AndroidState.result state)) h2
      rcases hr : androidEntries bytes group left
        (AndroidState.mk cursor offset addend (relocation :: AndroidState.result state)) with ⟨complete, next⟩
      rw [hr] at hrec
      obtain ⟨h6, added, ha1, ha2, ha3, ha4⟩ := hrec
      refine ⟨h6, added ++ [relocation], by simpa using ha1, by simp; omega, ?_, ?_⟩
      · intro hc
        have := ha3 hc
        simp
        omega
      · intro other ho
        rcases List.mem_append.mp ho with ho | ho
        · exact ha4 other ho
        · simp only [List.mem_singleton] at ho
          subst ho
          exact ⟨h3 ▸ h1, h4 ▸ h2, h5⟩

/-- A decoded group header belongs to the file's class and kind, and keeps the addend in 64 bits. -/
theorem androidGroupHeader_ok {bytes : ByteArray} {is64 rela : Bool} {cursor addend size cursor' addend' : Nat}
    {group : AndroidGroup} (ha : addend < 2 ^ 64)
    (h : androidGroupHeader bytes is64 rela cursor addend = some (size, group, cursor', addend')) :
    AndroidGroup.rela group = rela ∧ AndroidGroup.is64 group = is64 ∧ addend' < 2 ^ 64 := by
  simp only [androidGroupHeader, option_bind_ok] at h
  rcases h with ⟨⟨s, c1⟩, _, ⟨flags, c2⟩, _, ⟨d, c3⟩, _, ⟨i, c4⟩, _, h⟩
  split at h
  · simp only [option_bind_ok] at h
    rcases h with ⟨⟨delta, c5⟩, _, h⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _, rfl, _, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    split
    · exact Nat.mod_lt _ (by decide)
    · decide
  · simp only [Option.some.injEq, Prod.mk.injEq, option_bind_ok] at h
    obtain ⟨_, rfl, _, rfl, _, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    split
    · exact ha
    · decide

/-- Decoding never yields more relocations than the table announces, however the groups are sized. -/
theorem androidGroups_ok {bytes : ByteArray} {is64 rela : Bool} :
    ∀ (fuel remaining : Nat) (state : AndroidState), AndroidState.addend state < 2 ^ 64 →
      ∃ added, androidGroups bytes is64 rela fuel remaining state = added ++ AndroidState.result state ∧
        added.length ≤ remaining ∧ ∀ relocation ∈ added, PackedBounds rela relocation
  | 0, _, state, _ => ⟨[], by simp [androidGroups], by simp, by simp⟩
  | fuel + 1, remaining, state, ha => by
    unfold androidGroups
    split
    · exact ⟨[], by simp, by simp, by simp⟩
    rename_i hr
    split
    · exact ⟨[], by simp, by simp, by simp⟩
    rename_i size group cursor addend hheader
    have ⟨hrela, _, hadd⟩ := androidGroupHeader_ok ha hheader
    split
    · exact ⟨[], by simp, by simp, by simp⟩
    rename_i hsize
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hsize
    have hentries := androidEntries_ok (bytes := bytes) (group := group) size
      (AndroidState.mk cursor (AndroidState.offset state) addend (AndroidState.result state)) hadd
    rcases he : androidEntries bytes group size
      (AndroidState.mk cursor (AndroidState.offset state) addend (AndroidState.result state)) with ⟨complete, next⟩
    rw [he] at hentries
    obtain ⟨h1, added, h2, h3, _, h4⟩ := hentries
    simp only at h2
    cases complete with
    | true =>
      have ⟨more, h5, h6, h7⟩ := androidGroups_ok (bytes := bytes) (is64 := is64) (rela := rela) fuel
        (remaining - size) next h1
      simp only [↓reduceIte]
      refine ⟨more ++ added, by rw [h5, h2, List.append_assoc], by simp; omega, ?_⟩
      intro relocation hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h7 relocation hm
      · exact hrela ▸ h4 relocation hm
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨added, h2, by omega, ?_⟩
      intro relocation hm
      exact hrela ▸ h4 relocation hm

private theorem packedTop {bytes : ByteArray} {is64 rela : Bool} {count cursor initial limit : Nat}
    (hlimit : count ≤ limit) :
    (androidGroups bytes is64 rela count count (AndroidState.mk cursor initial 0 [])).reverse.length ≤ limit ∧
      ∀ relocation ∈ (androidGroups bytes is64 rela count count (AndroidState.mk cursor initial 0 [])).reverse,
        PackedBounds rela relocation := by
  have ⟨added, h1, h2, h3⟩ := androidGroups_ok (bytes := bytes) (is64 := is64) (rela := rela) count count
    (AndroidState.mk cursor initial 0 []) (by show 0 < 2 ^ 64; decide)
  have hr : androidGroups bytes is64 rela count count (AndroidState.mk cursor initial 0 []) = added := by
    simpa using h1
  rw [hr]
  refine ⟨by simp; omega, ?_⟩
  intro relocation hm
  exact h3 relocation (by simpa using hm)

/-- A packed table never yields more than the limit, and what it yields is in bounds. -/
theorem decodeAndroid_ok (bytes : ByteArray) (is64 rela : Bool) :
    (decodeAndroid bytes is64 rela).length ≤ Elf.maxPackedRelocations ∧
      ∀ relocation ∈ decodeAndroid bytes is64 rela, PackedBounds rela relocation := by
  unfold decodeAndroid
  split
  · simp [Elf.maxPackedRelocations]
  split
  · simp [Elf.maxPackedRelocations]
  split
  · simp [Elf.maxPackedRelocations]
  split
  · simp [Elf.maxPackedRelocations]
  rename_i hcount
  exact packedTop (by omega)

/-- A table without the `APS2` magic is empty, however long. -/
theorem decodeAndroid_requires_magic {bytes : ByteArray} {is64 rela : Bool}
    (h : bytes.size < 4 ∨ (bytes.extract 0 4 != ByteArray.mk #[65, 80, 83, 50]) = true) :
    decodeAndroid bytes is64 rela = [] := by
  unfold decodeAndroid
  rw [ite_eq_left]
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using h

/-! ### RELR -/

/-- A RELR bitmap marks exactly the words of its set bits: bit `i` at `base + (index + i) * width`. -/
theorem mem_relrBits {typ base width : Nat} :
    ∀ (value index : Nat) (result : List Elf.DynamicRelocation) (relocation : Elf.DynamicRelocation),
      relocation ∈ relrBits typ base width value index result ↔
        relocation ∈ result ∨ ∃ i, value.testBit i = true ∧
          relocation = ⟨base + (index + i) * width, typ, 0, 0, false⟩ := by
  intro value
  induction value using Nat.strongRecOn with
  | ind value ih =>
    intro index result relocation
    rw [relrBits]
    split
    · rename_i h0
      subst h0
      simp
    rename_i h0
    have hlt : value / 2 < value := by omega
    rw [ih (value / 2) hlt]
    constructor
    · rintro (hm | ⟨i, hb, rfl⟩)
      · split at hm
        · rename_i hodd
          simp only [List.mem_cons] at hm
          rcases hm with rfl | hm
          · refine .inr ⟨0, ?_, by simp⟩
            simp [Nat.testBit_zero, hodd]
          · exact .inl hm
        · exact .inl hm
      · refine .inr ⟨i + 1, ?_, ?_⟩
        · rw [Nat.testBit_succ]; exact hb
        · rw [show index + (i + 1) = index + 1 + i by omega]
    · rintro (hm | ⟨i, hb, rfl⟩)
      · refine .inl ?_
        split
        · exact List.mem_cons_of_mem _ hm
        · exact hm
      · cases i with
        | zero =>
          have hodd : value % 2 = 1 := by simpa [Nat.testBit_zero] using hb
          refine .inl ?_
          rw [ite_eq_left hodd]
          simp
        | succ i =>
          refine .inr ⟨i, by rwa [Nat.testBit_succ] at hb, ?_⟩
          rw [show index + (i + 1) = index + 1 + i by omega]

/-- An address entry relocates that word and the next base follows it. -/
theorem relrDecode_address {typ width entry base : Nat} {rest : List Nat} {result : List Elf.DynamicRelocation}
    (h : entry % 2 = 0) :
    relrDecode typ width (entry :: rest) base result =
      relrDecode typ width rest (entry + width) (⟨entry, typ, 0, 0, false⟩ :: result) := by
  rw [relrDecode, ite_eq_left h]

/-- A bitmap entry relocates the words it marks and moves the base by the `8 * width - 1` words it can mark. -/
theorem relrDecode_bitmap {typ width entry base : Nat} {rest : List Nat} {result : List Elf.DynamicRelocation}
    (h : entry % 2 ≠ 0) :
    relrDecode typ width (entry :: rest) base result =
      relrDecode typ width rest (base + (8 * width - 1) * width) (relrBits typ base width (entry / 2) 0 result) := by
  rw [relrDecode, ite_eq_right h]

/-- All RELR relocations are relative, and have no symbol and no explicit addend. -/
theorem relrDecode_sound {typ width : Nat} :
    ∀ (entries : List Nat) (base : Nat) (result : List Elf.DynamicRelocation),
      (∀ relocation ∈ result, relocation.typ = typ ∧ relocation.symbol = 0 ∧ relocation.explicitAddend = false) →
      ∀ relocation ∈ relrDecode typ width entries base result,
        relocation.typ = typ ∧ relocation.symbol = 0 ∧ relocation.explicitAddend = false
  | [], base, result, h, relocation, hm => by
    rw [relrDecode] at hm
    exact h relocation (by simpa using hm)
  | entry :: rest, base, result, h, relocation, hm => by
    rw [relrDecode] at hm
    split at hm
    · refine relrDecode_sound rest _ _ ?_ relocation hm
      intro other ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨rfl, rfl, rfl⟩
      · exact h other ho
    · refine relrDecode_sound rest _ _ ?_ relocation hm
      intro other ho
      rcases (mem_relrBits _ _ _ _).mp ho with ho | ⟨_, _, rfl⟩
      · exact h other ho
      · exact ⟨rfl, rfl, rfl⟩

/-! ### Classifying dynamic relocations -/

private theorem reference_choice (named notWeak : Bool) (offset : Nat) (name : String) (references : List (Nat × String))
    {symbolIndex : Nat} (hsym : ¬ symbolIndex = 0) (hn : named = !name.isEmpty) :
    (if (named && notWeak) = true then (offset, name) :: references else references) = references ∨
      ∃ name', (if (named && notWeak) = true then (offset, name) :: references else references) =
        (offset, name') :: references ∧ name' ≠ "" ∧ symbolIndex ≠ 0 := by
  by_cases hc : (named && notWeak) = true
  · refine .inr ⟨name, by simp [hc], ?_, hsym⟩
    simp only [Bool.and_eq_true] at hc
    rw [hn] at hc
    intro he
    subst he
    simp at hc
  · exact .inl (by rw [ite_eq_right hc])

/-- How one relocation can add to the facts: nothing, or the entry its kind justifies. -/
def ClassifiedBy (machine width : Nat) (relocation : Elf.DynamicRelocation) (result next : Elf.RelocationSpec) : Prop :=
  (next.relative = result.relative ∨ (next.relative = relocation.offset :: result.relative ∧ relocation.symbol = 0 ∧
      isRelativeType machine relocation.typ = true)) ∧
    (next.absolute = result.absolute ∨ ∃ target, next.absolute = (relocation.offset, target) :: result.absolute ∧
      target < 2 ^ width ∧ relocation.symbol ≠ 0) ∧
    (next.references = result.references ∨ ∃ name, next.references = (relocation.offset, name) :: result.references ∧
      name ≠ "" ∧ relocation.symbol ≠ 0)

theorem classifyRelocation_ok {image : Image} {headers : List Elf.ProgramHeader} {tags : List (Nat × Nat)}
    {header : Elf.Header} {result next : Elf.RelocationSpec} {relocation : Elf.DynamicRelocation}
    (h : classifyRelocation image headers tags header result relocation = .ok next) :
    ClassifiedBy header.machine image.addrWidth relocation result next := by
  unfold classifyRelocation at h
  simp only at h
  split at h
  · rename_i hsym
    split at h
    · cases h
      exact ⟨.inl rfl, .inl rfl, .inl rfl⟩
    · split at h
      · cases h
        exact ⟨.inl rfl, .inl rfl, .inl rfl⟩
      · rename_i hrelative
        cases h
        have hr : isRelativeType header.machine relocation.typ = true := by simpa using hrelative
        exact ⟨.inr ⟨rfl, hsym, hr⟩, .inl rfl, .inl rfl⟩
  · rename_i hsym
    simp only [bind_ok_iff] at h
    rcases h with ⟨symbol, _, h⟩
    split at h
    · cases h
      exact ⟨.inl rfl, .inl rfl, .inl rfl⟩
    rename_i dynamic _
    split at h
    · cases h
      exact ⟨.inl rfl, .inl rfl, .inl rfl⟩
    split at h
    · cases h
      exact ⟨.inl rfl, .inl rfl, .inl rfl⟩
    have hrefs := reference_choice (!dynamic.name.isEmpty) (!(decide (dynamic.sectionIndex = 0) &&
      decide (dynamic.binding = 2))) relocation.offset dynamic.name result.references hsym rfl
    split at h
    · cases h
      exact ⟨.inl rfl, .inl rfl, hrefs⟩
    · cases h
      exact ⟨.inl rfl, .inr ⟨_, rfl, Nat.mod_lt _ (Nat.pow_pos (by decide)), hsym⟩, hrefs⟩

/-- Folding the classification: every fact comes from a relocation that justifies it. -/
theorem foldClassify_ok {image : Image} {headers : List Elf.ProgramHeader} {tags : List (Nat × Nat)} {header : Elf.Header} :
    ∀ (relocations : List Elf.DynamicRelocation) (result next : Elf.RelocationSpec),
      relocations.foldlM (classifyRelocation image headers tags header) result = .ok next →
      (∀ offset ∈ next.relative, offset ∈ result.relative ∨ ∃ relocation ∈ relocations, relocation.offset = offset ∧
        relocation.symbol = 0 ∧ isRelativeType header.machine relocation.typ = true) ∧
      (∀ entry ∈ next.absolute, entry ∈ result.absolute ∨ (entry.2 < 2 ^ image.addrWidth ∧
        ∃ relocation ∈ relocations, relocation.offset = entry.1 ∧ relocation.symbol ≠ 0)) ∧
      (∀ entry ∈ next.references, entry ∈ result.references ∨ (entry.2 ≠ "" ∧
        ∃ relocation ∈ relocations, relocation.offset = entry.1 ∧ relocation.symbol ≠ 0))
  | [], result, next, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨fun _ hm => .inl hm, fun _ hm => .inl hm, fun _ hm => .inl hm⟩
  | head :: rest, result, next, h => by
    simp only [List.foldlM_cons, bind_ok_iff] at h
    rcases h with ⟨middle, hm, hrest⟩
    have ⟨c1, c2, c3⟩ := classifyRelocation_ok hm
    have ⟨f1, f2, f3⟩ := foldClassify_ok rest middle next hrest
    refine ⟨?_, ?_, ?_⟩
    · intro offset ho
      rcases f1 offset ho with ho | ⟨relocation, hr, a, b, c⟩
      · rcases c1 with e | ⟨e, a', b'⟩
        · rw [e] at ho; exact .inl ho
        · rw [e] at ho
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact .inr ⟨head, by simp, rfl, a', b'⟩
          · exact .inl ho
      · exact .inr ⟨relocation, by simp [hr], a, b, c⟩
    · intro entry ho
      rcases f2 entry ho with ho | ⟨hw, relocation, hr, a, b⟩
      · rcases c2 with e | ⟨t, e, a', b'⟩
        · rw [e] at ho; exact .inl ho
        · rw [e] at ho
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact .inr ⟨a', head, by simp, rfl, b'⟩
          · exact .inl ho
      · exact .inr ⟨hw, relocation, by simp [hr], a, b⟩
    · intro entry ho
      rcases f3 entry ho with ho | ⟨hw, relocation, hr, a, b⟩
      · rcases c3 with e | ⟨t, e, a', b'⟩
        · rw [e] at ho; exact .inl ho
        · rw [e] at ho
          simp only [List.mem_cons] at ho
          rcases ho with rfl | ho
          · exact .inr ⟨a', head, by simp, rfl, b'⟩
          · exact .inl ho
      · exact .inr ⟨hw, relocation, by simp [hr], a, b⟩

/-- The MIPS global GOT entries: each reference is the slot of an imported dynamic symbol from `DT_MIPS_GOTSYM` on,
past the `DT_MIPS_LOCAL_GOTNO` local entries. -/
theorem mipsGotLoop_ok {image : Image} {headers : List Elf.ProgramHeader} {tags : List (Nat × Nat)}
    {pltgot localCount gotsym width : Nat} :
    ∀ (remaining index : Nat) (result output : List (Nat × String)),
      mipsGotReferences.loop image headers tags pltgot localCount gotsym width remaining index result = .ok output →
      ∀ entry ∈ output, entry ∈ result ∨ ∃ i, index ≤ i ∧ i < index + remaining ∧
        entry.1 = pltgot + (localCount + i - gotsym) * width ∧
        ∃ symbol : Elf.DynamicSymbol, Elf.dynamicSymbol image headers tags i = .ok (some symbol) ∧ symbol.name = entry.2 ∧
          symbol.name ≠ "" ∧ symbol.sectionIndex = 0 ∧ symbol.binding ≠ 2
  | 0, index, result, output, h, entry, hm => by
    simp only [mipsGotReferences.loop] at h
    cases h
    exact .inl (by simpa using hm)
  | remaining + 1, index, result, output, h, entry, hm => by
    simp only [mipsGotReferences.loop, bind_ok_iff] at h
    rcases h with ⟨none | symbol, hd, h⟩
    · simp only at h
      cases h
      exact .inl (by simpa using hm)
    simp only at h
    have hrec := mipsGotLoop_ok remaining (index + 1) _ output h entry hm
    rcases hrec with hr | ⟨i, h1, h2, h3, h4⟩
    · split at hr
      · rename_i himported
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at himported
          obtain ⟨⟨⟨h0, hw⟩, _⟩, hn⟩ := himported
          refine .inr ⟨index, Nat.le_refl _, by omega, rfl, symbol, hd, rfl, ?_, h0, hw⟩
          intro he
          rw [he] at hn
          simp at hn
        · exact .inl hr
      · exact .inl hr
    · exact .inr ⟨i, by omega, by omega, h3, h4⟩

/-- Everything `dynamicRelocations` reports comes from a dynamic table: relative offsets from symbol-less relocations
of the relative type, absolute targets are in the address space, and named references have names. -/
theorem dynamicRelocations_sound {image : Image} {spec : Elf.RelocationSpec} (h : Elf.dynamicRelocations image = .ok spec) :
    ∃ header, ∃ relocations : List Elf.DynamicRelocation, parseHeader image.data = .ok header ∧
      (∀ offset ∈ spec.relative, ∃ relocation ∈ relocations, relocation.offset = offset ∧ relocation.symbol = 0 ∧
        isRelativeType header.machine relocation.typ = true) ∧
      (∀ entry ∈ spec.absolute, entry.2 < 2 ^ image.addrWidth ∧
        ∃ relocation ∈ relocations, relocation.offset = entry.1 ∧ relocation.symbol ≠ 0) := by
  simp only [Elf.dynamicRelocations, bind_ok_iff] at h
  rcases h with ⟨header, h1, headers, _, tags, _, h⟩
  split at h
  · cases h
    exact ⟨header, [], h1, by simp, by simp⟩
  simp only [bind_ok_iff] at h
  rcases h with ⟨relocations, _, result, hfold, got, _, h⟩
  cases h
  have ⟨f1, f2, _⟩ := foldClassify_ok relocations {} result hfold
  refine ⟨header, relocations, h1, ?_, ?_⟩
  · intro offset hm
    rcases f1 offset (by simpa using hm) with ho | hr
    · cases ho
    · exact hr
  · intro entry hm
    rcases f2 entry (by simpa using hm) with ho | hr
    · cases ho
    · exact hr

/-- Android tables are read through the program headers: an address that is not in the file yields nothing. -/
theorem readAndroidRelocations_unmapped {image : Image} {headers : List Elf.ProgramHeader} {addr size : Nat} {rela : Bool}
    (h : offsetOf headers image.data.size addr size = none) :
    readAndroidRelocations image headers addr size rela = [] := by
  simp [readAndroidRelocations, h]

theorem readAndroidRelocations_ok (image : Image) (headers : List Elf.ProgramHeader) (addr size : Nat) (rela : Bool) :
    (readAndroidRelocations image headers addr size rela).length ≤ Elf.maxPackedRelocations ∧
      ∀ relocation ∈ readAndroidRelocations image headers addr size rela, PackedBounds rela relocation := by
  simp only [readAndroidRelocations]
  split
  · simp [Elf.maxPackedRelocations]
  · exact decodeAndroid_ok _ _ _

/-- RELR tables are read a word at a time, and all their relocations are relative. -/
theorem readRelrRelocations_ok {image : Image} {headers : List Elf.ProgramHeader} {addr size machine : Nat}
    {result : List Elf.DynamicRelocation} (h : readRelrRelocations image headers addr size machine = .ok result) :
    ∀ relocation ∈ result, relocation.typ = relativeType machine ∧ relocation.symbol = 0 ∧
      relocation.explicitAddend = false := by
  simp only [readRelrRelocations, bind_ok_iff] at h
  rcases h with ⟨header, _, h⟩
  split at h
  · cases h
    simp
  simp only [bind_ok_iff] at h
  rcases h with ⟨entries, _, h⟩
  cases h
  exact relrDecode_sound _ _ _ (by simp)

/-- The SLEB128 reader consumes a continuation byte and goes on. -/
theorem sleb128_loop_continue {data : ByteArray} {fuel offset shift value : Nat} (h : offset < data.size)
    (hc : (data[offset]!.toNat &&& 0x80 != 0) = true) :
    sleb128.loop data (fuel + 1) offset shift value =
      sleb128.loop data fuel (offset + 1) (shift + 7)
        ((value + if shift < 64 then (data[offset]!.toNat &&& 0x7f) * 2 ^ shift else 0) % 0x10000000000000000) := by
  rw [sleb128.loop]
  rw [ite_eq_right (by omega)]
  simp only [hc, ↓reduceIte]

/-- The segments and mapped regions of every decoded ELF correspond one to one, relocatable or not. -/
theorem decode_agree {data : ByteArray} {image : Image} (h : Elf.decode data = .ok image) : SegmentsAgree image := by
  have ⟨header, hh⟩ := decode_header h
  by_cases ht : header.fileType = 1
  · obtain ⟨_, _, _, sections, names, _, hseg, hmem⟩ := decode_relocatable h hh ht
    generalize hprep : (ElfLinker.prepare (linkInput data header sections names)).data.size = size at hmem
    generalize hoh : ElfLinker.link (ElfLinker.prepare (linkInput data header sections names)) = output at hseg hmem
    refine ⟨output.regions.map fun region =>
      (ElfLinker.toSegment region, ElfLinker.toMemRegion output.memory size region), ?_, ?_, ?_⟩
    · rw [hseg]; simp [Function.comp_def]
    · rw [hmem]; simp [Function.comp_def]
    · intro pair hp
      simp only [List.mem_map] at hp
      rcases hp with ⟨region, _, rfl⟩
      have ⟨a, b, _⟩ := LinkerLaws.toSegment_toMemRegion output.memory size region
      exact ⟨a, b⟩
  · have ⟨_, _, _, _, entries, hs, hm, hp⟩ := decode_loaded h hh ht
    exact ⟨entries, hs, hm, fun pair hpair => ⟨(hp pair hpair).1, (hp pair hpair).2.1⟩⟩

/-- Every byte mapped by a decoded ELF lies inside one of its segments. -/
theorem decode_readByte_in_segment {data : ByteArray} {image : Image} {address : Nat} {byte : UInt8}
    (h : Elf.decode data = .ok image) (hr : image.memory.readByte address = some byte) :
    ∃ segment ∈ image.segments, segment.addr ≤ address ∧ address < segment.addr + segment.size :=
  readByte_in_segment (decode_agree h) hr

/-- Only the relocations of allocated sections are linked, as upstream: `-g` relocations cannot reach memory. -/
theorem rawRelocations_allocated {data : ByteArray} {header : Elf.Header} {sections : List Elf.SectionHeader}
    {relocation : ElfLinker.Rel} (h : relocation ∈ rawRelocations data header sections) :
    ∃ target, sections[relocation.target]? = some target ∧ ElfLinker.hasFlag target.flags ElfLinker.shfAlloc = true := by
  simp only [rawRelocations, List.mem_flatMap, List.mem_filter] at h
  rcases h with ⟨sec, ⟨_, hrelocates⟩, h⟩
  cases hr : sectionRelocations data header sec with
  | error e =>
    rw [hr] at h
    cases h
  | ok list =>
    rw [hr] at h
    have hm : relocation ∈ list := h
    have hentries : relocation.target = sec.info := by
      have ⟨hl, hf⟩ := mapM_ok hr
      have ⟨i, hi1, hi2⟩ := List.getElem_of_mem hm
      have hk := hf i hi1 (hl ▸ hi1)
      rw [hi2] at hk
      simp only [bind_ok_iff] at hk
      rcases hk with ⟨_, _, _, _, hk⟩
      split at hk
      · simp only [bind_ok_iff] at hk
        rcases hk with ⟨_, _, hk⟩
        rw [← Except.ok.inj hk]
      · rw [← Except.ok.inj hk]
    simp only [relocatesMemory, Bool.and_eq_true] at hrelocates
    rw [hentries]
    have halloc := hrelocates.2
    split at halloc
    · rename_i target ht
      exact ⟨target, ht, halloc⟩
    · cases halloc

/-! ### Worked files -/

/-- A well-formed little-endian ELF32 executable with `e_phoff = 52` and one LOAD entry. -/
def elf32Sample : ByteArray := ByteArray.mk #[
  0x7f, 0x45, 0x4c, 0x46, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 0, 3, 0, 1, 0, 0, 0, 0x00, 0x10, 0, 0, 52, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0,
  0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 0, 0x00, 0x10, 0, 0, 0x00, 0x20, 0, 0,
  84, 0, 0, 0, 84, 0, 0, 0, 5, 0, 0, 0, 0x00, 0x10, 0, 0]

/-- The sample decodes with its `p_vaddr`, `p_memsz` and `p_flags`. -/
theorem elf32Sample_decodes :
    (Elf.decode elf32Sample).toOption.map (fun image =>
      image.addrWidth :: image.entryPoint :: image.segments.flatMap fun segment => [segment.addr, segment.size]) =
        some [32, 0x1000, 0x1000, 84] ∧
      (Elf.decode elf32Sample).toOption.map (fun image =>
        image.segments.flatMap fun segment => [segment.readable, segment.writable, segment.executable]) =
        some [true, false, true] := by
  decide

/-- A well-formed ELF64 relocatable header: no program headers, so `e_phentsize = 0`, as linkers emit. -/
def elf64ObjectSample : ByteArray := ByteArray.mk #[
  0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 0, 62, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0]

theorem elf64ObjectSample_decodes : (Elf.decode elf64ObjectSample).isOk = true := by
  decide

end ElfParser

/-! ## Mach-O -/

namespace MachoParser

open_private Bap.Image.Macho Bap.Image.Macho Header Header.mk Header.endian Header.commandBytes Header.commandCount
  FileMapping FileMapping.offset FileMapping.size FileMapping.address
  ParseState ParseState.mk ParseState.segments ParseState.regions ParseState.mappings ParseState.entryOffset
  parseHeader parseSegment parseCommands parseSymbol

open Reader

/-- The field-reading tail of `parseHeader`, once the byte order is known. -/
def headerTail (data : ByteArray) (endian : Endian) : Except String Header := do
  let cpuType ← IO.Reader.u32 data endian 4
  let commandCount ← IO.Reader.u32 data endian 16
  let commandBytes ← IO.Reader.u32 data endian 20
  if 32 + commandBytes > data.size then
    .error "Mach-O load commands exceed input"
  else
    .ok (Header.mk endian cpuType commandCount commandBytes)

/-- An accepted header has one of the two 64-bit magics, and its load commands fit in the input. -/
theorem parseHeader_ok {data : ByteArray} {header : Header} (h : parseHeader data = .ok header) :
    ((IO.Reader.read data Endian.big 0 4 = .ok 0xcffaedfe ∧ Header.endian header = Endian.little) ∨
      (IO.Reader.read data Endian.big 0 4 = .ok 0xfeedfacf ∧ Header.endian header = Endian.big)) ∧
      32 + Header.commandBytes header ≤ data.size := by
  have tail : ∀ {endian}, headerTail data endian = .ok header → Header.endian header = endian ∧
      32 + Header.commandBytes header ≤ data.size := by
    intro endian ht
    simp only [headerTail, bind_ok_iff] at ht
    rcases ht with ⟨cpu, _, count, _, bytes, _, ht⟩
    by_cases hb : 32 + bytes > data.size
    · rw [ite_eq_left hb] at ht; cases ht
    · rw [ite_eq_right hb] at ht
      cases ht
      exact ⟨rfl, by simpa using hb⟩
  simp only [parseHeader, bind_ok_iff] at h
  rcases h with ⟨magic, hm, h⟩
  split at h
  · simp only [ok_bind] at h
    have ⟨he, hb⟩ := tail (endian := .little) h
    exact ⟨.inl ⟨hm, he⟩, hb⟩
  · simp only [ok_bind] at h
    have ⟨he, hb⟩ := tail (endian := .big) h
    exact ⟨.inr ⟨hm, he⟩, hb⟩
  · simp only [error_bind] at h; cases h

theorem parseHeader_rejects_short {data : ByteArray} (h : data.size < 32) : (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header => have := (parseHeader_ok hp).2; omega

theorem parseHeader_rejects_magic {data : ByteArray}
    (h : IO.Reader.read data Endian.big 0 4 ≠ .ok 0xcffaedfe) (h' : IO.Reader.read data Endian.big 0 4 ≠ .ok 0xfeedfacf) :
    (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header =>
    rcases (parseHeader_ok hp).1 with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact absurd hm h
    · exact absurd hm h'

/-- An accepted segment command maps file bytes then zeros, and its sections fit in the command. -/
theorem parseSegment_ok {data : ByteArray} {endian : Endian} {offset commandSize : Nat} {segment : Segment}
    {region : MemRegion} {mapping : FileMapping} {sections : List Section}
    (h : parseSegment data endian offset commandSize = .ok (segment, region, mapping, sections)) :
    segment.addr = region.addr ∧ segment.size = region.size ∧ segment.readable = region.readable ∧
      segment.writable = region.writable ∧ segment.executable = region.executable ∧
      FileMapping.address mapping = segment.addr ∧
      Loaded region.data data (FileMapping.offset mapping) (FileMapping.size mapping) segment.size ∧
      72 + sections.length * 80 ≤ commandSize := by
  simp only [parseSegment] at h
  by_cases hc : commandSize < 72
  · rw [ite_eq_left hc] at h; cases h
  rw [ite_eq_right hc] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨name, _, address, _, memorySize, _, fileOffset, _, fileSize, _, protection, _, count, _, h⟩
  by_cases hs : 72 + count * 80 > commandSize
  · rw [ite_eq_left hs] at h; cases h
  rw [ite_eq_right hs] at h
  by_cases hm : fileSize > memorySize
  · rw [ite_eq_left hm] at h; cases h
  rw [ite_eq_right hm] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨file, hfile, parsed, hp, h⟩
  cases h
  have hl := loaded_of_slice (memorySize := memorySize) hfile (by omega)
  have hlen := (mapM_ok hp).1
  simp only [List.length_range] at hlen
  exact ⟨rfl, hl.1.symm, rfl, rfl, rfl, rfl, hl, by rw [hlen]; omega⟩

/-- One parsed segment command, with its region and file mapping. -/
def GoodEntry (data : ByteArray) (entry : Segment × MemRegion × FileMapping) : Prop :=
  entry.1.addr = entry.2.1.addr ∧ entry.1.size = entry.2.1.size ∧ FileMapping.address entry.2.2 = entry.1.addr ∧
    Loaded entry.2.1.data data (FileMapping.offset entry.2.2) (FileMapping.size entry.2.2) entry.1.size

/-- The parse state's parallel lists stay parallel and describe the same segments. -/
def StateInvariant (data : ByteArray) (state : ParseState) : Prop :=
  ∃ entries : List (Segment × MemRegion × FileMapping),
    ParseState.segments state = entries.map Prod.fst ∧ ParseState.regions state = entries.map (·.2.1) ∧
    ParseState.mappings state = entries.map (·.2.2) ∧ ∀ entry ∈ entries, GoodEntry data entry

/-- Each load command advances at least 8 bytes and stays inside the command region. -/
theorem parseCommands_ok {data : ByteArray} {header : Header} :
    ∀ {remaining offset final : Nat} {state result : ParseState},
      parseCommands data header offset remaining state = .ok (final, result) →
      StateInvariant data state →
      offset + 8 * remaining ≤ final ∧ (0 < remaining → final ≤ 32 + Header.commandBytes header) ∧
        StateInvariant data result
  | 0, offset, final, state, result, h, hi => by
    simp only [parseCommands] at h
    cases h
    exact ⟨by simp, by simp, hi⟩
  | n + 1, offset, final, state, result, h, hi => by
    simp only [parseCommands, bind_ok_iff] at h
    rcases h with ⟨command, _, commandSize, _, h⟩
    by_cases h8 : commandSize < 8
    · rw [ite_eq_left h8] at h; cases h
    rw [ite_eq_right h8] at h
    by_cases hr : offset + commandSize > 32 + Header.commandBytes header
    · rw [ite_eq_left hr] at h; cases h
    rw [ite_eq_right hr] at h
    have step : ∃ next, parseCommands data header (offset + commandSize) n next = .ok (final, result) ∧
        StateInvariant data next := by
      obtain ⟨entries, hseg, hreg, hmap, hgood⟩ := hi
      split at h
      · simp only [bind_ok_iff] at h
        rcases h with ⟨⟨segment, region, mapping, sections⟩, hp, _, he, h⟩
        cases he
        refine ⟨_, h, entries ++ [(segment, region, mapping)], ?_, ?_, ?_, ?_⟩
        · simp [hseg]
        · simp [hreg]
        · simp [hmap]
        · intro entry he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hgood entry he
          · have ⟨h1, h2, _, _, _, h3, h4, _⟩ := parseSegment_ok hp
            exact ⟨h1, h2, h3, h4⟩
      · split at h
        · simp only [error_bind] at h; cases h
        · simp only [bind_ok_iff] at h
          rcases h with ⟨entryOffset, _, _, he, h⟩
          cases he
          exact ⟨_, h, entries, hseg, hreg, hmap, hgood⟩
      · split at h
        · simp only [error_bind] at h; cases h
        · simp only [bind_ok_iff] at h
          rcases h with ⟨a, _, b, _, c, _, d, _, h⟩
          split at h
          · simp only [error_bind] at h; cases h
          · simp only [ok_bind] at h
            exact ⟨_, h, entries, hseg, hreg, hmap, hgood⟩
      · simp only [ok_bind] at h
        exact ⟨_, h, entries, hseg, hreg, hmap, hgood⟩
    obtain ⟨next, hn, hin⟩ := step
    have ⟨h1, h2, h3⟩ := parseCommands_ok hn hin
    refine ⟨by omega, fun _ => ?_, h3⟩
    cases n with
    | zero =>
      simp only [parseCommands] at hn
      cases hn
      omega
    | succ m => exact h2 (by omega)

/-- Everything `Macho.decode` promises: the file's bytes, a consistent segment map and a mapped entry point. -/
theorem decode_ok {data : ByteArray} {image : Image} (h : Macho.decode data = .ok image) :
    image.data = data ∧ image.addrWidth = 64 ∧
    ∃ header state, parseHeader data = .ok header ∧ image.endian = Header.endian header ∧
      ∃ entries : List (Segment × MemRegion × FileMapping), image.segments = entries.map Prod.fst ∧
        image.memory.entries = (entries.map (·.2.1)).reverse.map (fun region => (region, ())) ∧
        (∀ entry ∈ entries, GoodEntry data entry) ∧
        ParseState.mappings state = entries.map (·.2.2) ∧
        (ParseState.entryOffset state = none → image.entryPoint = 0) ∧
        (∀ entry, ParseState.entryOffset state = some entry →
          ∃ mapping ∈ ParseState.mappings state, FileMapping.offset mapping ≤ entry ∧
            entry < FileMapping.offset mapping + FileMapping.size mapping ∧
            image.entryPoint = FileMapping.address mapping + entry - FileMapping.offset mapping) := by
  simp only [Macho.decode, bind_ok_iff] at h
  rcases h with ⟨header, h1, ⟨final, state⟩, h2, h⟩
  have ⟨_, _, entries, hseg, hreg, hmap, hgood⟩ := parseCommands_ok h2
    ⟨[], rfl, rfl, rfl, by simp⟩
  by_cases hf : (final != 32 + Header.commandBytes header) = true
  · rw [ite_eq_left hf] at h; cases h
  rw [ite_eq_right hf] at h
  have hmem : (List.foldl (fun memory region => MemoryMap.add region () memory) ({} : MemoryMap Unit)
      (ParseState.regions state)).entries =
      (entries.map (·.2.1)).reverse.map (fun region => (region, ())) := by
    rw [Map.foldl_add_entries, hreg]
    exact List.append_nil _
  split at h
  · rename_i hn
    have hn : ParseState.entryOffset state = none := hn
    simp only [ok_bind, bind_ok_iff] at h
    rcases h with ⟨symbols, _, h⟩
    cases h
    exact ⟨rfl, rfl, header, state, h1, rfl, entries, hseg, hmem, hgood, hmap, (fun _ => rfl),
      (fun e hs => by rw [hn] at hs; cases hs)⟩
  · rename_i entryOffset hs
    have hs : ParseState.entryOffset state = some entryOffset := hs
    split at h
    · rename_i mapping hfind
      simp only [ok_bind, bind_ok_iff] at h
      rcases h with ⟨symbols, _, h⟩
      cases h
      have hm : mapping ∈ ParseState.mappings state := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      exact ⟨rfl, rfl, header, state, h1, rfl, entries, hseg, hmem, hgood, hmap,
        (fun h0 => by rw [hs] at h0; cases h0),
        (fun e he => by rw [hs] at he; cases he; exact ⟨mapping, hm, hp.1, hp.2, rfl⟩)⟩
    · simp only [error_bind] at h; cases h

theorem decode_rejects_short {data : ByteArray} (h : data.size < 32) : (Macho.decode data).isOk = false := by
  cases hd : Macho.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, _, _, _, hp, _⟩ := decode_ok hd
    have := parseHeader_rejects_short (data := data) h
    simp [hp, Except.isOk, Except.toBool] at this

/-- A symbol's section flags decide whether it is a function; a symbol in `NO_SECT` is never one. -/
theorem parseSymbol_section {data : ByteArray} {endian : Endian} {stringsOffset stringsSize offset number : Nat}
    {sections : List Section} {symbol : Symbol}
    (hs : IO.Reader.get8 data (offset + 5) = .ok number)
    (h : parseSymbol data endian stringsOffset stringsSize sections offset = .ok (some symbol)) :
    symbol.isFunction = (match sectionOfNumber sections number with
      | some sec => sec.flags &&& 0x00000400 != 0
      | none => false) := by
  simp only [parseSymbol, bind_ok_iff] at h
  rcases h with ⟨nameOffset, _, h⟩
  by_cases h0 : nameOffset = 0
  · rw [ite_eq_left h0] at h; cases h
  rw [ite_eq_right h0] at h
  by_cases hn : nameOffset ≥ stringsSize
  · rw [ite_eq_left hn] at h; cases h
  rw [ite_eq_right hn] at h
  simp only [bind_ok_iff, hs] at h
  rcases h with ⟨name, _, kind, _, index, hi, address, _, h⟩
  cases hi
  cases h
  rfl

theorem parseSymbol_no_section {data : ByteArray} {endian : Endian} {stringsOffset stringsSize offset : Nat}
    {sections : List Section} {symbol : Symbol}
    (hs : IO.Reader.get8 data (offset + 5) = .ok 0)
    (h : parseSymbol data endian stringsOffset stringsSize sections offset = .ok (some symbol)) :
    symbol.isFunction = false :=
  parseSymbol_section hs h

end MachoParser

/-! ## PE -/

namespace PeParser

open_private Bap.Image.Pe Bap.Image.Pe Header Header.mk Header.sectionOffset Header.sectionCount Header.imageBase
  Header.entryPoint Header.width optionalLayout parseHeader parseSection parseSections parseSymbol parseSymbols

open Reader

/-- A PE32 optional header (magic `0x10b`) has a 32-bit `ImageBase` at offset 28, past `BaseOfData`, and at least the 96
bytes of its fields before the data directories. A PE32+ one (magic `0x20b`) has a 64-bit one at offset 24 and at least
112 bytes. There is no other. -/
theorem optionalLayout_ok {data : ByteArray} {offset size width base : Nat}
    (h : optionalLayout data offset size = .ok (width, base)) :
    (IO.Reader.u16 data .little offset = .ok 0x10b ∧ width = 32 ∧ 96 ≤ size ∧
        IO.Reader.u32 data .little (offset + 28) = .ok base) ∨
      (IO.Reader.u16 data .little offset = .ok 0x20b ∧ width = 64 ∧ 112 ≤ size ∧
        IO.Reader.u64 data .little (offset + 24) = .ok base) := by
  simp only [optionalLayout, bind_ok_iff] at h
  rcases h with ⟨magic, hm, h⟩
  by_cases h1 : (magic == 0x10b) = true
  · rw [ite_eq_left h1] at h
    have hmagic : magic = 0x10b := by simpa using h1
    subst hmagic
    split at h
    · cases h
    · rename_i hs
      simp only [bind_ok_iff] at h
      rcases h with ⟨b, hb, h⟩
      cases h
      exact .inl ⟨hm, rfl, by omega, hb⟩
  · rw [ite_eq_right h1] at h
    by_cases h2 : (magic == 0x20b) = true
    · rw [ite_eq_left h2] at h
      have hmagic : magic = 0x20b := by simpa using h2
      subst hmagic
      split at h
      · cases h
      · rename_i hs
        simp only [bind_ok_iff] at h
        rcases h with ⟨b, hb, h⟩
        cases h
        exact .inr ⟨hm, rfl, by omega, hb⟩
    · rw [ite_eq_right h2] at h
      cases h

/-- Any other magic is rejected. -/
theorem optionalLayout_rejects {data : ByteArray} {offset size magic : Nat}
    (hm : IO.Reader.u16 data .little offset = .ok magic) (h1 : magic ≠ 0x10b) (h2 : magic ≠ 0x20b) :
    (optionalLayout data offset size).isOk = false := by
  cases hl : optionalLayout data offset size with
  | error e => rfl
  | ok v =>
    rcases optionalLayout_ok (width := v.1) (base := v.2) hl with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hm] at h <;> cases h <;> simp_all

/-- An accepted PE header has the DOS and PE signatures, a known optional header and an in-bounds section table, and its
width and image base are those of the optional header's kind. -/
theorem parseHeader_ok {data : ByteArray} {header : Header} (h : parseHeader data = .ok header) :
    IO.Reader.u16 data .little 0 = .ok 0x5a4d ∧ 64 ≤ data.size ∧
      ∃ peOffset, IO.Reader.u32 data .little 60 = .ok peOffset ∧
        IO.Reader.u32 data .little peOffset = .ok 0x4550 ∧
        ((IO.Reader.u16 data .little (peOffset + 24) = .ok 0x10b ∧ Header.width header = 32 ∧
            IO.Reader.u32 data .little (peOffset + 24 + 28) = .ok (Header.imageBase header)) ∨
          (IO.Reader.u16 data .little (peOffset + 24) = .ok 0x20b ∧ Header.width header = 64 ∧
            IO.Reader.u64 data .little (peOffset + 24 + 24) = .ok (Header.imageBase header))) ∧
        Header.sectionOffset header + Header.sectionCount header * 40 ≤ data.size ∧
        ∃ entryRva, IO.Reader.u32 data .little (peOffset + 24 + 16) = .ok entryRva ∧
          Header.entryPoint header = Header.imageBase header + entryRva := by
  simp only [parseHeader, bind_ok_iff] at h
  rcases h with ⟨dos, hd, h⟩
  by_cases hd1 : (dos != 0x5a4d) = true
  · rw [ite_eq_left hd1] at h; cases h
  rw [ite_eq_right hd1] at h
  have hdos : dos = 0x5a4d := by simpa using hd1
  subst hdos
  simp only [bind_ok_iff] at h
  rcases h with ⟨peOffset, hpe, signature, hsig, h⟩
  by_cases hs1 : (signature != 0x4550) = true
  · rw [ite_eq_left hs1] at h; cases h
  rw [ite_eq_right hs1] at h
  have hsg : signature = 0x4550 := by simpa using hs1
  subst hsg
  simp only [bind_ok_iff] at h
  rcases h with ⟨machine, _, count, _, symOff, _, symCount, _, optSize, _, ⟨width, base⟩, hopt, h⟩
  dsimp only at h
  rcases h with ⟨entryRva, hentry, h⟩
  by_cases hsec : peOffset + 4 + 20 + optSize + count * 40 > data.size
  · rw [ite_eq_left hsec] at h; cases h
  rw [ite_eq_right hsec] at h
  split at h
  · cases h
  · cases h
    have hbound := read_bound hpe
    refine ⟨hd, by omega, peOffset, hpe, hsig, ?_, by simpa using hsec, entryRva, hentry, rfl⟩
    rcases optionalLayout_ok hopt with ⟨h1, h2, _, h3⟩ | ⟨h1, h2, _, h3⟩
    · exact .inl ⟨h1, h2, h3⟩
    · exact .inr ⟨h1, h2, h3⟩

theorem parseHeader_rejects_short {data : ByteArray} (h : data.size < 64) : (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header => have := (parseHeader_ok hp).2.1; omega

theorem parseHeader_rejects_signature {data : ByteArray} (h : IO.Reader.u16 data .little 0 ≠ .ok 0x5a4d) :
    (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header => exact absurd (parseHeader_ok hp).1 h

/-- A PE section is mapped from the file at `rawOffset`, zero-filled to `max virtualSize rawSize`. -/
theorem parseSection_ok {data : ByteArray} {imageBase offset : Nat} {sec : Section} {segment : Segment}
    {region : MemRegion} (h : parseSection data imageBase offset = .ok (sec, segment, region)) :
    segment.addr = region.addr ∧ segment.size = region.size ∧ sec.addr = region.addr ∧
      segment.readable = region.readable ∧ segment.writable = region.writable ∧
      segment.executable = region.executable ∧ segment.name = sec.name ∧
      imageBase ≤ region.addr ∧ sec.size ≤ segment.size ∧
      ∃ rawSize, Loaded region.data data sec.offset rawSize segment.size := by
  simp only [parseSection, bind_ok_iff] at h
  rcases h with ⟨name, _, virtualSize, _, rva, _, rawSize, _, rawOffset, _, flags, _, file, hfile, h⟩
  cases h
  have hl := loaded_of_slice (memorySize := max virtualSize rawSize) hfile (Nat.le_max_right ..)
  exact ⟨rfl, hl.1.symm, rfl, rfl, rfl, rfl, rfl, by simp, Nat.le_max_left .., rawSize, hl⟩

/-- The three lists `parseSections` returns are parallel, and one per declared section. -/
theorem parseSections_ok {data : ByteArray} {header : Header} {sections : List Section} {segments : List Segment}
    {regions : List MemRegion} (h : parseSections data header = .ok (sections, segments, regions)) :
    sections.length = Header.sectionCount header ∧ segments.length = Header.sectionCount header ∧
      ∃ entries : List (Section × Segment × MemRegion), sections = entries.map Prod.fst ∧
        segments = entries.map (·.2.1) ∧ regions = entries.map (·.2.2) ∧
        ∀ entry ∈ entries, entry.2.1.addr = entry.2.2.addr ∧ entry.2.1.size = entry.2.2.size ∧
          ∃ rawSize, Loaded entry.2.2.data data entry.1.offset rawSize entry.2.1.size := by
  simp only [parseSections, bind_ok_iff] at h
  rcases h with ⟨entries, he, h⟩
  have ⟨hl, hi⟩ := mapM_ok he
  simp only [List.length_range] at hl
  cases h
  refine ⟨by simpa using hl, by simpa using hl, entries, rfl, rfl, rfl, ?_⟩
  intro entry hm
  have ⟨i, hi1, hi2⟩ := List.getElem_of_mem hm
  have := hi i hi1 (by simpa using hl ▸ hi1)
  rw [hi2] at this
  obtain ⟨a, b, c⟩ := entry
  have ⟨h1, h2, _, _, _, _, _, _, _, h3⟩ := parseSection_ok this
  exact ⟨h1, h2, h3⟩

/-- Auxiliary records are skipped: symbols only accumulate, by at most the declared number. -/
theorem parseSymbols_ok {data : ByteArray} {header : Header} {sections : List Section} :
    ∀ {fuel index remaining : Nat} {symbols result : List Symbol}, remaining ≤ fuel →
      parseSymbols data header sections index remaining symbols = .ok result →
      ∃ added, result = symbols ++ added ∧ added.length ≤ remaining
  | _, index, 0, symbols, result, _, h => by
    rw [parseSymbols] at h
    cases h
    exact ⟨[], by simp, by simp⟩
  | 0, _, _ + 1, _, _, hf, _ => by omega
  | fuel + 1, index, n + 1, symbols, result, hf, h => by
    rw [parseSymbols] at h
    simp only [bind_ok_iff] at h
    rcases h with ⟨symbol, _, aux, _, h⟩
    by_cases ha : aux > n
    · rw [ite_eq_left ha] at h; cases h
    rw [ite_eq_right ha] at h
    have ⟨added, he, hl⟩ := parseSymbols_ok (fuel := fuel) (by omega) h
    exact ⟨symbol :: added, by simpa using he, by simp; omega⟩

/-- Everything `Pe.decode` promises about an accepted file. -/
theorem decode_ok {data : ByteArray} {image : Image} (h : Pe.decode data = .ok image) :
    ∃ header, parseHeader data = .ok header ∧ image.data = data ∧ image.addrWidth = Header.width header ∧
      image.endian = .little ∧ image.entryPoint = Header.entryPoint header ∧
      image.sections.length = Header.sectionCount header ∧ image.segments.length = Header.sectionCount header ∧
      ∃ entries : List (Section × Segment × MemRegion), image.segments = entries.map (·.2.1) ∧
        image.memory.entries = (entries.map (·.2.2)).reverse.map (fun region => (region, ())) ∧
        ∀ entry ∈ entries, entry.2.1.addr = entry.2.2.addr ∧ entry.2.1.size = entry.2.2.size := by
  simp only [Pe.decode, bind_ok_iff] at h
  rcases h with ⟨header, h1, ⟨sections, segments, regions⟩, h2, symbols, _, h⟩
  cases h
  have ⟨hs, hg, entries, _, hseg, hreg, hp⟩ := parseSections_ok h2
  refine ⟨header, h1, rfl, rfl, rfl, rfl, hs, hg, entries, hseg, ?_, fun entry he => ⟨(hp entry he).1, (hp entry he).2.1⟩⟩
  rw [Map.foldl_add_entries, hreg]
  exact List.append_nil _

theorem decode_rejects_short {data : ByteArray} (h : data.size < 64) : (Pe.decode data).isOk = false := by
  cases hd : Pe.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp, _⟩ := decode_ok hd
    have := parseHeader_rejects_short (data := data) h
    simp [hp, Except.isOk, Except.toBool] at this

/-- A PE32 file decodes to a 32-bit image, whose image base comes from its 32-bit field, and a PE32+ one to a 64-bit
image. The rest is what `decode_ok` says of both. -/
theorem decode_width {data : ByteArray} {image : Image} (h : Pe.decode data = .ok image) :
    ∃ peOffset, IO.Reader.u32 data .little 60 = .ok peOffset ∧
      ((IO.Reader.u16 data .little (peOffset + 24) = .ok 0x10b ∧ image.addrWidth = 32) ∨
        (IO.Reader.u16 data .little (peOffset + 24) = .ok 0x20b ∧ image.addrWidth = 64)) := by
  have ⟨header, hp, _, hw, _⟩ := decode_ok h
  have ⟨_, _, peOffset, hpe, _, hk, _⟩ := parseHeader_ok hp
  refine ⟨peOffset, hpe, ?_⟩
  rcases hk with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · exact .inl ⟨h1, hw.trans h2⟩
  · exact .inr ⟨h1, hw.trans h2⟩

/-- A symbol in section `number + 1` is relative to it; a symbol with a reserved or missing number is not. -/
theorem parseSymbol_address {data : ByteArray} {header : Header} {sections : List Section}
    {offset value number : Nat} {symbol : Symbol}
    (hv : IO.Reader.u32 data .little (offset + 8) = .ok value)
    (hs : IO.Reader.u16 data .little (offset + 12) = .ok number)
    (h : parseSymbol data header sections offset = .ok symbol) :
    symbol.addr = (match sectionOfNumber sections number with
      | some sec => sec.addr + value
      | none => value) := by
  simp only [parseSymbol, bind_ok_iff, hv, hs] at h
  rcases h with ⟨name, _, _, he1, _, he2, ty, _, storage, _, h⟩
  cases he1
  cases he2
  cases h
  rfl

/-- Section number 0 is `IMAGE_SYM_UNDEFINED`: its symbol keeps its value and is not a function. -/
theorem parseSymbol_undefined {data : ByteArray} {header : Header} {sections : List Section}
    {offset value : Nat} {symbol : Symbol}
    (hv : IO.Reader.u32 data .little (offset + 8) = .ok value)
    (hs : IO.Reader.u16 data .little (offset + 12) = .ok 0)
    (h : parseSymbol data header sections offset = .ok symbol) :
    symbol.addr = value ∧ symbol.isFunction = false := by
  simp only [parseSymbol, bind_ok_iff, hv, hs] at h
  rcases h with ⟨name, _, _, he1, _, he2, ty, _, storage, _, h⟩
  cases he1
  cases he2
  cases h
  exact ⟨rfl, rfl⟩

end PeParser

/-! ## COFF -/

namespace CoffParser

open_private Bap.Image.Coff Bap.Image.Coff Header Header.mk Header.machine Header.sectionOffset Header.sectionCount
  ObjectSection ObjectSection.mk ObjectSection.info ObjectSection.segment ObjectSection.region
  ObjectSection.relocationCount ObjectSection.relocationOffset
  parseHeader parseSection parseSections parseSymbol parseSymbols writeNat applyRelocation applyRelocations architecture
  isMapped isDiscarded sectionAlignment placeObject placeObjects placeUndefined isUndefined zeroRegion

open Reader

/-- COFF has no magic: acceptance only means the section table fits after the fixed header. -/
theorem parseHeader_ok {data : ByteArray} {header : Header} (h : parseHeader data = .ok header) :
    20 ≤ data.size ∧ 20 ≤ Header.sectionOffset header ∧
      Header.sectionOffset header + Header.sectionCount header * 40 ≤ data.size ∧
      IO.Reader.u16 data .little 0 = .ok (Header.machine header) := by
  simp only [parseHeader, bind_ok_iff] at h
  rcases h with ⟨machine, hm, count, _, symOff, _, symCount, _, optSize, _, h⟩
  by_cases hsec : 20 + optSize + count * 40 > data.size
  · rw [ite_eq_left hsec] at h; cases h
  rw [ite_eq_right hsec] at h
  split at h
  · cases h
  · cases h
    exact ⟨by omega, by simp [*], by simpa using hsec, hm⟩

theorem parseHeader_rejects_short {data : ByteArray} (h : data.size < 20) : (parseHeader data).isOk = false := by
  cases hp : parseHeader data with
  | error e => rfl
  | ok header => have := (parseHeader_ok hp).1; omega

/-- An object section's region and segment agree. It holds file bytes then zeros; an uninitialized section, or one
with no raw data pointer, takes no bytes from the file. -/
theorem parseSection_ok {data : ByteArray} {header : Header} {offset : Nat} {object : ObjectSection}
    (h : parseSection data header offset = .ok object) :
    (ObjectSection.segment object).addr = (ObjectSection.region object).addr ∧
      (ObjectSection.info object).addr = (ObjectSection.region object).addr ∧
      (ObjectSection.segment object).size = (ObjectSection.region object).size ∧
      (ObjectSection.info object).size ≤ (ObjectSection.segment object).size ∧
      ∃ fileSize, Loaded (ObjectSection.region object).data data (ObjectSection.info object).offset
          fileSize (ObjectSection.segment object).size ∧
        ((ObjectSection.info object).offset = 0 → fileSize = 0) ∧
        ((ObjectSection.info object).flags &&& 0x80 != 0 → fileSize = 0) := by
  simp only [parseSection, bind_ok_iff] at h
  rcases h with ⟨name, _, virtualSize, _, address, _, rawSize, _, rawOffset, _, relocOffset, _, relocCount, _,
    flags, _, file, hfile, h⟩
  by_cases hr : relocOffset + relocCount * 10 > data.size
  · rw [ite_eq_left hr] at h; cases h
  rw [ite_eq_right hr] at h
  cases h
  have hfit : (if rawOffset = 0 || flags &&& 0x80 != 0 then 0 else rawSize) ≤
      max (if virtualSize = 0 then rawSize else virtualSize) rawSize := by
    split
    · omega
    · exact Nat.le_max_right ..
  have hl := loaded_of_slice hfile hfit
  refine ⟨rfl, rfl, hl.1.symm, Nat.le_max_left .., _, hl, ?_, ?_⟩
  · intro h0
    have h0 : rawOffset = 0 := h0
    simp [h0]
  · intro h0
    have h0 : (flags &&& 0x80 != 0) = true := h0
    simp [h0]

/-- The segment and region of an uninitialized section read as zero for their whole size. -/
theorem parseSection_uninitialized_reads_zero {data : ByteArray} {header : Header} {offset i : Nat}
    {object : ObjectSection} (h : parseSection data header offset = .ok object)
    (hf : (ObjectSection.info object).flags &&& 0x80 != 0) (hi : i < (ObjectSection.segment object).size) :
    (ObjectSection.region object).readByte ((ObjectSection.region object).addr + i) = some 0 := by
  obtain ⟨_, _, _, _, fileSize, hl, _, hz⟩ := parseSection_ok h
  exact hl.readByte_zero (by rw [hz hf]; omega) hi

theorem symbols_ok {data : ByteArray} {header : Header} {sections : List Section} :
    ∀ {fuel index remaining : Nat} {symbols result : List (Nat × Symbol)}, remaining ≤ fuel →
      parseSymbols data header sections index remaining symbols = .ok result →
      ∃ added, result = symbols ++ added ∧ added.length ≤ remaining ∧ ∀ entry ∈ added, index ≤ entry.1
  | _, index, 0, symbols, result, _, h => by
    rw [parseSymbols] at h
    cases h
    exact ⟨[], by simp, by simp, by simp⟩
  | 0, _, _ + 1, _, _, hf, _ => by omega
  | fuel + 1, index, n + 1, symbols, result, hf, h => by
    rw [parseSymbols] at h
    simp only [bind_ok_iff] at h
    rcases h with ⟨symbol, _, aux, _, h⟩
    by_cases ha : aux > n
    · rw [ite_eq_left ha] at h; cases h
    rw [ite_eq_right ha] at h
    have ⟨added, he, hl, hi⟩ := symbols_ok (fuel := fuel) (by omega) h
    refine ⟨(index, symbol) :: added, by simpa using he, by simp; omega, ?_⟩
    intro entry hm
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Nat.le_refl _
    · have := hi entry hm
      omega

/-! ### Relocation writes -/

theorem get!_set! (bytes : ByteArray) (i j : Nat) (value : UInt8) (hi : i < bytes.size) :
    (bytes.set! i value).get! j = if i = j then value else bytes.get! j := by
  cases bytes with
  | mk array =>
    have hi : i < array.size := hi
    show (array.setIfInBounds i value)[j]! = if i = j then value else array[j]!
    by_cases hj : j < array.size
    · have hj' : j < (array.setIfInBounds i value).size := by simpa using hj
      rw [getElem!_pos (array.setIfInBounds i value) j hj', getElem!_pos array j hj,
        Array.getElem_setIfInBounds hj]
    · have hne : ¬ i = j := by omega
      rw [ite_eq_right hne, getElem!_neg (array.setIfInBounds i value) j (by simpa using hj),
        getElem!_neg array j hj]

theorem size_set! (bytes : ByteArray) (i : Nat) (value : UInt8) : (bytes.set! i value).size = bytes.size := by
  cases bytes
  show (Array.setIfInBounds _ _ _).size = _
  simp
  rfl

private def writes (data : ByteArray) (offset value : Nat) (k : Nat) : ByteArray :=
  (List.range k).foldl (init := data) fun result index =>
    result.set! (offset + index) (UInt8.ofNat (value / 256 ^ index % 256))

private theorem writes_succ (data : ByteArray) (offset value k : Nat) :
    writes data offset value (k + 1) =
      (writes data offset value k).set! (offset + k) (UInt8.ofNat (value / 256 ^ k % 256)) := by
  simp [writes, List.range_succ, List.foldl_append]

private theorem writes_spec {data : ByteArray} {offset value : Nat} :
    ∀ k, offset + k ≤ data.size →
      (writes data offset value k).size = data.size ∧
      (∀ j, j < offset ∨ offset + k ≤ j → (writes data offset value k).get! j = data.get! j) ∧
      ∀ i, i < k → (writes data offset value k).get! (offset + i) = UInt8.ofNat (value / 256 ^ i % 256)
  | 0, _ => ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  | k + 1, hb => by
    have ⟨hs, hf, hw⟩ := writes_spec (data := data) (offset := offset) (value := value) k (by omega)
    rw [writes_succ]
    have hlt : offset + k < (writes data offset value k).size := by omega
    refine ⟨by rw [size_set!, hs], ?_, ?_⟩
    · intro j hj
      rw [get!_set! _ _ _ _ hlt, ite_eq_right (by omega), hf j (by omega)]
    · intro i hi
      rw [get!_set! _ _ _ _ hlt]
      by_cases hik : i = k
      · subst hik; simp
      · rw [ite_eq_right (by omega), hw i (by omega)]

/-- A relocation write changes exactly its `size` bytes, to the little-endian digits of the value. -/
theorem writeNat_ok {data out : ByteArray} {offset size value : Nat}
    (h : writeNat data offset size value = .ok out) :
    offset + size ≤ data.size ∧ out.size = data.size ∧
      (∀ j, j < offset ∨ offset + size ≤ j → out.get! j = data.get! j) ∧
      ∀ i, i < size → (out.get! (offset + i)).toNat = value / 256 ^ i % 256 := by
  simp only [writeNat] at h
  by_cases hb : offset + size > data.size
  · rw [ite_eq_left hb] at h; cases h
  rw [ite_eq_right hb] at h
  have ho : out = writes data offset value size := (Except.ok.inj h).symm
  subst ho
  have ⟨hs, hf, hw⟩ := writes_spec (data := data) (offset := offset) (value := value) size (by omega)
  refine ⟨by omega, hs, hf, ?_⟩
  intro i hi
  rw [hw i hi, UInt8.toNat_ofNat']
  have : value / 256 ^ i % 256 < 256 := Nat.mod_lt _ (by decide)
  exact Nat.mod_eq_of_lt this

theorem writeNat_rejects {data : ByteArray} {offset size value : Nat} (h : data.size < offset + size) :
    (writeNat data offset size value).isOk = false := by
  simp only [writeNat]
  rw [ite_eq_left h]
  rfl

/-- The target architecture table is total, and its widths are the two supported pointer sizes. -/
theorem architecture_width (machine : Nat) :
    (architecture machine).2 = 32 ∨ (architecture machine).2 = 64 := by
  unfold architecture
  split <;> simp

/-! ### Relocations -/

private theorem resolves_mod (s a q m : Nat) (hm : 0 < m) :
    ((s % m + a % m + m - q % m) % m + q) % m = (s + a) % m := by
  have hq : q % m < m := Nat.mod_lt _ hm
  have hq' : q = m * (q / m) + q % m := (Nat.div_add_mod q m).symm
  have hsum : s % m + a % m + m - q % m + q = (s % m + a % m) + m * (q / m + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [Nat.mod_add_mod, hsum, Nat.add_mul_mod_self_left, Nat.add_mod s a]

/-- A displacement, added to the address `extra` bytes past the place, reaches the symbol plus the addend
(`S + A - (P + extra)`, as lld-link computes it). -/
theorem relocationValue_relative (extra symbol place addend number sectionAddr : Nat) :
    let value := (Coff.relocationValue (.relative extra) symbol place addend number sectionAddr).1
    value < 2 ^ 32 ∧ (value + (place + extra)) % 2 ^ 32 = (symbol + addend) % 2 ^ 32 := by
  exact ⟨Nat.mod_lt _ (by decide), resolves_mod _ _ _ _ (by decide)⟩

/-- `IMAGE_REL_*_SECREL`: the offset of the symbol from the start of its section, plus the addend. -/
theorem relocationValue_sectionRelative (symbol place addend number sectionAddr : Nat) :
    Coff.relocationValue .sectionRelative symbol place addend number sectionAddr =
      ((symbol - sectionAddr + addend) % 2 ^ 32, 4) := rfl

/-- `IMAGE_REL_*_SECTION`: the number of the symbol's section, plus the addend. -/
theorem relocationValue_section (symbol place addend number sectionAddr : Nat) :
    Coff.relocationValue .section symbol place addend number sectionAddr = ((number + addend) % 2 ^ 16, 2) := rfl

theorem relocationValue_absolute (size symbol place addend number sectionAddr : Nat) :
    Coff.relocationValue (.absolute size) symbol place addend number sectionAddr =
      ((symbol + addend) % 2 ^ (size * 8), size) := rfl

/-- The `IMAGE_REL_*` numbers against `llvm/BinaryFormat/COFF.h`. -/
theorem relocationKind_numbers :
    Coff.relocationKind 0x8664 1 = some (.absolute 8) ∧ Coff.relocationKind 0x8664 2 = some (.absolute 4) ∧
      Coff.relocationKind 0x8664 3 = some (.absolute 4) ∧ Coff.relocationKind 0x8664 4 = some (.relative 4) ∧
      Coff.relocationKind 0x8664 9 = some (.relative 9) ∧ Coff.relocationKind 0x8664 0xa = some .section ∧
      Coff.relocationKind 0x8664 0xb = some .sectionRelative ∧ Coff.relocationKind 0x014c 6 = some (.absolute 4) ∧
      Coff.relocationKind 0x014c 7 = some (.absolute 4) ∧ Coff.relocationKind 0x014c 0xa = some .section ∧
      Coff.relocationKind 0x014c 0xb = some .sectionRelative ∧ Coff.relocationKind 0x014c 0x14 = some (.relative 4) ∧
      Coff.relocationKind 0xaa64 3 = some (.arm64Branch 0 26) ∧ Coff.relocationKind 0x01c4 3 = none := by
  decide

/-- A successful relocation writes what `relocationValue` computes over the bytes at the place. -/
theorem applyRelocation_ok {data : ByteArray} {header : Header} {sections : List Section}
    {symbols : List (Nat × Symbol)} {object : ObjectSection} {region out : MemRegion} {index : Nat}
    (h : applyRelocation data header sections symbols object region index = .ok out) :
    out.addr = region.addr ∧ out.size = region.size ∧
      ∃ rva number kind, ∃ symbol : Symbol, ∃ sectionNumber sectionAddr addend,
        IO.Reader.u16 data .little (ObjectSection.relocationOffset object + index * 10 + 8) = .ok number ∧
        IO.Reader.u32 data .little (ObjectSection.relocationOffset object + index * 10) = .ok rva ∧
        Coff.relocationKind (Header.machine header) number = some kind ∧
        ∃ flags, let address := Coff.withThumbBit (Header.machine header) kind flags symbol.addr
        writeNat region.data rva
          (Coff.relocationValue kind address ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr).2
          (Coff.relocationValue kind address ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr).1 =
          .ok out.data := by
  simp only [applyRelocation, bind_ok_iff] at h
  rcases h with ⟨rva, hrva, symbolIndex, _, number, hnumber, h⟩
  split at h
  · cases h
  rename_i kind hkind
  split at h
  · cases h
  rename_i symbol _
  simp only [bind_ok_iff] at h
  rcases h with ⟨sectionNumber, _, addend, _, h⟩
  generalize hs : Coff.relocationValue kind _ _ addend sectionNumber _ = pair at h
  obtain ⟨value, size⟩ := pair
  rcases h with ⟨bytes, hw, h⟩
  cases h
  have ⟨sectionAddr, flags, hs'⟩ : ∃ sectionAddr flags, Coff.relocationValue kind
      (Coff.withThumbBit (Header.machine header) kind flags symbol.addr)
      ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr = (value, size) := ⟨_, _, hs⟩
  refine ⟨rfl, (writeNat_ok hw).2.1, rva, number, kind, symbol, sectionNumber, sectionAddr, addend, hnumber, hrva,
    hkind, flags, ?_⟩
  simp only
  rw [hs']
  exact hw

private def rel32Input : ByteArray := ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0, 4, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
/-- A `call` at 0 (`e8 rel32`, field at `P = 1`) to the instruction after it (`S = 5`) gets displacement 0. -/
theorem rel32_call_next_instruction :
    let object := ObjectSection.mk ⟨".text", 0, 0, 5, 0, 0⟩ ⟨".text", 0, 5, true, false, true⟩
      ⟨0, ByteArray.mk #[0xe8, 0, 0, 0, 0], true, false, true⟩ 0 1
    (applyRelocation rel32Input (Header.mk 0x8664 1 0 10 1 0) [] [(0, ⟨"f", 5, 0, true, false⟩)] object
      (ObjectSection.region object) 0).toOption.map (fun region => (region.data.get! 1).toNat) = some 0 := by
  rfl

/-- Relocating a section keeps its metadata, the region's address and size, and adds at most an error a relocation. -/
theorem applyRelocations_frame {data : ByteArray} {header : Header} {sections : List Section}
    {symbols : List (Nat × Symbol)} (object : ObjectSection) :
    let (out, errors) := applyRelocations data header sections symbols object
    ObjectSection.segment out = ObjectSection.segment object ∧ ObjectSection.info out = ObjectSection.info object ∧
      (ObjectSection.region out).addr = (ObjectSection.region object).addr ∧
      (ObjectSection.region out).size = (ObjectSection.region object).size ∧
      errors.length ≤ ObjectSection.relocationCount object := by
  have fold : ∀ (indices : List Nat) (region : MemRegion) (errors : List String),
      let result := indices.foldl (init := (region, errors)) fun x index =>
        match applyRelocation data header sections symbols object x.1 index with
        | .ok next => (next, x.2)
        | .error error => (x.1, error :: x.2)
      result.1.addr = region.addr ∧ result.1.size = region.size ∧ result.2.length ≤ errors.length + indices.length := by
    intro indices
    induction indices with
    | nil => intro region errors; exact ⟨rfl, rfl, by simp⟩
    | cons index rest ih =>
      intro region errors
      simp only [List.foldl_cons]
      cases hr : applyRelocation data header sections symbols object region index with
      | ok next =>
        have ⟨a1, s1, _⟩ := applyRelocation_ok hr
        have ⟨a2, s2, l2⟩ := ih next errors
        simp only
        refine ⟨a2.trans a1, s2.trans s1, ?_⟩
        simp only [List.length_cons] at l2 ⊢
        omega
      | error error =>
        have ⟨a2, s2, l2⟩ := ih region (error :: errors)
        simp only
        refine ⟨a2, s2, ?_⟩
        simp only [List.length_cons] at l2 ⊢
        omega
  have ⟨a, s, l⟩ := fold (List.range (ObjectSection.relocationCount object)) (ObjectSection.region object) []
  simp only [applyRelocations]
  rw [List.length_range, List.length_nil, Nat.zero_add] at l
  exact ⟨trivial, trivial, a, s, by rw [List.length_reverse]; exact l⟩

/-! ### Layout -/

/-- A section's segment and region describe the same memory. -/
def GoodObject (object : ObjectSection) : Prop :=
  (ObjectSection.segment object).addr = (ObjectSection.region object).addr ∧
    (ObjectSection.segment object).size = (ObjectSection.region object).size

theorem placeObject_good {cursor : Nat} {object : ObjectSection} (h : GoodObject object) :
    GoodObject (placeObject cursor object).1 := by
  unfold placeObject
  split
  · exact ⟨rfl, h.2⟩
  · exact h

theorem placeObject_flags (cursor : Nat) (object : ObjectSection) :
    (ObjectSection.info (placeObject cursor object).1).flags = (ObjectSection.info object).flags ∧
      (ObjectSection.segment (placeObject cursor object).1).size = (ObjectSection.segment object).size := by
  unfold placeObject
  split <;> exact ⟨rfl, rfl⟩

/-- A mapped section goes at or after the cursor, at its alignment, and the cursor moves past it. -/
theorem placeObject_mapped {cursor : Nat} {object : ObjectSection} (h : isMapped object = true) :
    let placed := (placeObject cursor object).1
    cursor ≤ (ObjectSection.info placed).addr ∧ (ObjectSection.segment placed).addr = (ObjectSection.info placed).addr ∧
      (placeObject cursor object).2 = (ObjectSection.info placed).addr + (ObjectSection.segment object).size := by
  simp only [placeObject, h, ↓reduceIte]
  refine ⟨?_, trivial, trivial⟩
  show cursor ≤ alignUp _ _
  have hle : max cursor (ObjectSection.info object).addr ≤
      alignUp (max cursor (ObjectSection.info object).addr) (sectionAlignment (ObjectSection.info object).flags) := by
    unfold alignUp
    split
    · exact Nat.le_refl _
    · rename_i ha
      have hpos : 0 < sectionAlignment (ObjectSection.info object).flags := by omega
      generalize sectionAlignment (ObjectSection.info object).flags = n at *
      generalize max cursor (ObjectSection.info object).addr = v at *
      have hdiv := Nat.div_add_mod (v + n - 1) n
      have hmod := Nat.mod_lt (v + n - 1) hpos
      have hcomm : (v + n - 1) / n * n = n * ((v + n - 1) / n) := Nat.mul_comm ..
      omega
  have : cursor ≤ max cursor (ObjectSection.info object).addr := Nat.le_max_left ..
  omega

theorem placeObject_cursor (cursor : Nat) (object : ObjectSection) : cursor ≤ (placeObject cursor object).2 := by
  by_cases h : isMapped object = true
  · have ⟨h1, _, h3⟩ := placeObject_mapped (cursor := cursor) h
    omega
  · simp [placeObject, h]

private theorem placeObjects_after :
    ∀ (objects : List ObjectSection) (cursor : Nat) (placed : ObjectSection), placed ∈ placeObjects cursor objects →
      isMapped placed = true → cursor ≤ (ObjectSection.segment placed).addr
  | [], _, _, h, _ => by simp [placeObjects] at h
  | object :: rest, cursor, placed, h, hm => by
    simp only [placeObjects, List.mem_cons] at h
    rcases h with rfl | h
    · have hflags := (placeObject_flags cursor object).1
      have hmapped : isMapped object = true := by
        simp only [isMapped] at hm ⊢
        rw [hflags] at hm
        exact hm
      have ⟨h1, h2, _⟩ := placeObject_mapped (cursor := cursor) hmapped
      rw [h2]
      exact h1
    · have := placeObjects_after rest _ placed h hm
      have := placeObject_cursor cursor object
      omega

/-- The sections of an object are laid out one after the other: no two mapped sections overlap. -/
theorem placeObjects_disjoint :
    ∀ (objects : List ObjectSection) (cursor : Nat),
      (placeObjects cursor objects).Pairwise fun left right =>
        isMapped left = true → isMapped right = true →
          (ObjectSection.segment left).addr + (ObjectSection.segment left).size ≤ (ObjectSection.segment right).addr
  | [], _ => by simp [placeObjects]
  | object :: rest, cursor => by
    simp only [placeObjects, List.pairwise_cons]
    refine ⟨?_, placeObjects_disjoint rest _⟩
    intro right hr hl hrm
    have hflags := (placeObject_flags cursor object).1
    have hmapped : isMapped object = true := by
      simp only [isMapped] at hl ⊢
      rw [hflags] at hl
      exact hl
    have ⟨_, ha, hc⟩ := placeObject_mapped (cursor := cursor) hmapped
    have hafter := placeObjects_after rest _ right hr hrm
    have hsize := (placeObject_flags cursor object).2
    rw [hsize, ha]
    omega

/-! ### Symbols -/

/-- A symbol in section `number + 1` is relative to it; a symbol with a reserved or missing number is not. -/
theorem parseSymbol_address {data : ByteArray} {header : Header} {sections : List Section}
    {offset value number : Nat} {symbol : Symbol}
    (hv : IO.Reader.u32 data .little (offset + 8) = .ok value)
    (hs : IO.Reader.u16 data .little (offset + 12) = .ok number)
    (h : parseSymbol data header sections offset = .ok symbol) :
    symbol.addr = (match sectionOfNumber sections number with
      | some sec => sec.addr + value
      | none => value) := by
  simp only [parseSymbol, bind_ok_iff, hv, hs] at h
  rcases h with ⟨name, _, _, he1, _, he2, ty, _, storage, _, h⟩
  cases he1
  cases he2
  cases h
  rfl

/-- Section number 0 is `IMAGE_SYM_UNDEFINED`: its symbol keeps its value and is not a function. -/
theorem parseSymbol_undefined {data : ByteArray} {header : Header} {sections : List Section}
    {offset value : Nat} {symbol : Symbol}
    (hv : IO.Reader.u32 data .little (offset + 8) = .ok value)
    (hs : IO.Reader.u16 data .little (offset + 12) = .ok 0)
    (h : parseSymbol data header sections offset = .ok symbol) :
    symbol.addr = value ∧ symbol.isFunction = false := by
  simp only [parseSymbol, bind_ok_iff, hv, hs] at h
  rcases h with ⟨name, _, _, he1, _, he2, ty, _, storage, _, h⟩
  cases he1
  cases he2
  cases h
  exact ⟨rfl, rfl⟩

theorem placeObjects_good : ∀ {objects : List ObjectSection} {cursor : Nat}, (∀ object ∈ objects, GoodObject object) →
    ∀ object ∈ placeObjects cursor objects, GoodObject object
  | [], _, _, _, h => by simp [placeObjects] at h
  | head :: rest, cursor, hg, object, h => by
    simp only [placeObjects, List.mem_cons] at h
    rcases h with rfl | h
    · exact placeObject_good (hg head (by simp))
    · exact placeObjects_good (fun o ho => hg o (by simp [ho])) _ h

theorem placeObjects_length : ∀ (objects : List ObjectSection) (cursor : Nat),
    (placeObjects cursor objects).length = objects.length
  | [], _ => rfl
  | _ :: rest, _ => by simp [placeObjects, placeObjects_length rest]

theorem zeroRegion_agree (name : String) (start stop : Nat) (writable : Bool) :
    ∀ pair ∈ zeroRegion name start stop writable, pair.1.addr = pair.2.addr ∧ pair.1.size = pair.2.size := by
  intro pair hm
  unfold zeroRegion at hm
  split at hm
  · simp only [List.mem_singleton] at hm
    subst hm
    refine ⟨rfl, ?_⟩
    show stop - start = (Array.replicate (stop - start) 0).size
    simp
  · cases hm

/-- Placing undefined symbols moves the cursor forward and keeps the symbol list's shape. -/
theorem placeUndefined_spec {data : ByteArray} {header : Header} {word : Nat} {select : Nat → Bool} {size : Nat → Nat} :
    ∀ (symbols : List (Nat × Symbol)) (cursor : Nat),
      cursor ≤ (placeUndefined data header word select size cursor symbols).2 ∧
        (placeUndefined data header word select size cursor symbols).1.map (fun entry => (entry.1, entry.2.name)) =
          symbols.map (fun entry => (entry.1, entry.2.name)) ∧
        ∀ entry ∈ (placeUndefined data header word select size cursor symbols).1, entry ∈ symbols ∨
          (cursor ≤ entry.2.addr ∧ entry.2.addr ≤ (placeUndefined data header word select size cursor symbols).2 ∧
            ∃ original ∈ symbols, isUndefined data header original = true ∧ original.1 = entry.1)
  | [], cursor => by simp [placeUndefined]
  | head :: rest, cursor => by
    unfold placeUndefined
    by_cases hc : (isUndefined data header head && select head.2.addr) = true
    · have hle : cursor ≤ alignUp cursor word := by
        unfold alignUp
        split
        · exact Nat.le_refl _
        · rename_i ha
          have hpos : 0 < word := by omega
          have hdiv := Nat.div_add_mod (cursor + word - 1) word
          have hmod := Nat.mod_lt (cursor + word - 1) hpos
          have hcomm : (cursor + word - 1) / word * word = word * ((cursor + word - 1) / word) := Nat.mul_comm ..
          omega
      have ⟨h1, h2, h3⟩ := placeUndefined_spec (data := data) (header := header) (word := word) (select := select)
        (size := size) rest (alignUp cursor word + size head.2.addr)
      rcases hrec : placeUndefined data header word select size (alignUp cursor word + size head.2.addr) rest with
        ⟨placed, stop⟩
      rw [hrec] at h1 h2 h3
      simp only [hc, ↓reduceIte, hrec]
      refine ⟨by omega, by simpa using h2, ?_⟩
      intro entry hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · refine .inr ⟨hle, by simp only at h1 ⊢; omega, head, by simp, ?_, rfl⟩
        simp only [Bool.and_eq_true] at hc
        exact hc.1
      · rcases h3 entry hm with h | ⟨a, b, original, ho, hu, hi⟩
        · exact .inl (by simp [h])
        · exact .inr ⟨by omega, b, original, by simp [ho], hu, hi⟩
    · have ⟨h1, h2, h3⟩ := placeUndefined_spec (data := data) (header := header) (word := word) (select := select)
        (size := size) rest cursor
      rcases hrec : placeUndefined data header word select size cursor rest with ⟨placed, stop⟩
      rw [hrec] at h1 h2 h3
      have hf : (isUndefined data header head && select head.2.addr) = false := by simpa using hc
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨h1, by simpa using h2, ?_⟩
      intro entry hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact .inl (by simp)
      · rcases h3 entry hm with h | ⟨a, b, original, ho, hu, hi⟩
        · exact .inl (by simp [h])
        · exact .inr ⟨a, b, original, by simp [ho], hu, hi⟩

/-- Everything `Coff.decode` promises: no entry point, little-endian, and regions and segments that agree, also after
relocation and for the synthetic regions. -/
theorem decodeReport_ok {data : ByteArray} {image : Image} {errors : List String}
    (h : Coff.decodeReport data = .ok (image, errors)) :
    ∃ header, parseHeader data = .ok header ∧ image.data = data ∧ image.endian = .little ∧ image.entryPoint = 0 ∧
      image.addrWidth = (architecture (Header.machine header)).2 ∧
      image.sections.length = Header.sectionCount header ∧
      ∃ pairs : List (Segment × MemRegion), image.segments = pairs.map Prod.fst ∧
        image.memory.entries = (pairs.map Prod.snd).reverse.map (fun region => (region, ())) ∧
        ∀ pair ∈ pairs, pair.1.addr = pair.2.addr ∧ pair.1.size = pair.2.size := by
  simp only [Coff.decodeReport, bind_ok_iff] at h
  rcases h with ⟨header, h1, parsed, h2, parsedSymbols, _, h⟩
  have hgood : ∀ object ∈ parsed, GoodObject object := by
    intro object hm
    have ⟨hl, hp⟩ := mapM_ok h2
    have ⟨i, hi1, hi2⟩ := List.getElem_of_mem hm
    have hi3 : i < (List.range (Header.sectionCount header)).length := hl ▸ hi1
    have := hp i hi1 hi3
    rw [hi2] at this
    have hs := parseSection_ok this
    exact ⟨hs.1, hs.2.2.1⟩
  have hplaced := placeObjects_good (cursor := 0) hgood
  have hlength : (placeObjects 0 parsed).length = Header.sectionCount header := by
    have hl := (mapM_ok h2).1
    simp only [List.length_range] at hl
    rw [placeObjects_length, hl]
  cases h
  generalize (placeUndefined data header ((architecture (Header.machine header)).snd / 8) (fun x => x == 0) _ _ _).fst = symbols
  generalize hplacedList : placeObjects 0 parsed = placed at hplaced hlength ⊢
  have hzero : ∀ a b c d, ∀ pair ∈ zeroRegion "%common" a b true ++ zeroRegion "EXTERNAL" c d false,
      pair.1.addr = pair.2.addr ∧ pair.1.size = pair.2.size := by
    intro a b c d pair hm
    rcases List.mem_append.mp hm with hm | hm
    · exact zeroRegion_agree _ _ _ _ _ hm
    · exact zeroRegion_agree _ _ _ _ _ hm
  generalize hx : zeroRegion "%common" _ _ true ++ zeroRegion "EXTERNAL" _ _ false = extra
  have hextra : ∀ pair ∈ extra, pair.1.addr = pair.2.addr ∧ pair.1.size = pair.2.size := by
    rw [← hx]
    exact hzero _ _ _ _
  generalize hm : List.filter (fun object => isMapped object && (ObjectSection.segment object).size != 0)
    (List.map Prod.fst (List.map _ placed)) = mapped
  have hmapped : ∀ object ∈ mapped, GoodObject object := by
    intro object hobject
    rw [← hm] at hobject
    simp only [List.mem_filter, List.mem_map] at hobject
    rcases hobject with ⟨⟨_, ⟨source, hsource, rfl⟩, rfl⟩, _⟩
    have hgoodSource := hplaced source hsource
    split
    · rename_i _
      have hf := applyRelocations_frame (data := data) (header := header)
        (sections := List.map (fun object => ObjectSection.info object) placed) (symbols := symbols) source
      rcases hrel : applyRelocations data header (List.map (fun object => ObjectSection.info object) placed) symbols source
        with ⟨out, errors'⟩
      rw [hrel] at hf
      have ⟨f1, _, f3, f4, _⟩ := hf
      exact ⟨by simp only [f1, f3]; exact hgoodSource.1, by simp only [f1, f4]; exact hgoodSource.2⟩
    · exact hgoodSource
  refine ⟨header, h1, rfl, rfl, rfl, rfl, by simpa using hlength,
    mapped.map (fun object => (ObjectSection.segment object, ObjectSection.region object)) ++ extra, ?_, ?_, ?_⟩
  · simp [List.map_append, List.map_map, Function.comp_def]
  · simp only [Map.foldl_add_entries]
    simp [List.map_append, List.map_map, Function.comp_def]
  · intro pair hp
    rcases List.mem_append.mp hp with hp | hp
    · simp only [List.mem_map] at hp
      rcases hp with ⟨object, ho, rfl⟩
      exact hmapped object ho
    · exact hextra pair hp

theorem decode_ok {data : ByteArray} {image : Image} (h : Coff.decode data = .ok image) :
    ∃ errors, Coff.decodeReport data = .ok (image, errors) := by
  simp only [Coff.decode, bind_ok_iff] at h
  rcases h with ⟨⟨out, errors⟩, h1, h⟩
  cases h
  exact ⟨errors, h1⟩

theorem decode_rejects_short {data : ByteArray} (h : data.size < 20) : (Coff.decode data).isOk = false := by
  cases hd : Coff.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hr⟩ := decode_ok hd
    have ⟨_, hp, _⟩ := decodeReport_ok hr
    have := parseHeader_rejects_short (data := data) h
    simp [hp, Except.isOk, Except.toBool] at this

end CoffParser

/-! ## Ogre -/

namespace OgreDoc

open_private Bap.Image.Ogre Bap.Image.Ogre archName decodeArch nat bool boolValue encodeField decodeSection
  decodeSegment decodeSymbol decodeFact

open Ogre

/-- Every architecture name decodes back to its architecture. -/
theorem decodeArch_archName (arch : Arch) : decodeArch (archName arch) = .ok arch := by
  cases arch <;> rfl

theorem boolValue_bool (value : Bool) : boolValue (bool value) = .ok value := by
  cases value <;> rfl

theorem toNat?_toString (value : Nat) : (toString value).toNat? = some value := by
  have htoList : (toString value).toList = Nat.toDigits 10 value := by
    rw [Nat.toString_eq_ofList_toDigits]; simp
  have hne : toString value ≠ "" := by
    intro e
    have := congrArg String.toList e
    rw [htoList] at this
    exact Nat.toDigits_ne_nil this
  have hdigit : ∀ c ∈ (toString value).toList, c.isDigit = true := by
    intro c hc
    rw [htoList] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  rw [String.toNat?_eq_some_ofDigitChars (String.isNat_of_isDigit hne hdigit), htoList]
  have hf : (Nat.toDigits 10 value).filter (· != '_') = Nat.toDigits 10 value := by
    apply List.filter_eq_self.mpr
    intro c hc
    have : c ≠ '_' := fun e => Nat.underscore_not_in_toDigits (e ▸ hc)
    simpa using this
  rw [hf, Nat.ofDigitChars_ten_toDigits]

/-- Printed naturals always parse back. -/
theorem sexp_nat_nat (value : Nat) : Sexp.nat (nat value) = .ok value := by
  show (match (toString value).toNat? with
    | some value => Except.ok value
    | none => Except.error _) = _
  rw [toNat?_toString]

theorem asAtom_atom (name : String) : Sexp.asAtom (.atom name) = .ok name := rfl

theorem decodeSection_record (sec : Section) :
    decodeSection [.atom sec.name, nat sec.addr, nat sec.offset, nat sec.size, nat sec.flags, nat sec.kind] =
      .ok (.section sec) := by
  simp only [decodeSection, asAtom_atom, sexp_nat_nat, Reader.ok_bind]

theorem decodeSegment_record (segment : Segment) :
    decodeSegment [.atom segment.name, nat segment.addr, nat segment.size, bool segment.readable,
      bool segment.writable, bool segment.executable] = .ok (.segment segment) := by
  simp only [decodeSegment, asAtom_atom, sexp_nat_nat, boolValue_bool, Reader.ok_bind]

theorem decodeSymbol_record (symbol : Symbol) :
    decodeSymbol [.atom symbol.name, nat symbol.addr, nat symbol.size, bool symbol.isFunction,
      bool symbol.isDebug] = .ok (.symbol symbol) := by
  simp only [decodeSymbol, asAtom_atom, sexp_nat_nat, boolValue_bool, Reader.ok_bind]

private theorem fact_section (args : List Sexp) : decodeFact (.tagged "section" args) = .ok [] := rfl
private theorem fact_named_region (args : List Sexp) : decodeFact (.tagged "named-region" args) = .ok [] := rfl
private theorem fact_segment (args : List Sexp) : decodeFact (.tagged "segment" args) = .ok [] := rfl
private theorem fact_named_symbol (args : List Sexp) : decodeFact (.tagged "named-symbol" args) = .ok [] := rfl
private theorem fact_symbol_chunk (args : List Sexp) : decodeFact (.tagged "symbol-chunk" args) = .ok [] := rfl

private theorem fact_section_record (sec : Section) :
    decodeFact (.tagged "section-record"
      [.atom sec.name, nat sec.addr, nat sec.offset, nat sec.size, nat sec.flags, nat sec.kind]) =
      .ok [.section sec] := by
  show (decodeSection _ >>= fun f => Except.ok [f]) = _
  rw [decodeSection_record]
  rfl

private theorem fact_segment_record (segment : Segment) :
    decodeFact (.tagged "segment-record" [.atom segment.name, nat segment.addr, nat segment.size,
      bool segment.readable, bool segment.writable, bool segment.executable]) = .ok [.segment segment] := by
  show (decodeSegment _ >>= fun f => Except.ok [f]) = _
  rw [decodeSegment_record]
  rfl

private theorem fact_symbol_record (symbol : Symbol) :
    decodeFact (.tagged "symbol-record" [.atom symbol.name, nat symbol.addr, nat symbol.size,
      bool symbol.isFunction, bool symbol.isDebug]) = .ok [.symbol symbol] := by
  show (decodeSymbol _ >>= fun f => Except.ok [f]) = _
  rw [decodeSymbol_record]
  rfl

private theorem fact_bits (width : Nat) : decodeFact (.tagged "bits" [nat width]) = .ok [.bits width] := by
  show (Sexp.nat (nat width) >>= fun w => Except.ok [Field.bits w]) = _
  rw [sexp_nat_nat]
  rfl

private theorem fact_little (value : Bool) :
    decodeFact (.tagged "is-little-endian" [bool value]) = .ok [.littleEndian value] := by
  show (boolValue (bool value) >>= fun v => Except.ok [Field.littleEndian v]) = _
  rw [boolValue_bool]
  rfl

private theorem fact_entry (address : Nat) :
    decodeFact (.tagged "entry-point" [nat address]) = .ok [.entryPoint address] := by
  show (Sexp.nat (nat address) >>= fun v => Except.ok [Field.entryPoint v]) = _
  rw [sexp_nat_nat]
  rfl

private theorem fact_code (address size offset : Nat) :
    decodeFact (.tagged "code-region" [nat address, nat size, nat offset]) =
      .ok [.codeRegion address size offset] := by
  show (Sexp.nat (nat address) >>= fun a => Sexp.nat (nat size) >>= fun s => Sexp.nat (nat offset) >>= fun o =>
    Except.ok [Field.codeRegion a s o]) = _
  rw [sexp_nat_nat, sexp_nat_nat, sexp_nat_nat]
  rfl

/-- Each field survives printing to S-expressions and decoding, one fact carrying it and the rest ignored. -/
theorem decodeFacts_encodeField (field : Field) :
    ∃ decoded, (encodeField field).mapM decodeFact = .ok decoded ∧ decoded.flatten = [field] := by
  cases field with
  | arch name => exact ⟨[[.arch name]], rfl, rfl⟩
  | bits width =>
    refine ⟨[[.bits width]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_bits]
    rfl
  | littleEndian value =>
    refine ⟨[[.littleEndian value]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_little]
    rfl
  | entryPoint address =>
    refine ⟨[[.entryPoint address]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_entry]
    rfl
  | «section» sec =>
    refine ⟨[[], [], [.section sec]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_section, fact_named_region, fact_section_record]
    rfl
  | segment segment =>
    refine ⟨[[], [], [.segment segment]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_segment, fact_named_region, fact_segment_record]
    rfl
  | symbol symbol =>
    refine ⟨[[], [], [.symbol symbol]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_named_symbol, fact_symbol_chunk, fact_symbol_record]
    rfl
  | codeRegion address size offset =>
    refine ⟨[[.codeRegion address size offset]], ?_, rfl⟩
    simp only [encodeField, List.mapM_cons, List.mapM_nil, fact_code]
    rfl

/-- Decoding all the facts of a document gives back its field list. -/
theorem decodeFacts_fields (fields : List Field) :
    ∃ decoded, (fields.flatMap encodeField).mapM decodeFact = .ok decoded ∧ decoded.flatten = fields := by
  induction fields with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons field rest ih =>
    obtain ⟨tail, ht, hf⟩ := ih
    obtain ⟨head, hh, hg⟩ := decodeFacts_encodeField field
    refine ⟨head ++ tail, ?_, by simp [hf, hg]⟩
    rw [List.flatMap_cons, List.mapM_append, hh, ht]
    rfl

/-- The printer and parser are inverses, on every document. -/
theorem parse_render (doc : Doc) : parse (render doc) = .ok doc := by
  obtain ⟨decoded, hd, hf⟩ := decodeFacts_fields doc.fields
  have hl : Sexp.asList (.list (doc.fields.flatMap encodeField)) = .ok (doc.fields.flatMap encodeField) := rfl
  have hp : Sexp.parse (render doc) = .ok (.list (doc.fields.flatMap encodeField)) :=
    Bap.Proofs.Core.SexpLaws.parse_render _
  simp only [parse, hp, hl, hd, Reader.ok_bind, hf]

/-- A region built from Ogre metadata: the file contents are not part of the document. -/
def zeroRegion (region : MemRegion) : MemRegion :=
  ⟨region.addr, ByteArray.mk (List.replicate region.size 0).toArray, true, false, true⟩

private theorem filterMap_none_nil {α β : Type} (values : List α) :
    values.filterMap (fun _ => (none : Option β)) = [] := by
  induction values <;> simp_all

/-- Rebuilding an image from its Ogre document keeps all metadata and the shape of its memory map.
Region contents are not recorded, and the map's order reverses. -/
theorem toImage_ofImage (image : Image) :
    ∃ rebuilt, toImage (ofImage image) = .ok rebuilt ∧ rebuilt.arch = image.arch ∧
      rebuilt.addrWidth = image.addrWidth ∧ rebuilt.endian = image.endian ∧
      rebuilt.entryPoint = image.entryPoint ∧ rebuilt.sections = image.sections ∧
      rebuilt.segments = image.segments ∧ rebuilt.symbols = image.symbols ∧
      rebuilt.memory.entries = (image.memory.entries.map fun entry => (zeroRegion entry.1, ())).reverse := by
  simp only [toImage, ofImage, List.cons_append, List.find?_cons, decodeArch_archName, Reader.ok_bind]
  refine ⟨_, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · cases image.endian <;> simp
  · simp [List.filterMap_append, List.filterMap_map, Function.comp_def, filterMap_none_nil]
  · simp [List.filterMap_append, List.filterMap_map, Function.comp_def, filterMap_none_nil]
  · simp [List.filterMap_append, List.filterMap_map, Function.comp_def, filterMap_none_nil]
  · rw [Map.foldl_add_entries]
    simp [List.filterMap_append, List.filterMap_map, Function.comp_def, filterMap_none_nil, zeroRegion,
      MemRegion.size, MemoryMap.empty]

theorem zeroRegion_contains (region : MemRegion) (address : Nat) :
    (zeroRegion region).contains address = region.contains address := by
  have hs : (zeroRegion region).size = region.size := by
    show (List.replicate region.size (0 : UInt8)).toArray.size = _
    simp
  cases hc : region.contains address
  · rw [Bool.eq_false_iff, ne_eq, Region.contains_iff] at hc ⊢
    rw [hs]
    exact hc
  · rw [Region.contains_iff] at hc ⊢
    rw [hs]
    exact hc

/-- The rebuilt map covers exactly the original addresses, and every mapped byte reads as zero. -/
theorem zero_memory {entries : List (MemRegion × Unit)} {address : Nat} :
    let rebuilt : MemoryMap Unit := ⟨(entries.map fun entry => (zeroRegion entry.1, ())).reverse⟩
    rebuilt.contains address = (MemoryMap.mk entries).contains address ∧
      ∀ byte, rebuilt.readByte address = some byte → byte = 0 := by
  intro rebuilt
  constructor
  · rw [Bool.eq_iff_iff, Map.contains_iff, Map.contains_iff]
    simp only [rebuilt, List.mem_reverse, List.mem_map]
    constructor
    · rintro ⟨_, ⟨entry, hm, rfl⟩, hc⟩
      exact ⟨entry, hm, by simpa [zeroRegion_contains] using hc⟩
    · rintro ⟨entry, hm, hc⟩
      exact ⟨_, ⟨entry, hm, rfl⟩, by simpa [zeroRegion_contains] using hc⟩
  · intro byte hb
    obtain ⟨_, hm, _, rfl⟩ := Map.readByte_some hb
    simp only [rebuilt, List.mem_reverse, List.mem_map] at hm
    obtain ⟨entry, _, rfl⟩ := hm
    show (List.replicate entry.1.size (0 : UInt8)).toArray[_]! = 0
    generalize address - _ = i
    by_cases hi : i < (List.replicate entry.1.size (0 : UInt8)).toArray.size
    · rw [getElem!_pos _ i hi]
      simp
    · rw [getElem!_neg _ i hi]
      rfl

/-- A document with no architecture cannot become an image. -/
theorem toImage_requires_arch {doc : Doc} (h : ∀ name, Field.arch name ∉ doc.fields) :
    (toImage doc).isOk = false := by
  simp only [toImage]
  split
  · rename_i name hfind
    exact absurd (List.mem_of_find?_eq_some hfind) (h name)
  · rfl

end OgreDoc

end Bap.Proofs.Image
