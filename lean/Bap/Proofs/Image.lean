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

private def foldWrites (memory : ByteArray) (writes : List Write) : ByteArray :=
  writes.foldl (init := memory) fun memory write =>
    writeNat memory write.little write.off write.n write.value

private theorem commit_run (site : Site) (writes : List Write) (state : LinkState) :
    (commit site writes).run state =
      if writes.all (fun write => site.off ≤ write.off && write.off + write.n ≤ site.limit &&
          write.off + write.n ≤ state.memory.size) = true then
        .ok () { state with memory := foldWrites state.memory writes }
      else .error (outside site) state := by
  show commit site writes state = _
  simp only [commit, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  split <;> rfl

private theorem commit_fold : ∀ (writes : List Write) (memory : ByteArray),
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
        let output := ElfLinker.link (linkInput data header sections names)
        image.segments = output.regions.map ElfLinker.toSegment ∧
        image.memory.entries = ((output.regions.map (ElfLinker.toMemRegion output.memory data.size)).reverse.map
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
    generalize hoh : ElfLinker.link (linkInput data header sections names) = output at hseg hmem
    refine ⟨output.regions.map fun region =>
      (ElfLinker.toSegment region, ElfLinker.toMemRegion output.memory data.size region), ?_, ?_, ?_⟩
    · rw [hseg]; simp [Function.comp_def]
    · rw [hmem]; simp [Function.comp_def]
    · intro pair hp
      simp only [List.mem_map] at hp
      rcases hp with ⟨region, _, rfl⟩
      have ⟨a, b, _⟩ := LinkerLaws.toSegment_toMemRegion output.memory data.size region
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
  Header.entryPoint parseHeader parseSection parseSections parseSymbol parseSymbols

open Reader

/-- An accepted PE header has the DOS and PE signatures, the PE32+ magic and an in-bounds section table. -/
theorem parseHeader_ok {data : ByteArray} {header : Header} (h : parseHeader data = .ok header) :
    IO.Reader.u16 data .little 0 = .ok 0x5a4d ∧ 64 ≤ data.size ∧
      ∃ peOffset, IO.Reader.u32 data .little 60 = .ok peOffset ∧
        IO.Reader.u32 data .little peOffset = .ok 0x4550 ∧
        IO.Reader.u16 data .little (peOffset + 24) = .ok 0x20b ∧
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
  rcases h with ⟨machine, _, count, _, symOff, _, symCount, _, optSize, _, optMagic, hmagic, h⟩
  by_cases hm1 : (optMagic != 0x20b) = true
  · rw [ite_eq_left hm1] at h; cases h
  rw [ite_eq_right hm1] at h
  have hm2 : optMagic = 0x20b := by simpa using hm1
  subst hm2
  by_cases hsz : optSize < 112
  · rw [ite_eq_left hsz] at h; cases h
  rw [ite_eq_right hsz] at h
  simp only [bind_ok_iff] at h
  rcases h with ⟨entryRva, hentry, base, _, h⟩
  by_cases hsec : peOffset + 4 + 20 + optSize + count * 40 > data.size
  · rw [ite_eq_left hsec] at h; cases h
  rw [ite_eq_right hsec] at h
  split at h
  · cases h
  · cases h
    have hbound := read_bound hpe
    exact ⟨hd, by omega, peOffset, hpe, hsig, hmagic, by simpa using hsec, entryRva, hentry, rfl⟩

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
    ∃ header, parseHeader data = .ok header ∧ image.data = data ∧ image.addrWidth = 64 ∧
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
      Coff.relocationKind 0xaa64 3 = none ∧ Coff.relocationKind 0x01c4 3 = none := by
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
        writeNat region.data rva
          (Coff.relocationValue kind symbol.addr ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr).2
          (Coff.relocationValue kind symbol.addr ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr).1 =
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
  generalize hs : Coff.relocationValue kind symbol.addr _ addend sectionNumber _ = pair at h
  obtain ⟨value, size⟩ := pair
  simp only at h
  rcases h with ⟨bytes, hw, h⟩
  cases h
  have ⟨sectionAddr, hs'⟩ : ∃ sectionAddr, Coff.relocationValue kind symbol.addr
      ((ObjectSection.info object).addr + rva) addend sectionNumber sectionAddr = (value, size) := ⟨_, hs⟩
  refine ⟨rfl, (writeNat_ok hw).2.1, rva, number, kind, symbol, sectionNumber, sectionAddr, addend, hnumber, hrva,
    hkind, ?_⟩
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
