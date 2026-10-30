import Lean
import Bap.Image.Loader
import Bap.Image.Coff

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

/-! ## ELF -/

namespace ElfParser

open_private Bap.Image.Elf Bap.Image.Elf word parseHeader parseProgramHeader parseSections parseSegments
  offsetOf tagValue sleb128 sleb128.loop alignUp codeAddress parseSymbol relativeType irelativeType symbolRelocationKind

open Reader

theorem word_bound {data : ByteArray} {endian : Endian} {is64 : Bool} {offset value : Nat}
    (h : word data endian is64 offset = .ok value) : offset + (if is64 then 8 else 4) ≤ data.size := by
  cases is64
  · exact read_bound (endian := endian) h
  · exact read_bound (endian := endian) h

/-- The field-reading tail of `parseHeader`, once class and encoding are known. -/
def headerFields (data : ByteArray) (endian : Endian) (is64 : Bool) : Except String Elf.Header := do
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
  rcases h with ⟨m, h1, e, h2, po, h3, so, h4, pes, h5, pc, h6, ses, h7, sc, h8, ssi, h9, h⟩
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

/-- Everything `Elf.decode` promises about an accepted file. -/
theorem decode_ok {data : ByteArray} {image : Image} (h : Elf.decode data = .ok image) :
    ∃ header, parseHeader data = .ok header ∧ image.data = data ∧
      image.addrWidth = (if header.is64 then 64 else 32) ∧ image.endian = header.endian ∧
      image.entryPoint = header.entryPoint ∧
      ∃ entries : List (Segment × MemRegion), image.segments = entries.map Prod.fst ∧
        image.memory.entries = (entries.map Prod.snd).reverse.map (fun region => (region, ())) ∧
        ∀ entry ∈ entries, LoadPair data entry := by
  simp only [Elf.decode, bind_ok_iff] at h
  rcases h with ⟨header, h1, ⟨segments, regions⟩, h2, sh, _, sections, _, symbols, _, h⟩
  cases h
  have ⟨entries, hs, hr, hp⟩ := parseSegments_ok h2
  refine ⟨header, h1, rfl, rfl, rfl, rfl, entries, hs, ?_, hp⟩
  rw [Map.foldl_add_entries, hr]
  simp

/-- A file with no program headers, like a relocatable object, decodes with no segments and no mapped memory. -/
theorem decode_no_program_headers {data : ByteArray} {image : Image} {header : Elf.Header}
    (h : Elf.decode data = .ok image) (hh : parseHeader data = .ok header) (h0 : header.programCount = 0) :
    image.segments = [] ∧ image.memory.entries = [] ∧ Elf.programHeaders data = .ok [] := by
  simp only [Elf.decode, bind_ok_iff, hh] at h
  rcases h with ⟨_, he, ⟨segments, regions⟩, h2, sh, _, _, _, _, _, h⟩
  cases he
  rw [parseSegments_no_entries h0] at h2
  cases h2
  cases h
  refine ⟨rfl, rfl, ?_⟩
  simp only [Elf.programHeaders, hh, Reader.ok_bind]
  rw [ite_eq_left h0]

theorem decode_rejects_short {data : ByteArray} (h : data.size < 52) : (Elf.decode data).isOk = false := by
  cases hd : Elf.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp, _⟩ := decode_ok hd
    have := parseHeader_rejects_short (data := data) h
    simp [hp, Except.isOk, Except.toBool] at this

theorem decode_rejects_magic {data : ByteArray}
    (h : ¬ (byteAt data 0 = 0x7f ∧ byteAt data 1 = 0x45 ∧ byteAt data 2 = 0x4c ∧ byteAt data 3 = 0x46)) :
    (Elf.decode data).isOk = false := by
  cases hd : Elf.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp, _⟩ := decode_ok hd
    have := parseHeader_rejects_magic h
    simp [hp, Except.isOk, Except.toBool] at this

/-- Every byte mapped by a decoded ELF lies inside one of its LOAD segments. -/
theorem decode_readByte_in_segment {data : ByteArray} {image : Image} {address : Nat} {byte : UInt8}
    (h : Elf.decode data = .ok image) (hr : image.memory.readByte address = some byte) :
    ∃ segment ∈ image.segments, segment.addr ≤ address ∧ address < segment.addr + segment.size := by
  have ⟨_, _, _, _, _, _, entries, hs, hm, hp⟩ := decode_ok h
  have ⟨entry, hentry, hc, _⟩ := Map.readByte_some hr
  rw [hm] at hentry
  simp only [List.mem_map, List.mem_reverse] at hentry
  rcases hentry with ⟨region, ⟨pair, hpair, rfl⟩, rfl⟩
  refine ⟨pair.1, ?_, ?_⟩
  · rw [hs]; exact List.mem_map_of_mem hpair
  · have ⟨h1, h2, _⟩ := hp pair hpair
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
theorem relocationInfo_split (info : Nat) :
    info = info / 0x100 * 0x100 + info % 0x100 ∧ info % 0x100 < 0x100 ∧
      info = info / 0x100000000 * 0x100000000 + info % 0x100000000 ∧ info % 0x100000000 < 0x100000000 := by
  omega

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
          relocation.typ = (if header.is64 then info % 0x100000000 else info % 0x100) ∧
          relocation.symbol = (if header.is64 then info / 0x100000000 else info / 0x100) ∧
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
  cases rela with
  | true =>
    simp only [↓reduceIte, bind_ok_iff] at hk
    rcases hk with ⟨addend, h3, hk⟩
    rw [← Except.ok.inj hk]
    exact ⟨h1, rfl, info, h2, rfl, rfl, fun _ => h3, fun e => by cases e⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Reader.ok_bind] at hk
    rw [← Except.ok.inj hk]
    exact ⟨h1, rfl, info, h2, rfl, rfl, (fun e => by cases e), fun _ => rfl⟩

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

/-- Applying a relocation keeps its region's address and size, and only changes the relocated field. -/
theorem applyRelocation_frame {data : ByteArray} {header : Header} {symbols : List (Nat × Symbol)}
    {object : ObjectSection} {region out : MemRegion} {index : Nat}
    (h : applyRelocation data header symbols object region index = .ok out) :
    out.addr = region.addr ∧ out.size = region.size := by
  simp only [applyRelocation, bind_ok_iff] at h
  rcases h with ⟨rva, _, symbolIndex, _, kind, _, h⟩
  split at h <;> first
    | (simp only [error_bind] at h; cases h)
    | (simp only [ok_bind] at h
       split at h
       · cases h
       · simp only [bind_ok_iff] at h
         rcases h with ⟨addend, _, bytes, hw, h⟩
         cases h
         exact ⟨rfl, (writeNat_ok hw).2.1⟩)

/-- `IMAGE_REL_AMD64_REL32` and `REL32_1` to `REL32_5`: the stored displacement, added to the address `kind` bytes
past the field, reaches the symbol plus the addend (`S + A - (P + kind)`, as lld-link computes it). -/
theorem applyRelocation_rel32 {data : ByteArray} {header : Header} {symbols : List (Nat × Symbol)}
    {object : ObjectSection} {region out : MemRegion} {index rva symbolIndex kind addend : Nat} {symbol : Symbol}
    (hm : Header.machine header = 0x8664)
    (hrva : IO.Reader.u32 data .little (ObjectSection.relocationOffset object + index * 10) = .ok rva)
    (hsym : IO.Reader.u32 data .little (ObjectSection.relocationOffset object + index * 10 + 4) = .ok symbolIndex)
    (hkind : IO.Reader.u16 data .little (ObjectSection.relocationOffset object + index * 10 + 8) = .ok kind)
    (hk : 4 ≤ kind ∧ kind ≤ 9)
    (hfind : symbols.find? (fun entry => entry.1 = symbolIndex) = some (symbolIndex, symbol))
    (hadd : IO.Reader.read region.data .little rva 4 = .ok addend)
    (h : applyRelocation data header symbols object region index = .ok out) :
    ∃ value, value < 2 ^ 32 ∧
      (value + ((ObjectSection.info object).addr + rva + kind)) % 2 ^ 32 = (symbol.addr + addend) % 2 ^ 32 ∧
      writeNat region.data rva 4 value = .ok out.data := by
  simp only [applyRelocation, bind_ok_iff, hrva, hsym, hkind, hm] at h
  rcases h with ⟨_, e1, _, e2, _, e3, h⟩
  cases e1
  cases e2
  cases e3
  have hk' : kind = 4 ∨ kind = 5 ∨ kind = 6 ∨ kind = 7 ∨ kind = 8 ∨ kind = 9 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [hfind, hadd, ok_bind, ↓reduceIte, bind_ok_iff] at h
     rcases h with ⟨bytes, hw, h⟩
     cases h
     exact ⟨_, Nat.mod_lt _ (by decide), resolves_mod _ _ _ _ (by decide), hw⟩)

private def rel32Input : ByteArray := ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0, 4, 0]

set_option maxRecDepth 100000 in
/-- A `call` at 0 (`e8 rel32`, field at `P = 1`) to the instruction after it (`S = 5`) gets displacement 0. -/
theorem rel32_call_next_instruction :
    let object := ObjectSection.mk ⟨".text", 0, 0, 5, 0, 0⟩ ⟨".text", 0, 5, true, false, true⟩
      ⟨0, ByteArray.mk #[0xe8, 0, 0, 0, 0], true, false, true⟩ 0 1
    (applyRelocation rel32Input (Header.mk 0x8664 1 0 0 0 0) [(0, ⟨"f", 5, 0, true, false⟩)] object
      (ObjectSection.region object) 0).toOption.map (fun region => (region.data.get! 1).toNat) = some 0 := by
  rfl

theorem applyRelocations_frame {data : ByteArray} {header : Header} {symbols : List (Nat × Symbol)}
    {object out : ObjectSection} (h : applyRelocations data header symbols object = .ok out) :
    ObjectSection.segment out = ObjectSection.segment object ∧ ObjectSection.info out = ObjectSection.info object ∧
      (ObjectSection.region out).addr = (ObjectSection.region object).addr ∧
      (ObjectSection.region out).size = (ObjectSection.region object).size := by
  have fold : ∀ (indices : List Nat) (region result : MemRegion),
      indices.foldlM (m := Except String) (fun region index => applyRelocation data header symbols object region index)
        region = .ok result → result.addr = region.addr ∧ result.size = region.size := by
    intro indices
    induction indices with
    | nil =>
      intro region result hf
      simp only [List.foldlM_nil] at hf
      cases hf
      exact ⟨rfl, rfl⟩
    | cons index rest ih =>
      intro region result hf
      simp only [List.foldlM_cons, bind_ok_iff] at hf
      rcases hf with ⟨next, hn, hf⟩
      have ⟨a1, s1⟩ := applyRelocation_frame hn
      have ⟨a2, s2⟩ := ih next result hf
      exact ⟨a2.trans a1, s2.trans s1⟩
  simp only [applyRelocations, bind_ok_iff] at h
  rcases h with ⟨region, hr, h⟩
  cases h
  have ⟨a, b⟩ := fold _ _ _ hr
  exact ⟨rfl, rfl, a, b⟩

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

/-- Everything `Coff.decode` promises: no entry point, little-endian, and one mapped region per section, of the size
of its segment even after relocation. -/
theorem decode_ok {data : ByteArray} {image : Image} (h : Coff.decode data = .ok image) :
    ∃ header, parseHeader data = .ok header ∧ image.data = data ∧ image.endian = .little ∧ image.entryPoint = 0 ∧
      image.addrWidth = (architecture (Header.machine header)).2 ∧
      image.sections.length = Header.sectionCount header ∧
      image.segments.length = Header.sectionCount header ∧
      ∃ objects : List ObjectSection, image.segments = objects.map ObjectSection.segment ∧
        image.memory.entries = (objects.map ObjectSection.region).reverse.map (fun region => (region, ())) ∧
        ∀ object ∈ objects, (ObjectSection.segment object).addr = (ObjectSection.region object).addr ∧
          (ObjectSection.segment object).size = (ObjectSection.region object).size := by
  simp only [Coff.decode, bind_ok_iff] at h
  rcases h with ⟨header, h1, objects, h2, indexed, _, relocated, h3, h⟩
  cases h
  have ⟨hl, hp⟩ := mapM_ok h2
  simp only [List.length_range] at hl
  have ⟨hl', hr⟩ := mapM_ok h3
  refine ⟨header, h1, rfl, rfl, rfl, rfl, by simpa using hl, by simpa using hl'.trans hl, relocated, rfl, ?_, ?_⟩
  · rw [Map.foldl_add_entries]
    exact List.append_nil _
  · intro object hm
    have ⟨i, hi1, hi2⟩ := List.getElem_of_mem hm
    have hi3 : i < objects.length := hl' ▸ hi1
    have ha := hr i hi1 hi3
    rw [hi2] at ha
    have ⟨fs, _, fa, fz⟩ := applyRelocations_frame ha
    have hi4 : i < (List.range (Header.sectionCount header)).length := by simpa [hl] using hi3
    have hs := parseSection_ok (hp i hi3 hi4)
    rw [fs, fa, fz]
    exact ⟨hs.1, hs.2.2.1⟩

theorem decode_rejects_short {data : ByteArray} (h : data.size < 20) : (Coff.decode data).isOk = false := by
  cases hd : Coff.decode data with
  | error e => rfl
  | ok image =>
    have ⟨_, hp, _⟩ := decode_ok hd
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

/-- The printer/parser roundtrip, conditional only on the S-expression layer reading back what it printed.
`Sexp.parse` depends on the `partial` `Sexp.skipSpace`, so that condition cannot be discharged here. -/
theorem parse_render {doc : Doc}
    (h : Sexp.parse (render doc) = .ok (.list (doc.fields.flatMap encodeField))) :
    parse (render doc) = .ok doc := by
  obtain ⟨decoded, hd, hf⟩ := decodeFacts_fields doc.fields
  have hl : Sexp.asList (.list (doc.fields.flatMap encodeField)) = .ok (doc.fields.flatMap encodeField) := rfl
  simp only [parse, h, hl, hd, Reader.ok_bind, hf]

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
