import Bap.Core.Types
import Bap.Core.Word
import Std.Data.TreeMap

namespace Bap

structure Memory (addressWidth : Nat) where
  pages : Std.TreeMap Nat ByteArray := {}

namespace Memory

def pageSize : Nat := 256

instance : Repr (Memory addressWidth) where
  reprPrec memory _ := s!"memory({memory.pages.size} pages)"

def empty (addressWidth : Nat) : Memory addressWidth := ⟨{}⟩

def cells (memory : Memory addressWidth) : List (BitVec addressWidth × UInt8) :=
  memory.pages.toList.flatMap fun entry =>
    let base := entry.1 * pageSize
    (List.range entry.2.size).filterMap fun offset =>
      let byte := entry.2[offset]!
      if byte = 0 then none else some (BitVec.ofNat addressWidth (base + offset), byte)

def readByte (memory : Memory addressWidth) (address : BitVec addressWidth) : UInt8 :=
  let address := address.toNat
  match memory.pages.get? (address / pageSize) with
  | some page => page[address % pageSize]!
  | none => 0

def writeByte (memory : Memory addressWidth) (address : BitVec addressWidth) (value : UInt8) :
    Memory addressWidth :=
  let address := address.toNat
  let index := address / pageSize
  let page := (memory.pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
  ⟨memory.pages.insert index (page.set! (address % pageSize) value)⟩

def ofCells (cells : List (BitVec addressWidth × UInt8)) : Memory addressWidth :=
  cells.foldl (init := empty addressWidth) fun memory cell => writeByte memory cell.1 cell.2

/-- Writes `data` to consecutive addresses, wrapping at `limit`, the size of the address space. -/
private def writePages (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address : Nat) (data : ByteArray) (offset : Nat) : Std.TreeMap Nat ByteArray :=
  if offset ≥ data.size then pages else
    let absolute := (address + offset) % limit
    let index := absolute / pageSize
    let pageOffset := absolute % pageSize
    let count := min (min (pageSize - pageOffset) (data.size - offset)) (limit - absolute)
    let chunk := data.extract offset (offset + count)
    let page := if count = pageSize then chunk else
      let existing := (pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
      existing.extract 0 pageOffset ++ chunk ++ existing.extract (pageOffset + count) pageSize
    writePages limit hlimit (pages.insert index page) address data (offset + count)
termination_by data.size - offset
decreasing_by
  have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
  have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
  omega

def writeRegion (memory : Memory addressWidth) (address : Nat) (data : ByteArray) : Memory addressWidth :=
  ⟨writePages (2 ^ addressWidth) (Nat.two_pow_pos _) memory.pages address data 0⟩

def writeSortedCells (memory : Memory addressWidth) (cells : List (BitVec addressWidth × UInt8)) : Memory addressWidth :=
  let groups := cells.foldl (init := ([] : List (Nat × Array UInt8))) fun groups cell =>
    match groups with
    | [] => [(cell.1.toNat, #[cell.2])]
    | (start, bytes) :: rest =>
      if cell.1.toNat = start + bytes.size then (start, bytes.push cell.2) :: rest
      else if cell.1.toNat = start + bytes.size - 1 then (start, bytes.set! (bytes.size - 1) cell.2) :: rest
      else (cell.1.toNat, #[cell.2]) :: (start, bytes) :: rest
  groups.foldl (init := memory) fun memory group =>
    writeRegion memory group.1 (ByteArray.mk group.2)

def writeCells (memory : Memory addressWidth) (cells : List (BitVec addressWidth × UInt8)) : Memory addressWidth :=
  writeSortedCells memory (cells.mergeSort fun left right => left.1.toNat ≤ right.1.toNat)

/-- Reads `size` consecutive addresses, wrapping at `limit`, the size of the address space. -/
private def readPages (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address size offset : Nat) (output : ByteArray) : ByteArray :=
  if offset ≥ size then output else
    let absolute := (address + offset) % limit
    let index := absolute / pageSize
    let pageOffset := absolute % pageSize
    let count := min (min (pageSize - pageOffset) (size - offset)) (limit - absolute)
    let page := (pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
    readPages limit hlimit pages address size (offset + count) (output ++ page.extract pageOffset (pageOffset + count))
termination_by size - offset
decreasing_by
  have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
  have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
  omega

def readRegion (memory : Memory addressWidth) (address size : Nat) : ByteArray :=
  readPages (2 ^ addressWidth) (Nat.two_pow_pos _) memory.pages address size 0 (ByteArray.emptyWithCapacity size)

private def byteAt (value : Nat) (offset : Nat) : UInt8 :=
  UInt8.ofNat ((value >>> (8 * offset)) % 256)

def write (memory : Memory addressWidth) (address : BitVec addressWidth)
    (value : BitVec valueWidth) (endian : Endian) (size : Nat) :
    Except String (Memory addressWidth) := do
  if size * 8 ≠ valueWidth then
    .error s!"expected {size * 8} bits, actual {valueWidth}"
  else
    let bytes := (List.range size).map fun offset =>
      let byteOffset := match endian with
        | .little => offset
        | .big => size - 1 - offset
      byteAt value.toNat byteOffset
    .ok (writeRegion memory address.toNat (ByteArray.mk bytes.toArray))

def read (memory : Memory addressWidth) (address : BitVec addressWidth)
    (endian : Endian) (size : Nat) : BitVec (size * 8) :=
  let bytes := (List.range size).map fun offset =>
    readByte memory (address + BitVec.ofNat addressWidth offset)
  let ordered := match endian with
    | .little => bytes.reverse
    | .big => bytes
  let value := ordered.foldl (fun result byte => result * 256 + byte.toNat) 0
  BitVec.ofNat (size * 8) value

/-! ### What the interpreters actually run

Nearly every access falls inside one page. `read` and `write` below say what an access means, byte by byte, and these
are the same functions for that case, without the arithmetic on the address of each byte: the `csimp` theorems make
the compiler call them, and the theorems about `read` and `write` hold of what runs. -/

/-- An address space holds whole pages. -/
private theorem add_lt_limit {addressWidth : Nat} (address : BitVec addressWidth) (hw : 8 ≤ addressWidth) {offset : Nat}
    (h : address.toNat % pageSize + offset < pageSize) : address.toNat + offset < 2 ^ addressWidth := by
  simp only [pageSize] at h
  have hpow : 2 ^ addressWidth = 256 * 2 ^ (addressWidth - 8) := by
    conv => lhs; rw [show addressWidth = 8 + (addressWidth - 8) by omega, Nat.pow_add]
  have hlt := address.isLt
  have hq : address.toNat / 256 < 2 ^ (addressWidth - 8) := by
    apply Nat.div_lt_of_lt_mul
    omega
  have hq' : 256 * (address.toNat / 256 + 1) ≤ 256 * 2 ^ (addressWidth - 8) := Nat.mul_le_mul_left _ hq
  omega

private theorem toNat_add_ofNat {addressWidth : Nat} (address : BitVec addressWidth) (hw : 8 ≤ addressWidth) {offset : Nat}
    (h : address.toNat % pageSize + offset < pageSize) :
    (address + BitVec.ofNat addressWidth offset).toNat = address.toNat + offset := by
  have hsum := add_lt_limit address hw h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega), Nat.mod_eq_of_lt hsum]

/-- The bytes `offset + n - 1` down to `offset` of a page, the first one read becoming the most significant. -/
private def readDown (page : ByteArray) (offset : Nat) : Nat → Nat → Nat
  | 0, value => value
  | n + 1, value => readDown page offset n (value * 256 + page[offset + n]!.toNat)

/-- The `n` bytes from `offset` of a page, the first one read becoming the most significant. -/
private def readUp (page : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, value => value
  | n + 1, offset, value => readUp page n (offset + 1) (value * 256 + page[offset]!.toNat)

private theorem readDown_eq (byte : Nat → UInt8) (page : ByteArray) (offset : Nat) (hbyte : ∀ i, byte i = page[offset + i]!)
    (n value : Nat) : readDown page offset n value =
      (((List.range n).map byte).reverse).foldl (fun result byte => result * 256 + byte.toNat) value := by
  induction n generalizing value with
  | zero => rfl
  | succ n ih =>
    rw [readDown, ih, List.range_succ, List.map_append, List.reverse_append]
    simp [hbyte]

private theorem readUp_eq (byte : Nat → UInt8) (page : ByteArray) (hbyte : ∀ i, byte i = page[i]!)
    (n offset value : Nat) : readUp page n offset value =
      (((List.range' offset n)).map byte).foldl (fun result byte => result * 256 + byte.toNat) value := by
  induction n generalizing offset value with
  | zero => rfl
  | succ n ih =>
    rw [readUp, ih, List.range'_succ]
    simp [hbyte]

/-- `read`, for an access inside of one page. -/
private def readFast (memory : Memory addressWidth) (address : BitVec addressWidth) (endian : Endian) (size : Nat) :
    BitVec (size * 8) :=
  let offset := address.toNat % pageSize
  if 8 ≤ addressWidth ∧ offset + size ≤ pageSize then
    match memory.pages.get? (address.toNat / pageSize) with
    | some page =>
      match endian with
      | .little => BitVec.ofNat (size * 8) (readDown page offset size 0)
      | .big => BitVec.ofNat (size * 8) (readUp page size offset 0)
    | none => 0
  else
    read memory address endian size

/-- The byte of a memory at an offset of the page of an address. -/
private theorem readByte_offset (memory : Memory addressWidth) (address : BitVec addressWidth) (hw : 8 ≤ addressWidth)
    {offset : Nat} (h : address.toNat % pageSize + offset < pageSize) :
    readByte memory (address + BitVec.ofNat addressWidth offset) =
      match memory.pages.get? (address.toNat / pageSize) with
      | some page => page[address.toNat % pageSize + offset]!
      | none => 0 := by
  have hnat := toNat_add_ofNat address hw h
  simp only [readByte, hnat]
  simp only [pageSize] at h ⊢
  rw [show (address.toNat + offset) / 256 = address.toNat / 256 by omega,
    show (address.toNat + offset) % 256 = address.toNat % 256 + offset by omega]

private theorem foldl_bytes_zero (bytes : List UInt8) (hzero : ∀ byte ∈ bytes, byte = 0) :
    bytes.foldl (fun result byte => result * 256 + byte.toNat) 0 = 0 := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    have := hzero byte (by simp)
    subst this
    simpa using ih fun b hb => hzero b (by simp [hb])

@[csimp] private theorem read_eq_readFast : @read = @readFast := by
  funext addressWidth memory address endian size
  simp only [readFast]
  split
  next hfit =>
    obtain ⟨hw, hfit⟩ := hfit
    have hbytes : ∀ offset, offset ∈ List.range size →
        readByte memory (address + BitVec.ofNat addressWidth offset) =
          match memory.pages.get? (address.toNat / pageSize) with
          | some page => page[address.toNat % pageSize + offset]!
          | none => 0 := fun offset ho =>
      readByte_offset memory address hw (by have := List.mem_range.mp ho; omega)
    simp only [read, List.map_congr_left hbytes]
    cases hget : memory.pages.get? (address.toNat / pageSize) with
    | some page =>
      cases endian with
      | little => simp only [readDown_eq (fun o => page[address.toNat % pageSize + o]!) page _ (fun _ => rfl)]
      | big =>
        simp only [readUp_eq (fun o => page[o]!) page (fun _ => rfl), List.range'_eq_map_range, List.map_map]
        rfl
    | none =>
      have hzero : ∀ (bytes : List UInt8), (∀ byte ∈ bytes, byte = 0) → BitVec.ofNat (size * 8)
          (bytes.foldl (fun result byte => result * 256 + byte.toNat) 0) = 0 := fun bytes h => by
        rw [foldl_bytes_zero bytes h]; rfl
      cases endian <;> (apply hzero; simp)
  next => rfl

private theorem page_ext {left right : ByteArray} (hsize : left.size = right.size)
    (h : ∀ offset, offset < left.size → left[offset]! = right[offset]!) : left = right := by
  apply ByteArray.ext
  apply Array.ext hsize
  intro offset h1 h2
  have := h offset h1
  rw [show left[offset]! = left.data[offset] from getElem!_pos left offset h1,
    show right[offset]! = right.data[offset] from getElem!_pos right offset (hsize ▸ h1)] at this
  exact this

theorem bang_eq (page : ByteArray) (j : Nat) : page[j]! = (page.data[j]?).getD 0 := by
  have : page[j]! = page.data[j]! := by
    by_cases h : j < page.size
    · rw [getElem!_pos page j h, getElem!_pos page.data j h]; rfl
    · rw [getElem!_neg page j h, getElem!_neg page.data j h]
  rw [this, getElem!_def]
  cases page.data[j]? <;> rfl

theorem get!_extract (page : ByteArray) (b e j : Nat) (hj : j < e - b) (he : e ≤ page.size) :
    (page.extract b e)[j]! = page[b + j]! := by
  have hmin : min e page.size = e := by omega
  have hd : min e page.data.size = e := hmin
  rw [bang_eq, bang_eq, ByteArray.data_extract, Array.getElem?_extract, hd, ite_eq_left hj]

/-- The page `writePages` builds for one chunk. -/
theorem chunk_page (data existing : ByteArray) (offset count po : Nat)
    (hsize : existing.size = pageSize) (hcount : po + count ≤ pageSize) (hdata : offset + count ≤ data.size) :
    let page := if count = pageSize then data.extract offset (offset + count) else
      existing.extract 0 po ++ data.extract offset (offset + count) ++ existing.extract (po + count) pageSize
    page.size = pageSize ∧ ∀ o, o < pageSize →
      page[o]! = if po ≤ o ∧ o < po + count then data[offset + (o - po)]! else existing[o]! := by
  intro page
  have hps : pageSize = 256 := rfl
  have hchunk : (data.extract offset (offset + count)).size = count := by
    simp only [ByteArray.size_extract]; omega
  by_cases hfull : count = pageSize
  · have hpage : page = data.extract offset (offset + count) := ite_eq_left hfull
    rw [hpage]
    have h0 : po = 0 := by omega
    subst h0
    refine ⟨by rw [hchunk, hfull], fun o ho => ?_⟩
    rw [ite_eq_left (by omega), get!_extract _ _ _ _ (by omega) (by omega)]
    simp
  · have hpage : page = existing.extract 0 po ++ data.extract offset (offset + count) ++
        existing.extract (po + count) pageSize := ite_eq_right hfull
    rw [hpage]
    have hl : (existing.extract 0 po).size = po := by
      simp only [ByteArray.size_extract]; omega
    have hr : (existing.extract (po + count) pageSize).size = pageSize - (po + count) := by
      simp only [ByteArray.size_extract, hsize]; omega
    refine ⟨by simp only [ByteArray.size_append, hl, hr, hchunk]; omega, fun o ho => ?_⟩
    have hsplit : ∀ (a b c : ByteArray), (a ++ b ++ c)[o]! =
        if o < a.size then a[o]! else if o < a.size + b.size then b[o - a.size]! else c[o - a.size - b.size]! := by
      intro a b c
      have h1 : (a.data ++ b.data).size = a.size + b.size := by
        rw [Array.size_append]
        rfl
      have h2 : a.data.size = a.size := rfl
      simp only [bang_eq, ByteArray.data_append, Array.getElem?_append, h1, h2]
      by_cases h3 : o < a.size
      · simp only [h3, ite_true, show o < a.size + b.size by omega]
      · by_cases h4 : o < a.size + b.size
        · simp only [h3, h4, ite_true, ite_false]
        · simp only [h3, h4, ite_false, Nat.sub_add_eq]
    rw [hsplit, hl, hchunk]
    by_cases h1 : o < po
    · rw [ite_eq_left h1, ite_eq_right (by omega), get!_extract _ _ _ _ (by omega) (by omega)]
      simp
    · by_cases h2 : o < po + count
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (by omega),
          get!_extract _ _ _ _ (by omega) (by omega)]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega),
          get!_extract _ _ _ _ (by omega) (by omega)]
        congr 1
        omega

/-- Sets the `n` bytes from `offset` of a page. -/
private def setBytes (page : ByteArray) (offset : Nat) (byte : Nat → UInt8) : Nat → ByteArray
  | 0 => page
  | n + 1 => (setBytes page offset byte n).set! (offset + n) (byte n)

private theorem size_setBytes (page : ByteArray) (offset : Nat) (byte : Nat → UInt8) (n : Nat) :
    (setBytes page offset byte n).size = page.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [setBytes, ByteArray.size_set!, ih]

private theorem get_setBytes (page : ByteArray) (offset : Nat) (byte : Nat → UInt8) (n : Nat) (hn : offset + n ≤ page.size)
    (o : Nat) : (setBytes page offset byte n)[o]! = if offset ≤ o ∧ o < offset + n then byte (o - offset) else page[o]! := by
  induction n with
  | zero =>
    rw [setBytes, ite_eq_right (by omega)]
  | succ n ih =>
    rw [setBytes, bang_eq, show ((setBytes page offset byte n).set! (offset + n) (byte n)).data =
      (setBytes page offset byte n).data.setIfInBounds (offset + n) (byte n) from rfl, Array.getElem?_setIfInBounds]
    have hsz : offset + n < (setBytes page offset byte n).data.size := by
      have := size_setBytes page offset byte n
      simp only [ByteArray.size] at this
      simp only [ByteArray.size] at hn
      omega
    by_cases ho : offset + n = o
    · subst ho
      have hsz' : offset + n < (setBytes page offset byte n).size := hsz
      simp [hsz']
    · have := ih (by omega)
      rw [bang_eq] at this
      simp only [ho, ite_false, this]
      by_cases h1 : offset ≤ o ∧ o < offset + n
      · rw [ite_eq_left h1, ite_eq_left ⟨h1.1, by omega⟩]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- `write`, for an access inside of one page. -/
private def writeFast (memory : Memory addressWidth) (address : BitVec addressWidth)
    (value : BitVec valueWidth) (endian : Endian) (size : Nat) : Except String (Memory addressWidth) :=
  let index := address.toNat / pageSize
  let offset := address.toNat % pageSize
  let existing := (memory.pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
  if size * 8 = valueWidth ∧ 8 ≤ addressWidth ∧ offset + size ≤ pageSize ∧ 0 < size ∧ existing.size = pageSize then
    let bits := value.toNat
    .ok ⟨memory.pages.insert index (setBytes existing offset
      (fun i => byteAt bits (match endian with
        | .little => i
        | .big => size - 1 - i)) size)⟩
  else
    write memory address value endian size

/-- A write that fits in a page and has more than nothing to write replaces that page. -/
private theorem writeRegion_fit (memory : Memory addressWidth) (address : BitVec addressWidth) (data : ByteArray)
    (byte : Nat → UInt8) (hw : 8 ≤ addressWidth) (hfit : address.toNat % pageSize + data.size ≤ pageSize) (hpos : 0 < data.size)
    (hexisting : ((memory.pages.get? (address.toNat / pageSize)).getD
      (ByteArray.mk (List.replicate pageSize 0).toArray)).size = pageSize)
    (hdata : ∀ i, i < data.size → data[i]! = byte i) :
    writeRegion memory address.toNat data = ⟨memory.pages.insert (address.toNat / pageSize) (setBytes
      ((memory.pages.get? (address.toNat / pageSize)).getD (ByteArray.mk (List.replicate pageSize 0).toArray))
      (address.toNat % pageSize) byte data.size)⟩ := by
  have hlt := address.isLt
  have hend : address.toNat + (data.size - 1) < 2 ^ addressWidth :=
    add_lt_limit address hw (by omega)
  simp only [writeRegion]
  congr 1
  rw [writePages, ite_eq_right (by omega)]
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hlt, Nat.sub_zero]
  have hcount : min (min (pageSize - address.toNat % pageSize) data.size) (2 ^ addressWidth - address.toNat) =
      data.size := by omega
  simp only [hcount, Nat.zero_add]
  rw [writePages, ite_eq_left (by omega)]
  generalize hexist : (memory.pages.get? (address.toNat / pageSize)).getD
    (ByteArray.mk (List.replicate pageSize 0).toArray) = existing at hexisting ⊢
  congr 1
  obtain ⟨hsize, hget⟩ := chunk_page data existing 0 data.size (address.toNat % pageSize) hexisting hfit (by omega)
  simp only [Nat.zero_add] at hsize hget
  apply page_ext (by rw [hsize, size_setBytes, hexisting])
  intro o ho
  rw [hsize] at ho
  rw [hget o ho, get_setBytes _ _ _ _ (by omega)]
  split
  · exact hdata _ (by omega)
  · rfl

@[csimp] private theorem write_eq_writeFast : @write = @writeFast := by
  funext addressWidth valueWidth memory address value endian size
  simp only [writeFast]
  split
  next hfit =>
    obtain ⟨hwidth, hw, hfit, hpos, hexisting⟩ := hfit
    have key : ∀ f : Nat → UInt8, writeRegion memory address.toNat (ByteArray.mk ((List.range size).map f).toArray) =
        ⟨memory.pages.insert (address.toNat / pageSize) (setBytes
          ((memory.pages.get? (address.toNat / pageSize)).getD (ByteArray.mk (List.replicate pageSize 0).toArray))
          (address.toNat % pageSize) f size)⟩ := by
      intro f
      have hdata : (ByteArray.mk ((List.range size).map f).toArray).size = size := by
        show ((List.range size).map f).toArray.size = size
        simp
      have := writeRegion_fit memory address (ByteArray.mk ((List.range size).map f).toArray) f hw
        (by rw [hdata]; exact hfit) (by rw [hdata]; exact hpos) hexisting (by
          intro i hi
          rw [hdata] at hi
          rw [getElem!_pos _ i (by rw [hdata]; exact hi)]
          show ((List.range size).map f).toArray[i]'(by simpa using hi) = _
          simp)
      rwa [hdata] at this
    cases endian <;> simp only [write, hwidth, ne_eq, not_true_eq_false, ite_false, key] <;> rfl
  next => rfl

end Memory

inductive Value where
  | bits {width : Nat} (value : BitVec width)
  | memory {addressWidth : Nat} (value : Memory addressWidth)
  | undefined
  deriving Repr

namespace Value

def type : Value → Typ
  | @Value.bits width _ => .imm width
  | @Value.memory addressWidth _ => .mem addressWidth 8
  | .undefined => .unknown

def asBits : Value → Except String (Σ width, BitVec width)
  | .bits value => .ok ⟨_, value⟩
  | .memory _ => .error "expected a bitvector, got memory"
  | .undefined => .error "expected a bitvector, got an undefined value"

end Value
end Bap
