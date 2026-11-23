import Bap.Image.Basic

namespace Bap.Analysis.Strings

inductive Encoding where
  | ascii | utf16le | utf16be
  deriving DecidableEq, Repr

structure StringRecord where
  address : Nat
  text : String
  encoding : Encoding
  deriving DecidableEq, Repr

private def printable (byte : UInt8) : Bool := 0x20 ≤ byte.toNat && byte.toNat ≤ 0x7e

private def finish (minimum width : Nat) (next : Nat) (chars : List Char) (results : List (Nat × String)) :=
  if chars.length ≥ minimum then (next - chars.length * width, String.ofList chars) :: results else results

private def scanAscii (minimum : Nat) (next : Nat) (chars : List Char) (results : List (Nat × String)) :
    List UInt8 → List (Nat × String)
  | [] => (finish minimum 1 next chars results).reverse
  | byte :: rest =>
    if printable byte then
      scanAscii minimum (next + 1) (chars ++ [Char.ofNat byte.toNat]) results rest
    else
      scanAscii minimum (next + 1) [] (finish minimum 1 next chars results) rest

/-! What runs of `scanAscii`, and of `scanUtf16` below, keeps the characters of a run newest first, so that a run costs its
length rather than its square, which adding each at the end does: a megabyte of text without a byte that isn't printable is 10^12
steps of that. What is proved of the scans is of them as they are written. -/

private def finishReversed (minimum width : Nat) (next : Nat) (reversed : List Char) (results : List (Nat × String)) :=
  if reversed.length ≥ minimum then (next - reversed.length * width, String.ofList reversed.reverse) :: results else results

private theorem finishReversed_eq (minimum width next : Nat) (reversed : List Char) (results : List (Nat × String)) :
    finishReversed minimum width next reversed results = finish minimum width next reversed.reverse results := by
  simp [finishReversed, finish]

private def scanAsciiReversed (minimum : Nat) (next : Nat) (reversed : List Char) (results : List (Nat × String)) :
    List UInt8 → List (Nat × String)
  | [] => (finishReversed minimum 1 next reversed results).reverse
  | byte :: rest =>
    if printable byte then
      scanAsciiReversed minimum (next + 1) (Char.ofNat byte.toNat :: reversed) results rest
    else
      scanAsciiReversed minimum (next + 1) [] (finishReversed minimum 1 next reversed results) rest

private theorem scanAsciiReversed_eq (minimum : Nat) (bytes : List UInt8) :
    ∀ (next : Nat) (reversed : List Char) (results : List (Nat × String)),
      scanAsciiReversed minimum next reversed results bytes = scanAscii minimum next reversed.reverse results bytes := by
  induction bytes with
  | nil => intro next reversed results; simp [scanAsciiReversed, scanAscii, finishReversed_eq]
  | cons byte rest ih =>
    intro next reversed results
    simp only [scanAsciiReversed, scanAscii, finishReversed_eq, ih, List.reverse_cons, List.reverse_nil]

private def scanAsciiFast (minimum : Nat) (next : Nat) (chars : List Char) (results : List (Nat × String))
    (bytes : List UInt8) : List (Nat × String) :=
  scanAsciiReversed minimum next chars.reverse results bytes

@[csimp] private theorem scanAscii_eq_fast : @scanAscii = @scanAsciiFast := by
  funext minimum next chars results bytes
  simp [scanAsciiFast, scanAsciiReversed_eq]

private def pairs : List UInt8 → List (UInt8 × UInt8)
  | first :: second :: rest => (first, second) :: pairs rest
  | _ => []

private def decodePair (little : Bool) (first second : UInt8) : Option Char :=
  if little then
    if second = 0 && printable first then some (Char.ofNat first.toNat) else none
  else
    if first = 0 && printable second then some (Char.ofNat second.toNat) else none

private def scanUtf16 (minimum : Nat) (little : Bool) (next : Nat) (chars : List Char)
    (results : List (Nat × String)) : List (UInt8 × UInt8) → List (Nat × String)
  | [] => (finish minimum 2 next chars results).reverse
  | (first, second) :: rest =>
    match decodePair little first second with
    | some char => scanUtf16 minimum little (next + 2) (chars ++ [char]) results rest
    | none => scanUtf16 minimum little (next + 2) [] (finish minimum 2 next chars results) rest

private def scanUtf16Reversed (minimum : Nat) (little : Bool) (next : Nat) (reversed : List Char)
    (results : List (Nat × String)) : List (UInt8 × UInt8) → List (Nat × String)
  | [] => (finishReversed minimum 2 next reversed results).reverse
  | (first, second) :: rest =>
    match decodePair little first second with
    | some char => scanUtf16Reversed minimum little (next + 2) (char :: reversed) results rest
    | none => scanUtf16Reversed minimum little (next + 2) [] (finishReversed minimum 2 next reversed results) rest

private theorem scanUtf16Reversed_eq (minimum : Nat) (little : Bool) (units : List (UInt8 × UInt8)) :
    ∀ (next : Nat) (reversed : List Char) (results : List (Nat × String)),
      scanUtf16Reversed minimum little next reversed results units =
        scanUtf16 minimum little next reversed.reverse results units := by
  induction units with
  | nil => intro next reversed results; simp [scanUtf16Reversed, scanUtf16, finishReversed_eq]
  | cons unit rest ih =>
    intro next reversed results
    obtain ⟨first, second⟩ := unit
    simp only [scanUtf16Reversed, scanUtf16, finishReversed_eq]
    cases decodePair little first second <;> simp [ih]

private def scanUtf16Fast (minimum : Nat) (little : Bool) (next : Nat) (chars : List Char)
    (results : List (Nat × String)) (units : List (UInt8 × UInt8)) : List (Nat × String) :=
  scanUtf16Reversed minimum little next chars.reverse results units

@[csimp] private theorem scanUtf16_eq_fast : @scanUtf16 = @scanUtf16Fast := by
  funext minimum little next chars results units
  simp [scanUtf16Fast, scanUtf16Reversed_eq]

/-- Whether `new` is the better reading of bytes that `old` reads too: the longer, or of the same length the one at an even
address, where a string of 16-bit units is put. -/
private def better (new old : StringRecord) : Bool :=
  new.text.length > old.text.length || (new.text.length == old.text.length && new.address % 2 == 0 && old.address % 2 != 0)

/-- Of readings by address, those that share no byte with a better one before or after: the same bytes read as of the other byte
order, or from the other byte of a unit, are a shorter string of the same text or the same one a byte apart. -/
private def disjoint : List StringRecord → List StringRecord → List StringRecord
  | kept, [] => kept.reverse
  | [], record :: rest => disjoint [record] rest
  | last :: kept, record :: rest =>
    if record.address < last.address + 2 * last.text.length then
      disjoint ((if better record last then record else last) :: kept) rest
    else disjoint (record :: last :: kept) rest

/-- The strings of an image: of ASCII, and of UTF-16 of either byte order, which may start at any byte of a region. -/
def strings (image : Bap.Image.Image) (minimum : Nat := 4) : List StringRecord :=
  image.memory.entries.flatMap fun entry =>
    let region := entry.1
    let bytes := region.data.toList
    let ascii := (scanAscii minimum region.addr [] [] bytes).map fun result =>
      ⟨result.1, result.2, .ascii⟩
    let wide := [(true, 0), (false, 0), (true, 1), (false, 1)].flatMap fun (little, skip) =>
      if skip ≤ bytes.length then
        (scanUtf16 minimum little (region.addr + skip) [] [] (pairs (bytes.drop skip))).map fun result =>
          (⟨result.1, result.2, if little then .utf16le else .utf16be⟩ : StringRecord)
      else []
    ascii ++ disjoint [] (wide.mergeSort fun a b => a.address ≤ b.address)

end Bap.Analysis.Strings
