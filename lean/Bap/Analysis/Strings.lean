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

def strings (image : Bap.Image.Image) (minimum : Nat := 4) : List StringRecord :=
  image.memory.entries.flatMap fun entry =>
    let region := entry.1
    let ascii := (scanAscii minimum region.addr [] [] region.data.toList).map fun result =>
      ⟨result.1, result.2, .ascii⟩
    let little := (scanUtf16 minimum true region.addr [] [] (pairs region.data.toList)).map fun result =>
      ⟨result.1, result.2, .utf16le⟩
    let big := (scanUtf16 minimum false region.addr [] [] (pairs region.data.toList)).map fun result =>
      ⟨result.1, result.2, .utf16be⟩
    ascii ++ little ++ big

end Bap.Analysis.Strings
