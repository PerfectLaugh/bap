import Bap.Core.Types

namespace Bap.IO.Reader

def get8 (data : ByteArray) (offset : Nat) : Except String Nat := do
  if offset ≥ data.size then
    .error s!"read past end of input at {offset}"
  else
    .ok (data.get! offset).toNat

private def readLoop (data : ByteArray) (endian : Endian) (offset count : Nat) :
    Nat → Nat → Except String Nat
  | 0, result => .ok result
  | index + 1, result => do
    let byte ← get8 data (offset + index)
    let result := match endian with
      | .little => result + byte * 256 ^ index
      | .big => result + byte * 256 ^ (count - index - 1)
    readLoop data endian offset count index result

def read (data : ByteArray) (endian : Endian) (offset count : Nat) : Except String Nat := do
  if offset + count > data.size then
    .error s!"{count}-byte read past end of input at {offset}"
  else
    readLoop data endian offset count count 0

def u16 (data : ByteArray) (endian : Endian) (offset : Nat) : Except String Nat := read data endian offset 2
def u32 (data : ByteArray) (endian : Endian) (offset : Nat) : Except String Nat := read data endian offset 4
def u64 (data : ByteArray) (endian : Endian) (offset : Nat) : Except String Nat := read data endian offset 8

def slice (data : ByteArray) (offset size : Nat) : Except String ByteArray := do
  if offset + size > data.size then
    .error s!"slice past end of input at {offset} with size {size}"
  else
    .ok (data.extract offset (offset + size))

def cstring (data : ByteArray) (offset : Nat) : Except String String := do
  let rec loop (index : Nat) (chars : List Char) : Except String String := do
    if offset + index ≥ data.size then
      .error "unterminated string"
    else
      let byte := (data.get! (offset + index)).toNat
      if byte = 0 then
        .ok (String.ofList chars.reverse)
      else
        loop (index + 1) (Char.ofNat byte :: chars)
  loop 0 []

/-- The first zero from `index` that is before `limit`, of the `fuel` bytes from there. -/
def zeroFrom (data : ByteArray) (limit : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, index =>
    if index < limit then
      if data.get! index = 0 then some index else zeroFrom data limit fuel (index + 1)
    else none

/-- Where the string at `offset` ends: at its zero, which is before `stop` and in the input. Nothing is made to say so. -/
def cstringEnd (data : ByteArray) (offset stop : Nat) : Option Nat :=
  zeroFrom data (min stop data.size) (min stop data.size - offset) offset

/-- The string at `offset` of a table that ends at `stop`: what `cstring` reads, of a string that ends in its table
(`Bap.Proofs.IO.cstring_of_cstringIn`), and nothing of the input past the table is looked at. -/
def cstringIn (data : ByteArray) (offset stop : Nat) : Except String String :=
  match cstringEnd data offset stop with
  | none => .error "unterminated string"
  | some finish =>
    .ok (String.ofList ((List.range (finish - offset)).map fun index => Char.ofNat (data.get! (offset + index)).toNat))

end Bap.IO.Reader
