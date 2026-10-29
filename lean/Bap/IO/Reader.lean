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

end Bap.IO.Reader
