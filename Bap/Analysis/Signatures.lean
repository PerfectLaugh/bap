import Bap.Image.Basic
import Bap.Bil.Wire

namespace Bap.Analysis.Signatures

structure Signature where
  name : String
  data : ByteArray
  mask : ByteArray
  deriving DecidableEq

def create (name : String) (data mask : ByteArray) : Except String Signature := do
  if data.isEmpty then
    .error "signature is empty"
  else if data.size != mask.size then
    .error "signature data and mask have different lengths"
  else
    .ok ⟨name, data, mask⟩

def matchesAt (signature : Signature) (data : ByteArray) (offset : Nat) : Bool :=
  if offset + signature.data.size > data.size then false
  else
    (List.range signature.data.size).all fun index =>
      data[offset + index]!.toNat &&& signature.mask[index]!.toNat =
        signature.data[index]!.toNat &&& signature.mask[index]!.toNat

def find (image : Bap.Image.Image) (signature : Signature) : List Nat :=
  image.memory.entries.flatMap fun entry =>
    let region := entry.1
    if signature.data.size > region.data.size then []
    else
      (List.range (region.data.size - signature.data.size + 1)).filterMap fun offset =>
        if matchesAt signature region.data offset then some (region.addr + offset) else none

private def hexByte (value : UInt8) : String :=
  let digits := String.ofList (Nat.toDigits 16 value.toNat)
  if digits.length < 2 then "0" ++ digits else digits

private def encodeBytes (data : ByteArray) : Sexp :=
  .list (data.toList.map fun byte => .atom (hexByte byte))

private def decodeBytes (input : Sexp) : Except String ByteArray := do
  let atoms ← Sexp.asList input
  let values ← atoms.mapM fun atom => do
    let atom ← Sexp.asAtom atom
    Bil.Wire.parseHex atom
  if values.any fun value => value ≥ 256 then
    .error "signature byte is out of range"
  else
    .ok (ByteArray.mk (values.map UInt8.ofNat).toArray)

private def encode (signature : Signature) : Sexp :=
  .tagged "signature" [.atom signature.name, encodeBytes signature.data, encodeBytes signature.mask]

private def decode (input : Sexp) : Except String Signature := do
  let args ← Sexp.expectTagged "signature" 3 input
  match args with
  | [name, data, mask] =>
    let name ← Sexp.asAtom name
    let data ← decodeBytes data
    let mask ← decodeBytes mask
    create name data mask
  | _ => .error "invalid signature"

def save (signatures : List Signature) (path : String) : IO Unit :=
  IO.FS.writeFile path (toString (Sexp.list (signatures.map encode)))

def load (path : String) : IO (List Signature) := do
  let input ← IO.FS.readFile path
  match Sexp.parse input with
  | .error error => throw <| IO.userError error
  | .ok input =>
    match Sexp.asList input with
    | .error error => throw <| IO.userError error
    | .ok items =>
      let rec decodeAll : List Sexp → IO (List Signature)
        | [] => pure []
        | item :: rest => do
          match decode item with
          | .error error => throw <| IO.userError error
          | .ok signature => pure (signature :: (← decodeAll rest))
      decodeAll items

end Bap.Analysis.Signatures
