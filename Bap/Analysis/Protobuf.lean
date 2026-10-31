import Bap.Core.Types

namespace Bap.Analysis.Protobuf

inductive Value where
  | varint (value : Nat)
  | bytes (value : ByteArray)
  deriving DecidableEq

structure Field where
  number : Nat
  wire : Nat
  value : Value
  deriving DecidableEq

private def varint (data : ByteArray) (offset : Nat) : Except String (Nat × Nat) := do
  let rec loop (shift : Nat) (offset : Nat) (value : Nat) : Except String (Nat × Nat) := do
    if shift > 63 then
      .error "oversized protobuf varint"
    else if offset ≥ data.size then
      .error "truncated protobuf varint"
    else
      let byte := data[offset]!.toNat
      let value := value + (byte % 128) * 2 ^ shift
      if value ≥ 2 ^ 64 then
        .error "protobuf varint exceeds 64 bits"
      else if byte < 128 then
        .ok (value, offset + 1)
      else
        loop (shift + 7) (offset + 1) value
  loop 0 offset 0

def fields (data : ByteArray) : Except String (List Field) := do
  let rec loop (fuel : Nat) (offset : Nat) (result : List Field) : Except String (List Field) := do
    match fuel with
    | 0 => .error "too many protobuf fields"
    | fuel + 1 =>
      if offset ≥ data.size then
        .ok result.reverse
      else
        let (tag, offset) ← varint data offset
        let number := tag / 8
        let wire := tag % 8
        if number = 0 then
          .error "protobuf field zero"
        else if number ≥ 2 ^ 29 then
          .error "protobuf field number above 2^29 - 1"
        else
          match wire with
          | 0 =>
            let (value, offset) ← varint data offset
            loop fuel offset (⟨number, wire, .varint value⟩ :: result)
          | 1 =>
            if offset + 8 > data.size then .error "truncated fixed64 field"
            else loop fuel (offset + 8) (⟨number, wire, .bytes (data.extract offset (offset + 8))⟩ :: result)
          | 2 =>
            let (size, offset) ← varint data offset
            if offset + size > data.size then .error "truncated length-delimited field"
            else loop fuel (offset + size) (⟨number, wire, .bytes (data.extract offset (offset + size))⟩ :: result)
          | 5 =>
            if offset + 4 > data.size then .error "truncated fixed32 field"
            else loop fuel (offset + 4) (⟨number, wire, .bytes (data.extract offset (offset + 4))⟩ :: result)
          | _ => .error s!"unsupported protobuf wire type {wire}"
  loop (data.size + 1) 0 []

structure SignedPbiData where
  payload : ByteArray
  signature : ByteArray
  unsignedFields : List Field

def validateSignedPbiData (data : ByteArray) : Except String SignedPbiData := do
  let top ← fields data
  match top with
  | [first, second] =>
    if first.number != 1 || first.wire != 2 || second.number != 2 || second.wire != 2 then
      .error "SignedPbiData must contain exactly bytes fields 1 and 2"
    else
      match first.value, second.value with
      | .bytes payload, .bytes signature =>
        if payload.size = 0 || signature.size = 0 then
          .error "SignedPbiData payload and signature must be non-empty"
        else
          let inner ← fields payload
          if inner.isEmpty then .error "UnsignedPbiData payload has no fields"
          else .ok ⟨payload, signature, inner⟩
      | _, _ => .error "SignedPbiData fields must be length-delimited"
  | _ => .error "SignedPbiData must contain exactly bytes fields 1 and 2"

end Bap.Analysis.Protobuf
