import Bap.Crypto.AES

namespace Bap.Crypto.KeyWrap

private def defaultIv : List UInt8 := List.replicate 8 (UInt8.ofNat 0xa6)

private def xorByte (left right : UInt8) : UInt8 := UInt8.ofNat (left.toNat ^^^ right.toNat)

private def tBytes (value : Nat) : List UInt8 :=
  (List.range 8).map fun index => UInt8.ofNat (value / 256 ^ (7 - index) % 256)

private def xorT (a : List UInt8) (t : Nat) : List UInt8 :=
  (a.zip (tBytes t)).map fun pair => xorByte pair.1 pair.2

private def replaceAt (values : List (List UInt8)) (index : Nat) (value : List UInt8) : List (List UInt8) :=
  (List.range values.length).map fun current => if current = index then value else values[current]!

def unwrap (key input : ByteArray) : Except String ByteArray := do
  if input.size < 24 || input.size % 8 != 0 then
    .error "RFC 3394 input must be at least 24 bytes and 8-byte aligned"
  else
    let n := input.size / 8 - 1
    let data := input.toList
    let initialA := data.take 8
    let initialR := (List.range n).map fun index => data.drop (8 + index * 8) |>.take 8
    let rec round (remaining : Nat) (j : Nat) (a : List UInt8) (r : List (List UInt8)) :
        Except String (List UInt8 × List (List UInt8)) := do
      if remaining = 0 then
        .ok (a, r)
      else
        let rec item (i : Nat) (a : List UInt8) (r : List (List UInt8)) :
            Except String (List UInt8 × List (List UInt8)) := do
          let t := n * j + i + 1
          let block := ByteArray.mk ((xorT a t ++ r[i]!).toArray)
          let decrypted ← AES.decryptBlock key block
          let nextA := decrypted.toList.take 8
          let nextR := replaceAt r i (decrypted.toList.drop 8)
          if i = 0 then .ok (nextA, nextR) else item (i - 1) nextA nextR
        let (a, r) ← item (n - 1) a r
        if j = 0 then .ok (a, r) else round (remaining - 1) (j - 1) a r
    let (a, r) ← round 6 5 initialA initialR
    if a != defaultIv then
      .error "RFC 3394 integrity check failed"
    else
      .ok (ByteArray.mk r.flatten.toArray)

end Bap.Crypto.KeyWrap
