import BapTests.Support

namespace Bap.Tests.Core

open Bap

def run : IO Unit := do
  let input := " ; comment\n(bil ((special \"hello\\nworld\")))"
  let parsed ← match Sexp.parse input with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  let reparsed ← match Sexp.parse (toString parsed) with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  assertEqual "S-expression parse/render round trip" parsed reparsed
  assertEqual "four-bit wraparound" 1 (BitVec.ofNat 4 15 + BitVec.ofNat 4 2).toNat
  assertEqual "wide bitvector normalization" 0 (BitVec.ofNat 128 (2 ^ 128)).toNat
  assertEqual "unsigned division by zero" 15 (Word.udiv (BitVec.ofNat 4 7) 0).toNat
  assertEqual "unsigned remainder by zero" 7 (Word.urem (BitVec.ofNat 4 7) 0).toNat
  assertEqual "left shift" 0xc4 (Word.shl (BitVec.ofNat 8 0xb1) (BitVec.ofNat 8 2)).toNat
  assertEqual "arithmetic right shift" 0xec
    (Word.ashr (BitVec.ofNat 8 0xb1) (BitVec.ofNat 8 2)).toNat
  assertEqual "BAP signed modulus" 2
    (Word.smod (BitVec.ofNat 8 5) (BitVec.ofNat 8 0xfd)).toNat
  let memory := Memory.empty 32
  let address := BitVec.ofNat 32 0x1000
  let value := BitVec.ofNat 32 0xdeadbeef
  let little ← match Memory.write memory address value .little 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let big ← match Memory.write memory address value .big 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  assertEqual "little-endian read-after-write" value.toNat (Memory.read little address .little 4).toNat
  assertEqual "big-endian read-after-write" value.toNat (Memory.read big address .big 4).toNat
  assertEqual "opposite-endian read" 0xefbeadde (Memory.read little address .big 4).toNat
  assertEqual "memory default byte" 0 (Memory.readByte memory address).toNat

end Bap.Tests.Core
