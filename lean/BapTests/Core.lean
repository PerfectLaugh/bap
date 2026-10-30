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
  let large := String.ofList (List.replicate 100000 'a')
  let parsedLarge ← match Sexp.parse large with
    | .ok value => pure value
    | .error error => throw <| IO.userError error
  assertEqual "large S-expression atom" (Sexp.atom large) parsedLarge
  assertEqual "four-bit wraparound" 1 (BitVec.ofNat 4 15 + BitVec.ofNat 4 2).toNat
  assertEqual "wide bitvector normalization" 0 (BitVec.ofNat 128 (2 ^ 128)).toNat
  assertEqual "unsigned division by zero" 15 (Word.udiv (BitVec.ofNat 4 7) 0).toNat
  assertEqual "unsigned remainder by zero" 7 (Word.urem (BitVec.ofNat 4 7) 0).toNat
  assertEqual "left shift" 0xc4 (Word.shl (BitVec.ofNat 8 0xb1) (BitVec.ofNat 8 2)).toNat
  assertEqual "arithmetic right shift" 0xec
    (Word.ashr (BitVec.ofNat 8 0xb1) (BitVec.ofNat 8 2)).toNat
  assertEqual "signed modulus follows the divisor" 0xff
    (Word.smod (BitVec.ofNat 8 5) (BitVec.ofNat 8 0xfd)).toNat
  assertEqual "signed modulus of negative dividend" 2
    (Word.smod (BitVec.ofInt 8 (-7)) (BitVec.ofNat 8 3)).toNat
  assertEqual "signed modulus by zero keeps the dividend" 0xff
    (Word.smod (BitVec.ofInt 8 (-1)) 0).toNat
  assertEqual "signed modulus of both negative" 0xff
    (Word.smod (BitVec.ofInt 8 (-7)) (BitVec.ofInt 8 (-3))).toNat
  [Sexp.atom "'a", .atom "'", .atom "", .atom "a'b", .atom "a b", .atom "a\"b\\c\n", .list [.atom "'x", .list []]].forM
    fun value => do
      let parsed ← match Sexp.parse (toString value) with
        | .ok parsed => pure parsed
        | .error error => throw <| IO.userError error
      assertEqual s!"S-expression round trip {value}" value parsed
  let memory := Memory.empty 32
  let address := BitVec.ofNat 32 0x1000
  let value := BitVec.ofNat 32 0xdeadbeef
  let little ← match Memory.write memory address value .little 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let big ← match Memory.write memory address value .big 4 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  let top := BitVec.ofNat 16 0xffff
  let wrapped ← match Memory.write (Memory.empty 16) top (BitVec.ofNat 16 0x1234) .little 2 with
    | .ok memory => pure memory
    | .error error => throw <| IO.userError error
  assertEqual "read-after-write across the address-space top" 0x1234 (Memory.read wrapped top .little 2).toNat
  assertEqual "wrapped byte lands at address zero" 0x12 (Memory.readByte wrapped (BitVec.ofNat 16 0)).toNat
  assertEqual "region reads wrap too" [0x34, 0x12] ((Memory.readRegion wrapped 0xffff 2).toList.map (·.toNat))
  let region := ByteArray.mk ((List.range 600).map (fun i => UInt8.ofNat i)).toArray
  let regionMemory : Memory 16 := Memory.writeRegion (Memory.empty 16) 0xff00 region
  assertEqual "large wrapped region round trip" region.toList
    (Memory.readRegion regionMemory 0xff00 600).toList
  let narrow : Memory 4 := Memory.writeRegion (Memory.empty 4) 15 (ByteArray.mk #[1, 2])
  assertEqual "region wraps in a space smaller than a page" [1, 2]
    ((Memory.readRegion narrow 15 2).toList.map (·.toNat))
  assertEqual "little-endian read-after-write" value.toNat (Memory.read little address .little 4).toNat
  assertEqual "big-endian read-after-write" value.toNat (Memory.read big address .big 4).toNat
  assertEqual "opposite-endian read" 0xefbeadde (Memory.read little address .big 4).toNat
  assertEqual "memory default byte" 0 (Memory.readByte memory address).toNat

end Bap.Tests.Core
