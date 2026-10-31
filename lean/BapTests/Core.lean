import BapTests.Support

namespace Bap.Tests.Core

open Bap

/-- The byte by byte meaning of an access, against which what runs is compared. -/
private def bytewise (memory : Memory width) (address : BitVec width) (endian : Endian) (size : Nat) : Nat :=
  let bytes := (List.range size).map fun offset =>
    Memory.readByte memory (address + BitVec.ofNat width offset)
  let ordered : List UInt8 := match endian with
    | .little => bytes.reverse
    | .big => bytes
  ordered.foldl (fun result byte => result * 256 + byte.toNat) 0

/-- `Memory.read` and `Memory.write` compile to their one-page forms, here at the edges of those. -/
private def memoryAccesses : IO Unit := do
  let value : BitVec 64 := 0x0123456789abcdef
  for address in [0, 1, 248, 249, 255, 256, 0x1234, 0xfff8, 0xffff] do
    for endian in [Endian.little, Endian.big] do
      match Memory.write (Memory.empty 64) (BitVec.ofNat 64 address) value endian 8 with
      | .error error => throw <| IO.userError error
      | .ok memory =>
        for at' in [address, address + 3, address + 7] do
          assertEqual s!"read {at'} after write {address}" (bytewise memory (BitVec.ofNat 64 at') endian 8)
            (Memory.read memory (BitVec.ofNat 64 at') endian 8).toNat
        assertEqual s!"write {address} reads back" value.toNat (Memory.read memory (BitVec.ofNat 64 address) endian 8).toNat
  -- what a narrow address space does: the page is bigger than it, so everything wraps
  let narrow := Memory.empty 4
  match Memory.write narrow (BitVec.ofNat 4 14) (0xaabbccdd : BitVec 32) .little 4 with
  | .error error => throw <| IO.userError error
  | .ok memory =>
    assertEqual "a write wraps in a narrow address space" 0xdd (Memory.readByte memory (BitVec.ofNat 4 14)).toNat
    assertEqual "its last byte is past the wrap" 0xaa (Memory.readByte memory (BitVec.ofNat 4 1)).toNat
    assertEqual "a read wraps too" 0xaabbccdd (Memory.read memory (BitVec.ofNat 4 14) .little 4).toNat
  assertEqual "zero bytes read as nothing" 0 (Memory.read (Memory.empty 64) 16 .little 0).toNat
  match Memory.write (Memory.empty 64) 16 (0 : BitVec 0) .little 0 with
  | .ok memory => assertEqual "zero bytes write nothing" 0 memory.pages.size
  | .error error => throw <| IO.userError error
  match Memory.write (Memory.empty 64) 16 (0 : BitVec 8) .little 2 with
  | .ok _ => throw <| IO.userError "a size that doesn't fit the value is an error"
  | .error error => assertEqual "a size that doesn't fit the value" "expected 16 bits, actual 8" error
  -- a page of the wrong size, which only a hand-made memory has, still goes by the general rule
  let short : Memory 64 := ⟨(Std.TreeMap.empty).insert 0 (ByteArray.mk #[1, 2, 3])⟩
  assertEqual "a short page reads zeros past it" 0x0003 (Memory.read short 2 .little 2).toNat
  match Memory.write short 1 (0x7f : BitVec 8) .little 1 with
  | .ok memory =>
    assertEqual "a write to a short page keeps its size" 3 ((memory.pages.get? 0).map (·.size)).get!
    assertEqual "and keeps what it had" 1 (Memory.readByte memory 0).toNat
  | .error error => throw <| IO.userError error
  let region := (Memory.empty 64).writeRegion 250 (ByteArray.mk ((List.range 600).map UInt8.ofNat).toArray)
  assertEqual "a region reads back" (ByteArray.mk ((List.range 600).map UInt8.ofNat).toArray).toList (region.readRegion 250 600).toList

/-- RFC 3394's vector of section 4.1. The specification of `Bap.Proofs.Crypto` is for proofs: it is far too slow to run. -/
private def keyWrap : IO Unit := do
  let kek := ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f]
  let plain := ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]
  let wrapped := ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,
    0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5]
  match Crypto.KeyWrap.unwrap kek wrapped with
  | .ok out => assertEqual "RFC 3394 unwrap" plain.toList out.toList
  | .error error => throw <| IO.userError error
  let bad := ByteArray.mk (wrapped.toList.set 0 0x1e).toArray
  assertTrue "what fails the integrity check isn't unwrapped" (match Crypto.KeyWrap.unwrap kek bad with
    | .ok _ => false
    | .error _ => true)

def run : IO Unit := do
  memoryAccesses
  keyWrap
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
