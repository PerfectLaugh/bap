import Bap.Core.Types
import Bap.Core.Word
import Std.Data.HashMap

namespace Bap

structure Memory (addressWidth : Nat) where
  pages : Std.HashMap Nat ByteArray := {}

namespace Memory

def pageSize : Nat := 256

instance : Repr (Memory addressWidth) where
  reprPrec memory _ := s!"memory({memory.pages.size} pages)"

def empty (addressWidth : Nat) : Memory addressWidth := ⟨{}⟩

def cells (memory : Memory addressWidth) : List (BitVec addressWidth × UInt8) :=
  memory.pages.toList.flatMap fun entry =>
    let base := entry.1 * pageSize
    (List.range entry.2.size).filterMap fun offset =>
      let byte := entry.2[offset]!
      if byte = 0 then none else some (BitVec.ofNat addressWidth (base + offset), byte)

def readByte (memory : Memory addressWidth) (address : BitVec addressWidth) : UInt8 :=
  let address := address.toNat
  match memory.pages.get? (address / pageSize) with
  | some page => page[address % pageSize]!
  | none => 0

def writeByte (memory : Memory addressWidth) (address : BitVec addressWidth) (value : UInt8) :
    Memory addressWidth :=
  let address := address.toNat
  let index := address / pageSize
  let page := (memory.pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
  ⟨memory.pages.insert index (page.set! (address % pageSize) value)⟩

def ofCells (cells : List (BitVec addressWidth × UInt8)) : Memory addressWidth :=
  cells.foldl (init := empty addressWidth) fun memory cell => writeByte memory cell.1 cell.2

private partial def writePages (pages : Std.HashMap Nat ByteArray) (address : Nat)
    (data : ByteArray) (offset : Nat) : Std.HashMap Nat ByteArray :=
  if offset ≥ data.size then pages else
    let absolute := address + offset
    let index := absolute / pageSize
    let pageOffset := absolute % pageSize
    let count := min (pageSize - pageOffset) (data.size - offset)
    let chunk := data.extract offset (offset + count)
    let page := if count = pageSize then chunk else
      let existing := (pages.get? index).getD (ByteArray.mk (List.replicate pageSize 0).toArray)
      existing.extract 0 pageOffset ++ chunk ++ existing.extract (pageOffset + count) pageSize
    writePages (pages.insert index page) address data (offset + count)

def writeRegion (memory : Memory addressWidth) (address : Nat) (data : ByteArray) : Memory addressWidth :=
  ⟨writePages memory.pages address data 0⟩

private def byteAt (value : Nat) (offset : Nat) : UInt8 :=
  UInt8.ofNat ((value / 256 ^ offset) % 256)

def write (memory : Memory addressWidth) (address : BitVec addressWidth)
    (value : BitVec valueWidth) (endian : Endian) (size : Nat) :
    Except String (Memory addressWidth) := do
  if size * 8 ≠ valueWidth then
    .error s!"expected {size * 8} bits, actual {valueWidth}"
  else
    .ok <| (List.range size).foldl (init := memory) fun result offset =>
      let byteOffset := match endian with
        | .little => offset
        | .big => size - 1 - offset
      let nextAddress := address + BitVec.ofNat addressWidth offset
      writeByte result nextAddress (byteAt value.toNat byteOffset)

def read (memory : Memory addressWidth) (address : BitVec addressWidth)
    (endian : Endian) (size : Nat) : BitVec (size * 8) :=
  let bytes := (List.range size).map fun offset =>
    readByte memory (address + BitVec.ofNat addressWidth offset)
  let ordered := match endian with
    | .little => bytes.reverse
    | .big => bytes
  let value := ordered.foldl (fun result byte => result * 256 + byte.toNat) 0
  BitVec.ofNat (size * 8) value

end Memory

inductive Value where
  | bits {width : Nat} (value : BitVec width)
  | memory {addressWidth : Nat} (value : Memory addressWidth)
  | undefined
  deriving Repr

namespace Value

def type : Value → Typ
  | @Value.bits width _ => .imm width
  | @Value.memory addressWidth _ => .mem addressWidth 8
  | .undefined => .unknown

def asBits : Value → Except String (Σ width, BitVec width)
  | .bits value => .ok ⟨_, value⟩
  | .memory _ => .error "expected a bitvector, got memory"
  | .undefined => .error "expected a bitvector, got an undefined value"

end Value
end Bap
