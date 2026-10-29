import Bap.Core.Types
import Bap.Core.Word

namespace Bap

structure Memory (addressWidth : Nat) where
  cells : List (BitVec addressWidth × UInt8) := []
  deriving Repr

namespace Memory

def empty (addressWidth : Nat) : Memory addressWidth := ⟨[]⟩

def readByte (memory : Memory addressWidth) (address : BitVec addressWidth) : UInt8 :=
  match memory.cells.find? fun cell => cell.1 == address with
  | some cell => cell.2
  | none => 0

def writeByte (memory : Memory addressWidth) (address : BitVec addressWidth) (value : UInt8) :
    Memory addressWidth :=
  ⟨ (address, value) :: memory.cells.filter fun cell => cell.1 != address ⟩

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

@[simp] theorem readByte_writeByte_same
    (memory : Memory addressWidth) (address : BitVec addressWidth) (value : UInt8) :
    readByte (writeByte memory address value) address = value := by
  simp [readByte, writeByte]

theorem readByte_empty (address : BitVec addressWidth) :
    readByte (empty addressWidth) address = 0 := by
  rfl

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
