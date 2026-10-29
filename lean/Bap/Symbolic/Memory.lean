import Bap.Symbolic.Expr
import Bap.Core.Types

namespace Bap.Symbolic

structure Memory where
  cells : List (Expr × Expr) := []
  deriving Repr

namespace Memory

def empty : Memory := {}

def readByte (memory : Memory) (address : Expr) : Expr :=
  match memory.cells.find? fun cell => Expr.structuralEq cell.1 address with
  | some cell => cell.2
  | none => .const (BitVec.zero 8)

def writeByte (memory : Memory) (address value : Expr) : Memory :=
  ⟨ (address, value) :: memory.cells.filter fun cell => !Expr.structuralEq cell.1 address ⟩

private def offsetAddress (address : Expr) (offset : Nat) : Expr :=
  if offset = 0 then address else .app "bvadd" address.width [address, .const (BitVec.ofNat address.width offset)]

private def byteAt (value : Expr) (offset : Nat) : Expr :=
  .extract (offset * 8 + 7) (offset * 8) value

def read (memory : Memory) (address : Expr) (endian : Endian) (size : Nat) : Expr :=
  let bytes := (List.range size).map fun offset => readByte memory (offsetAddress address offset)
  let ordered := if endian = Bap.Endian.little then bytes.reverse else bytes
  match ordered with
  | [] => .const (BitVec.zero 0)
  | first :: rest => rest.foldl (fun result byte => .concat result byte) first

def write (memory : Memory) (address value : Expr) (endian : Endian) (size : Nat) : Memory :=
  (List.range size).foldl (init := memory) fun memory offset =>
    let byteOffset := if endian = Bap.Endian.little then offset else size - 1 - offset
    writeByte memory (offsetAddress address offset) (byteAt value byteOffset)

end Memory
end Bap.Symbolic
