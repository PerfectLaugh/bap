import Bap.Symbolic.Expr
import Bap.Core.Types

namespace Bap.Symbolic

/-- A memory: an unconstrained initial content, identified by `name`, under a list of writes, newest
first. An image is loaded by writing its bytes at their concrete addresses. -/
structure Memory where
  name : String := "mem"
  cells : List (Expr × Expr) := []
  deriving Repr

namespace Memory

def empty : Memory := {}

/-- Two addresses that denote different locations under every assignment. -/
def definitelyDistinct : Expr → Expr → Bool
  | @Expr.const width value, @Expr.const width' value' => !(width == width' && value.toNat == value'.toNat)
  | _, _ => false

/-- Reads an address through a list of writes: the newest write whose address equals the read address
provides the byte, so writes through addresses that are not known to differ guard it with an equality. -/
def readCells (name : String) (address : Expr) : List (Expr × Expr) → Expr
  | [] => .select name address
  | cell :: rest =>
    if Expr.structuralEq cell.1 address then cell.2
    else if definitelyDistinct cell.1 address then readCells name address rest
    else .ite (.app "=" 1 [cell.1, address]) cell.2 (readCells name address rest)

@[simp] theorem readCells_cons_same (name : String) (address value : Expr) (rest : List (Expr × Expr)) :
    readCells name address ((address, value) :: rest) = value := by
  simp [readCells, Expr.eq_of_structuralEq]

def readByte (memory : Memory) (address : Expr) : Expr :=
  readCells memory.name address memory.cells

def writeByte (memory : Memory) (address value : Expr) : Memory :=
  { memory with cells := (address, value) :: memory.cells.filter fun cell => !Expr.structuralEq cell.1 address }

private def offsetAddress (address : Expr) (offset : Nat) : Expr :=
  match address with
  | @Expr.const width value => .const (value + BitVec.ofNat width offset)
  | _ => if offset = 0 then address else .app "bvadd" address.width [address, .const (BitVec.ofNat address.width offset)]

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
