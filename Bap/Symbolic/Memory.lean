import Bap.Symbolic.Expr
import Bap.Core.Types

namespace Bap.Symbolic

/-- A memory: an unconstrained initial content, identified by `name`, under a list of writes, newest
first. An image is loaded by writing its bytes at their concrete addresses. -/
structure Memory where
  name : String := "mem"
  /-- A memory chosen by a condition: its initial contents are those of one of two others. -/
  branch : Option (Expr × Memory × Memory) := none
  cells : List (Expr × Expr) := []
  deriving Repr

namespace Memory

def empty : Memory := {}

/-- An address as a base expression and a constant offset, modulo the size of the address space. -/
def baseOffset : Expr → Expr × Nat
  | e@(.app "bvadd" width [base, @Expr.const constWidth value]) =>
    if constWidth = width ∧ base.width = width then
      let (inner, offset) := baseOffset base
      (inner, (offset + value.toNat) % 2 ^ width)
    else (e, 0)
  | e@(.app "bvsub" width [base, @Expr.const constWidth value]) =>
    if constWidth = width ∧ base.width = width then
      let (inner, offset) := baseOffset base
      (inner, (offset + (2 ^ width - value.toNat)) % 2 ^ width)
    else (e, 0)
  | e => (e, 0)

/-- Two addresses that denote different locations under every assignment: different widths, different constants,
or different offsets from one base. Comparing addresses of different widths would not be well sorted. -/
def definitelyDistinct : Expr → Expr → Bool
  | @Expr.const width value, @Expr.const width' value' => !(width == width' && value.toNat == value'.toNat)
  | left, right =>
    let (leftBase, leftOffset) := baseOffset left
    let (rightBase, rightOffset) := baseOffset right
    left.width != right.width || (leftOffset != rightOffset && Expr.structuralEq leftBase rightBase)

/-- Reads an address through a list of writes: the newest write whose address equals the read address
provides the byte, so writes through addresses that are not known to differ guard it with an equality. -/
def readCells (initial address : Expr) : List (Expr × Expr) → Expr
  | [] => initial
  | cell :: rest =>
    if Expr.structuralEq cell.1 address then cell.2
    else if definitelyDistinct cell.1 address then readCells initial address rest
    else .ite (.app "=" 1 [cell.1, address]) cell.2 (readCells initial address rest)

@[simp] theorem readCells_cons_same (initial address value : Expr) (rest : List (Expr × Expr)) :
    readCells initial address ((address, value) :: rest) = value := by
  simp [readCells, Expr.eq_of_structuralEq]

/-- The byte a memory holds at an address before any of its own writes. -/
def readInitial : Memory → Expr → Expr
  | ⟨name, none, _⟩, address => .select name address
  | ⟨_, some (condition, yes, no), _⟩, address =>
    .ite condition (readCells (readInitial yes address) address yes.cells)
      (readCells (readInitial no address) address no.cells)

def readByte (memory : Memory) (address : Expr) : Expr :=
  readCells (readInitial memory address) address memory.cells

def writeByte (memory : Memory) (address value : Expr) : Memory :=
  { memory with cells := (address, value) :: memory.cells.filter fun cell => !Expr.structuralEq cell.1 address }

private def offsetAddress (address : Expr) (offset : Nat) : Expr :=
  match address with
  | @Expr.const width value => .const (value + BitVec.ofNat width offset)
  | _ => if offset = 0 then address else .app "bvadd" address.width [address, .const (BitVec.ofNat address.width offset)]

private def byteAt (value : Expr) (offset : Nat) : Expr :=
  .extract (offset * 8 + 7) (offset * 8) value

/-- The bytes of a read, most significant first. -/
def readBytes (memory : Memory) (address : Expr) (endian : Endian) (size : Nat) : List Expr :=
  let bytes := (List.range size).map fun offset => readByte memory (offsetAddress address offset)
  if endian = Bap.Endian.little then bytes.reverse else bytes

/-- The value of a read, which has `size` bytes: reading none has no value, as SMT-LIB has no empty sort. -/
def read (memory : Memory) (address : Expr) (endian : Endian) (size : Nat) : Except String Expr :=
  match readBytes memory address endian size with
  | [] => .error "a load must have at least one byte"
  | first :: rest => .ok (rest.foldl (fun result byte => .concat result byte) first)

def write (memory : Memory) (address value : Expr) (endian : Endian) (size : Nat) : Memory :=
  (List.range size).foldl (init := memory) fun memory offset =>
    let byteOffset := if endian = Bap.Endian.little then offset else size - 1 - offset
    writeByte memory (offsetAddress address offset) (byteAt value byteOffset)

end Memory
end Bap.Symbolic
