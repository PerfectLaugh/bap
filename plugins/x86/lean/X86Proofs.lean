import Lean

namespace X86

structure AddEffects (w : Nat) where
  result : BitVec w
  cf : BitVec 1
  pf : BitVec 1
  af : BitVec 1
  zf : BitVec 1
  sf : BitVec 1
  of : BitVec 1

def msb (x : BitVec w) : BitVec 1 :=
  BitVec.extractLsb' (w - 1) 1 x

def parity (x : BitVec 8) : BitVec 1 :=
  let p1 := x ^^^ BitVec.ushiftRight x 4
  let p2 := p1 ^^^ BitVec.ushiftRight p1 2
  let p3 := p2 ^^^ BitVec.ushiftRight p2 1
  BitVec.ofBool (BitVec.extractLsb' 0 1 p3 == 0#1)

def add (x y : BitVec w) : AddEffects w :=
  let r := x + y
  {
    result := r
    cf := BitVec.ofBool (BitVec.ult r x)
    pf := parity (BitVec.extractLsb' 0 8 r)
    af := BitVec.extractLsb' 4 1 (r ^^^ x ^^^ y)
    zf := BitVec.ofBool (r == 0#w)
    sf := msb r
    of := BitVec.ofBool (msb x == msb y && msb r != msb x)
  }

def add8Result (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 8 x
  let y' := BitVec.extractLsb' 0 8 y
  BitVec.extractLsb' 8 56 x ++ (add x' y').result

def add16Result (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 16 x
  let y' := BitVec.extractLsb' 0 16 y
  BitVec.extractLsb' 16 48 x ++ (add x' y').result

def add32Result (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 32 x
  let y' := BitVec.extractLsb' 0 32 y
  BitVec.zeroExtend 64 (add x' y').result

structure SubEffects (w : Nat) where
  result : BitVec w
  cf : BitVec 1
  pf : BitVec 1
  af : BitVec 1
  zf : BitVec 1
  sf : BitVec 1
  of : BitVec 1

def sub (x y : BitVec w) : SubEffects w :=
  let r := x - y
  {
    result := r
    cf := msb ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& r))
    pf := parity (BitVec.extractLsb' 0 8 r)
    af := BitVec.extractLsb' 4 1 (r ^^^ x ^^^ y)
    zf := BitVec.ofBool (r == 0#w)
    sf := msb r
    of := msb ((x ^^^ y) &&& (x ^^^ r))
  }

structure LogicEffects (w : Nat) where
  result : BitVec w
  cf : BitVec 1
  pf : BitVec 1
  zf : BitVec 1
  sf : BitVec 1
  of : BitVec 1

def logic (r : BitVec w) : LogicEffects w :=
  {
    result := r
    cf := 0#1
    pf := parity (BitVec.extractLsb' 0 8 r)
    zf := BitVec.ofBool (r == 0#w)
    sf := msb r
    of := 0#1
  }

def logicalAnd (x y : BitVec w) : LogicEffects w := logic (x &&& y)
def logicalOr (x y : BitVec w) : LogicEffects w := logic (x ||| y)
def logicalXor (x y : BitVec w) : LogicEffects w := logic (x ^^^ y)

def result8 (f : BitVec 8 -> BitVec 8 -> BitVec 8) (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 8 x
  let y' := BitVec.extractLsb' 0 8 y
  BitVec.extractLsb' 8 56 x ++ f x' y'

def result16 (f : BitVec 16 -> BitVec 16 -> BitVec 16) (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 16 x
  let y' := BitVec.extractLsb' 0 16 y
  BitVec.extractLsb' 16 48 x ++ f x' y'

def result32 (f : BitVec 32 -> BitVec 32 -> BitVec 32) (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 32 x
  let y' := BitVec.extractLsb' 0 32 y
  BitVec.zeroExtend 64 (f x' y')

example (x y : BitVec 64) : (add x y).result = x + y := by rfl
example (x y : BitVec 64) : (add x y).zf = BitVec.ofBool (x + y == 0#64) := by rfl
example (x : BitVec 64) : add32Result x 0#64 = BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 x) := by
  simp [add32Result, add]

end X86
