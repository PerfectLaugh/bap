import Lean

namespace Lifter

def add (x y : BitVec w) : BitVec w := x + y
def sub (x y : BitVec w) : BitVec w := x - y
def logicalAnd (x y : BitVec w) : BitVec w := x &&& y
def logicalOr (x y : BitVec w) : BitVec w := x ||| y
def logicalXor (x y : BitVec w) : BitVec w := x ^^^ y

def result32 (f : BitVec 32 -> BitVec 32 -> BitVec 32)
    (x y : BitVec 64) : BitVec 64 :=
  let x' := BitVec.extractLsb' 0 32 x
  let y' := BitVec.extractLsb' 0 32 y
  BitVec.zeroExtend 64 (f x' y')

example (x y : BitVec 64) : add x y = x + y := by rfl
example (x y : BitVec 64) : sub x y = x - y := by rfl
example (x y : BitVec 64) : logicalAnd x y = x &&& y := by rfl
example (x y : BitVec 64) : logicalOr x y = x ||| y := by rfl
example (x y : BitVec 64) : logicalXor x y = x ^^^ y := by rfl

end Lifter
