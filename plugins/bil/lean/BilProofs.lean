import Lean

example (x : BitVec 8) : x + 0#8 = x := by bv_decide
example (x : BitVec 8) : x - x = 0#8 := by bv_decide
example (x : BitVec 8) : x * 1#8 = x := by bv_decide
example (x : BitVec 8) : x / 1#8 = x := by bv_decide
example (x : BitVec 8) : BitVec.sdiv x 1#8 = x := by bv_decide
example (x : BitVec 8) : x % 1#8 = 0#8 := by bv_decide
example (x : BitVec 8) : BitVec.srem x 1#8 = 0#8 := by bv_decide
example (x : BitVec 8) : BitVec.shiftLeft x (BitVec.toNat 0#8) = x := by bv_decide
example (x : BitVec 8) : BitVec.ushiftRight x (BitVec.toNat 0#8) = x := by bv_decide
example (x : BitVec 8) : BitVec.sshiftRight x (BitVec.toNat 0#8) = x := by bv_decide
example (x : BitVec 8) : x &&& 255#8 = x := by bv_decide
example (x : BitVec 8) : x ||| 0#8 = x := by bv_decide
example (x : BitVec 8) : x ^^^ x = 0#8 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (x == x) = 1#1 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (x != x) = 0#1 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (BitVec.ult x x) = 0#1 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (BitVec.ule x x) = 1#1 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (BitVec.slt x x) = 0#1 := by bv_decide
example (x : BitVec 8) : BitVec.ofBool (BitVec.sle x x) = 1#1 := by bv_decide
example (x : BitVec 8) : -(-x) = x := by bv_decide
example (x : BitVec 8) : ~~~(~~~x) = x := by bv_decide
example (x : BitVec 8) : BitVec.extractLsb 7 0 (BitVec.zeroExtend 16 x) = x := by bv_decide
example (x : BitVec 8) : BitVec.extractLsb 7 0 (BitVec.signExtend 16 x) = x := by bv_decide
example (x y : BitVec 8) : BitVec.extractLsb 15 8 (x ++ y) = x := by bv_decide
example (x y : BitVec 8) : BitVec.extractLsb 7 0 (x ++ y) = y := by bv_decide
example (x : BitVec 16) : BitVec.extractLsb 15 8 x ++ BitVec.extractLsb 7 0 x = x := by bv_decide
example (x y : BitVec 8) : (if 1#1 = BitVec.ofNat 1 1 then x else y) = x := by bv_decide

namespace Bil

theorem mba_xor_add_two_and (x y : BitVec 8) :
    (x ^^^ y) + 2#8 * (x &&& y) = x + y := by bv_decide

theorem mba_xor_add_and (x y : BitVec 8) :
    (x ^^^ y) + (x &&& y) = x ||| y := by bv_decide

theorem mba_or_add_and (x y : BitVec 8) :
    (x ||| y) + (x &&& y) = x + y := by bv_decide

theorem mba_or_sub_and (x y : BitVec 8) :
    (x ||| y) - (x &&& y) = x ^^^ y := by bv_decide

theorem mba_or_sub_xor (x y : BitVec 8) :
    (x ||| y) - (x ^^^ y) = x &&& y := by bv_decide

theorem mba_add_sub_two_and (x y : BitVec 8) :
    x + y - 2#8 * (x &&& y) = x ^^^ y := by bv_decide

end Bil
