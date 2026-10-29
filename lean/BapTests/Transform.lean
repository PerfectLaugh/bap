import BapTests.Support

namespace Bap.Tests.Transform

open Bap
open Bap.Bil
open Bap.IR

private def reg (name : String) : Var := ⟨name, .imm 32, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

def run : IO Unit := do
  let x := reg "x"
  let y := reg "y"
  let nested := Exp.letIn x (.var x) (.var x)
  assertEqual "free variables respect let binding" [x] (freeVars nested)
  let substituted := substitute [(x, int 1)] (.letIn x (.var x) (.var x))
  let expected := Exp.letIn x (int 1) (.var x)
  assertEqual "substitution respects shadowing" (expString expected) (expString substituted)
  let closed := Exp.bin .add (int 40) (int 2)
  let folded := foldExp closed
  assertEqual "constant folding" (expString (int 42)) (expString folded)
  assertBits "folded expression evaluates" (BitVec.ofNat 32 42) (evalExp [] folded)
  let identity := Exp.bin .add (.var x) (int 0)
  assertEqual "add-zero simplification" (expString (.var x)) (expString (simplifyExp identity))
  let zero := Exp.bin .mul (.var x) (int 0)
  assertEqual "multiply-zero simplification" (expString (int 0)) (expString (simplifyExp zero))
  let conditional := Exp.ite (int 1) (.var x) (.var y)
  assertEqual "constant condition simplification" (expString (.var x)) (expString (simplifyExp conditional))
  let block : Blk := ⟨1, [], [⟨1, y, closed⟩], []⟩
  let simplified := simplifyBlk block
  match simplified.defs with
  | [defn] => assertEqual "block expression simplification" (expString (int 42)) (expString defn.rhs)
  | defs => throw <| IO.userError s!"unexpected definitions {repr defs}"
  let sub : Sub := { tid := 1, name := "prune", blks := [block, ⟨2, [], [], []⟩] }
  assertEqual "unreachable subroutine block removed" 1 (pruneSub sub).blks.length

end Bap.Tests.Transform
