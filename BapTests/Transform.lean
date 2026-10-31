import BapTests.Support

namespace Bap.Tests.Transform

open Bap
open Bap.Bil
open Bap.IR

private def reg (name : String) : Var := ⟨name, .imm 32, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

/-- `simplifyExp` as it reads: it evaluates each node first. What runs is one pass that knows where that fails. -/
private def simplifyBySpec (exp : Exp) : Exp :=
  match evalExp [] exp with
  | .ok (.bits value) => .int value
  | _ =>
    match exp with
    | .int _ | .var _ | .unknown _ _ => exp
    | .load memory address endian size => .load (simplifyBySpec memory) (simplifyBySpec address) endian size
    | .store memory address value endian size =>
      .store (simplifyBySpec memory) (simplifyBySpec address) (simplifyBySpec value) endian size
    | .bin op left right =>
      let left := simplifyBySpec left
      let right := simplifyBySpec right
      match op, left, right with
      | .add, @Exp.int width zero, _ =>
        if zero = 0 ∧ hasImmWidth right width then right else .bin op left right
      | .add, _, @Exp.int width zero =>
        if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
      | .sub, _, @Exp.int width zero =>
        if zero = 0 ∧ hasImmWidth left width then left else .bin op left right
      | .mul, @Exp.int width one, _ =>
        if !hasImmWidth right width then .bin op left right
        else if one = 1 then right
        else if one = 0 ∧ !hasUnknown right then left
        else .bin op left right
      | .mul, _, @Exp.int width one =>
        if !hasImmWidth left width then .bin op left right
        else if one = 1 then left
        else if one = 0 ∧ !hasUnknown left then right
        else .bin op left right
      | _, _, _ => .bin op left right
    | .un op value => .un op (simplifyBySpec value)
    | .cast kind width value => .cast kind width (simplifyBySpec value)
    | .letIn var value body => .letIn var (simplifyBySpec value) (simplifyBySpec body)
    | .ite condition yes no =>
      let condition := simplifyBySpec condition
      let yes := simplifyBySpec yes
      let no := simplifyBySpec no
      match condition with
      | @Exp.int 1 value => if value = 1 then yes else no
      | _ => .ite condition yes no
    | .extract high low value => .extract high low (simplifyBySpec value)
    | .concat left right => .concat (simplifyBySpec left) (simplifyBySpec right)

private def simplifyFastPath : IO Unit := do
  let x := reg "x"
  let one := int 1
  let zero := int 0
  let bit := Exp.int (1#1)
  let mem : Var := ⟨"mem", .mem 64 8, 0, false⟩
  let cases : List Exp := [
    one, .var x, .unknown "u" (.imm 64),
    .bin .add one one, .bin .add zero (.var x), .bin .add (.var x) zero, .bin .sub (.var x) zero,
    .bin .mul one (.var x), .bin .mul zero (.var x), .bin .mul (.var x) zero, .bin .mul (.unknown "u" (.imm 64)) zero,
    .bin .add (.bin .mul one one) (.bin .add zero (.var x)), .bin .div one zero, .bin .add one bit,
    .un .neg one, .un .not (.var x), .cast .low 8 one, .cast .high 8 (.var x), .cast .high 128 one,
    .extract 7 0 one, .extract 7 0 (.var x), .extract 100 0 one, .concat one one, .concat one (.var x), .concat (.var x) one,
    .ite bit one (.var x), .ite (.int (0#1)) one (.var x), .ite one one (.var x), .ite (.var x) one zero,
    .ite bit (.bin .add one one) (.bin .add zero (.var x)),
    .letIn x one (.var x), .letIn x (.var x) (.bin .add one one), .letIn x one one, .letIn x (.bin .add one one) (.bin .add zero (.var x)),
    .load (.var mem) one .little 8, .load one one .little 8, .store (.var mem) one one .little 8,
    .store one (.var x) one .little 8, .load (.var mem) (.bin .add one one) .little 8]
  for exp in cases do
    assertEqual s!"simplifying {expString exp}" (expString (simplifyBySpec exp)) (expString (simplifyExp exp))

def run : IO Unit := do
  simplifyFastPath
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
  let conditional := Exp.ite (.int (BitVec.ofNat 1 1)) (.var x) (.var y)
  assertEqual "constant condition simplification" (expString (.var x)) (expString (simplifyExp conditional))
  let block : Blk := ⟨1, [], [⟨1, y, closed⟩], []⟩
  let simplified := simplifyBlk block
  match simplified.defs with
  | [defn] => assertEqual "block expression simplification" (expString (int 42)) (expString defn.rhs)
  | defs => throw <| IO.userError s!"unexpected definitions {repr defs}"
  let killed : Blk := ⟨1, [⟨1, y, [(2, .var x)]⟩], [⟨2, x, .var y⟩], [⟨3, none, .ret (.indirect (.var x))⟩]⟩
  assertEqual "a block's own writes hide what its jumps and definitions read" [x] killed.freeVars
  let reads : Blk := ⟨1, [], [], [⟨3, some (.var y), .ret (.indirect (.var x))⟩]⟩
  assertEqual "a jump read nothing writes is free" [y, x] reads.freeVars
  let sub : Sub := { tid := 1, name := "prune", blks := [block, ⟨2, [], [], []⟩] }
  assertEqual "unreachable subroutine block removed" 1 (pruneSub sub).blks.length

end Bap.Tests.Transform
