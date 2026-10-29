import BapTests.Support

namespace Bap.Tests.Optimize

open Bap
open Bap.Bil
open Bap.IR

private def reg (name : String) : Var := ⟨name, .imm 32, 0, false⟩
private def mem : Var := ⟨"mem", .mem 32 8, 0, false⟩
private def x := reg "x"
private def y := reg "y"
private def z := reg "z"
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def defn (tid : Tid) (var : Var) (rhs : Exp) : Def := ⟨tid, var, rhs⟩
private def goto (tid destination : Tid) : Jmp := ⟨tid, none, .goto (.direct destination)⟩
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

private def sample : Sub :=
  let store := Exp.store (.var mem) (int 0) (.var z) .little 4
  {
    tid := 1
    name := "optimize"
    blks := [
      ⟨1, [], [defn 1 x (int 40)], [goto 1 2]⟩,
      ⟨2, [], [defn 2 y (.bin .add (.var x) (int 2))], [goto 2 3]⟩,
      ⟨3, [], [defn 3 z (.var y), defn 4 mem store], [⟨5, none, .goto (.indirect (.var z))⟩]⟩,
      ⟨99, [], [defn 99 (reg "unused") (int 9)], []⟩
    ]
  }

def run : IO Unit := do
  let cfg := Cfg.fromSub sample
  let (ins, outs) := cfg.liveness
  assertTrue "liveness propagates across blocks" ((Assoc.get 2 outs).getD [] |>.contains y)
  assertTrue "jump target is live" ((Assoc.get 3 ins).getD [] |>.contains z)
  let propagated := propagateConstants cfg
  match propagated.block 2 with
  | some block =>
    match block.defs with
    | [defn] => assertEqual "cross-block constant propagation" (expString (int 42)) (expString defn.rhs)
    | _ => throw <| IO.userError "missing propagated definition"
  | none => throw <| IO.userError "missing propagated block"
  match propagated.block 3 with
  | some block =>
    match block.defs with
    | [result, _] => assertEqual "live result folded before DCE" (expString (int 42)) (expString result.rhs)
    | _ => throw <| IO.userError "missing propagated result"
  | none => throw <| IO.userError "missing propagated result block"
  let optimized := optimize sample
  assertEqual "optimization prunes unreachable blocks" [1, 2, 3] (optimized.blks.map Blk.tid)
  assertEqual "dead entry definition removed" 0 ((optimized.block 1).map (fun blk => blk.defs.length) |>.getD 999)
  assertEqual "dead intermediate definition removed" 0 ((optimized.block 2).map (fun blk => blk.defs.length) |>.getD 999)
  match optimized.block 3 with
  | none => throw <| IO.userError "missing optimized block"
  | some block =>
    assertEqual "only side-effecting store retained" 1 block.defs.length
    match block.defs with
    | [store] =>
      assertTrue "store remains side effecting" (match store.rhs with | .store _ _ _ _ _ => true | _ => false)
      match store.rhs with
      | .store _ _ value _ _ =>
        assertEqual "stored value folded" (expString (int 42)) (expString value)
      | _ => pure ()
    | _ => pure ()

end Bap.Tests.Optimize
