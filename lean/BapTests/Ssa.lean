import BapTests.Support

namespace Bap.Tests.Ssa

open Bap
open Bap.Bil
open Bap.IR

private def x : Var := ⟨"x", .imm 32, 0, false⟩
private def y : Var := ⟨"y", .imm 32, 0, false⟩
private def int (value : Nat) : Exp := .int (BitVec.ofNat 32 value)
private def defn (tid : Tid) (var : Var) (rhs : Exp) : Def := ⟨tid, var, rhs⟩
private def goto (tid destination : Tid) : Jmp := ⟨tid, none, .goto (.direct destination)⟩
private def expString (exp : Exp) : String := toString (Wire.printExp exp)

private def sample : Sub :=
  {
    tid := 1
    name := "diamond"
    blks := [
      ⟨1, [], [defn 1 x (int 0)], [goto 1 2, goto 2 3]⟩,
      ⟨2, [], [defn 2 x (int 1)], [goto 3 4]⟩,
      ⟨3, [], [defn 3 x (int 2)], [goto 4 4]⟩,
      ⟨4, [], [defn 4 y (.var x)], []⟩,
      ⟨99, [], [defn 99 x (int 7)], []⟩
    ]
  }

def run : IO Unit := do
  let connected := Cfg.connected sample
  assertEqual "connected CFG pseudo entry" pseudoStart connected.start
  assertTrue "connected CFG includes disconnected component" (connected.reachable.contains 99)
  assertTrue "disconnected component linked from pseudo entry" ((connected.predecessors 99).contains pseudoStart)
  assertTrue "disconnected component linked to pseudo exit" ((connected.successors 99).contains pseudoExit)
  let ssa := toSsa sample
  assertEqual "SSA preserves block order" [1, 2, 3, 4, 99] (ssa.blks.map Blk.tid)
  assertTrue "SSA removes pseudo blocks" (!(ssa.blks.map Blk.tid).contains pseudoStart)
  match ssa.block 4 with
  | none => throw <| IO.userError "missing SSA join"
  | some join =>
    assertEqual "one phi at diamond join" 1 join.phis.length
    match join.phis with
    | [phi] =>
      assertEqual "phi receives fresh version" 4 phi.var.index
      match Assoc.get 2 phi.values, Assoc.get 3 phi.values with
      | some left, some right =>
        assertEqual "left phi input version" (expString (.var (x.version 2))) (expString left)
        assertEqual "right phi input version" (expString (.var (x.version 3))) (expString right)
      | _, _ => throw <| IO.userError "missing phi inputs"
    | _ => pure ()
    match join.defs with
    | [defn] =>
      assertEqual "join definition uses phi version" (expString (.var (x.version 4))) (expString defn.rhs)
    | _ => throw <| IO.userError "missing join definition"
  match ssa.block 99 with
  | some block =>
    match block.defs with
    | [defn] => assertEqual "disconnected definition renamed" 5 defn.var.index
    | _ => throw <| IO.userError "missing disconnected definition"
  | none => throw <| IO.userError "disconnected block removed"
  let definitions := ssa.blks.flatMap Blk.definedVars
  assertEqual "SSA definitions are unique" definitions.length definitions.eraseDups.length
  let empty : Sub := ⟨1, "empty", [], []⟩
  assertEqual "empty subroutine SSA" 0 (toSsa empty).blks.length

end Bap.Tests.Ssa
