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

/-- `x := z; y := x` followed by a jump that reads `y`. -/
private def usedInBlock : Sub :=
  ⟨1, "used-in-block", [], [
    ⟨1, [], [defn 1 x (.var z), defn 2 y (.var x)], [goto 3 2]⟩,
    ⟨2, [], [], [⟨4, some (.var y), .ret (.indirect (.var y))⟩]⟩]⟩

/-- `x := z; x := y` followed by a jump that reads `x`: the first write is dead. -/
private def overwritten : Sub :=
  ⟨1, "overwritten", [], [
    ⟨1, [], [defn 1 x (.var z), defn 2 x (.var y)], [⟨3, none, .ret (.indirect (.var x))⟩]⟩]⟩

/-- `x := 1; L: y := x; x := 2; if z goto L else M; M: ret y`. -/
private def loop : Sub :=
  ⟨1, "loop", [], [
    ⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩,
    ⟨2, [], [defn 3 y (.var x), defn 4 x (int 2)], [⟨5, some (.var z), .goto (.direct 2)⟩, goto 6 3]⟩,
    ⟨3, [], [], [⟨7, none, .ret (.indirect (.var y))⟩]⟩]⟩

/-- `L: y := x; x := 1; goto L`: the entry state of `x` is unknown on the first iteration. -/
private def entryLoop : Sub :=
  ⟨1, "entry-loop", [], [
    ⟨1, [], [defn 1 y (.var x), defn 2 x (int 1)], [goto 3 1]⟩]⟩

/-- `x := 1; L: y := x; if z goto L else M`: `x` is 1 on every path into `L`. -/
private def stableLoop : Sub :=
  ⟨1, "stable-loop", [], [
    ⟨1, [], [defn 1 x (int 1)], [goto 2 2]⟩,
    ⟨2, [], [defn 3 y (.var x)], [⟨4, some (.var z), .goto (.direct 2)⟩, goto 5 3]⟩,
    ⟨3, [], [], []⟩]⟩

private def regressions : IO Unit := do
  match (propagateConstants (Cfg.fromSub stableLoop)).block 2 with
  | some block =>
    match block.defs with
    | [read] => assertEqual "constant stable around a loop is folded" (expString (int 1)) (expString read.rhs)
    | _ => throw <| IO.userError "missing stable loop definition"
  | none => throw <| IO.userError "missing stable loop block"
  let kept := (optimize usedInBlock).block 1 |>.map (·.defs.length) |>.getD 0
  assertEqual "definition read later in its block survives" 2 kept
  let single := (optimize overwritten).block 1 |>.map (fun blk => blk.defs.map (expString ·.rhs)) |>.getD []
  assertEqual "overwritten definition removed" [expString (.var y)] single
  match (propagateConstants (Cfg.fromSub loop)).block 2 with
  | some block =>
    match block.defs with
    | [read, _] => assertEqual "loop read not folded to first iteration" (expString (.var x)) (expString read.rhs)
    | _ => throw <| IO.userError "missing loop definitions"
  | none => throw <| IO.userError "missing loop block"
  match (propagateConstants (Cfg.fromSub entryLoop)).block 1 with
  | some block =>
    match block.defs with
    | [read, _] => assertEqual "entry state stays unknown" (expString (.var x)) (expString read.rhs)
    | _ => throw <| IO.userError "missing entry definitions"
  | none => throw <| IO.userError "missing entry block"
  let straight : Sub := ⟨1, "straight", [], [⟨1, [], [], [goto 1 2]⟩, ⟨2, [], [], []⟩]⟩
  let (ins, outs) := (Cfg.fromSub straight).livenessFrom 2 [x]
  assertTrue "seed live out of the exit" ((Assoc.get 2 outs).getD [] |>.contains x)
  assertTrue "seed live into the exit" ((Assoc.get 2 ins).getD [] |>.contains x)
  assertTrue "seed reaches the predecessor" ((Assoc.get 1 ins).getD [] |>.contains x)

def run : IO Unit := do
  regressions
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
