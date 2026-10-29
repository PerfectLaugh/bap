import BapTests.Support

namespace Bap.Tests.Graph

open Bap
open Bap.IR

private def goto (tid destination : Tid) : Jmp := ⟨tid, none, .goto (.direct destination)⟩

private def diamond : Sub :=
  {
    tid := 1
    name := "diamond"
    blks := [
      ⟨1, [], [], [goto 1 2, goto 2 3]⟩,
      ⟨2, [], [], [goto 3 4]⟩,
      ⟨3, [], [], [goto 4 4]⟩,
      ⟨4, [], [], []⟩,
      ⟨99, [], [], []⟩
    ]
  }

def run : IO Unit := do
  let cfg := Cfg.fromSub diamond
  assertEqual "CFG entry" 1 cfg.start
  assertEqual "direct successors" [2, 3] (cfg.successors 1)
  assertEqual "join predecessors" [2, 3] (cfg.predecessors 4)
  assertTrue "reachable join" (cfg.reachable.contains 4)
  assertTrue "unreachable block excluded" (!cfg.reachable.contains 99)
  assertEqual "dominators entry" (some [1]) (Assoc.get 1 cfg.dominators)
  assertEqual "dominators left arm" (some [2, 1]) (Assoc.get 2 cfg.dominators)
  assertEqual "dominators join" (some [4, 1]) (Assoc.get 4 cfg.dominators)
  assertEqual "immediate dominator join" (some 1) (Assoc.get 4 cfg.immediateDominators)
  assertEqual "frontier left arm" (some [4]) (Assoc.get 2 cfg.dominanceFrontier)
  assertEqual "frontier right arm" (some [4]) (Assoc.get 3 cfg.dominanceFrontier)
  let pruned := cfg.prune
  assertEqual "pruned block count" 4 pruned.blocks.length
  assertTrue "pruned graph excludes unreachable" (!pruned.graph.nodes.contains 99)
  assertEqual "prune preserves entry" cfg.start pruned.start

end Bap.Tests.Graph
