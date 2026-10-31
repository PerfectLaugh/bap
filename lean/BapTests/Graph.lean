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
  let loop : Bap.Graph.Graph Nat := ⟨[0, 1], [(0, 1), (1, 0)]⟩
  assertEqual "back edge to start in frontier of start" (some [0])
    (Assoc.get 0 (Bap.Graph.dominanceFrontier loop 0))
  assertEqual "back edge to start in frontier of source" (some [0])
    (Assoc.get 1 (Bap.Graph.dominanceFrontier loop 0))
  -- the compiler runs `Bap.Graph.Fast` on a CFG: it gives the very lists of the definitions
  let graphs : List (Bap.Graph.Graph Nat × Nat) := [
    (cfg.graph, 1), (loop, 0), (⟨[], []⟩, 0), (⟨[1], []⟩, 2),
    (⟨[1, 2, 2, 3], [(1, 2), (2, 3), (1, 2), (3, 2), (2, 9), (9, 1)]⟩, 1),
    (⟨[5, 4, 3, 2, 1], [(5, 1), (5, 2), (1, 3), (2, 3), (3, 4), (4, 1), (4, 5)]⟩, 5),
    (⟨[0, 1, 2, 3, 4], [(0, 1), (0, 2), (1, 3), (2, 3), (3, 1), (3, 4), (4, 0)]⟩, 0)]
  for (graph, start) in graphs do
    assertEqual "fast reachable is reachable" (Bap.Graph.reachable graph start) (Bap.Graph.Fast.reachable graph start)
    assertEqual "fast reachableFrom is reachableFrom" (Bap.Graph.reachableFrom graph [start, 3, start])
      (Bap.Graph.Fast.reachableFrom graph [start, 3, start])
    assertEqual "fast dominators are dominators" (Bap.Graph.dominators graph start) (Bap.Graph.Fast.dominators graph start)
    assertEqual "fast immediate dominators are immediate dominators" (Bap.Graph.immediateDominators graph start)
      (Bap.Graph.Fast.immediateDominators graph start)
    assertEqual "fast dominance frontier is the dominance frontier" (Bap.Graph.dominanceFrontier graph start)
      (Bap.Graph.Fast.dominanceFrontier graph start)

end Bap.Tests.Graph
