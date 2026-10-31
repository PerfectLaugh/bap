import Bap.Graph.Fast
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

/-- `Graph.reachableFrom` as it reads: rounds, in the order of the nodes. -/
private partial def roundsBySpec (graph : Graph.Graph Nat) (seen : List Nat) : List Nat :=
  let next := seen ++ graph.nodes.filter fun node =>
    !seen.contains node && graph.edges.any fun edge => edge.2 == node && seen.contains edge.1
  if next == seen then seen else roundsBySpec graph next

private def reachableBySpec (graph : Graph.Graph Nat) (seeds : List Nat) : List Nat :=
  roundsBySpec graph (seeds.filter graph.nodes.contains).eraseDups

/-- A round of the fast search looks at what the last one found, and gives what a round over all the nodes gives. -/
private def roundsFastPath : IO Unit := do
  let graphs : List (Graph.Graph Nat) := [
    {},
    { nodes := [1, 2, 3], edges := [(1, 2), (2, 1), (3, 3), (9, 1), (1, 9)] },
    { nodes := (List.range 40).reverse, edges := (List.range 40).flatMap fun i => [(i, (i * 7 + 3) % 40), (i, (i * i + 1) % 40)] },
    { nodes := [5, 5, 6, 7, 6, 5], edges := [(5, 6), (6, 5), (6, 7), (6, 7)] },
    { nodes := (List.range 60).reverse, edges := (List.range 59).map fun i => (i, i + 1) },
    { nodes := List.range 30, edges := (List.range 30).flatMap fun i => [(i, 2 * i % 31), (i, 3 * i % 31)] }]
  for graph in graphs do
    for seeds in [[], [0], [5, 1, 5], [100, 3], graph.nodes.take 2] do
      assertEqual "a search over the graph" (reachableBySpec graph seeds) (Graph.Fast.reachableFrom graph seeds)

def run : IO Unit := do
  roundsFastPath
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
  -- A graph on which the equations of dominators have more than one solution, and irreducible ones, where a walk up from two nodes may stop short.
  for (name, graph, start) in [
      ("a loop entered by its head", (⟨[1, 2, 3, 4], [(1, 2), (2, 3), (3, 4), (4, 3)]⟩ : Bap.Graph.Graph Nat), 1),
      ("a loop with two entries", ⟨[1, 2, 3, 4, 5], [(1, 2), (1, 3), (2, 3), (3, 2), (2, 4), (3, 4), (4, 5), (5, 4)]⟩, 1),
      ("a node that nothing reaches goes to one that is", ⟨[1, 2, 3, 9], [(1, 2), (2, 3), (9, 3)]⟩, 1),
      ("the start in a loop", ⟨[1, 2, 3], [(1, 2), (2, 3), (3, 1)]⟩, 1),
      ("a start that is not a node", ⟨[1, 2], [(1, 2)]⟩, 7)] do
    assertEqual s!"immediate dominators of {name}" (Bap.Graph.immediateDominators graph start) (Bap.Graph.Fast.immediateDominators graph start)
    assertEqual s!"dominance frontier of {name}" (Bap.Graph.dominanceFrontier graph start) (Bap.Graph.Fast.dominanceFrontier graph start)
  -- Long chains and chains of diamonds take as long as they have blocks.
  let chain (count : Nat) : Bap.Graph.Graph Nat := ⟨List.range count, (List.range (count - 1)).map fun n => (n, n + 1)⟩
  let diamonds (count : Nat) : Bap.Graph.Graph Nat := ⟨List.range (3 * count + 1), (List.range count).flatMap fun n =>
    [(3 * n, 3 * n + 1), (3 * n, 3 * n + 2), (3 * n + 1, 3 * n + 3), (3 * n + 2, 3 * n + 3)]⟩
  assertEqual "the immediate dominator at the end of a long chain" (some 9998) (Bap.Assoc.get 9999 (Bap.Graph.Fast.immediateDominators (chain 10000) 0))
  assertEqual "the immediate dominator at the end of chain of diamonds" (some (3 * 2999)) (Bap.Assoc.get (3 * 3000) (Bap.Graph.Fast.immediateDominators (diamonds 3000) 0))
  assertEqual "the frontier of an arm of a diamond" (some [3 * 2000 + 3]) (Bap.Assoc.get (3 * 2000 + 1) (Bap.Graph.Fast.dominanceFrontier (diamonds 3000) 0))

end Bap.Tests.Graph
