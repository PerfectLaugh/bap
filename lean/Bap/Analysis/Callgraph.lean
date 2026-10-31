import Bap.Analysis.Xrefs
import Bap.Graph.Fast

namespace Bap.Analysis.Callgraph

structure Callgraph where
  graph : Graph.Graph Nat := {}
  functions : List Image.Symbol := []

def create (index : Xrefs.Index) : Callgraph := {
  graph := {
    nodes := (index.functions.map Image.Symbol.addr ++
      index.xrefs.filterMap fun xref => match xref.kind with
        | .call => some xref.target
        | _ => none).eraseDups
    edges := (index.xrefs.filterMap fun xref =>
      if xref.kind = .call then
        (Xrefs.functionOf index xref.source).map fun caller => (caller.addr, xref.target)
      else
        none) |>.eraseDups
  }
  functions := index.functions
}

def reachable (callgraph : Callgraph) (roots : List Nat) : List Nat :=
  Graph.reachableFrom callgraph.graph roots

def stronglyConnected (callgraph : Callgraph) : List (List Nat) :=
  let components := callgraph.graph.nodes.foldl (init := (callgraph.graph.nodes, [])) fun current node =>
    if !current.1.contains node then current
    else
      let forward := Graph.reachable callgraph.graph node
      let component := forward.filter fun candidate =>
        (Graph.reachable callgraph.graph candidate).contains node
      (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])
  components.2

private def stronglyConnectedFast (callgraph : Callgraph) : List (List Nat) :=
  let components := callgraph.graph.nodes.foldl (init := (callgraph.graph.nodes, [])) fun current node =>
    if !current.1.contains node then current
    else
      let forward := Graph.Fast.reachable callgraph.graph node
      let component := forward.filter fun candidate =>
        (Graph.Fast.reachable callgraph.graph candidate).contains node
      (current.1.filter fun candidate => !component.contains candidate, current.2 ++ [component])
  components.2

@[csimp] private theorem stronglyConnected_eq_fast : @stronglyConnected = @stronglyConnectedFast := by
  funext callgraph
  simp only [stronglyConnected, stronglyConnectedFast, Graph.Fast.reachable_eq]

def recursiveFunctions (callgraph : Callgraph) : List Nat :=
  let components := stronglyConnected callgraph
  callgraph.graph.nodes.filter fun node =>
    components.any (fun component => component.length > 1 && component.contains node) ||
      callgraph.graph.edges.contains (node, node)

def render (callgraph : Callgraph) : String :=
  let lines := callgraph.graph.edges.map fun edge =>
    match callgraph.functions.find? (fun symbol => symbol.addr = edge.1),
      callgraph.functions.find? (fun symbol => symbol.addr = edge.2) with
    | some caller, some callee => s!"  {caller.name} -> {callee.name};"
    | _, _ => s!"  fn_{edge.1} -> fn_{edge.2};"
  "digraph callgraph {\n" ++ String.intercalate "\n" lines ++ "\n}"

end Bap.Analysis.Callgraph
