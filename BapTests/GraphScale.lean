import Lean
import BapTests.Support
import Bap.Primus.Lifted

open Lean Elab Command in
/-- Bring private declarations of module `mod`, namespace `ns`, into scope by short name. -/
local elab "open_private " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

/-! Lowering a graph takes time in proportion to its blocks. It has been cubic in them, then quadratic, each time without a
test failing, as a small graph does not show it. -/

namespace Bap.Tests.GraphScale

open Bap Bap.Primus.Lifted
open_private Bap.Primus.Lifted Bap.Primus.Lifted lowerGraph definitelyWritten writtenAt Lowering Lowering.ops

private def register (index : Nat) : Bap.Var := { name := s!"R{index}", typ := .imm 64 }

/-- Eight moves, of registers that differ from block to block. -/
private def block (index : Nat) : Block :=
  ⟨0x1000 + index * 16, 0x1000 + (index + 1) * 16,
    (List.range 8).map fun offset => .move (register ((index + offset) % 24)) (.int (BitVec.ofNat 64 (index + offset)))⟩

/-- A chain with an edge back every ten blocks. -/
private def graph (count : Nat) : List Block × List (Nat × Nat) :=
  ((List.range count).map block, (List.range (count - 1)).flatMap fun index =>
    let address := 0x1000 + index * 16
    (address, address + 16) :: if index % 10 == 9 then [(address, 0x1000 + (index - 9) * 16)] else [])

def run : IO Unit := do
  let count := 6400
  let (blocks, edges) := graph count
  let started ← IO.monoMsNow
  let table := definitelyWritten 0x1000 blocks edges
  let facts := (List.range count).foldl (init := 0) fun total index => total + (writtenAt table (0x1000 + index * 16)).length
  assertEqual "a large graph has what it wrote" 153440 facts
  let ops := match lowerGraph blocks edges with
    | some lowering => (Lowering.ops lowering).length
    | none => 0
  assertEqual "a large graph lowers" 226144 ops
  -- Some 100 ms, and it was over 5 s when quadratic: this holds on a machine that is busy with the other tests.
  assertTrue "a large graph lowers in time that is linear" ((← IO.monoMsNow) - started < 3000)

end Bap.Tests.GraphScale
