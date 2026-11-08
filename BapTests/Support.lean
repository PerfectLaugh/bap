import Bap

namespace Bap.Tests

/-- Tests build environments as lists, and give what a run leaves back to what takes one. -/
instance {α : Type} : CoeOut (Bap.VarMap α) (List (Bap.Var × α)) := ⟨Bap.VarMap.toList⟩

def assertEqual [DecidableEq α] [Repr α] (name : String) (expected actual : α) : IO Unit := do
  if expected = actual then
    IO.println s!"ok: {name}"
  else
    throw <| IO.userError s!"{name}: expected {repr expected}, got {repr actual}"

def assertTrue (name : String) (condition : Bool) : IO Unit := do
  if condition then
    IO.println s!"ok: {name}"
  else
    throw <| IO.userError name

def assertBits (name : String) (expected : BitVec width) (actual : Except String Value) : IO Unit := do
  match actual with
  | .ok (@Value.bits actualWidth value) =>
    if h : actualWidth = width then
      let actual : BitVec width := h ▸ value
      assertEqual name expected actual
    else
      throw <| IO.userError s!"{name}: expected width {width}, got {actualWidth}"
  | .ok value => throw <| IO.userError s!"{name}: expected bits, got {repr value}"
  | .error error => throw <| IO.userError s!"{name}: {error}"

end Bap.Tests
