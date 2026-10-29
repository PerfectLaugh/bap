import BapTests.Support

namespace Bap.Tests.Opinions

open Bap
open Bap.Knowledge

private def named : Slot .string := ⟨"name", stringDomain⟩
private def address : Slot .nat := ⟨"address", maxDomain⟩
private def object : Object := ⟨"program", "main", 1⟩
private def low : Agent := ⟨"low", 1⟩
private def high : Agent := ⟨"high", 2⟩
private def peer : Agent := ⟨"peer", 2⟩

def run : IO Unit := do
  let state := suggest low named object "alpha" {}
  let state := suggest high named object "beta" state
  let state := suggest low named object "gamma" state
  assertEqual "same-agent opinion replaced" 2 state.opinions.length
  match resolve named object state with
  | .ok value => assertEqual "highest trust opinion wins" "beta" value
  | .error error => throw <| IO.userError s!"resolve failed: {repr error}"
  match provide address object 42 state with
  | .error error => throw <| IO.userError s!"provide failed: {repr error}"
  | .ok next =>
    match resolve named object next with
    | .ok value => assertEqual "provide preserves opinions" "beta" value
    | .error error => throw <| IO.userError s!"resolve after provide failed: {repr error}"
  match resolve named object {} with
  | .ok value => assertEqual "empty opinion resolution" "" value
  | .error error => throw <| IO.userError s!"empty resolve failed: {repr error}"
  let agreeing := suggest high named object "same" {}
  let agreeing := suggest peer named object "same" agreeing
  match resolve named object agreeing with
  | .ok value => assertEqual "equal-trust agreement resolves" "same" value
  | .error error => throw <| IO.userError s!"agreement failed: {repr error}"
  let conflicting := suggest high named object "left" {}
  let conflicting := suggest peer named object "right" conflicting
  match resolve named object conflicting with
  | .error (.incompatible "name") => IO.println "ok: equal-trust conflict rejected"
  | .error error => throw <| IO.userError s!"wrong opinion conflict: {repr error}"
  | .ok _ => throw <| IO.userError "equal-trust conflict was accepted"
  match resolve (⟨"name", maxDomain⟩ : Slot .nat) object conflicting with
  | .error (.typeMismatch "name") => IO.println "ok: opinion kind mismatch rejected"
  | .error error => throw <| IO.userError s!"wrong opinion mismatch: {repr error}"
  | .ok _ => throw <| IO.userError "opinion kind mismatch was accepted"
  let numbers := suggest high address object 10 {}
  let numbers := suggest peer address object 20 numbers
  match resolve address object numbers with
  | .ok value => assertEqual "equal-trust values joined" 20 value
  | .error error => throw <| IO.userError s!"numeric resolve failed: {repr error}"

end Bap.Tests.Opinions
