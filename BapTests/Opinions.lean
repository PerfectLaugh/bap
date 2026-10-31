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
  assertEqual "an agent may vote for several values" 3 state.opinions.length
  assertEqual "repeated vote is ignored" state.version (suggest low named object "alpha" state).version
  assertEqual "empty opinion is ignored" state.version (suggest low named object "" state).version
  match resolve named object state with
  | .ok value => assertEqual "heaviest opinion wins" "beta" value
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
  | .ok value => assertEqual "equal weights settled by voter names" "right" value
  | .error error => throw <| IO.userError s!"disagreement must not conflict: {repr error}"
  let outvoted := suggest high named object "lone" {}
  let outvoted := suggest low named object "crowd" outvoted
  let outvoted := suggest ⟨"other", 2⟩ named object "crowd" outvoted
  match resolve named object outvoted with
  | .ok value => assertEqual "weak agents can outvote a strong one" "crowd" value
  | .error error => throw <| IO.userError s!"vote failed: {repr error}"
  match resolve (⟨"name", maxDomain⟩ : Slot .nat) object conflicting with
  | .error (.typeMismatch "name") => IO.println "ok: opinion kind mismatch rejected"
  | .error error => throw <| IO.userError s!"wrong opinion mismatch: {repr error}"
  | .ok _ => throw <| IO.userError "opinion kind mismatch was accepted"
  let numbers := suggest high address object 10 {}
  let numbers := suggest peer address object 20 numbers
  match resolve address object numbers with
  | .ok value => assertEqual "equal-trust values are voted on, not joined" 20 value
  | .error error => throw <| IO.userError s!"numeric resolve failed: {repr error}"

end Bap.Tests.Opinions
