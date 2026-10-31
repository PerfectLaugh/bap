import Bap.Analysis.Slice
import Bap.Emu
import Std.Data.HashSet

namespace Bap.Analysis.DynamicSlice

structure Result where
  sites : List Nat := []
  live : List Slice.Location := []
  gaps : List Nat := []
  complete : Bool := true
  deriving Repr

private def writesCriterion (access : Emu.TraceAccess) (criteria : List Slice.Location) : Bool :=
  access.write && criteria.any (Slice.Location.mem access.address access.size).overlaps

/-- The dynamic slice of a static one. -/
private def ofStatic (static : Slice.Result) (pcs : List Nat) (accesses : List Emu.TraceAccess)
    (criteria : List Slice.Location) : Result :=
  let sites := static.sites.filter pcs.contains
  let outside := accesses.filterMap fun access =>
    if writesCriterion access criteria && !static.sites.contains access.pc then some access.pc else none
  let gaps := (static.sites.filter (fun site => !pcs.contains site) ++ outside).eraseDups
  {
    sites
    live := static.live
    gaps
    complete := static.determined && !static.calls.any pcs.contains && gaps.isEmpty
  }

/-- `ofStatic`, with what it looks in hashed. -/
private def ofStaticFast (static : Slice.Result) (pcs : List Nat) (accesses : List Emu.TraceAccess)
    (criteria : List Slice.Location) : Result :=
  let traced : Std.HashSet Nat := Std.HashSet.ofList pcs
  let statically : Std.HashSet Nat := Std.HashSet.ofList static.sites
  let sites := static.sites.filter traced.contains
  let outside := accesses.filterMap fun access =>
    if writesCriterion access criteria && !statically.contains access.pc then some access.pc else none
  let gaps := (static.sites.filter (fun site => !traced.contains site) ++ outside).eraseDups
  {
    sites
    live := static.live
    gaps
    complete := static.determined && !static.calls.any traced.contains && gaps.isEmpty
  }

private theorem contains_hashed (list : List Nat) : (Std.HashSet.ofList list).contains = list.contains := by
  funext address
  simp [Std.HashSet.contains_ofList]

@[csimp] private theorem ofStatic_eq_fast : @ofStatic = @ofStaticFast := by
  funext static pcs accesses criteria
  simp only [ofStatic, ofStaticFast, contains_hashed]

def backwardWithAccesses (project : Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Emu.TraceAccess) (criteria : List Slice.Location) : Result :=
  ofStatic (Slice.backwardProject project entry criteria) pcs accesses criteria

def backward (project : Project.Project) (entry : Nat) (pcs : List Nat)
    (criteria : List Slice.Location) : Result :=
  backwardWithAccesses project entry pcs [] criteria

/-- `backwardWithAccesses` on what is prepared, for many over one project. -/
def backwardPlanned (plan : Slice.ProjectPlan) (entry : Nat) (pcs : List Nat)
    (accesses : List Emu.TraceAccess) (criteria : List Slice.Location) : Result :=
  ofStatic (plan.slice entry criteria) pcs accesses criteria

end Bap.Analysis.DynamicSlice
