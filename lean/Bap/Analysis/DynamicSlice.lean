import Bap.Analysis.Slice
import Bap.Emu

namespace Bap.Analysis.DynamicSlice

structure Result where
  sites : List Nat := []
  live : List Slice.Location := []
  gaps : List Nat := []
  complete : Bool := true
  deriving Repr

private def writesCriterion (access : Emu.TraceAccess) (criteria : List Slice.Location) : Bool :=
  access.write && criteria.any (Slice.Location.mem access.address access.size).overlaps

def backwardWithAccesses (project : Project.Project) (entry : Nat) (pcs : List Nat)
    (accesses : List Emu.TraceAccess) (criteria : List Slice.Location) : Result :=
  let static := Slice.backwardProject project entry criteria
  let sites := static.sites.filter pcs.contains
  let outside := accesses.filterMap fun access =>
    if writesCriterion access criteria && !static.sites.contains access.pc then some access.pc else none
  let gaps := (static.sites.filter (fun site => !pcs.contains site) ++ outside).eraseDups
  {
    sites
    live := static.live
    gaps
    complete := static.complete && gaps.isEmpty
  }

def backward (project : Project.Project) (entry : Nat) (pcs : List Nat)
    (criteria : List Slice.Location) : Result :=
  backwardWithAccesses project entry pcs [] criteria

end Bap.Analysis.DynamicSlice
