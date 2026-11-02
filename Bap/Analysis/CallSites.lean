import Std.Data.TreeMap

/-! Where a thread's calls come back to. A program that recurses has many of them, and every instruction may be at one, so that looking
at them can't go through them: this says at once whether an address is one, and a return takes what it ends. -/

namespace Bap.Analysis

structure CallSites where
  /-- The innermost first. -/
  sites : List Nat := []
  depth : Nat := 0
  /-- How many of `sites` are each address. It is a tree, as what a thread had before a change may still be held. -/
  counts : Std.TreeMap Nat Nat := {}
  deriving Inhabited

namespace CallSites

def push (calls : CallSites) (site : Nat) : CallSites :=
  { sites := site :: calls.sites, depth := calls.depth + 1, counts := calls.counts.insert site (calls.counts.getD site 0 + 1) }

/-- Whether a call goes back to this address, or to it with the bit of Thumb. -/
def isSite (calls : CallSites) (pc : Nat) : Bool :=
  calls.depth != 0 && (calls.counts.contains pc || calls.counts.contains (pc + 1))

private def forget (counts : Std.TreeMap Nat Nat) (site : Nat) : Std.TreeMap Nat Nat :=
  match counts.getD site 0 with
  | 0 | 1 => counts.erase site
  | count => counts.insert site (count - 1)

/-- What is left when it has come back to this address, with how many calls that ended: those within it too, which may not have come back. -/
def pop (calls : CallSites) (pc : Nat) : Option (CallSites × Nat) :=
  if !calls.isSite pc then none
  else
    let rec go : List Nat → Std.TreeMap Nat Nat → Nat → Option (CallSites × Nat)
      | [], _, _ => none
      | site :: rest, counts, gone =>
        let counts := forget counts site
        if site == pc || site == pc + 1 then some ({ sites := rest, depth := calls.depth - (gone + 1), counts }, gone + 1)
        else go rest counts (gone + 1)
    go calls.sites calls.counts 0

/-- It again, from the sites alone. -/
def ofSites (sites : List Nat) : CallSites :=
  sites.foldr (fun site calls => calls.push site) {}

end CallSites

end Bap.Analysis
