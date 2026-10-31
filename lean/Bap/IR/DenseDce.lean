import Bap.IR.LiveSets

/-! `eliminateDeadCode` with its variables as numbers. The passes of `Bap.IR.Optimize` go over the same blocks and look up the
same variables many times: all of that is done once here, for arrays to do what hash maps do there. -/

namespace Bap.IR.DenseDce

open Bap Bap.Bil Bap.IR.LiveSets Bap.Proofs.IR

local macro "blockIn" : term =>
  return Lean.mkIdent (.num (`_private ++ `Bap.IR.Liveness) 0 ++ `Bap.IR.blockIn)

structure DDef where
  defn : Def
  var : Nat
  reads : List Nat
  effect : Bool

structure DPhi where
  phi : Phi
  var : Nat
  inputs : List (Tid × List Nat)

structure DBlk where
  tid : Tid
  jmps : List Jmp
  phis : List DPhi
  defs : List DDef
  jmpReads : List Nat

abbrev Ids := Std.HashMap Bap.Var Nat

@[inline] def idOf (ids : Ids) (x : Bap.Var) : Nat := ids.getD x 0

/-- Numbers for everything `vars` lists, from `ids.size`. -/
def internAll (ids : Ids) (vars : List Bap.Var) : Ids :=
  vars.foldl (fun ids x => if ids.contains x then ids else ids.insert x ids.size) ids

def denseDef (effect : Bil.Exp → Bool) (ids : Ids) (d : Def) : DDef :=
  ⟨d, idOf ids d.var, (Bil.freeVars d.rhs).map (idOf ids), effect d.rhs⟩

def densePhi (ids : Ids) (p : Phi) : DPhi :=
  ⟨p, idOf ids p.var, p.values.map fun input => (input.1, (Bil.freeVars input.2).map (idOf ids))⟩

def denseBlk (effect : Bil.Exp → Bool) (ids : Ids) (blk : Blk) : DBlk :=
  ⟨blk.tid, blk.jmps, blk.phis.map (densePhi ids), blk.defs.map (denseDef effect ids), (blk.jmps.flatMap Jmp.freeVars).map (idOf ids)⟩

def DBlk.toBlk (d : DBlk) : Blk := ⟨d.tid, d.phis.map DPhi.phi, d.defs.map DDef.defn, d.jmps⟩

def internBlock (ids : Ids) (blk : Blk) : Ids := internAll ids (vocabulary blk)

/-- A row of blocks: short ones are searched. -/
inductive Row where
  | short (blocks : List Nat)
  | long (blocks : Std.HashSet Nat)

def Row.ofList (blocks : List Nat) : Row :=
  if blocks.length ≤ 16 then .short blocks else .long (Std.HashSet.ofList blocks)

def Row.contains : Row → Nat → Bool
  | .short blocks, b => blocks.contains b
  | .long blocks, b => blocks.contains b

/-- Sets of numbers in one array: a number is in the current set if it has the current stamp. -/
structure Marks where
  stamps : Array Nat
  stamp : Nat

namespace Marks
def empty (size : Nat) : Marks := ⟨Array.replicate size 0, 1⟩
@[inline] def clear (m : Marks) : Marks := { m with stamp := m.stamp + 1 }
@[inline] def contains (m : Marks) (x : Nat) : Bool := m.stamps.getD x 0 == m.stamp
@[inline] def add (m : Marks) (x : Nat) : Marks := { m with stamps := m.stamps.setIfInBounds x m.stamp }
@[inline] def remove (m : Marks) (x : Nat) : Marks := { m with stamps := m.stamps.setIfInBounds x 0 }
end Marks

structure Graphs where
  tids : Array Tid
  preds : Array (List Nat)
  succs : Array (List Nat)
  reach : Array Bool
  sites : Array (List Nat)
  definers : Array (List Nat)
  protect : Array Bool

@[inline] def killedD (d : DBlk) (x : Nat) : Bool := d.phis.any (·.var == x) || d.defs.any (·.var == x)
@[inline] def hasPhiD (d : DBlk) (x : Nat) : Bool := d.phis.any (·.var == x)

def dummy : DBlk := ⟨0, [], [], [], []⟩

@[inline] def blkAt (blocks : Array DBlk) (i : Nat) : DBlk := blocks.getD i dummy

/-- What the phis of a block read on the edge from `source`. -/
def phiReadsD (source : Tid) (d : DBlk) : List Nat :=
  d.phis.flatMap fun phi => (Assoc.get source phi.inputs).getD []

/-- The `blockIn` of a block from nothing live after it. -/
def exposedD (kills : Marks) (d : DBlk) : List Nat × Marks :=
  let kills := kills.clear
  let kills := d.phis.foldl (fun kills phi => kills.add phi.var) kills
  let step := d.defs.foldl (init := (([] : List Nat), kills)) fun state defn =>
    (defn.reads.foldl (fun out y => if state.2.contains y then out else y :: out) state.1, state.2.add defn.var)
  (d.jmpReads.foldl (fun out y => if step.2.contains y then out else y :: out) step.1, step.2)

@[specialize] def visitPredsD (skip : Nat → Bool) (preds : List Nat) (state : Marks × List Nat × List Nat) : Marks × List Nat × List Nat :=
  preds.foldl (init := state) fun state p =>
    if state.1.contains p then state
    else if skip p then state
    else (state.1.add p, p :: state.2.1, p :: state.2.2)

/-- The blocks that `x` is live in, from what starts it, going back through what `skip` lets through. -/
@[specialize] def floodD (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) (skip : Nat → Bool) : Nat → Marks → List Nat → List Nat → Option (List Nat × Marks)
  | 0, _, _, _ => none
  | _ + 1, seen, row, [] => some (row, seen)
  | fuel + 1, seen, row, t :: work =>
    if hasPhiD (blkAt blocks t) x then
      floodD blocks preds x skip fuel seen row work
    else
      let next := visitPredsD skip (preds.getD t []) (seen, row, work)
      floodD blocks preds x skip fuel next.1 next.2.1 next.2.2

/-- What starts each variable of `affected`. -/
def seedsD (g : Graphs) (blocks : Array DBlk) (affected : Array Bool) (kills : Marks) (sites : List Nat) (seeds : Array (List Nat)) :
    Array (List Nat) × Marks :=
  sites.foldl (init := (seeds, kills)) fun state s =>
    let d := blkAt blocks s
    let state := if g.reach.getD s false then
        let ex := exposedD state.2 d
        (ex.1.foldl (fun seeds y => if affected.getD y false then seeds.modify y (s :: ·) else seeds) state.1, ex.2)
      else state
    let seeds := (g.preds.getD s []).foldl (init := state.1) fun seeds p =>
      let bp := blkAt blocks p
      (phiReadsD (g.tids.getD p 0) d).foldl (fun seeds y => if affected.getD y false && !killedD bp y then seeds.modify y (p :: ·) else seeds) seeds
    (seeds, state.2)

def nodup (seen : Marks) (l : List Nat) : List Nat × Marks :=
  l.foldl (init := ([], seen.clear)) fun state x => if state.2.contains x then state else (x :: state.1, state.2.add x)

/-- The rows of `xs`, from what starts them. -/
def refreshRows (blocks : Array DBlk) (preds : Array (List Nat)) (seeds : Array (List Nat)) :
    Array Row → Marks → List Nat → Option (Array Row × Marks)
  | rows, seen, [] => some (rows, seen)
  | rows, seen, x :: rest =>
    match seeds.getD x [] with
    | [] => refreshRows blocks preds seeds (rows.setIfInBounds x (.short [])) seen rest
    | start =>
      match floodD blocks preds x (fun p => killedD (blkAt blocks p) x) (start.length + blocks.size + 1) (start.foldl Marks.add seen.clear) start start with
      | none => none
      | some (row, seen) => refreshRows blocks preds seeds (rows.setIfInBounds x (Row.ofList row)) seen rest

def affectedMarks (size : Nat) (affected : List Nat) : Array Bool :=
  affected.foldl (fun mark x => mark.setIfInBounds x true) (Array.replicate size false)

def refreshD (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (affected : List Nat) (kills seen : Marks) :
    Option (Array Row × Marks × Marks) :=
  let sites := nodup seen (affected.flatMap fun x => g.sites.getD x [])
  let seeds := seedsD g blocks (affectedMarks rows.size affected) kills sites.1 (Array.replicate rows.size [])
  match refreshRows blocks g.preds seeds.1 rows sites.2 affected with
  | none => none
  | some (rows, seen) => some (rows, seeds.2, seen)

/-- The scan of `dceDefsDropped`. -/
def scanDefsD (defs : List DDef) (live : Marks) : List DDef × Marks × List Nat :=
  defs.foldr (init := ([], live, [])) fun defn state =>
    if state.2.1.contains defn.var || defn.effect then
      (defn :: state.1, defn.reads.foldl Marks.add (state.2.1.remove defn.var), state.2.2)
    else
      (state.1, state.2.1, defn.var :: defn.reads ++ state.2.2)

def phiMentionsD (phi : DPhi) : List Nat := phi.var :: phi.inputs.flatMap Prod.snd

/-- What the phis of the successors read on the edges from a block. -/
def readsD (blocks : Array DBlk) (tid : Tid) (succs : List Nat) (reads : Marks) : Marks :=
  succs.foldl (fun reads s => (phiReadsD tid (blkAt blocks s)).foldl Marks.add reads) reads.clear

/-- Whether a variable a block assigns is live at its end, or its jumps don't count. -/
def queryD (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (succs : List Nat) (reads : Marks) (x : Nat) : Bool :=
  g.protect.getD x false || reads.contains x ||
    succs.any fun s => (rows.getD x (.short [])).contains s && !hasPhiD (blkAt blocks s) x

/-- What is live at the end of a block. -/
def liveD (query : Nat → Bool) (d : DBlk) (live : Marks) : Marks :=
  let live := live.clear
  let live := d.defs.foldl (fun live defn => if query defn.var then live.add defn.var else live) live
  let live := d.phis.foldl (fun live phi => if query phi.var then live.add phi.var else live) live
  d.jmpReads.foldl Marks.add live

/-- What is live at the end of block `i`. -/
def endLive (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (i : Nat) (d : DBlk) (reads live : Marks) : Marks × Marks :=
  let succs := if g.reach.getD i false then g.succs.getD i [] else []
  let reads := readsD blocks (g.tids.getD i 0) succs reads
  (reads, liveD (queryD g blocks rows succs reads) d live)

def scanD (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (i : Nat) (d : DBlk) (reads live : Marks) :
    DBlk × List Nat × Marks × Marks :=
  let (reads, live) := endLive g blocks rows i d reads live
  let result := scanDefsD d.defs live
  let live := result.2.1
  let phis := d.phis.filter fun phi => live.contains phi.var
  let lost := (d.phis.filter fun phi => !live.contains phi.var).flatMap phiMentionsD
  ({ d with defs := result.1, phis := phis }, result.2.2 ++ lost, reads, live)

/-- The blocks of the dirty list, scanned, and what the definitions they removed mention, with where. -/
def scanAll (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (dirty : List Nat) (reads live : Marks) :
    Array DBlk × List (Nat × Nat) × Marks × Marks :=
  let result := dirty.foldl (init := (([] : List (Nat × DBlk)), ([] : List (Nat × Nat)), reads, live)) fun state i =>
    let r := scanD g blocks rows i (blkAt blocks i) state.2.2.1 state.2.2.2
    ((i, r.1) :: state.1, r.2.1.map (fun y => (y, i)) ++ state.2.1, r.2.2.1, r.2.2.2)
  (result.1.foldl (fun blocks update => blocks.setIfInBounds update.1 update.2) blocks, result.2)

/-! A removed read can only take a variable out of the blocks that read it first, and those it was only live in because of them:
going back from where it was read, as far as the blocks that read it themselves or assign it. A removed assignment has no effect on
where it is live, as it went because nothing was to read it. So a pass costs what it removes, however many blocks mention a variable. -/

/-- Whether a variable is read before any assignment to it, in what is left of a block. -/
def exposedDefsD (x : Nat) (jmpReads : List Nat) : List DDef → Bool
  | [] => jmpReads.contains x
  | defn :: rest => defn.reads.contains x || (defn.var != x && exposedDefsD x jmpReads rest)

/-- Whether a block needs a variable live at its start, whatever comes after it. -/
def exposesD (d : DBlk) (x : Nat) : Bool := !hasPhiD d x && exposedDefsD x d.jmpReads d.defs

def Row.erase : Row → Nat → Row
  | .short blocks, b => .short (blocks.filter (· != b))
  | .long blocks, b => .long (blocks.erase b)

/-- The blocks that can lose `x`: those of `sites`, what is before them, and what is only live through those. -/
def lostD (g : Graphs) (blocks : Array DBlk) (row : Row) (x : Nat) (sites : List Nat) (seen : Marks) : Option (List Nat × Marks) :=
  let first := visitPredsD (fun p => !row.contains p || exposesD (blkAt blocks p) x)
    (sites ++ sites.flatMap fun s => g.preds.getD s []) (seen.clear, [], [])
  floodD blocks g.preds x (fun p => !row.contains p || killedD (blkAt blocks p) x || exposesD (blkAt blocks p) x)
    (first.2.1.length + blocks.size + 1) first.1 first.2.1 first.2.1

/-- Whether a block that can lose `x` keeps it on its own, from a block after it that can't lose it or a phi that reads it. -/
def survivesD (g : Graphs) (blocks : Array DBlk) (row : Row) (lost : Marks) (x : Nat) (t : Nat) : Bool :=
  !killedD (blkAt blocks t) x && (g.succs.getD t []).any fun s =>
    (row.contains s && !lost.contains s && !hasPhiD (blkAt blocks s) x) || (phiReadsD (g.tids.getD t 0) (blkAt blocks s)).contains x

/-- The blocks that can lose `x` and don't. -/
def keptD (g : Graphs) (blocks : Array DBlk) (row : Row) (x : Nat) (lostList : List Nat) (lost seen : Marks) : Option (List Nat × Marks) :=
  let start := lostList.filter (survivesD g blocks row lost x)
  floodD blocks g.preds x (fun p => !lost.contains p || killedD (blkAt blocks p) x)
    (start.length + blocks.size + 1) (start.foldl Marks.add seen.clear) start start

/-- What assigns `x` right before the blocks of a list, on top of `dirty`. -/
def addKillers (g : Graphs) (blocks : Array DBlk) (x : Nat) (l : List Nat) (dirty : List Nat) : List Nat :=
  l.foldl (fun dirty t => (g.preds.getD t []).foldl (fun dirty p => if killedD (blkAt blocks p) x then p :: dirty else dirty) dirty) dirty

/-- The row of `x`, after what mentions it went from `sites`, and the blocks to look at again for it. -/
def updateVar (g : Graphs) (blocks : Array DBlk) (x : Nat) (sites : List Nat) (rows : Array Row) (dirty : List Nat) (seen seen2 : Marks) :
    Option (Array Row × List Nat × Marks × Marks) :=
  let row := rows.getD x (.short [])
  match lostD g blocks row x sites seen with
  | none => none
  | some (lostList, lost) =>
    match keptD g blocks row x lostList lost seen2 with
    | none => none
    | some (_, kept) =>
      let erased := lostList.filter fun t => !kept.contains t
      some (rows.modify x (fun row => erased.foldl Row.erase row), addKillers g blocks x (erased ++ sites) dirty, lost, kept)

/-- `updateVar` for all that the last pass removed. A variable with several is done the first time. -/
def updateAll (g : Graphs) (blocks : Array DBlk) : List (Nat × Nat) → Array Row → Array (List Nat) → List Nat → Marks → Marks →
    Option (Array Row × Array (List Nat) × List Nat × Marks × Marks)
  | [], rows, groups, dirty, seen, seen2 => some (rows, groups, dirty, seen, seen2)
  | pair :: rest, rows, groups, dirty, seen, seen2 =>
    match groups.getD pair.1 [] with
    | [] => updateAll g blocks rest rows groups dirty seen seen2
    | sites =>
      match updateVar g blocks pair.1 sites rows dirty seen seen2 with
      | none => none
      | some (rows, dirty, seen, seen2) => updateAll g blocks rest rows (groups.setIfInBounds pair.1 []) dirty seen seen2

def addGroups (pairs : List (Nat × Nat)) (groups : Array (List Nat)) : Array (List Nat) :=
  pairs.foldl (fun groups pair => groups.modify pair.1 (pair.2 :: ·)) groups

def loopD (g : Graphs) (fallback : Array DBlk → Nat → Cfg) (ofBlocks : Array DBlk → Cfg) :
    Nat → Array DBlk → Array Row → List Nat → Array (List Nat) → Marks → Marks → Marks → Marks → Cfg
  | 0, blocks, _, _, _, _, _, _, _ => ofBlocks blocks
  | fuel + 1, blocks, rows, dirty, groups, seen, seen2, reads, live =>
    let result := scanAll g blocks rows dirty reads live
    match result.2.1 with
    | [] => ofBlocks result.1
    | dropped =>
      match updateAll g result.1 dropped rows (addGroups dropped groups) [] seen seen2 with
      | none => fallback result.1 fuel
      | some (rows, groups, next, seen, seen2) =>
        let dirtyList := nodup seen next
        loopD g fallback ofBlocks fuel result.1 rows dirtyList.1 groups dirtyList.2 seen2 result.2.2.1 result.2.2.2

/-- The position of each tid. -/
def indexOf : Nat → List Blk → Std.HashMap Tid Nat → Std.HashMap Tid Nat
  | _, [], table => table
  | i, blk :: rest, table => indexOf (i + 1) rest (table.insert blk.tid i)

/-- Each block is at the position of its tid: no other has it. -/
def indexChecks (index : Std.HashMap Tid Nat) : Nat → List Blk → Bool
  | _, [] => true
  | i, blk :: rest => index.get? blk.tid == some i && indexChecks index (i + 1) rest

/-- For each number, the positions of the blocks whose `vars` have it. -/
def positionTable (ids : Ids) (vars : Blk → List Bap.Var) : Nat → List Blk → Array (List Nat) → Array (List Nat)
  | _, [], table => table
  | i, blk :: rest, table =>
    positionTable ids vars (i + 1) rest ((vars blk).foldl (fun table y => table.modify (idOf ids y) (i :: ·)) table)

def predsTable (index : Std.HashMap Tid Nat) (succsOf : Tid → List Nat) (reachable : List Tid) (preds : Array (List Nat)) : Array (List Nat) :=
  reachable.foldl (init := preds) fun preds t =>
    match index.get? t with
    | none => preds
    | some p => (succsOf t).foldl (fun preds s => preds.modify s (p :: ·)) preds

def reachTable (index : Std.HashMap Tid Nat) (reachable : List Tid) (reach : Array Bool) : Array Bool :=
  reachable.foldl (init := reach) fun reach t =>
    match index.get? t with
    | none => reach
    | some p => reach.setIfInBounds p true

/-- The positions of the blocks after a tid. -/
def succsIn (successors : Std.HashMap Tid (List Tid)) (index : Std.HashMap Tid Nat) (t : Tid) : List Nat :=
  (Bap.Graph.Fast.dedup (successors.getD t [])).filterMap index.get?

def graphsOf (ids : Ids) (protectedVars : List Bap.Var) (cfg : Cfg) (index : Std.HashMap Tid Nat) : Graphs :=
  let n := cfg.blocks.length
  let nVars := ids.size
  let reachable := cfg.reachable
  let successors := Bap.Graph.Fast.successorTable cfg.graph
  { tids := (cfg.blocks.map Blk.tid).toArray
    preds := predsTable index (succsIn successors index) reachable (Array.replicate n [])
    succs := (cfg.blocks.map fun blk => succsIn successors index blk.tid).toArray
    reach := reachTable index reachable (Array.replicate n false)
    sites := positionTable ids vocabulary 0 cfg.blocks (Array.replicate nVars [])
    definers := positionTable ids assigned 0 cfg.blocks (Array.replicate nVars [])
    protect := protectedVars.foldl (fun protect x => protect.setIfInBounds (idOf ids x) true) (Array.replicate nVars false) }

/-- `fallback` is for two blocks with the same tid, and for what runs out of fuel. -/
def run (effect : Bil.Exp → Bool) (protectedVars : List Bap.Var) (cfg : Cfg) (fuel : Nat) (fallback : Cfg → Nat → Cfg) : Cfg :=
  let index := indexOf 0 cfg.blocks {}
  if !indexChecks index 0 cfg.blocks then fallback cfg fuel else
  let ids : Ids := cfg.blocks.foldl internBlock (internAll {} protectedVars)
  let nVars := ids.size
  let n := cfg.blocks.length
  let blocks : Array DBlk := (cfg.blocks.map (denseBlk effect ids)).toArray
  let g := graphsOf ids protectedVars cfg index
  match refreshD g blocks (Array.replicate nVars (.short [])) (List.range nVars) (Marks.empty nVars) (Marks.empty (max nVars n)) with
  | none => fallback cfg fuel
  | some (rows, _, seen) =>
    loopD g (fun blocks fuel => fallback { cfg with blocks := blocks.toList.map DBlk.toBlk } fuel)
      (fun blocks => { cfg with blocks := blocks.toList.map DBlk.toBlk }) fuel blocks rows (List.range n) (Array.replicate nVars [])
      seen (Marks.empty (max nVars n)) (Marks.empty nVars) (Marks.empty nVars)

/-! ### Marks -/

namespace Marks

/-- The stamp is not in use by what isn't marked, nor is it what `remove` leaves. -/
structure WF (m : Marks) (size : Nat) : Prop where
  size : m.stamps.size = size
  pos : 1 ≤ m.stamp
  le : ∀ i, m.stamps.getD i 0 ≤ m.stamp

theorem getD_set (a : Array Nat) (i j v : Nat) :
    (a.setIfInBounds i v).getD j 0 = if i = j ∧ i < a.size then v else a.getD j 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h
    by_cases hs : i < a.size
    · simp [hs]
    · simp [hs]
  · simp [h]

theorem wf_empty (size : Nat) : (empty size).WF size := by
  refine ⟨by simp [empty], by simp [empty], fun i => ?_⟩
  simp only [empty, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

theorem WF.clear {m : Marks} {n : Nat} (h : m.WF n) : m.clear.WF n :=
  ⟨h.size, by simp [Marks.clear], fun i => Nat.le_succ_of_le (h.le i)⟩

theorem contains_clear {m : Marks} {n : Nat} (h : m.WF n) (x : Nat) : m.clear.contains x = false := by
  have := h.le x
  simp only [Marks.clear, Marks.contains, beq_eq_false_iff_ne]
  omega

theorem WF.add {m : Marks} {n : Nat} (h : m.WF n) (x : Nat) : (m.add x).WF n := by
  refine ⟨by simpa [Marks.add] using h.size, h.pos, fun i => ?_⟩
  simp only [Marks.add, getD_set]
  split
  · exact Nat.le_refl _
  · exact h.le i

theorem WF.remove {m : Marks} {n : Nat} (h : m.WF n) (x : Nat) : (m.remove x).WF n := by
  refine ⟨by simpa [Marks.remove] using h.size, h.pos, fun i => ?_⟩
  simp only [Marks.remove, getD_set]
  split
  · exact Nat.zero_le _
  · exact h.le i

theorem contains_add {m : Marks} {n : Nat} (h : m.WF n) {x : Nat} (hx : x < n) (y : Nat) :
    (m.add x).contains y = true ↔ y = x ∨ m.contains y = true := by
  simp only [Marks.add, Marks.contains, getD_set, h.size, hx, and_true, beq_iff_eq]
  by_cases he : x = y
  · simp [he]
  · have : y ≠ x := fun e => he e.symm
    simp [he, this]

/-- Without the bound: what is marked was added or was there. -/
theorem contains_add_of {m : Marks} {x y : Nat} (h : (m.add x).contains y = true) : y = x ∨ m.contains y = true := by
  simp only [Marks.add, Marks.contains, getD_set, beq_iff_eq] at h
  split at h
  · rename_i hc
    exact Or.inl hc.1.symm
  · simp [Marks.contains, h]

theorem contains_remove {m : Marks} {n : Nat} (h : m.WF n) {x : Nat} (hx : x < n) (y : Nat) :
    (m.remove x).contains y = true ↔ y ≠ x ∧ m.contains y = true := by
  have hpos := h.pos
  simp only [Marks.remove, Marks.contains, getD_set, h.size, hx, and_true, beq_iff_eq]
  by_cases he : x = y
  · subst he
    simp only [↓reduceIte, ne_eq, not_true_eq_false, false_and, iff_false]
    omega
  · have : y ≠ x := fun e => he e.symm
    simp [he, this]

theorem WF.foldl_add {m : Marks} {n : Nat} (h : m.WF n) (l : List Nat) : (l.foldl Marks.add m).WF n := by
  induction l generalizing m with
  | nil => exact h
  | cons a as ih => exact ih (h.add a)

theorem contains_foldl_add {m : Marks} {n : Nat} (h : m.WF n) {l : List Nat} (hl : ∀ x ∈ l, x < n) (y : Nat) :
    (l.foldl Marks.add m).contains y = true ↔ y ∈ l ∨ m.contains y = true := by
  induction l generalizing m with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [ih (h.add a) fun x hx => hl x (List.mem_cons_of_mem _ hx), contains_add h (hl a List.mem_cons_self), List.mem_cons]
    grind

end Marks

theorem mem_nodup {seen : Marks} {n : Nat} (hw : seen.WF n) (l : List Nat) (x : Nat) : x ∈ (nodup seen l).1 ↔ x ∈ l := by
  have key : ∀ (l : List Nat) (state : List Nat × Marks), state.2.WF n → (∀ y, state.2.contains y = true → y ∈ state.1) →
      (l.foldl (init := state) fun state x => if state.2.contains x then state else (x :: state.1, state.2.add x)).2.WF n ∧
      ∀ y, y ∈ (l.foldl (init := state) fun state x => if state.2.contains x then state else (x :: state.1, state.2.add x)).1 ↔ y ∈ state.1 ∨ y ∈ l := by
    intro l
    induction l with
    | nil => intro state hw _; exact ⟨hw, by simp⟩
    | cons a as ih =>
      intro state hw hs
      simp only [List.foldl_cons]
      split
      · rename_i hc
        obtain ⟨h1, h2⟩ := ih state hw hs
        refine ⟨h1, fun y => ?_⟩
        rw [h2, List.mem_cons]
        have := hs a hc
        grind
      · obtain ⟨h1, h2⟩ := ih (a :: state.1, state.2.add a) (hw.add a) (by
          intro y hy
          rcases Marks.contains_add_of hy with rfl | hy
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hs y hy))
        refine ⟨h1, fun y => ?_⟩
        rw [h2]
        simp only [List.mem_cons]
        grind
  have := (key l ([], seen.clear) hw.clear (by
    intro y hy
    rw [Marks.contains_clear hw] at hy
    cases hy)).2 x
  simpa [nodup] using this

theorem nodup_wf {seen : Marks} {n : Nat} (hw : seen.WF n) (l : List Nat) : (nodup seen l).2.WF n := by
  have key : ∀ (l : List Nat) (state : List Nat × Marks), state.2.WF n →
      (l.foldl (init := state) fun state x => if state.2.contains x then state else (x :: state.1, state.2.add x)).2.WF n := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a as ih =>
      intro state h
      simp only [List.foldl_cons]
      split
      · exact ih _ h
      · exact ih _ (h.add a)
  exact key l _ hw.clear

theorem Row.contains_ofList (blocks : List Nat) (b : Nat) : (Row.ofList blocks).contains b = true ↔ b ∈ blocks := by
  unfold Row.ofList
  split <;> simp [Row.contains, Std.HashSet.contains_ofList]

/-! ### Numbers for variables -/

/-- The numbers: all different, and below the number of them. -/
structure IdsWF (ids : Ids) : Prop where
  lt : ∀ x, ids.contains x = true → idOf ids x < ids.size
  inj : ∀ x y, ids.contains x = true → ids.contains y = true → idOf ids x = idOf ids y → x = y

theorem idsWF_empty : IdsWF ({} : Ids) := ⟨by simp, by simp⟩

private theorem get_insert {ids : Ids} {x y : Bap.Var} {v : Nat} :
    idOf (ids.insert x v) y = if x = y then v else idOf ids y := by
  simp only [idOf, Std.HashMap.getD_insert]
  by_cases h : x = y <;> simp [h]

theorem internAll_wf {ids : Ids} (h : IdsWF ids) (vars : List Bap.Var) : IdsWF (internAll ids vars) := by
  induction vars generalizing ids with
  | nil => exact h
  | cons a as ih =>
    simp only [internAll, List.foldl_cons]
    apply ih
    split
    · exact h
    · rename_i hn
      constructor
      · intro x hx
        rw [get_insert, Std.HashMap.size_insert]
        have hna : a ∉ ids := by simpa using hn
        simp only [hna, ↓reduceIte]
        by_cases he : a = x
        · simp [he]
        · have hx' : ids.contains x = true := by simpa [Std.HashMap.contains_insert, he] using hx
          simp only [he, ↓reduceIte]
          have := h.lt x hx'
          omega
      · intro x y hx hy he
        rw [get_insert, get_insert] at he
        by_cases hax : a = x
        · by_cases hay : a = y
          · rw [← hax, ← hay]
          · have hy' : ids.contains y = true := by simpa [Std.HashMap.contains_insert, hay] using hy
            simp only [hax, ↓reduceIte] at he
            simp only [← hax, hay, ↓reduceIte] at he
            have := h.lt y hy'
            omega
        · by_cases hay : a = y
          · have hx' : ids.contains x = true := by simpa [Std.HashMap.contains_insert, hax] using hx
            simp only [hax, ↓reduceIte, ← hay] at he
            have := h.lt x hx'
            omega
          · have hx' : ids.contains x = true := by simpa [Std.HashMap.contains_insert, hax] using hx
            have hy' : ids.contains y = true := by simpa [Std.HashMap.contains_insert, hay] using hy
            simp only [hax, hay, ↓reduceIte] at he
            exact h.inj x y hx' hy' he

theorem contains_internAll (ids : Ids) (vars : List Bap.Var) (x : Bap.Var) :
    (internAll ids vars).contains x = true ↔ ids.contains x = true ∨ x ∈ vars := by
  induction vars generalizing ids with
  | nil => simp [internAll]
  | cons a as ih =>
    simp only [internAll, List.foldl_cons, List.mem_cons]
    rw [show as.foldl (fun ids x => if ids.contains x then ids else ids.insert x ids.size)
      (if ids.contains a then ids else ids.insert a ids.size) = internAll (if ids.contains a then ids else ids.insert a ids.size) as from rfl, ih]
    split
    · rename_i hc
      by_cases hx : x = a
      · subst hx
        simp [hc]
      · simp [hx]
    · simp only [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq]
      grind

/-! ### Going back from what starts a variable -/

section Flood

variable {blocks : Array DBlk} {preds : Array (List Nat)} {x : Nat} {skip : Nat → Bool}

/-- The blocks where a variable is live, as far as `floodD` goes. -/
structure FloodSpec (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) (skip : Nat → Bool) (live : Nat → Prop) : Prop where
  step : ∀ t, live t → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [], skip p = false → live p

private structure FloodInv (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) (skip : Nat → Bool) (live : Nat → Prop) (seen : Marks) (row work : List Nat) : Prop where
  sound : ∀ t ∈ row, live t
  marked : ∀ t, seen.contains t = true → t ∈ row
  closed : ∀ t ∈ row, t ∉ work → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [],
    skip p = false → p ∈ row
  work : ∀ t ∈ work, t ∈ row

private theorem visitPreds_inv {live : Nat → Prop} {n : Nat} (ps : List Nat) (hlive : ∀ p ∈ ps, skip p = false → live p)
    (state : Marks × List Nat × List Nat) (hw : state.1.WF n) (hsound : ∀ t ∈ state.2.1, live t)
    (hmarked : ∀ t, state.1.contains t = true → t ∈ state.2.1) (hwork : ∀ t ∈ state.2.2, t ∈ state.2.1) :
    let next := visitPredsD skip ps state
    next.1.WF n ∧ (∀ t ∈ next.2.1, live t) ∧ (∀ t, next.1.contains t = true → t ∈ next.2.1) ∧ (∀ t ∈ next.2.2, t ∈ next.2.1) ∧
      (∀ t ∈ state.2.1, t ∈ next.2.1) ∧ (∀ t ∈ state.2.2, t ∈ next.2.2) ∧ (∀ t ∈ next.2.1, t ∈ state.2.1 ∨ t ∈ next.2.2) ∧
      ∀ p ∈ ps, skip p = false → p ∈ next.2.1 := by
  induction ps generalizing state with
  | nil => exact ⟨hw, hsound, hmarked, hwork, fun _ h => h, fun _ h => h, fun _ h => Or.inl h, by simp⟩
  | cons p rest ih =>
    simp only [visitPredsD, List.foldl_cons]
    split
    · rename_i hc
      have := ih (fun q hq => hlive q (List.mem_cons_of_mem _ hq)) state hw hsound hmarked hwork
      refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, fun q hq hk => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact this.2.2.2.2.1 _ (hmarked _ hc)
      · exact this.2.2.2.2.2.2.2 q hq hk
    · split
      · rename_i hk
        have := ih (fun q hq => hlive q (List.mem_cons_of_mem _ hq)) state hw hsound hmarked hwork
        refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, fun q hq hk' => ?_⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hk] at hk'
          cases hk'
        · exact this.2.2.2.2.2.2.2 q hq hk'
      · rename_i hk
        have hk' : skip p = false := by simpa using hk
        have := ih (fun q hq => hlive q (List.mem_cons_of_mem _ hq)) (state.1.add p, p :: state.2.1, p :: state.2.2) (hw.add p)
          (by
            intro t ht
            rcases List.mem_cons.1 ht with rfl | ht
            · exact hlive _ List.mem_cons_self hk'
            · exact hsound t ht)
          (by
            intro t ht
            rcases Marks.contains_add_of ht with rfl | ht
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmarked t ht))
          (by
            intro t ht
            rcases List.mem_cons.1 ht with rfl | ht
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hwork t ht))
        refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, fun t ht => this.2.2.2.2.1 t (List.mem_cons_of_mem _ ht),
          fun t ht => this.2.2.2.2.2.1 t (List.mem_cons_of_mem _ ht), fun t ht => ?_, fun q hq hk2 => ?_⟩
        · rcases this.2.2.2.2.2.2.1 t ht with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inr (this.2.2.2.2.2.1 _ List.mem_cons_self)
            · exact Or.inl h
          · exact Or.inr h
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact this.2.2.2.2.1 _ List.mem_cons_self
          · exact this.2.2.2.2.2.2.2 q hq hk2

private theorem floodD_inv {live : Nat → Prop} {n : Nat} (hspec : FloodSpec blocks preds x skip live) (fuel : Nat) (seen : Marks) (row work : List Nat)
    (result : List Nat) (seen' : Marks) (hw : seen.WF n) (hinv : FloodInv blocks preds x skip live seen row work)
    (hr : floodD blocks preds x skip fuel seen row work = some (result, seen')) :
    seen'.WF n ∧ FloodInv blocks preds x skip live seen' result [] ∧ ∀ t ∈ row, t ∈ result := by
  induction fuel generalizing seen row work with
  | zero => simp [floodD] at hr
  | succ fuel ih =>
    cases work with
    | nil =>
      simp only [floodD, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hw, hinv, fun _ h => h⟩
    | cons t work =>
      simp only [floodD] at hr
      split at hr
      · rename_i hphi
        obtain ⟨h1, h2, h3⟩ := ih seen row work hw ⟨hinv.sound, hinv.marked, fun q hq hn hp p hps hk => by
          by_cases hqt : q = t
          · subst hqt
            rw [hphi] at hp
            cases hp
          · exact hinv.closed q hq (by simpa [hqt] using hn) hp p hps hk, fun q hq => hinv.work q (List.mem_cons_of_mem _ hq)⟩ hr
        exact ⟨h1, h2, h3⟩
      · rename_i hphi
        have hphi' : hasPhiD (blkAt blocks t) x = false := by simpa using hphi
        have htr := hinv.work t List.mem_cons_self
        obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := visitPreds_inv (skip := skip) (live := live) (n := n) (preds.getD t [])
          (fun p hp hk => hspec.step t (hinv.sound t htr) hphi' p hp hk) (seen, row, work) hw hinv.sound hinv.marked
          (fun q hq => hinv.work q (List.mem_cons_of_mem _ hq))
        obtain ⟨h1, h2, h3⟩ := ih _ _ _ n1 ⟨n2, n3, fun q hq hn hp p hps hk => by
          by_cases hqt : q = t
          · subst hqt
            exact n8 p hps hk
          · rcases n7 q hq with hq' | hq'
            · have hn' : q ∉ t :: work := by
                simp only [List.mem_cons, not_or]
                exact ⟨hqt, fun hm => hn (n6 q hm)⟩
              exact n5 _ (hinv.closed q hq' hn' hp p hps hk)
            · exact (hn hq').elim, n4⟩ hr
        exact ⟨h1, h2, fun q hq => h3 q (n5 q hq)⟩

/-- What `floodD` finds, from what starts a variable: if the fuel lasts, all that is live, and nothing else. -/
theorem floodD_spec {live : Nat → Prop} {n : Nat} (hspec : FloodSpec blocks preds x skip live) {fuel : Nat} {seen seen' : Marks} {start result : List Nat}
    (hw : seen.WF n) (hmarked : ∀ t, seen.contains t = true → t ∈ start) (hstart : ∀ t ∈ start, live t)
    (hleast : ∀ Row : Nat → Prop, (∀ t ∈ start, Row t) →
      (∀ t, Row t → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [], skip p = false → Row p) → ∀ t, live t → Row t)
    (hr : floodD blocks preds x skip fuel seen start start = some (result, seen')) :
    seen'.WF n ∧ ∀ t, t ∈ result ↔ live t := by
  obtain ⟨h1, h2, h3⟩ := floodD_inv hspec fuel seen start start result seen' hw ⟨hstart, hmarked, fun _ _ hn => (hn (by assumption)).elim, fun _ h => h⟩ hr
  refine ⟨h1, fun t => ⟨h2.sound t, hleast (· ∈ result) h3 ?_ t⟩⟩
  intro q hq hp p hps hk
  exact h2.closed q hq (by simp) hp p hps hk

end Flood

/-! ### What the numbers stand for -/

section Blocks

variable {ids : Ids} {effect : Bil.Exp → Bool}

private theorem any_congr {α : Type} {f g : α → Bool} {l : List α} (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.any_cons, h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Every variable a list of them mentions has a number. -/
private theorem id_eq_iff (h : IdsWF ids) {x y : Bap.Var} (hx : ids.contains x = true) (hy : ids.contains y = true) :
    (idOf ids y == idOf ids x) = (y == x) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨h.inj y x hy hx, fun e => e ▸ rfl⟩

theorem hasPhiD_dense (h : IdsWF ids) {blk : Blk} (hv : ∀ y ∈ vocabulary blk, ids.contains y = true) {x : Bap.Var}
    (hx : ids.contains x = true) : hasPhiD (denseBlk effect ids blk) (idOf ids x) = hasPhi blk x := by
  simp only [hasPhiD, denseBlk, hasPhi, List.any_map]
  apply any_congr
  intro phi hp
  exact id_eq_iff h (y := phi.var) hx (hv _ (by
    simp only [vocabulary, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨phi, hp, rfl⟩))))

theorem killedD_dense (h : IdsWF ids) {blk : Blk} (hv : ∀ y ∈ vocabulary blk, ids.contains y = true) {x : Bap.Var}
    (hx : ids.contains x = true) : killedD (denseBlk effect ids blk) (idOf ids x) = killed blk x := by
  simp only [killedD, denseBlk, killed, List.any_map]
  congr 1
  · apply any_congr
    intro phi hp
    exact id_eq_iff h (y := phi.var) hx (hv _ (by
    simp only [vocabulary, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨phi, hp, rfl⟩))))
  · apply any_congr
    intro d hd
    exact id_eq_iff h (y := d.var) hx (hv _ (by
      simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)))

theorem phiReadsD_dense (h : IdsWF ids) {blk : Blk} (hv : ∀ y ∈ vocabulary blk, ids.contains y = true) (source : Tid) {x : Bap.Var}
    (hx : ids.contains x = true) : idOf ids x ∈ phiReadsD source (denseBlk effect ids blk) ↔ x ∈ phiReads source blk := by
  simp only [phiReadsD, denseBlk, List.mem_flatMap, List.mem_map]
  have hget : ∀ phi : Phi, (∀ y, (∃ input ∈ phi.values, y ∈ Bil.freeVars input.2) → ids.contains y = true) →
      (idOf ids x ∈ (Assoc.get source (densePhi ids phi).inputs).getD [] ↔
        ∃ value, Assoc.get source phi.values = some value ∧ x ∈ Bil.freeVars value) := by
    intro phi hphi
    have hlook : Assoc.get source (densePhi ids phi).inputs =
        (Assoc.get source phi.values).map fun value => (Bil.freeVars value).map (idOf ids) := by
      simp only [densePhi]
      generalize phi.values = values
      induction values with
      | nil => rfl
      | cons head tail ih =>
        obtain ⟨k, v⟩ := head
        simp only [List.map_cons, Assoc.get, List.lookup_cons] at ih ⊢
        cases source == k with
        | true => rfl
        | false => exact ih
    rw [hlook]
    cases hg : Assoc.get source phi.values with
    | none => simp
    | some value =>
      have hmem : (source, value) ∈ phi.values := by
        have := List.lookup_eq_some_iff.1 hg
        obtain ⟨l, r, hl, _⟩ := this
        simp [hl]
      simp only [Option.map_some, Option.getD_some, Option.some.injEq, exists_eq_left', List.mem_map]
      constructor
      · rintro ⟨y, hy, he⟩
        have := h.inj y x (hphi y ⟨(source, value), hmem, hy⟩) hx he
        exact this ▸ hy
      · intro hy
        exact ⟨x, hy, rfl⟩
  have hreads : ∀ phi ∈ blk.phis, ∀ y, (∃ input ∈ phi.values, y ∈ Bil.freeVars input.2) → ids.contains y = true := by
    rintro phi hp y ⟨input, hi, hy⟩
    apply hv
    simp only [vocabulary, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl (Or.inr ⟨phi, hp, input, hi, hy⟩))
  rw [mem_phiReads]
  constructor
  · rintro ⟨_, ⟨phi, hp, rfl⟩, hm⟩
    obtain ⟨value, hg, hy⟩ := (hget phi (hreads phi hp)).1 hm
    exact ⟨phi, hp, value, hg, hy⟩
  · rintro ⟨phi, hp, value, hg, hy⟩
    exact ⟨_, ⟨phi, hp, rfl⟩, (hget phi (hreads phi hp)).2 ⟨value, hg, hy⟩⟩

/-- All the numbers of a block are below `n`. -/
def BlockBound (d : DBlk) (n : Nat) : Prop :=
  (∀ phi ∈ d.phis, phi.var < n) ∧ (∀ defn ∈ d.defs, defn.var < n ∧ ∀ y ∈ defn.reads, y < n) ∧ ∀ y ∈ d.jmpReads, y < n

/-- The list of the fold over the definitions of `exposedD`. -/
private theorem exposedDefs {n : Nat} (defs : List Def) (hdefs : ∀ d ∈ defs, ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true)
    (hids : IdsWF ids) (hn : ids.size ≤ n) (out : List Nat) (kills : Marks) (hw : kills.WF n) {x : Bap.Var} (hx : ids.contains x = true) :
    let dense := defs.map (denseDef effect ids)
    let step := dense.foldl (init := (out, kills)) fun state defn =>
      (defn.reads.foldl (fun out y => if state.2.contains y then out else y :: out) state.1, state.2.add defn.var)
    step.2.WF n ∧ (step.2.contains (idOf ids x) = true ↔ kills.contains (idOf ids x) = true ∨ ∃ d ∈ defs, d.var = x) ∧
      (idOf ids x ∈ step.1 ↔ idOf ids x ∈ out ∨ (kills.contains (idOf ids x) = false ∧ Exposed defs x)) := by
  induction defs generalizing out kills with
  | nil => simp [Exposed, hw]
  | cons d ds ih =>
    have hd := hdefs d List.mem_cons_self
    have hreads : ∀ (l : List Nat) (o : List Nat), idOf ids x ∈ l.foldl (fun out y => if kills.contains y then out else y :: out) o ↔
        idOf ids x ∈ o ∨ (idOf ids x ∈ l ∧ kills.contains (idOf ids x) = false) := by
      intro l
      induction l with
      | nil => simp
      | cons a as iha =>
        intro o
        simp only [List.foldl_cons, iha, List.mem_cons]
        split
        · rename_i hc
          by_cases he : idOf ids x = a
          · subst he
            simp [hc]
          · simp [he]
        · rename_i hc
          by_cases he : idOf ids x = a
          · subst he
            simp [Bool.eq_false_iff.2 hc]
          · simp [he]
    simp only [List.map_cons, List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (fun e he => hdefs e (List.mem_cons_of_mem _ he)) ((denseDef effect ids d).reads.foldl (fun out y => if kills.contains y then out else y :: out) out)
      (kills.add (denseDef effect ids d).var) (hw.add _)
    have hlt : (denseDef effect ids d).var < n := Nat.lt_of_lt_of_le (hids.lt _ hd.1) hn
    have hadd : (kills.add (denseDef effect ids d).var).contains (idOf ids x) = true ↔ d.var = x ∨ kills.contains (idOf ids x) = true := by
      rw [Marks.contains_add hw hlt]
      constructor
      · rintro (he | he)
        · exact Or.inl (hids.inj _ _ hd.1 hx he.symm)
        · exact Or.inr he
      · rintro (he | he)
        · exact Or.inl (he ▸ rfl)
        · exact Or.inr he
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, hadd]
      simp only [List.mem_cons, exists_eq_or_imp]
      grind
    · rw [h3, hreads]
      have hmem : idOf ids x ∈ (denseDef effect ids d).reads ↔ x ∈ Bil.freeVars d.rhs := by
        simp only [denseDef, List.mem_map]
        constructor
        · rintro ⟨y, hy, he⟩
          exact hids.inj y x (hd.2 y hy) hx he ▸ hy
        · exact fun hy => ⟨x, hy, rfl⟩
      rw [hmem]
      have hnot : (kills.add (denseDef effect ids d).var).contains (idOf ids x) = false ↔ d.var ≠ x ∧ kills.contains (idOf ids x) = false := by
        simp only [Bool.eq_false_iff, ne_eq, hadd, not_or]
      rw [hnot]
      simp only [Exposed]
      have hne : d.var ≠ x ↔ x ≠ d.var := ne_comm
      rw [hne]
      grind

theorem exposedD_spec {n : Nat} (hids : IdsWF ids) (hn : ids.size ≤ n) {blk : Blk} (hv : ∀ y ∈ vocabulary blk, ids.contains y = true) {kills : Marks}
    (hw : kills.WF n) {x : Bap.Var} (hx : ids.contains x = true) :
    (exposedD kills (denseBlk effect ids blk)).2.WF n ∧
      (idOf ids x ∈ (exposedD kills (denseBlk effect ids blk)).1 ↔ x ∈ blockIn blk []) := by
  have hphis : ∀ (l : List Phi) (m : Marks), m.WF n → (∀ p ∈ l, ids.contains p.var = true) →
      ((l.map (densePhi ids)).foldl (fun kills phi => kills.add phi.var) m).WF n ∧
      (((l.map (densePhi ids)).foldl (fun kills phi => kills.add phi.var) m).contains (idOf ids x) = true ↔
        m.contains (idOf ids x) = true ∨ ∃ p ∈ l, p.var = x) := by
    intro l
    induction l with
    | nil => intro m hm _; simp [hm]
    | cons p ps ih =>
      intro m hm hp
      simp only [List.map_cons, List.foldl_cons]
      have hpv := hp p List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (m.add (densePhi ids p).var) (hm.add _) fun q hq => hp q (List.mem_cons_of_mem _ hq)
      refine ⟨h1, ?_⟩
      have hlt : (densePhi ids p).var < n := Nat.lt_of_lt_of_le (hids.lt _ hpv) hn
      rw [h2, Marks.contains_add hm hlt]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((he | he) | he)
        · exact Or.inr (Or.inl (hids.inj _ _ hpv hx he.symm))
        · exact Or.inl he
        · exact Or.inr (Or.inr he)
      · rintro (he | he | he)
        · exact Or.inl (Or.inr he)
        · exact Or.inl (Or.inl (he ▸ rfl))
        · exact Or.inr he
  have hpv : ∀ p ∈ blk.phis, ids.contains p.var = true := fun p hp => hv _ (by
    simp only [vocabulary, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩)))
  have hdv : ∀ d ∈ blk.defs, ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true := fun d hd =>
    ⟨hv _ (by
      simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)), fun y hy => hv _ (by
      simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact Or.inl (Or.inr ⟨d, hd, Or.inr hy⟩))⟩
  obtain ⟨p1, p2⟩ := hphis blk.phis kills.clear hw.clear hpv
  have hclear := Marks.contains_clear hw (idOf ids x)
  rw [hclear] at p2
  obtain ⟨d1, d2, d3⟩ := exposedDefs (effect := effect) blk.defs hdv hids hn [] _ p1 hx
  have final : ∀ step : List Nat × Marks, step.2.WF n →
      (step.2.contains (idOf ids x) = true ↔
        ((blk.phis.map (densePhi ids)).foldl (fun kills phi => kills.add phi.var) kills.clear).contains (idOf ids x) = true ∨ ∃ d ∈ blk.defs, d.var = x) →
      (idOf ids x ∈ step.1 ↔ idOf ids x ∈ ([] : List Nat) ∨
        (((blk.phis.map (densePhi ids)).foldl (fun kills phi => kills.add phi.var) kills.clear).contains (idOf ids x) = false ∧ Exposed blk.defs x)) →
      step.2.WF n ∧ (idOf ids x ∈ ((blk.jmps.flatMap Jmp.freeVars).map (idOf ids)).foldl (fun out y => if step.2.contains y then out else y :: out) step.1 ↔
        x ∈ blockIn blk []) := by
    intro step d1 d2 d3
    refine ⟨d1, ?_⟩
    have hjmp : ∀ (l : List Nat) (o : List Nat), idOf ids x ∈ l.foldl (fun out y => if step.2.contains y then out else y :: out) o ↔
        idOf ids x ∈ o ∨ (idOf ids x ∈ l ∧ step.2.contains (idOf ids x) = false) := by
      intro l
      induction l with
      | nil => simp
      | cons a as iha =>
        intro o
        simp only [List.foldl_cons, iha, List.mem_cons]
        split
        · rename_i hc
          by_cases he : idOf ids x = a
          · subst he
            simp [hc]
          · simp [he]
        · rename_i hc
          by_cases he : idOf ids x = a
          · subst he
            simp [Bool.eq_false_iff.2 hc]
          · simp [he]
    rw [hjmp, d3, mem_blockIn]
    have hreadJ : idOf ids x ∈ (blk.jmps.flatMap Jmp.freeVars).map (idOf ids) ↔ ∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars := by
      simp only [List.mem_map, List.mem_flatMap]
      constructor
      · rintro ⟨y, ⟨j, hj, hy⟩, he⟩
        have hyv : ids.contains y = true := hv _ (by
          simp only [vocabulary, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨j, hj, hy⟩)
        exact ⟨j, hj, hids.inj y x hyv hx he ▸ hy⟩
      · rintro ⟨j, hj, hy⟩
        exact ⟨x, ⟨j, hj, hy⟩, rfl⟩
    rw [hreadJ]
    have hkill : step.2.contains (idOf ids x) = false ↔ (∀ p ∈ blk.phis, p.var ≠ x) ∧ ∀ d ∈ blk.defs, d.var ≠ x := by
      simp only [Bool.eq_false_iff, ne_eq, d2, p2]
      simp
    have hfirst : ((blk.phis.map (densePhi ids)).foldl (fun kills phi => kills.add phi.var) kills.clear).contains (idOf ids x) = false ↔ ∀ p ∈ blk.phis, p.var ≠ x := by
      simp only [Bool.eq_false_iff, ne_eq, p2]
      simp
    rw [hkill, hfirst]
    simp only [List.not_mem_nil, false_or, or_false]
    grind
  exact final _ d1 d2 d3

end Blocks

/-! ### Where a variable is live -/

section Refresh

/-- Where the blocks are, by position. -/
def At (cfg : Cfg) (i : Nat) (blk : Blk) : Prop := cfg.blocks[i]? = some blk

/-- The tables of `Graphs`, for a CFG with a block for each tid. -/
structure GraphsOK (g : Graphs) (ids : Ids) (cfg : Cfg) (protectedVars : List Bap.Var) (n : Nat) : Prop where
  tids : ∀ i blk, At cfg i blk → g.tids.getD i 0 = blk.tid
  block : ∀ i blk, At cfg i blk → cfg.block blk.tid = some blk
  index : ∀ t blk, cfg.block t = some blk → ∃ i, At cfg i blk ∧ blk.tid = t
  unique : ∀ i j a b, At cfg i a → At cfg j b → a.tid = b.tid → i = j
  count : cfg.blocks.length = n
  preds_in : ∀ i, ∀ p ∈ g.preds.getD i [], p < n
  preds : ∀ i b p c, At cfg i b → At cfg p c → (p ∈ g.preds.getD i [] ↔ c.tid ∈ cfg.reachable ∧ b.tid ∈ cfg.successors c.tid)
  succs_in : ∀ i, ∀ p ∈ g.succs.getD i [], p < n
  succs : ∀ i b s c, At cfg i b → At cfg s c → (s ∈ g.succs.getD i [] ↔ c.tid ∈ cfg.successors b.tid)
  reach : ∀ i b, At cfg i b → (g.reach.getD i false = true ↔ b.tid ∈ cfg.reachable)
  sites : ∀ i b, At cfg i b → ∀ y ∈ vocabulary b, i ∈ g.sites.getD (idOf ids y) []
  sites_in : ∀ y, ∀ s ∈ g.sites.getD y [], s < n
  definers : ∀ i b, At cfg i b → ∀ y ∈ assigned b, i ∈ g.definers.getD (idOf ids y) []
  definers_in : ∀ y, ∀ s ∈ g.definers.getD y [], s < n
  protect : ∀ x, ids.contains x = true → (g.protect.getD (idOf ids x) false = true ↔ x ∈ protectedVars)

/-- The dense blocks are those of a CFG. -/
structure Mirror (effect : Bil.Exp → Bool) (ids : Ids) (blocks : Array DBlk) (cfg : Cfg) : Prop where
  blocks : blocks.toList = cfg.blocks.map (denseBlk effect ids)
  named : ∀ blk ∈ cfg.blocks, ∀ y ∈ vocabulary blk, ids.contains y = true
  wf : IdsWF ids

variable {effect : Bil.Exp → Bool} {ids : Ids} {blocks : Array DBlk} {cfg : Cfg}

theorem Mirror.blkAt (h : Mirror effect ids blocks cfg) {i : Nat} {blk : Blk} (hi : At cfg i blk) :
    Bap.IR.DenseDce.blkAt blocks i = denseBlk effect ids blk := by
  have hl : blocks.toList[i]? = some (denseBlk effect ids blk) := by
    rw [h.blocks, List.getElem?_map]
    simp only [At] at hi
    simp [hi]
  have ha : blocks[i]? = some (denseBlk effect ids blk) := by
    simpa using hl
  simp only [Bap.IR.DenseDce.blkAt, Array.getD_eq_getD_getElem?, ha, Option.getD_some]

theorem At.mem {i : Nat} {blk : Blk} (hi : At cfg i blk) : blk ∈ cfg.blocks := by
  simp only [At] at hi
  exact List.mem_of_getElem? hi

theorem exists_at {blk : Blk} (h : blk ∈ cfg.blocks) : ∃ i, At cfg i blk := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, by simp only [At]; rw [List.getElem?_eq_getElem hi, he]⟩

theorem exposedD_wf {m : Marks} {N : Nat} (hm : m.WF N) (d : DBlk) : (exposedD m d).2.WF N := by
  have hp : ∀ (l : List DPhi) (m : Marks), m.WF N → (l.foldl (fun kills phi => kills.add phi.var) m).WF N := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons a as ih => exact fun m h => ih _ (h.add _)
  have hd : ∀ (l : List DDef) (o : List Nat) (m : Marks), m.WF N →
      (l.foldl (init := (o, m)) fun state defn =>
        (defn.reads.foldl (fun out y => if state.2.contains y then out else y :: out) state.1, state.2.add defn.var)).2.WF N := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons a as ih => exact fun o m h => ih _ _ (h.add _)
  exact hd _ _ _ (hp _ _ hm.clear)

theorem getD_modify (a : Array (List Nat)) (y j : Nat) (f : List Nat → List Nat) :
    (a.modify y f).getD j [] = if j = y ∧ y < a.size then f (a.getD j []) else a.getD j [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : y = j
  · subst h
    by_cases hs : y < a.size
    · simp [hs]
    · simp [hs]
  · have : j ≠ y := fun e => h e.symm
    simp [h, this]

private theorem addAll_spec (l : List Nat) (cond : Nat → Bool) (v : Nat) (seeds : Array (List Nat)) {N : Nat} (hs : seeds.size = N)
    (hc : ∀ y, cond y = true → y < N) (y i : Nat) :
    (l.foldl (fun seeds y => if cond y then seeds.modify y (v :: ·) else seeds) seeds).size = N ∧
      (i ∈ (l.foldl (fun seeds y => if cond y then seeds.modify y (v :: ·) else seeds) seeds).getD y [] ↔
        i ∈ seeds.getD y [] ∨ (i = v ∧ y ∈ l ∧ cond y = true)) := by
  induction l generalizing seeds with
  | nil => simp [hs]
  | cons a as ih =>
    simp only [List.foldl_cons]
    split
    · rename_i hca
      have hsz : (seeds.modify a (v :: ·)).size = N := by simpa using hs
      obtain ⟨h1, h2⟩ := ih (seeds.modify a (v :: ·)) hsz
      refine ⟨h1, ?_⟩
      rw [h2, getD_modify, List.mem_cons]
      by_cases hy : y = a
      · subst hy
        have hlt : y < seeds.size := hs ▸ hc y hca
        simp only [hlt, and_self, ↓reduceIte, List.mem_cons, hca]
        grind
      · simp only [hy, false_and, ↓reduceIte, false_or]
    · rename_i hca
      obtain ⟨h1, h2⟩ := ih seeds hs
      refine ⟨h1, ?_⟩
      rw [h2, List.mem_cons]
      by_cases hy : y = a
      · subst hy
        simp [hca]
      · simp [hy]

/-- What starts a variable. -/
theorem seedsD_spec {g : Graphs} {N : Nat} (mark : Array Bool) (hmark : mark.size = N) (sites : List Nat)
    (y i : Nat) (E : Nat → Prop) (hE : ∀ m : Marks, m.WF N → ∀ s ∈ sites, (y ∈ (exposedD m (Bap.IR.DenseDce.blkAt blocks s)).1 ↔ E s))
    (seeds : Array (List Nat)) (hseeds : seeds.size = N) (kills : Marks) (hk : kills.WF N) :
    (seedsD g blocks mark kills sites seeds).1.size = N ∧ (seedsD g blocks mark kills sites seeds).2.WF N ∧
      (i ∈ (seedsD g blocks mark kills sites seeds).1.getD y [] ↔ i ∈ seeds.getD y [] ∨ (mark.getD y false = true ∧ ∃ s ∈ sites,
        (i = s ∧ g.reach.getD s false = true ∧ E s) ∨
        (i ∈ g.preds.getD s [] ∧ y ∈ phiReadsD (g.tids.getD i 0) (Bap.IR.DenseDce.blkAt blocks s) ∧ killedD (Bap.IR.DenseDce.blkAt blocks i) y = false))) := by
  have hbound : ∀ z, mark.getD z false = true → z < N := by
    intro z hz
    cases Nat.lt_or_ge z N with
    | inl h => exact h
    | inr hn =>
      have : mark[z]? = none := by
        simp only [Array.getElem?_eq_none_iff]
        omega
      simp [Array.getD_eq_getD_getElem?, this] at hz
  have hphi : ∀ (ps : List Nat) (d : DBlk) (seeds : Array (List Nat)), seeds.size = N →
      (ps.foldl (init := seeds) fun seeds p =>
        (phiReadsD (g.tids.getD p 0) d).foldl (fun seeds y =>
          if mark.getD y false && !killedD (Bap.IR.DenseDce.blkAt blocks p) y then seeds.modify y (p :: ·) else seeds) seeds).size = N ∧
      (i ∈ (ps.foldl (init := seeds) fun seeds p =>
        (phiReadsD (g.tids.getD p 0) d).foldl (fun seeds y =>
          if mark.getD y false && !killedD (Bap.IR.DenseDce.blkAt blocks p) y then seeds.modify y (p :: ·) else seeds) seeds).getD y [] ↔
        i ∈ seeds.getD y [] ∨ (i ∈ ps ∧ y ∈ phiReadsD (g.tids.getD i 0) d ∧ mark.getD y false = true ∧ killedD (Bap.IR.DenseDce.blkAt blocks i) y = false)) := by
    intro ps d
    induction ps with
    | nil => intro seeds hs; simp [hs]
    | cons p rest ih =>
      intro seeds hs
      simp only [List.foldl_cons]
      obtain ⟨a1, a2⟩ := addAll_spec (phiReadsD (g.tids.getD p 0) d) (fun y => mark.getD y false && !killedD (Bap.IR.DenseDce.blkAt blocks p) y) p seeds hs
        (fun z hz => hbound z (by simp only [Bool.and_eq_true] at hz; exact hz.1)) y i
      obtain ⟨b1, b2⟩ := ih _ a1
      refine ⟨b1, ?_⟩
      rw [b2, a2, List.mem_cons]
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ((h | ⟨rfl, h1, h2, h3⟩) | ⟨h1, h2, h3, h4⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inl rfl, h1, h2, h3⟩
        · exact Or.inr ⟨Or.inr h1, h2, h3, h4⟩
      · rintro (h | ⟨h | h1, h2, h3, h4⟩)
        · exact Or.inl (Or.inl h)
        · subst h
          exact Or.inl (Or.inr ⟨rfl, h2, h3, h4⟩)
        · exact Or.inr ⟨h1, h2, h3, h4⟩
  simp only [seedsD]
  induction sites generalizing seeds kills with
  | nil => simp [hseeds, hk]
  | cons s rest ih =>
    simp only [List.foldl_cons]
    have hE' : ∀ m : Marks, m.WF N → ∀ s ∈ rest, (y ∈ (exposedD m (Bap.IR.DenseDce.blkAt blocks s)).1 ↔ E s) :=
      fun m hm q hq => hE m hm q (List.mem_cons_of_mem _ hq)
    generalize hst : (if g.reach.getD s false = true then _ else (seeds, kills)) = st
    have hst2 : st.2.WF N ∧ st.1.size = N ∧ (i ∈ st.1.getD y [] ↔ i ∈ seeds.getD y [] ∨ (i = s ∧ g.reach.getD s false = true ∧ E s ∧ mark.getD y false = true)) := by
      subst hst
      split
      · rename_i hr
        obtain ⟨a1, a2⟩ := addAll_spec (exposedD kills (Bap.IR.DenseDce.blkAt blocks s)).1 (fun y => mark.getD y false) s seeds hseeds hbound y i
        refine ⟨exposedD_wf hk _, a1, ?_⟩
        rw [a2, hE kills hk s List.mem_cons_self]
        simp only [hr, true_and]
      · rename_i hr
        simp [hseeds, hk, hr]
    obtain ⟨c1, c2, c3⟩ := hst2
    obtain ⟨p1, p2⟩ := hphi (g.preds.getD s []) (Bap.IR.DenseDce.blkAt blocks s) st.1 c2
    obtain ⟨r1, r2, r3⟩ := ih hE' _ p1 _ c1
    refine ⟨r1, r2, ?_⟩
    rw [r3, p2, c3]
    simp only [List.mem_cons, exists_eq_or_imp]
    grind

theorem seedsD_wf {g : Graphs} {N : Nat} {kills : Marks} (hk : kills.WF N) (mark : Array Bool) (blocks : Array DBlk) (sites : List Nat)
    (seeds : Array (List Nat)) : (seedsD g blocks mark kills sites seeds).2.WF N := by
  simp only [seedsD]
  induction sites generalizing seeds kills with
  | nil => exact hk
  | cons s rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact exposedD_wf hk _
    · exact hk

theorem mem_affectedMarks (size : Nat) (affected : List Nat) (y : Nat) :
    (affectedMarks size affected).getD y false = true ↔ y ∈ affected ∧ y < size := by
  have key : ∀ (l : List Nat) (m : Array Bool), m.size = size →
      (l.foldl (fun mark x => mark.setIfInBounds x true) m).size = size ∧
      ((l.foldl (fun mark x => mark.setIfInBounds x true) m).getD y false = true ↔ m.getD y false = true ∨ (y ∈ l ∧ y < size)) := by
    intro l
    induction l with
    | nil => intro m h; simp [h]
    | cons a as ih =>
      intro m h
      simp only [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (m.setIfInBounds a true) (by simpa using h)
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons]
      by_cases he : a = y
      · subst he
        by_cases hs : a < size
        · simp [h, hs]
        · simp [h, hs]
      · have : y ≠ a := fun e => he e.symm
        simp [he, this]
  have hz : (Array.replicate size false).getD y false = false := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [affectedMarks, (key affected (Array.replicate size false) (by simp)).2, hz]
  simp

theorem size_affectedMarks (size : Nat) (affected : List Nat) : (affectedMarks size affected).size = size := by
  have key : ∀ (l : List Nat) (m : Array Bool), (l.foldl (fun mark x => mark.setIfInBounds x true) m).size = m.size := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a as ih => intro m; simp only [List.foldl_cons]; rw [ih]; simp
  rw [affectedMarks, key]
  simp

/-- The rows for numbers `xs`, as far as `floodD` goes. `L y i` says what the row of `y` has to be. -/
theorem refreshRows_spec {preds : Array (List Nat)} {seeds : Array (List Nat)} {n : Nat} (L : Nat → Nat → Prop)
    (xs : List Nat) (hflood : ∀ y ∈ xs, FloodSpec blocks preds y (fun p => killedD (Bap.IR.DenseDce.blkAt blocks p) y) (L y)) (hsound : ∀ y ∈ xs, ∀ i, i ∈ seeds.getD y [] → L y i)
    (hleast : ∀ y ∈ xs, ∀ (Row : Nat → Prop), (∀ t ∈ seeds.getD y [], Row t) →
      (∀ t, Row t → hasPhiD (Bap.IR.DenseDce.blkAt blocks t) y = false → ∀ p ∈ preds.getD t [], killedD (Bap.IR.DenseDce.blkAt blocks p) y = false → Row p) →
      ∀ t, L y t → Row t)
    (rows result : Array Row) (seen seen' : Marks) (hxs : ∀ y ∈ xs, y < rows.size) (hw : seen.WF n) (hb : ∀ y ∈ xs, ∀ t ∈ seeds.getD y [], t < n)
    (hr : refreshRows blocks preds seeds rows seen xs = some (result, seen')) :
    seen'.WF n ∧ result.size = rows.size ∧ (∀ y, y ∉ xs → result.getD y (.short []) = rows.getD y (.short [])) ∧
      ∀ y ∈ xs, ∀ i, (result.getD y (.short [])).contains i = true ↔ L y i := by
  induction xs generalizing rows seen with
  | nil =>
    simp only [refreshRows, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hw, rfl, fun _ _ => rfl, by simp⟩
  | cons x rest ih =>
    have hgetRows : ∀ (r : Row) (a : Array Row) (y : Nat), x < a.size →
        (a.setIfInBounds x r).getD y (.short []) = if y = x then r else a.getD y (.short []) := by
      intro r a y hs
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      by_cases he : y = x
      · subst he
        simp [hs]
      · have : x ≠ y := fun e => he e.symm
        simp [he, this]
    have hx := hxs x List.mem_cons_self
    have hrest : ∀ (r : Row), ∀ y ∈ rest, y < (rows.setIfInBounds x r).size := fun r y hy => by
      simpa using hxs y (List.mem_cons_of_mem _ hy)
    have hfinish : ∀ (r : Row) (s : Marks), s.WF n → (∀ i, r.contains i = true ↔ L x i) →
        refreshRows blocks preds seeds (rows.setIfInBounds x r) s rest = some (result, seen') →
        seen'.WF n ∧ result.size = rows.size ∧ (∀ y, y ∉ x :: rest → result.getD y (.short []) = rows.getD y (.short [])) ∧
          ∀ y ∈ x :: rest, ∀ i, (result.getD y (.short [])).contains i = true ↔ L y i := by
      intro r s hsw hcorrect hnext
      obtain ⟨a1, a2, a3, a4⟩ := ih (fun y hy => hflood y (List.mem_cons_of_mem _ hy)) (fun y hy => hsound y (List.mem_cons_of_mem _ hy))
        (fun y hy => hleast y (List.mem_cons_of_mem _ hy)) (rows.setIfInBounds x r) s (hrest r) hsw (fun y hy => hb y (List.mem_cons_of_mem _ hy)) hnext
      refine ⟨a1, by simpa using a2, fun y hy => ?_, fun y hy i => ?_⟩
      · simp only [List.mem_cons, not_or] at hy
        rw [a3 y hy.2, hgetRows _ _ _ hx]
        simp [hy.1]
      · by_cases hyr : y ∈ rest
        · exact a4 y hyr i
        · have hyx : y = x := by simpa [hyr] using hy
          subst hyx
          rw [a3 y hyr, hgetRows _ _ _ hx]
          simpa using hcorrect i
    simp only [refreshRows] at hr
    cases hs : seeds.getD x [] with
    | nil =>
      rw [hs] at hr
      dsimp only at hr
      refine hfinish _ _ hw ?_ hr
      intro i
      simp only [Row.contains, List.contains_nil, Bool.false_eq_true, false_iff]
      intro hl
      exact (hleast x List.mem_cons_self (fun _ => False) (by simp [hs]) (fun _ h => h.elim) i hl)
    | cons first more =>
      rw [hs] at hr
      dsimp only at hr
      rw [← hs] at hr
      cases hf : floodD blocks preds x (fun p => killedD (Bap.IR.DenseDce.blkAt blocks p) x) ((seeds.getD x []).length + blocks.size + 1) ((seeds.getD x []).foldl Marks.add seen.clear) (seeds.getD x []) (seeds.getD x []) with
      | none =>
        rw [hf] at hr
        cases hr
      | some pair =>
        rw [hf] at hr
        obtain ⟨row, s⟩ := pair
        dsimp only at hr
        have hwc : (((seeds.getD x []).foldl Marks.add seen.clear)).WF n := hw.clear.foldl_add _
        have hin : ∀ t ∈ seeds.getD x [], t < n := hb x List.mem_cons_self
        have hmarked : ∀ t, ((seeds.getD x []).foldl Marks.add seen.clear).contains t = true → t ∈ seeds.getD x [] := by
          intro t ht
          rw [Marks.contains_foldl_add hw.clear hin, Marks.contains_clear hw] at ht
          simpa using ht
        obtain ⟨f1, f2⟩ := floodD_spec (hflood x List.mem_cons_self) hwc hmarked (fun t ht => hsound x List.mem_cons_self t ht) (hleast x List.mem_cons_self) hf
        exact hfinish _ _ f1 (fun i => by rw [Row.contains_ofList, f2]) hr

/-- What a row of the rows has in it, for a variable. -/
def RowsOK (ids : Ids) (cfg : Cfg) (rows : Array Row) (x : Bap.Var) : Prop :=
  ∀ i b, At cfg i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn cfg b.tid)

theorem refreshD_spec {g : Graphs} {ps : List Bap.Var} {n M : Nat} (hm : Mirror effect ids blocks cfg) (hg : GraphsOK g ids cfg ps n) (hnM : n ≤ M)
    {rows rows' : Array Row} (hsize : ids.size = rows.size) {affected : List Nat} {kills seen kills' seen' : Marks}
    (hk : kills.WF rows.size) (hs : seen.WF M)
    (hold : ∀ x, ids.contains x = true → idOf ids x ∉ affected → RowsOK ids cfg rows x)
    (hnames : ∀ y ∈ affected, ∃ x, ids.contains x = true ∧ idOf ids x = y)
    (hr : refreshD g blocks rows affected kills seen = some (rows', kills', seen')) :
    rows'.size = rows.size ∧ kills'.WF rows.size ∧ seen'.WF M ∧ ∀ x, ids.contains x = true → RowsOK ids cfg rows' x := by
  have hids := hm.wf
  have hat : ∀ {i}, i < n → ∃ b, At cfg i b := by
    intro i hi
    have hl : i < cfg.blocks.length := hg.count ▸ hi
    exact ⟨cfg.blocks[i], by simp only [At]; simp [hl]⟩
  have hsame : ∀ {i a b}, At cfg i a → At cfg i b → a = b := by
    intro i a b ha hb
    simp only [At] at ha hb
    rw [ha] at hb
    exact Option.some.inj hb
  have hnamed : ∀ {i b}, At cfg i b → ∀ y ∈ vocabulary b, ids.contains y = true := fun hi => hm.named _ hi.mem
  simp only [refreshD] at hr
  generalize hsites : nodup seen (affected.flatMap fun x => g.sites.getD x []) = sites at hr
  have hsitesMem : ∀ s, s ∈ sites.1 ↔ s ∈ affected.flatMap fun x => g.sites.getD x [] := fun s => by
    rw [← hsites]
    exact mem_nodup hs _ s
  have hsitesWF : sites.2.WF M := by
    rw [← hsites]
    exact nodup_wf hs _
  let mark := affectedMarks rows.size affected
  have hmark : mark.size = rows.size := size_affectedMarks _ _
  have hseedsSize : (Array.replicate rows.size ([] : List Nat)).size = rows.size := by simp
  have hrepl : ∀ y i, i ∉ (Array.replicate rows.size ([] : List Nat)).getD y [] := by
    intro y i
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp
  have hspec : ∀ x, ids.contains x = true → ∀ i,
      let result := seedsD g blocks mark kills sites.1 (Array.replicate rows.size [])
      result.1.size = rows.size ∧ result.2.WF rows.size ∧
      (i ∈ result.1.getD (idOf ids x) [] ↔ i ∈ (Array.replicate rows.size ([] : List Nat)).getD (idOf ids x) [] ∨ (mark.getD (idOf ids x) false = true ∧ ∃ s ∈ sites.1,
        (i = s ∧ g.reach.getD s false = true ∧ ∃ b, At cfg s b ∧ x ∈ blockIn b []) ∨
        (i ∈ g.preds.getD s [] ∧ idOf ids x ∈ phiReadsD (g.tids.getD i 0) (Bap.IR.DenseDce.blkAt blocks s) ∧ killedD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x) = false))) := by
    intro x hx i
    refine seedsD_spec mark hmark sites.1 (idOf ids x) i (fun s => ∃ b, At cfg s b ∧ x ∈ blockIn b []) ?_ _ hseedsSize kills hk
    intro m hmw s hsm
    obtain ⟨a, _, hsa⟩ := List.mem_flatMap.1 ((hsitesMem s).1 hsm)
    obtain ⟨b, hb⟩ := hat (hg.sites_in a s hsa)
    rw [hm.blkAt hb]
    have := (exposedD_spec (effect := effect) hids (Nat.le_of_eq hsize) (hnamed hb) hmw hx).2
    rw [this]
    constructor
    · exact fun h => ⟨b, hb, h⟩
    · rintro ⟨c, hc, h⟩
      rw [hsame hb hc]
      exact h
  generalize hseeds : seedsD g blocks mark kills sites.1 (Array.replicate rows.size []) = seeds at hspec
  have hseeds2 : seedsD g blocks (affectedMarks rows.size affected) kills sites.1 (Array.replicate rows.size []) = seeds := hseeds
  rw [hseeds2] at hr
  cases hrr : refreshRows blocks g.preds seeds.1 rows sites.2 affected with
  | none =>
    rw [hrr] at hr
    cases hr
  | some pair =>
    rw [hrr] at hr
    obtain ⟨result, s2⟩ := pair
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl⟩ := hr
    have hmarkOf : ∀ x, ids.contains x = true → idOf ids x ∈ affected → mark.getD (idOf ids x) false = true := by
      intro x hx ha
      exact (mem_affectedMarks _ _ _).2 ⟨ha, hsize ▸ hids.lt x hx⟩
    let L : Nat → Nat → Prop := fun y i => ∃ x b, ids.contains x = true ∧ idOf ids x = y ∧ At cfg i b ∧ x ∈ liveIn cfg b.tid
    have hstep : ∀ y ∈ affected, FloodSpec blocks g.preds y (fun p => killedD (Bap.IR.DenseDce.blkAt blocks p) y) (L y) := by
      intro y _
      refine ⟨?_⟩
      rintro t ⟨x, b, hx, rfl, hb, hl⟩ hp p hps hk'
      obtain ⟨c, hc⟩ := hat (hg.preds_in t p hps)
      refine ⟨x, c, hx, rfl, hc, ?_⟩
      rw [hm.blkAt hb, hasPhiD_dense hids (hnamed hb) hx, hasPhi_false_iff] at hp
      rw [hm.blkAt hc, killedD_dense hids (hnamed hc) hx] at hk'
      obtain ⟨h1, h2⟩ := (hg.preds t b p c hb hc).1 hps
      refine live_of_edge h1 (hg.block p c hc) (fun hkk => ?_) h2 ⟨b, hg.block t b hb, Or.inl ⟨hl, hp⟩⟩
      have := (killed_iff c x).2 hkk
      rw [hk'] at this
      cases this
    have hsoundAll : ∀ y ∈ affected, ∀ i, i ∈ seeds.1.getD y [] → L y i := by
      intro y hy i hi
      obtain ⟨x, hx, rfl⟩ := hnames y hy
      rcases ((hspec x hx i).2.2).1 hi with hz | ⟨_, s, hss, hc⟩
      · exact (hrepl _ _ hz).elim
      · rcases hc with ⟨rfl, hre, b, hb, hg'⟩ | ⟨hip, hread, hk'⟩
        · exact ⟨x, b, hx, rfl, hb, live_of_gen ((hg.reach i b hb).1 hre) (hg.block i b hb) hg'⟩
        · obtain ⟨c, hc⟩ := hat (hg.preds_in s i hip)
          obtain ⟨a, _, hsa⟩ := List.mem_flatMap.1 ((hsitesMem s).1 hss)
          obtain ⟨b, hb⟩ := hat (hg.sites_in a s hsa)
          refine ⟨x, c, hx, rfl, hc, ?_⟩
          obtain ⟨h1, h2⟩ := (hg.preds s b i c hb hc).1 hip
          rw [hm.blkAt hc, killedD_dense hids (hnamed hc) hx] at hk'
          rw [hm.blkAt hb, hg.tids i c hc, phiReadsD_dense hids (hnamed hb) _ hx] at hread
          refine live_of_edge h1 (hg.block i c hc) (fun hkk => ?_) h2 ⟨b, hg.block s b hb, Or.inr hread⟩
          have := (killed_iff c x).2 hkk
          rw [hk'] at this
          cases this
    have hleastAll : ∀ y ∈ affected, ∀ (Row : Nat → Prop), (∀ t ∈ seeds.1.getD y [], Row t) →
        (∀ t, Row t → hasPhiD (Bap.IR.DenseDce.blkAt blocks t) y = false → ∀ p ∈ g.preds.getD t [], killedD (Bap.IR.DenseDce.blkAt blocks p) y = false → Row p) →
        ∀ t, L y t → Row t := by
      intro y hy Row hstart hclosed t
      obtain ⟨x, hx, rfl⟩ := hnames y hy
      rintro ⟨x', b, hx', he, hb, hl⟩
      have hxx : x' = x := hids.inj _ _ hx' hx he
      subst hxx
      have hsiteOf : ∀ i c, At cfg i c → x' ∈ vocabulary c → i ∈ sites.1 := by
        intro i c hc hv
        rw [hsitesMem, List.mem_flatMap]
        exact ⟨_, hy, hg.sites i c hc x' hv⟩
      have hRow := live_least cfg x' (fun τ => ∃ j c, At cfg j c ∧ c.tid = τ ∧ Row j) ?_ ?_ hl
      · obtain ⟨j, c, hc, htid, hj⟩ := hRow
        have := hg.unique j t c b hc hb htid
        exact this ▸ hj
      · intro τ hτ blk hblk hgen
        obtain ⟨i, hi, htid⟩ := hg.index τ blk hblk
        subst htid
        refine ⟨i, blk, hi, rfl, hstart i ?_⟩
        refine ((hspec x' hx i).2.2).2 (Or.inr ⟨hmarkOf x' hx hy, i, hsiteOf i blk hi (vocabulary_of_gen hgen), Or.inl ⟨rfl, (hg.reach i blk hi).2 hτ, blk, hi, hgen⟩⟩)
      · intro τ hτ blk hblk hkk σ hσ hneed
        obtain ⟨i, hi, htid⟩ := hg.index τ blk hblk
        subst htid
        obtain ⟨bs, hbs, hc⟩ := hneed
        obtain ⟨is, his, hstid⟩ := hg.index σ bs hbs
        subst hstid
        have hkf : killedD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x') = false := by
          rw [hm.blkAt hi, killedD_dense hids (hnamed hi) hx, Bool.eq_false_iff]
          exact fun h => hkk ((killed_iff blk x').1 h)
        have hip : i ∈ g.preds.getD is [] := (hg.preds is bs i blk his hi).2 ⟨hτ, hσ⟩
        refine ⟨i, blk, hi, rfl, ?_⟩
        rcases hc with ⟨⟨j, c, hcj, htid, hj⟩, hnp⟩ | hread
        · have hje := hg.unique j is c bs hcj his htid
          subst hje
          refine hclosed j hj ?_ i hip hkf
          rw [hm.blkAt his, hasPhiD_dense hids (hnamed his) hx, hasPhi_false_iff]
          exact hnp
        · refine hstart i ?_
          refine ((hspec x' hx i).2.2).2 (Or.inr ⟨hmarkOf x' hx hy, is, hsiteOf is bs his (vocabulary_of_read hread), Or.inr ⟨hip, ?_, hkf⟩⟩)
          rw [hm.blkAt his, hg.tids i blk hi, phiReadsD_dense hids (hnamed his) _ hx]
          exact hread
    have hbAll : ∀ y ∈ affected, ∀ t ∈ seeds.1.getD y [], t < n := by
      intro y hy t ht
      obtain ⟨x, hx, rfl⟩ := hnames y hy
      rcases ((hspec x hx t).2.2).1 ht with hz | ⟨_, s, hss, hc⟩
      · exact (hrepl _ _ hz).elim
      · obtain ⟨a, _, hsa⟩ := List.mem_flatMap.1 ((hsitesMem s).1 hss)
        rcases hc with ⟨rfl, _⟩ | ⟨hip, _⟩
        · exact hg.sites_in a t hsa
        · exact hg.preds_in s t hip
    have hxs : ∀ y ∈ affected, y < rows.size := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hnames y hy
      exact hsize ▸ hids.lt x hx
    obtain ⟨r1, r2, r3, r4⟩ := refreshRows_spec (n := M) L affected hstep hsoundAll hleastAll rows result sites.2 s2 hxs hsitesWF
      (fun y hy t ht => Nat.lt_of_lt_of_le (hbAll y hy t ht) hnM) hrr
    refine ⟨r2, ?_, r1, ?_⟩
    · rw [← hseeds]
      exact seedsD_wf hk _ _ _ _
    · intro x hx i b hb
      by_cases ha : idOf ids x ∈ affected
      · rw [r4 _ ha]
        constructor
        · rintro ⟨x', c, hx', he, hc, hl⟩
          rw [hids.inj _ _ hx' hx he] at hl
          rw [hsame hb hc]
          exact hl
        · exact fun hl => ⟨x, b, hx, rfl, hb, hl⟩
      · rw [r3 _ ha]
        exact hold x hx ha i b hb

theorem block_of_unique {l : List Blk} (hu : ∀ (i j : Nat) (a b : Blk), l[i]? = some a → l[j]? = some b → a.tid = b.tid → i = j) {blk : Blk} (hb : blk ∈ l) :
    l.find? (fun candidate => candidate.tid = blk.tid) = some blk := by
  induction l with
  | nil => simp at hb
  | cons h t ih =>
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.1 hb
    by_cases ht : h.tid = blk.tid
    · have hj0 : j = 0 := hu j 0 blk h (by rw [List.getElem?_eq_getElem hj, he]) rfl ht.symm
      subst hj0
      simp only [List.getElem_cons_zero] at he
      subst he
      simp
    · have hne : blk ≠ h := fun e => ht (e ▸ rfl)
      have hbt : blk ∈ t := by simpa [hne] using hb
      rw [List.find?_cons]
      simp only [ht, decide_false]
      apply ih _ hbt
      intro i k a b ha hb' hab
      have := hu (i + 1) (k + 1) a b (by simpa using ha) (by simpa using hb') hab
      omega

theorem Mirror.ofBlocks (h : Mirror effect ids blocks cfg) : blocks.toList.map DBlk.toBlk = cfg.blocks := by
  rw [h.blocks, List.map_map]
  have : ∀ l : List Blk, l.map (DBlk.toBlk ∘ denseBlk effect ids) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
      simp only [List.map_cons, ih]
      congr 1
      cases a with
      | mk tid phis defs jmps =>
        simp only [Function.comp, DBlk.toBlk, denseBlk, List.map_map]
        have h1 : ∀ l : List Phi, l.map (DPhi.phi ∘ densePhi ids) = l := by
          intro l
          induction l with
          | nil => rfl
          | cons x xs ih => simp only [List.map_cons, ih]; rfl
        have h2 : ∀ l : List Def, l.map (DDef.defn ∘ denseDef effect ids) = l := by
          intro l
          induction l with
          | nil => rfl
          | cons x xs ih => simp only [List.map_cons, ih]; rfl
        rw [h1, h2]
  exact this _

/-! ### The tables, from a CFG -/

theorem internAll_onto {ids : Ids} (hw : IdsWF ids) (ho : ∀ y < ids.size, ∃ x, ids.contains x = true ∧ idOf ids x = y) (vars : List Bap.Var) :
    ∀ y < (internAll ids vars).size, ∃ x, (internAll ids vars).contains x = true ∧ idOf (internAll ids vars) x = y := by
  induction vars generalizing ids with
  | nil => exact ho
  | cons a as ih =>
    simp only [internAll, List.foldl_cons]
    have hnext : ∀ y < (if ids.contains a then ids else ids.insert a ids.size).size, ∃ x,
        (if ids.contains a then ids else ids.insert a ids.size).contains x = true ∧
          idOf (if ids.contains a then ids else ids.insert a ids.size) x = y := by
      split
      · exact ho
      · rename_i hn
        intro y hy
        have hna : a ∉ ids := by simpa using hn
        rw [Std.HashMap.size_insert] at hy
        simp only [hna, ↓reduceIte] at hy
        by_cases hys : y = ids.size
        · exact ⟨a, by simp, by subst hys; simp [idOf]⟩
        · obtain ⟨x, hx, he⟩ := ho y (by omega)
          have hne : a ≠ x := fun e => hn (e ▸ hx)
          refine ⟨x, by simp [Std.HashMap.contains_insert, hx], ?_⟩
          rw [get_insert]
          simpa [hne] using he
    have hwf : IdsWF (if ids.contains a then ids else ids.insert a ids.size) := by
      have := internAll_wf hw [a]
      simpa [internAll] using this
    exact ih hwf hnext

theorem indexChecks_spec (index : Std.HashMap Tid Nat) (k : Nat) (l : List Blk) (h : indexChecks index k l = true) :
    ∀ i b, l[i]? = some b → index.get? b.tid = some (k + i) := by
  induction l generalizing k with
  | nil => simp
  | cons a as ih =>
    simp only [indexChecks, Bool.and_eq_true, beq_iff_eq] at h
    intro i b hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      simpa using h.1
    | succ i =>
      have := ih (k + 1) h.2 i b (by simpa using hb)
      rw [this]
      congr 1
      omega

theorem indexOf_spec (blocks : List Blk) (k : Nat) (l : List Blk) (table : Std.HashMap Tid Nat)
    (hl : ∀ i b, l[i]? = some b → blocks[k + i]? = some b)
    (ht : ∀ t s, table.get? t = some s → ∃ c, blocks[s]? = some c ∧ c.tid = t) :
    ∀ t s, (indexOf k l table).get? t = some s → ∃ c, blocks[s]? = some c ∧ c.tid = t := by
  induction l generalizing k table with
  | nil => exact ht
  | cons a as ih =>
    simp only [indexOf]
    apply ih
    · intro i b hb
      have := hl (i + 1) b (by simpa using hb)
      rwa [show k + (i + 1) = k + 1 + i by omega] at this
    · intro t s hg
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at hg
      split at hg
      · rename_i he
        have hte : a.tid = t := by simpa using he
        simp only [Option.some.injEq] at hg
        subst hg
        exact ⟨a, by simpa using hl 0 a (by simp), hte⟩
      · exact ht t s hg

private theorem positionTable_spec (ids : Ids) (vars : Blk → List Bap.Var) (N : Nat) (k : Nat) (l : List Blk) (table : Array (List Nat)) (hs : table.size = N)
    (hbound : ∀ blk ∈ l, ∀ y ∈ vars blk, idOf ids y < N) :
    (∀ y s, s ∈ (positionTable ids vars k l table).getD y [] → s ∈ table.getD y [] ∨ (k ≤ s ∧ s < k + l.length)) ∧
      (∀ y s, s ∈ table.getD y [] → s ∈ (positionTable ids vars k l table).getD y []) ∧
      ∀ i b, l[i]? = some b → ∀ y ∈ vars b, k + i ∈ (positionTable ids vars k l table).getD (idOf ids y) [] := by
  induction l generalizing k table with
  | nil =>
    simp only [positionTable]
    exact ⟨fun _ _ h => Or.inl h, fun _ _ h => h, by simp⟩
  | cons a as ih =>
    simp only [positionTable]
    have hfold : ∀ (ys : List Bap.Var) (t : Array (List Nat)), t.size = N → (∀ y ∈ ys, idOf ids y < N) →
        (ys.foldl (fun table y => table.modify (idOf ids y) (k :: ·)) t).size = N ∧
        (∀ y s, s ∈ (ys.foldl (fun table y => table.modify (idOf ids y) (k :: ·)) t).getD y [] ↔ s ∈ t.getD y [] ∨ (s = k ∧ ∃ z ∈ ys, idOf ids z = y)) := by
      intro ys
      induction ys with
      | nil => intro t h _; simp [h]
      | cons z zs iz =>
        intro t h hb
        simp only [List.foldl_cons]
        have hzb := hb z List.mem_cons_self
        obtain ⟨a1, a2⟩ := iz (t.modify (idOf ids z) (k :: ·)) (by simpa using h) fun q hq => hb q (List.mem_cons_of_mem _ hq)
        refine ⟨a1, fun y s => ?_⟩
        rw [a2, getD_modify]
        have hlt : idOf ids z < t.size := h ▸ hzb
        by_cases hy : y = idOf ids z
        · subst hy
          simp only [and_self, hlt, ↓reduceIte, List.mem_cons, exists_eq_or_imp]
          grind
        · have : idOf ids z ≠ y := fun e => hy e.symm
          simp [hy, this]
    obtain ⟨f1, f2⟩ := hfold (vars a) table hs (hbound a List.mem_cons_self)
    obtain ⟨r1, r2, r3⟩ := ih (k + 1) _ f1 fun blk hb y hy => hbound blk (List.mem_cons_of_mem _ hb) y hy
    refine ⟨?_, ?_, ?_⟩
    · intro y s hm
      rcases r1 y s hm with h | ⟨h1, h2⟩
      · rcases (f2 y s).1 h with h | ⟨rfl, _⟩
        · exact Or.inl h
        · exact Or.inr ⟨Nat.le_refl _, by simp⟩
      · exact Or.inr ⟨by omega, by simp only [List.length_cons]; omega⟩
    · intro y s hm
      exact r2 y s ((f2 y s).2 (Or.inl hm))
    · intro i b hb y hy
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        exact r2 _ _ ((f2 _ _).2 (Or.inr ⟨by simp, y, hy, rfl⟩))
      | succ i =>
        have := r3 i b (by simpa using hb) y hy
        rwa [show k + 1 + i = k + (i + 1) by omega] at this

private theorem getD_replicate_nil (n y : Nat) : (Array.replicate n ([] : List Nat)).getD y [] = [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem graphsOf_ok {ids : Ids} {cfg : Cfg} {ps : List Bap.Var} (hids : IdsWF ids)
    (hnamed : ∀ blk ∈ cfg.blocks, ∀ y ∈ vocabulary blk, ids.contains y = true) (hps : ∀ x ∈ ps, ids.contains x = true)
    (hcheck : indexChecks (indexOf 0 cfg.blocks {}) 0 cfg.blocks = true) :
    GraphsOK (graphsOf ids ps cfg (indexOf 0 cfg.blocks {})) ids cfg ps cfg.blocks.length := by
  generalize hindex : indexOf 0 cfg.blocks {} = index at hcheck ⊢
  have hin : ∀ i b, At cfg i b → index.get? b.tid = some i := fun i b hb => by
    have := indexChecks_spec index 0 cfg.blocks hcheck i b hb
    simpa using this
  have hout : ∀ t s, index.get? t = some s → ∃ c, At cfg s c ∧ c.tid = t := by
    rw [← hindex]
    exact indexOf_spec cfg.blocks 0 cfg.blocks {} (fun i b hb => by simpa using hb) (by simp)
  have hat : ∀ {i b c}, At cfg i b → At cfg i c → b = c := by
    intro i a b ha hb
    simp only [At] at ha hb
    rw [ha] at hb
    exact Option.some.inj hb
  have hlt : ∀ {i b}, At cfg i b → i < cfg.blocks.length := by
    intro i b hb
    simp only [At] at hb
    exact (List.getElem?_eq_some_iff.1 hb).1
  have hunique : ∀ i j a b, At cfg i a → At cfg j b → a.tid = b.tid → i = j := by
    intro i j a b ha hb he
    have h1 := hin i a ha
    rw [he, hin j b hb] at h1
    exact (Option.some.inj h1).symm
  have hsO : ∀ t s, s ∈ succsIn (Bap.Graph.Fast.successorTable cfg.graph) index t ↔ ∃ τ ∈ cfg.successors t, index.get? τ = some s := by
    intro t s
    rw [succsIn, Bap.Graph.Fast.successors_eq cfg.graph t, List.mem_filterMap]
    rfl
  have hsB : ∀ t s, s ∈ succsIn (Bap.Graph.Fast.successorTable cfg.graph) index t → s < cfg.blocks.length := by
    intro t s hs
    obtain ⟨τ, _, hτ⟩ := (hsO t s).1 hs
    obtain ⟨c, hc, _⟩ := hout τ s hτ
    exact hlt hc
  have hpredsT : ∀ (R : List Tid) (preds : Array (List Nat)), preds.size = cfg.blocks.length →
      (predsTable index (succsIn (Bap.Graph.Fast.successorTable cfg.graph) index) R preds).size = cfg.blocks.length ∧ ∀ i p, p ∈ (predsTable index (succsIn (Bap.Graph.Fast.successorTable cfg.graph) index) R preds).getD i [] ↔
        p ∈ preds.getD i [] ∨ ∃ t ∈ R, index.get? t = some p ∧ i ∈ succsIn (Bap.Graph.Fast.successorTable cfg.graph) index t := by
    intro R
    induction R with
    | nil => intro preds hp; simp [predsTable, hp]
    | cons t ts ih =>
      intro preds hp
      simp only [predsTable, List.foldl_cons]
      have hmod : ∀ (ss : List Nat) (p : Nat) (a : Array (List Nat)), a.size = cfg.blocks.length → (∀ s ∈ ss, s < cfg.blocks.length) →
          (ss.foldl (fun preds s => preds.modify s (p :: ·)) a).size = cfg.blocks.length ∧
          ∀ i q, q ∈ (ss.foldl (fun preds s => preds.modify s (p :: ·)) a).getD i [] ↔ q ∈ a.getD i [] ∨ (q = p ∧ i ∈ ss) := by
        intro ss p
        induction ss with
        | nil => intro a h _; simp [h]
        | cons s rest iz =>
          intro a h hb
          simp only [List.foldl_cons]
          obtain ⟨z1, z2⟩ := iz (a.modify s (p :: ·)) (by simpa using h) fun q hq => hb q (List.mem_cons_of_mem _ hq)
          refine ⟨z1, fun i q => ?_⟩
          rw [z2, getD_modify]
          have hsl : s < a.size := h ▸ hb s List.mem_cons_self
          by_cases his : i = s
          · subst his
            simp only [and_self, hsl, ↓reduceIte, List.mem_cons, true_or, and_true]
            grind
          · simp [his]
      cases hg : index.get? t with
      | none =>
        obtain ⟨a1, a2⟩ := ih preds hp
        refine ⟨a1, fun i p => ?_⟩
        simp only [predsTable] at a2
        rw [a2]
        simp only [List.mem_cons, exists_eq_or_imp, hg, reduceCtorEq, false_and, false_or]
      | some q =>
        obtain ⟨m1, m2⟩ := hmod (succsIn (Bap.Graph.Fast.successorTable cfg.graph) index t) q preds hp (hsB t)
        obtain ⟨a1, a2⟩ := ih _ m1
        refine ⟨a1, fun i p => ?_⟩
        simp only [predsTable] at a2
        rw [a2, m2]
        simp only [List.mem_cons, exists_eq_or_imp, hg, Option.some.injEq]
        grind
  have hreachT : ∀ (R : List Tid) (reach : Array Bool), reach.size = cfg.blocks.length →
      (reachTable index R reach).size = cfg.blocks.length ∧ ∀ i, (reachTable index R reach).getD i false = true ↔
        reach.getD i false = true ∨ ∃ t ∈ R, index.get? t = some i := by
    intro R
    induction R with
    | nil => intro reach h; simp [reachTable, h]
    | cons t ts ih =>
      intro reach h
      simp only [reachTable, List.foldl_cons]
      cases hg : index.get? t with
      | none =>
        obtain ⟨a1, a2⟩ := ih reach h
        refine ⟨a1, fun i => ?_⟩
        simp only [reachTable] at a2
        rw [a2]
        simp only [Std.HashMap.get?_eq_getElem?] at hg ⊢
        simp [hg]
      | some q =>
        obtain ⟨a1, a2⟩ := ih (reach.setIfInBounds q true) (by simpa using h)
        refine ⟨a1, fun i => ?_⟩
        simp only [reachTable] at a2
        rw [a2]
        obtain ⟨c, hc, _⟩ := hout t q hg
        have hql : q < reach.size := h ▸ hlt hc
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons, exists_eq_or_imp, hg, Option.some.injEq]
        by_cases he : q = i
        · subst he
          simp [hql]
        · simp [he]
  have hprotect : ∀ (l : List Bap.Var) (a : Array Bool), a.size = ids.size → (∀ x ∈ l, ids.contains x = true) → ∀ x, ids.contains x = true →
      ((l.foldl (fun protect x => protect.setIfInBounds (idOf ids x) true) a).getD (idOf ids x) false = true ↔ a.getD (idOf ids x) false = true ∨ x ∈ l) := by
    intro l
    induction l with
    | nil => intro a _ _ x _; simp
    | cons z zs ih =>
      intro a ha hb x hx
      simp only [List.foldl_cons]
      have hz := hb z List.mem_cons_self
      rw [ih _ (by simpa using ha) (fun q hq => hb q (List.mem_cons_of_mem _ hq)) x hx]
      have hzl : idOf ids z < a.size := ha ▸ hids.lt z hz
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons]
      by_cases he : x = z
      · subst he
        simp [hzl]
      · have hne : idOf ids z ≠ idOf ids x := fun e => he (hids.inj x z hx hz e.symm)
        simp [hne, he]
  have hsitesB : ∀ blk ∈ cfg.blocks, ∀ y ∈ vocabulary blk, idOf ids y < ids.size := fun blk hb y hy => hids.lt y (hnamed blk hb y hy)
  have hasgV : ∀ blk, ∀ y ∈ assigned blk, y ∈ vocabulary blk := by
    intro blk y hy
    simp only [assigned, List.mem_append, List.mem_map] at hy
    simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons]
    rcases hy with ⟨d, hd, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨p, hp, rfl⟩))
  obtain ⟨s1, _, s3⟩ := positionTable_spec ids vocabulary ids.size 0 cfg.blocks (Array.replicate ids.size []) (by simp) hsitesB
  obtain ⟨d1, _, d3⟩ := positionTable_spec ids assigned ids.size 0 cfg.blocks (Array.replicate ids.size []) (by simp)
    fun blk hb y hy => hsitesB blk hb y (hasgV blk y hy)
  obtain ⟨p1, p2⟩ := hpredsT cfg.reachable (Array.replicate cfg.blocks.length []) (by simp)
  obtain ⟨r1, r2⟩ := hreachT cfg.reachable (Array.replicate cfg.blocks.length false) (by simp)
  have hsuccsAt : ∀ i, (cfg.blocks.map fun blk => succsIn (Bap.Graph.Fast.successorTable cfg.graph) index blk.tid).toArray.getD i [] =
      ((cfg.blocks[i]?).map fun b => succsIn (Bap.Graph.Fast.successorTable cfg.graph) index b.tid).getD [] := by
    intro i
    simp [Array.getD_eq_getD_getElem?]
  have hsuccMem : ∀ b s c, At cfg s c → (s ∈ succsIn (Bap.Graph.Fast.successorTable cfg.graph) index b ↔ c.tid ∈ cfg.successors b) := by
    intro b s c hc
    rw [hsO]
    constructor
    · rintro ⟨τ, hτ, hg⟩
      obtain ⟨c', hc', ht⟩ := hout τ s hg
      rw [hat hc hc', ht]
      exact hτ
    · intro hm
      exact ⟨c.tid, hm, hin s c hc⟩
  refine ⟨?_, ?_, ?_, hunique, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i b hb
    have hbi : cfg.blocks[i]? = some b := hb
    simp [graphsOf, Array.getD_eq_getD_getElem?, hbi]
  · intro i b hb
    exact block_of_unique (fun p q a c h1 h2 he => hunique p q a c h1 h2 he) hb.mem
  · intro t b h
    have hsome : b.tid = t := by simpa using List.find?_some h
    obtain ⟨i, hi⟩ := exists_at (List.mem_of_find?_eq_some h)
    exact ⟨i, hi, hsome⟩
  · intro i p hp
    simp only [graphsOf] at hp
    have := (p2 i p).1 hp
    rcases this with h | ⟨t, _, hg, _⟩
    · rw [getD_replicate_nil] at h
      simp at h
    · obtain ⟨c, hc, _⟩ := hout t p hg
      exact hlt hc
  · intro i b p c hb hc
    simp only [graphsOf]
    rw [p2, getD_replicate_nil]
    have hmem := fun t => hsuccMem t i b hb
    simp only [List.not_mem_nil, false_or]
    constructor
    · rintro ⟨t, hR, hg, hi⟩
      obtain ⟨c', hc', ht⟩ := hout t p hg
      have hcc := hat hc hc'
      subst hcc
      subst ht
      exact ⟨hR, (hmem _).1 hi⟩
    · rintro ⟨hR, hs⟩
      exact ⟨c.tid, hR, hin p c hc, (hmem _).2 hs⟩
  · intro i p hp
    simp only [graphsOf] at hp
    rw [hsuccsAt] at hp
    cases hb : cfg.blocks[i]? with
    | none => simp [hb] at hp
    | some b =>
      simp only [hb, Option.map_some, Option.getD_some] at hp
      exact hsB b.tid p hp
  · intro i b s c hb hc
    have hbi : cfg.blocks[i]? = some b := hb
    simp only [graphsOf]
    rw [hsuccsAt, hbi]
    simp only [Option.map_some, Option.getD_some]
    exact hsuccMem b.tid s c hc
  · intro i b hb
    simp only [graphsOf]
    rw [r2]
    have hz : (Array.replicate cfg.blocks.length false).getD i false = false := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    simp only [hz, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨t, hR, hg⟩
      obtain ⟨c, hc, ht⟩ := hout t i hg
      have := hat hb hc
      subst this
      rw [ht]
      exact hR
    · intro hR
      exact ⟨b.tid, hR, hin i b hb⟩
  · intro i b hb y hy
    have := s3 i b hb y hy
    simpa [graphsOf] using this
  · intro y s hs
    rcases s1 y s hs with h | ⟨_, h⟩
    · rw [getD_replicate_nil] at h
      simp at h
    · simpa using h
  · intro i b hb y hy
    have := d3 i b hb y hy
    simpa [graphsOf] using this
  · intro y s hs
    rcases d1 y s hs with h | ⟨_, h⟩
    · rw [getD_replicate_nil] at h
      simp at h
    · simpa using h
  · intro x hx
    simp only [graphsOf]
    rw [hprotect ps _ (by simp) hps x hx]
    have hz : (Array.replicate ids.size false).getD (idOf ids x) false = false := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    simp [hz]

theorem internBlocks_spec (l : List Blk) (ids : Ids) (hw : IdsWF ids) (ho : ∀ y < ids.size, ∃ x, ids.contains x = true ∧ idOf ids x = y) :
    IdsWF (l.foldl internBlock ids) ∧ (∀ y < (l.foldl internBlock ids).size, ∃ x, (l.foldl internBlock ids).contains x = true ∧ idOf (l.foldl internBlock ids) x = y) ∧
      (∀ x, ids.contains x = true → (l.foldl internBlock ids).contains x = true) ∧
      ∀ blk ∈ l, ∀ y ∈ vocabulary blk, (l.foldl internBlock ids).contains y = true := by
  induction l generalizing ids with
  | nil => exact ⟨hw, ho, fun _ h => h, by simp⟩
  | cons a as ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := ih (internBlock ids a) (internAll_wf hw _) (internAll_onto hw ho _)
    refine ⟨h1, h2, fun x hx => h3 x ((contains_internAll _ _ _).2 (Or.inl hx)), fun blk hb y hy => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h3 y ((contains_internAll _ _ _).2 (Or.inr hy))
    · exact h4 blk hb y hy

end Refresh

/-! ### What a removal takes out of a row -/

section Losses

variable {effect : Bil.Exp → Bool} {ids : Ids} {blocks : Array DBlk} {cfg old : Cfg}

theorem Row.contains_erase (r : Row) (b i : Nat) : (r.erase b).contains i = true ↔ r.contains i = true ∧ i ≠ b := by
  cases r with
  | short l => simp [Row.erase, Row.contains]
  | long s =>
    simp only [Row.erase, Row.contains, Std.HashSet.contains_erase, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩

theorem Row.contains_eraseAll (l : List Nat) (r : Row) (i : Nat) :
    (l.foldl Row.erase r).contains i = true ↔ r.contains i = true ∧ i ∉ l := by
  induction l generalizing r with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih, Row.contains_erase, List.mem_cons, not_or]
    exact and_assoc

private theorem exposedDefsD_dense (h : IdsWF ids) {x : Bap.Var} (hx : ids.contains x = true) (jmps : List Nat)
    (defs : List Def) (hd : ∀ d ∈ defs, ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true) :
    exposedDefsD (idOf ids x) jmps (defs.map (denseDef effect ids)) = true ↔
      Bap.Proofs.IR.Exposed defs x ∨ (idOf ids x ∈ jmps ∧ ∀ d ∈ defs, d.var ≠ x) := by
  induction defs with
  | nil => simp [exposedDefsD, Bap.Proofs.IR.Exposed]
  | cons d ds ih =>
    obtain ⟨hv, hr⟩ := hd d List.mem_cons_self
    have hmem : idOf ids x ∈ (Bil.freeVars d.rhs).map (idOf ids) ↔ x ∈ Bil.freeVars d.rhs := by
      simp only [List.mem_map]
      exact ⟨fun ⟨y, hy, he⟩ => h.inj y x (hr y hy) hx he ▸ hy, fun hy => ⟨x, hy, rfl⟩⟩
    have hne : idOf ids d.var = idOf ids x ↔ d.var = x := ⟨h.inj _ _ hv hx, fun e => e ▸ rfl⟩
    simp only [List.map_cons, exposedDefsD, denseDef, Bool.or_eq_true, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
      bne_iff_ne, ne_eq, hmem, hne, ih fun e he => hd e (List.mem_cons_of_mem _ he), Bap.Proofs.IR.Exposed, List.mem_cons, forall_eq_or_imp]
    grind

theorem exposesD_dense (h : IdsWF ids) {blk : Blk} (hv : ∀ y ∈ vocabulary blk, ids.contains y = true) {x : Bap.Var}
    (hx : ids.contains x = true) : exposesD (denseBlk effect ids blk) (idOf ids x) = true ↔ x ∈ blockIn blk [] := by
  have hd : ∀ d ∈ blk.defs, ids.contains d.var = true ∧ ∀ y ∈ Bil.freeVars d.rhs, ids.contains y = true := by
    intro d hd
    constructor
    · exact hv _ (by
        simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
        exact Or.inl (Or.inr ⟨d, hd, Or.inl rfl⟩))
    · intro y hy
      exact hv _ (by
        simp only [vocabulary, List.mem_append, List.mem_flatMap, List.mem_cons]
        exact Or.inl (Or.inr ⟨d, hd, Or.inr hy⟩))
  have hj : idOf ids x ∈ (blk.jmps.flatMap Jmp.freeVars).map (idOf ids) ↔ ∃ jmp ∈ blk.jmps, x ∈ jmp.freeVars := by
    simp only [List.mem_map, List.mem_flatMap]
    constructor
    · rintro ⟨y, ⟨j, hj, hy⟩, he⟩
      have := h.inj y x (hv y (by
        simp only [vocabulary, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨j, hj, hy⟩)) hx he
      exact ⟨j, hj, this ▸ hy⟩
    · rintro ⟨j, hj, hy⟩
      exact ⟨x, ⟨j, hj, hy⟩, rfl⟩
  have hp := hasPhiD_dense (effect := effect) h hv hx
  simp only [exposesD, Bool.and_eq_true, Bool.not_eq_true', hp, hasPhi_false_iff]
  have he := exposedDefsD_dense (effect := effect) h hx ((blk.jmps.flatMap Jmp.freeVars).map (idOf ids)) blk.defs hd
  simp only [denseBlk]
  rw [he, Bap.Proofs.IR.mem_blockIn, hj]
  simp

/-- The marks of the blocks a visit has seen. -/
private theorem visitPreds_marks {n : Nat} {skip : Nat → Bool} (ps : List Nat) (hlt : ∀ p ∈ ps, p < n) (state : Marks × List Nat × List Nat)
    (hw : state.1.WF n) (hall : ∀ t ∈ state.2.1, state.1.contains t = true) :
    ∀ t ∈ (visitPredsD skip ps state).2.1, (visitPredsD skip ps state).1.contains t = true := by
  induction ps generalizing state with
  | nil => exact hall
  | cons p rest ih =>
    simp only [visitPredsD, List.foldl_cons]
    have hrest := fun q hq => hlt q (List.mem_cons_of_mem _ hq)
    split
    · exact ih hrest state hw hall
    · split
      · exact ih hrest state hw hall
      · refine ih hrest (state.1.add p, p :: state.2.1, p :: state.2.2) (hw.add p) ?_
        intro t ht
        rw [Marks.contains_add hw (hlt p List.mem_cons_self)]
        rcases List.mem_cons.1 ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hall t ht)

private theorem visitPreds_wf {n : Nat} {skip : Nat → Bool} (ps : List Nat) (state : Marks × List Nat × List Nat) (hw : state.1.WF n) :
    (visitPredsD skip ps state).1.WF n := by
  induction ps generalizing state with
  | nil => exact hw
  | cons p rest ih =>
    simp only [visitPredsD, List.foldl_cons]
    split
    · exact ih state hw
    · split
      · exact ih state hw
      · exact ih _ (hw.add p)

private theorem floodD_marks {preds : Array (List Nat)} {x n : Nat} {skip : Nat → Bool} (hp : ∀ t, ∀ p ∈ preds.getD t [], p < n)
    (fuel : Nat) (seen : Marks) (row work : List Nat) (result : List Nat) (seen' : Marks) (hw : seen.WF n)
    (hall : ∀ t ∈ row, seen.contains t = true) (hr : floodD blocks preds x skip fuel seen row work = some (result, seen')) :
    ∀ t ∈ result, seen'.contains t = true := by
  induction fuel generalizing seen row work with
  | zero => simp [floodD] at hr
  | succ fuel ih =>
    cases work with
    | nil =>
      simp only [floodD, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hall
    | cons t work =>
      simp only [floodD] at hr
      split at hr
      · exact ih seen row work hw hall hr
      · exact ih _ _ _ (visitPreds_wf _ (seen, row, work) hw) (visitPreds_marks _ (hp t) (seen, row, work) hw hall) hr

/-- What `lostD` finds. -/
private theorem lostD_spec {g : Graphs} {row : Row} {x n N : Nat} {sites : List Nat} {seen seen' : Marks} {lost : List Nat} (hNn : N ≤ n)
    (hp : ∀ t, ∀ p ∈ g.preds.getD t [], p < N) (hs : ∀ s ∈ sites, s < N) (hw : seen.WF n)
    (hr : lostD g blocks row x sites seen = some (lost, seen')) :
    seen'.WF n ∧ (∀ t, seen'.contains t = true ↔ t ∈ lost) ∧ (∀ t ∈ lost, t < N ∧ row.contains t = true ∧ exposesD (blkAt blocks t) x = false) ∧
      (∀ s ∈ sites ++ sites.flatMap (fun s => g.preds.getD s []), row.contains s = true → exposesD (blkAt blocks s) x = false → s ∈ lost) ∧
      ∀ t ∈ lost, hasPhiD (blkAt blocks t) x = false → ∀ p ∈ g.preds.getD t [], row.contains p = true → killedD (blkAt blocks p) x = false →
        exposesD (blkAt blocks p) x = false → p ∈ lost := by
  simp only [lostD] at hr
  generalize hps : sites ++ sites.flatMap (fun s => g.preds.getD s []) = ps at hr
  have hlt : ∀ p ∈ ps, p < N := by
    intro p hm
    rw [← hps] at hm
    rcases List.mem_append.1 hm with h | h
    · exact hs p h
    · obtain ⟨s, _, h⟩ := List.mem_flatMap.1 h
      exact hp s p h
  have hpn : ∀ t, ∀ p ∈ g.preds.getD t [], p < n := fun t p h => Nat.lt_of_lt_of_le (hp t p h) hNn
  let live : Nat → Prop := fun t => t < N ∧ row.contains t = true ∧ exposesD (blkAt blocks t) x = false
  generalize hfirst : visitPredsD (fun p => !row.contains p || exposesD (blkAt blocks p) x) ps (seen.clear, [], []) = first at hr
  obtain ⟨n1, n2, n3, _, _, _, _, n8⟩ := visitPreds_inv (skip := fun p => !row.contains p || exposesD (blkAt blocks p) x)
    (live := live) (n := n) ps
    (fun p hm hk => ⟨hlt p hm, by simpa using hk⟩) (seen.clear, [], []) hw.clear (by simp)
    (fun t ht => by
      have := Marks.contains_clear hw t
      simp only at ht
      rw [this] at ht
      cases ht) (by simp)
  rw [hfirst] at n1 n2 n3 n8
  have hm0 := visitPreds_marks (skip := fun p => !row.contains p || exposesD (blkAt blocks p) x) ps (fun p h => Nat.lt_of_lt_of_le (hlt p h) hNn) (seen.clear, [], []) hw.clear (by simp)
  rw [hfirst] at hm0
  have hspec : FloodSpec blocks g.preds x (fun p => !row.contains p || killedD (blkAt blocks p) x || exposesD (blkAt blocks p) x) live := by
    refine ⟨fun t _ _ p hpp hk => ?_⟩
    have hk' : row.contains p = true ∧ killedD (blkAt blocks p) x = false ∧ exposesD (blkAt blocks p) x = false := by
      simpa [and_assoc] using hk
    exact ⟨hp t p hpp, hk'.1, hk'.2.2⟩
  obtain ⟨h1, h2, h3⟩ := floodD_inv (n := n) hspec _ first.1 first.2.1 first.2.1 lost seen' n1 ⟨n2, n3, fun _ h hn => (hn h).elim, fun _ h => h⟩ hr
  have hm := floodD_marks (hp := hpn) (blocks := blocks) _ first.1 first.2.1 first.2.1 lost seen' n1 hm0 hr
  refine ⟨h1, fun t => ⟨h2.marked t, hm t⟩, h2.sound, ?_, ?_⟩
  · intro s hm hc he
    exact h3 s (n8 s hm (by simp [hc, he]))
  · intro t ht hph p hps hc hk he
    exact h2.closed t ht (by simp) hph p hps (by simp [hc, hk, he])

/-- What `keptD` finds. -/
private theorem keptD_spec {g : Graphs} {row : Row} {x n : Nat} {lostList : List Nat} {lost seen seen' : Marks} {kept : List Nat}
    (hp : ∀ t, ∀ p ∈ g.preds.getD t [], p < n) (hl : ∀ t ∈ lostList, t < n) (hw : seen.WF n) {live : Nat → Prop}
    (hstart : ∀ t ∈ lostList, survivesD g blocks row lost x t = true → live t)
    (hstep : ∀ t, live t → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ g.preds.getD t [], lost.contains p = true → killedD (blkAt blocks p) x = false → live p)
    (hr : keptD g blocks row x lostList lost seen = some (kept, seen')) :
    seen'.WF n ∧ (∀ t, seen'.contains t = true ↔ t ∈ kept) ∧ (∀ t ∈ kept, live t) ∧
      (∀ t ∈ lostList, survivesD g blocks row lost x t = true → t ∈ kept) ∧
      ∀ t ∈ kept, hasPhiD (blkAt blocks t) x = false → ∀ p ∈ g.preds.getD t [], lost.contains p = true → killedD (blkAt blocks p) x = false → p ∈ kept := by
  simp only [keptD] at hr
  generalize hst : lostList.filter (survivesD g blocks row lost x) = start at hr
  have hin : ∀ t ∈ start, t < n := fun t ht => hl t (List.mem_filter.1 (hst ▸ ht)).1
  have hwc : (start.foldl Marks.add seen.clear).WF n := hw.clear.foldl_add _
  have hmk : ∀ t, (start.foldl Marks.add seen.clear).contains t = true ↔ t ∈ start := by
    intro t
    rw [Marks.contains_foldl_add hw.clear hin, Marks.contains_clear hw]
    simp
  have hspec : FloodSpec blocks g.preds x (fun p => !lost.contains p || killedD (blkAt blocks p) x) live := by
    refine ⟨fun t hl hph p hps hk => ?_⟩
    have : lost.contains p = true ∧ killedD (blkAt blocks p) x = false := by simpa using hk
    exact hstep t hl hph p hps this.1 this.2
  have hstarts : ∀ t ∈ start, live t := by
    intro t ht
    rw [← hst] at ht
    exact hstart t (List.mem_filter.1 ht).1 (List.mem_filter.1 ht).2
  obtain ⟨h1, h2, h3⟩ := floodD_inv (n := n) hspec _ _ start start kept seen' hwc ⟨hstarts, fun t ht => (hmk t).1 ht, fun _ h hn => (hn h).elim, fun _ h => h⟩ hr
  have hm := floodD_marks (hp := hp) (blocks := blocks) _ _ start start kept seen' hwc (fun t ht => (hmk t).2 ht) hr
  refine ⟨h1, fun t => ⟨h2.marked t, hm t⟩, h2.sound, ?_, ?_⟩
  · intro t ht hs
    exact h3 t (hst ▸ List.mem_filter.2 ⟨ht, hs⟩)
  · intro t ht hph p hps hc hk
    exact h2.closed t ht (by simp) hph p hps (by simp [hc, hk])

private theorem addKillers_spec {g : Graphs} {x : Nat} (l dirty : List Nat) :
    (∀ d ∈ dirty, d ∈ addKillers g blocks x l dirty) ∧
      (∀ t ∈ l, ∀ p ∈ g.preds.getD t [], killedD (blkAt blocks p) x = true → p ∈ addKillers g blocks x l dirty) ∧
      ∀ d ∈ addKillers g blocks x l dirty, d ∈ dirty ∨ ∃ t ∈ l, d ∈ g.preds.getD t [] := by
  have hin : ∀ (ps acc : List Nat), (∀ d ∈ acc, d ∈ ps.foldl (fun dirty p => if killedD (blkAt blocks p) x then p :: dirty else dirty) acc) ∧
      (∀ p ∈ ps, killedD (blkAt blocks p) x = true → p ∈ ps.foldl (fun dirty p => if killedD (blkAt blocks p) x then p :: dirty else dirty) acc) ∧
      ∀ d ∈ ps.foldl (fun dirty p => if killedD (blkAt blocks p) x then p :: dirty else dirty) acc, d ∈ acc ∨ d ∈ ps := by
    intro ps
    induction ps with
    | nil => simp
    | cons a as ih =>
      intro acc
      simp only [List.foldl_cons]
      split
      · rename_i hk
        obtain ⟨i1, i2, i3⟩ := ih (a :: acc)
        refine ⟨fun d hd => i1 d (List.mem_cons_of_mem _ hd), fun p hp hk' => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact i1 _ List.mem_cons_self
          · exact i2 p hp hk'
        · rcases i3 d hd with h | h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inr List.mem_cons_self
            · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
      · rename_i hk
        obtain ⟨i1, i2, i3⟩ := ih acc
        refine ⟨i1, fun p hp hk' => ?_, fun d hd => ?_⟩
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact (hk hk').elim
          · exact i2 p hp hk'
        · rcases i3 d hd with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)
  simp only [addKillers]
  induction l generalizing dirty with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    obtain ⟨j1, j2, j3⟩ := hin (g.preds.getD a []) dirty
    obtain ⟨i1, i2, i3⟩ := ih ((g.preds.getD a []).foldl (fun dirty p => if killedD (blkAt blocks p) x then p :: dirty else dirty) dirty)
    refine ⟨fun d hd => i1 d (j1 d hd), fun t ht p hp hk => ?_, fun d hd => ?_⟩
    · rcases List.mem_cons.1 ht with rfl | ht
      · exact i1 p (j2 p hp hk)
      · exact i2 t ht p hp hk
    · rcases i3 d hd with h | ⟨t, ht, h⟩
      · rcases j3 d h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, h⟩

/-- A block that can only have less to say about a variable. -/
structure Shrinks (x : Bap.Var) (before after : Blk) : Prop where
  kill : Killed after x → Killed before x
  phi : (∀ phi ∈ before.phis, phi.var ≠ x) → ∀ phi ∈ after.phis, phi.var ≠ x

/-- How the CFG before a removal goes with the one after it, as far as a variable goes, where `sites` are the blocks that lost a mention of it. -/
structure Removal (old cfg : Cfg) (x : Bap.Var) (sites : List Nat) : Prop where
  reach : old.reachable = cfg.reachable
  succs : ∀ t, old.successors t = cfg.successors t
  block : ∀ t before, old.block t = some before → ∃ i after, At cfg i after ∧ after.tid = t ∧ Shrinks x before after ∧ (i ∉ sites → Agree x before after)
  sub : ∀ t, x ∈ liveIn cfg t → x ∈ liveIn old t

/-- Where a variable was live and may not be any more is what goes back from what lost it. -/
private theorem removal_cover {g : Graphs} {ps : List Bap.Var} {n : Nat} {x : Bap.Var} {sites : List Nat} (hg : GraphsOK g ids cfg ps n)
    (hrm : Removal old cfg x sites) (C : Nat → Prop) (R : Nat → Prop) (hrow : ∀ i b, At cfg i b → (R i ↔ x ∈ liveIn old b.tid))
    (hseed : ∀ i b, At cfg i b → R i → x ∉ blockIn b [] → i ∈ sites → C i)
    (hpred : ∀ s ∈ sites, ∀ p ∈ g.preds.getD s [], ∀ b, At cfg p b → R p → x ∉ blockIn b [] → C p)
    (hclosed : ∀ t b, At cfg t b → C t → (∀ phi ∈ b.phis, phi.var ≠ x) → ∀ p ∈ g.preds.getD t [], ∀ c, At cfg p c → R p → ¬ Killed c x → x ∉ blockIn c [] → C p)
    {i : Nat} {b : Blk} (hb : At cfg i b) (hl : x ∈ liveIn old b.tid) : C i ∨ x ∈ liveIn cfg b.tid := by
  have hkey := live_least old x (fun τ => x ∈ liveIn old τ ∧ ∀ i b, At cfg i b → b.tid = τ → C i ∨ x ∈ liveIn cfg τ) ?_ ?_ hl
  · exact hkey.2 i b hb rfl
  · intro τ hτ before hbefore hgen
    have hlo : x ∈ liveIn old τ := live_of_gen hτ hbefore hgen
    refine ⟨hlo, ?_⟩
    obtain ⟨j, after, hj, htid, _, hag⟩ := hrm.block τ before hbefore
    subst htid
    intro k c hc hct
    have hkj := hg.unique k j c after hc hj hct
    subst hkj
    have hsame : c = after := by
      simp only [At] at hc hj
      rw [hc] at hj
      exact Option.some.inj hj
    subst hsame
    have hreachNew : c.tid ∈ cfg.reachable := hrm.reach ▸ hτ
    by_cases hgn : x ∈ blockIn c []
    · exact Or.inr (live_of_gen hreachNew (hg.block k c hc) hgn)
    · by_cases hs : k ∈ sites
      · exact Or.inl (hseed k c hc ((hrow k c hc).2 hlo) hgn hs)
      · exact (hgn ((hag hs).gen.1 hgen)).elim
  · intro τ hτ before hbefore hk σ hσ he
    obtain ⟨obs, hobs, hcase⟩ := he
    have hlo : x ∈ liveIn old τ := live_of_edge hτ hbefore hk hσ ⟨obs, hobs, by
      rcases hcase with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨h1.1, h2⟩
      · exact Or.inr h1⟩
    refine ⟨hlo, ?_⟩
    obtain ⟨j, after, hj, htid, hsh, _⟩ := hrm.block τ before hbefore
    subst htid
    obtain ⟨js, bs, hjs, hst, hshs, hags⟩ := hrm.block σ obs hobs
    subst hst
    intro k c hc hct
    have hkj := hg.unique k j c after hc hj hct
    subst hkj
    have hsame : c = after := by
      simp only [At] at hc hj
      rw [hc] at hj
      exact Option.some.inj hj
    subst hsame
    have hreachNew : c.tid ∈ cfg.reachable := hrm.reach ▸ hτ
    have hkn : ¬ Killed c x := fun h => hk (hsh.kill h)
    have hsucc : bs.tid ∈ cfg.successors c.tid := by rw [← hrm.succs]; exact hσ
    have hip : k ∈ g.preds.getD js [] := (hg.preds js bs k c hjs hc).2 ⟨hreachNew, hsucc⟩
    by_cases hgn : x ∈ blockIn c []
    · exact Or.inr (live_of_gen hreachNew (hg.block k c hc) hgn)
    have hbsb := hg.block js bs hjs
    rcases hcase with ⟨hr, hp⟩ | hr
    · have hpn := hshs.phi hp
      rcases hr.2 js bs hjs rfl with hC | hnew
      · exact Or.inl (hclosed js bs hjs hC hpn k hip c hc ((hrow k c hc).2 hlo) hkn hgn)
      · exact Or.inr (live_of_edge hreachNew (hg.block k c hc) hkn hsucc ⟨bs, hbsb, Or.inl ⟨hnew, hpn⟩⟩)
    · by_cases hs : js ∈ sites
      · exact Or.inl (hpred js hs k hip c hc ((hrow k c hc).2 hlo) hgn)
      · exact Or.inr (live_of_edge hreachNew (hg.block k c hc) hkn hsucc ⟨bs, hbsb, Or.inr (((hags hs).reads c.tid).1 hr)⟩)

/-- The row of a variable after a removal, from the one before it, what can lose it and what doesn't. -/
private theorem removal_exact {g : Graphs} {ps : List Bap.Var} {n : Nat} {x : Bap.Var} {sites : List Nat} (hg : GraphsOK g ids cfg ps n)
    (hrm : Removal old cfg x sites) (C K R : Nat → Prop) (hrow : ∀ i b, At cfg i b → (R i ↔ x ∈ liveIn old b.tid))
    (hcover : ∀ i b, At cfg i b → x ∈ liveIn old b.tid → C i ∨ x ∈ liveIn cfg b.tid)
    (hgen : ∀ i b, At cfg i b → C i → x ∉ blockIn b [])
    (hKsound : ∀ i b, At cfg i b → K i → x ∈ liveIn cfg b.tid)
    (hsurvive : ∀ i b, At cfg i b → C i → ¬ Killed b x → ∀ is bs, At cfg is bs → bs.tid ∈ cfg.successors b.tid →
      ((R is ∧ ¬ C is ∧ ∀ phi ∈ bs.phis, phi.var ≠ x) ∨ x ∈ phiReads b.tid bs) → K i)
    (hKclosed : ∀ t b, At cfg t b → K t → (∀ phi ∈ b.phis, phi.var ≠ x) → ∀ p c, At cfg p c → c.tid ∈ cfg.reachable → b.tid ∈ cfg.successors c.tid → C p → ¬ Killed c x → K p)
    {i : Nat} {b : Blk} (hb : At cfg i b) : (R i ∧ (¬ C i ∨ K i)) ↔ x ∈ liveIn cfg b.tid := by
  constructor
  · rintro ⟨hr, hc | hc⟩
    · rcases hcover i b hb ((hrow i b hb).1 hr) with h | h
      · exact (hc h).elim
      · exact h
    · exact hKsound i b hb hc
  · intro hl
    have hkey := live_least cfg x (fun τ => x ∈ liveIn cfg τ ∧ ∀ i b, At cfg i b → b.tid = τ → ¬ C i ∨ K i) ?_ ?_ hl
    · exact ⟨(hrow i b hb).2 (hrm.sub _ hl), hkey.2 i b hb rfl⟩
    · intro τ hτ blk hblk hgn
      refine ⟨live_of_gen hτ hblk hgn, ?_⟩
      intro k c hc hct
      obtain rfl : blk = c := Option.some.inj (by rw [← hblk, ← hct]; exact hg.block k c hc)
      exact Or.inl fun hC => hgen k blk hc hC hgn
    · intro τ hτ blk hblk hk σ hσ he
      have hlv : x ∈ liveIn cfg τ := live_of_edge hτ hblk hk hσ (by
        obtain ⟨bs, hbs, hc⟩ := he
        refine ⟨bs, hbs, ?_⟩
        rcases hc with ⟨h1, h2⟩ | h1
        · exact Or.inl ⟨h1.1, h2⟩
        · exact Or.inr h1)
      refine ⟨hlv, ?_⟩
      intro k c hc hct
      obtain rfl : blk = c := Option.some.inj (by rw [← hblk, ← hct]; exact hg.block k c hc)
      by_cases hC : C k
      · refine Or.inr ?_
        obtain ⟨bs, hbs, hcase⟩ := he
        obtain ⟨is, his, hst⟩ := hg.index σ bs hbs
        subst hst
        subst hct
        rcases hcase with ⟨h1, h2⟩ | h1
        · rcases h1.2 is bs his rfl with hn | hK
          · exact hsurvive k blk hc hC hk is bs his hσ (Or.inl ⟨(hrow is bs his).2 (hrm.sub _ h1.1), hn, h2⟩)
          · exact hKclosed is bs his hK h2 k blk hc hτ hσ hC hk
        · exact hsurvive k blk hc hC hk is bs his hσ (Or.inr h1)
      · exact Or.inl hC

private theorem getD_modify_row (a : Array Row) (y j : Nat) (f : Row → Row) (d : Row) :
    (a.modify y f).getD j d = if j = y ∧ y < a.size then f (a.getD j d) else a.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : y = j
  · subst h
    by_cases hs : y < a.size
    · simp [hs]
    · simp [hs]
  · have : j ≠ y := fun e => h e.symm
    simp [h, this]

/-- What `updateVar` leaves. -/
theorem updateVar_spec {g : Graphs} {ps : List Bap.Var} {n M : Nat} {x : Bap.Var} {sites : List Nat} {rows rows' : Array Row} {dirty dirty' : List Nat}
    {seen seen2 s1 s2 : Marks} (hm : Mirror effect ids blocks cfg) (hg : GraphsOK g ids cfg ps n) (hnM : n ≤ M) (hx : ids.contains x = true) (hxs : idOf ids x < rows.size)
    (hrm : Removal old cfg x sites) (hsites : ∀ s ∈ sites, s < n) (hrow : ∀ i b, At cfg i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn old b.tid))
    (hs1 : seen.WF M) (hs2 : seen2.WF M)
    (hr : updateVar g blocks (idOf ids x) sites rows dirty seen seen2 = some (rows', dirty', s1, s2)) :
    s1.WF M ∧ s2.WF M ∧ rows'.size = rows.size ∧ (∀ y, y ≠ idOf ids x → rows'.getD y (.short []) = rows.getD y (.short [])) ∧
      (∀ i b, At cfg i b → ((rows'.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn cfg b.tid)) ∧
      (∀ d ∈ dirty, d ∈ dirty') ∧ (∀ d ∈ dirty', d ∈ dirty ∨ d < n) ∧
      ∀ t b, At cfg t b → (t ∈ sites ∨ (x ∈ liveIn old b.tid ∧ x ∉ liveIn cfg b.tid)) →
        ∀ p ∈ g.preds.getD t [], killedD (Bap.IR.DenseDce.blkAt blocks p) (idOf ids x) = true → p ∈ dirty' := by
  have hids := hm.wf
  have hnamed : ∀ {j b}, At cfg j b → ∀ y ∈ vocabulary b, ids.contains y = true := fun hj => hm.named _ hj.mem
  have hat : ∀ {i}, i < n → ∃ b, At cfg i b := by
    intro i hi
    have hl : i < cfg.blocks.length := hg.count ▸ hi
    exact ⟨cfg.blocks[i], by simp only [At]; simp [hl]⟩
  have hpM : ∀ t, ∀ p ∈ g.preds.getD t [], p < M := fun t p hp => Nat.lt_of_lt_of_le (hg.preds_in t p hp) hnM
  simp only [updateVar] at hr
  generalize hrowv : rows.getD (idOf ids x) (.short []) = row at hr hrow
  cases hl : lostD g blocks row (idOf ids x) sites seen with
  | none => rw [hl] at hr; cases hr
  | some lostPair =>
    rw [hl] at hr
    obtain ⟨lost, lostM⟩ := lostPair
    dsimp only at hr
    obtain ⟨l1, l2, l3, l4, l5⟩ := lostD_spec hnM (hg.preds_in) hsites hs1 hl
    have hphiIff : ∀ {i b}, At cfg i b → (hasPhiD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x) = false ↔ ∀ phi ∈ b.phis, phi.var ≠ x) := by
      intro i b hb
      rw [hm.blkAt hb, hasPhiD_dense hids (hnamed hb) hx, hasPhi_false_iff]
    have hkillIff : ∀ {i b}, At cfg i b → (killedD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x) = true ↔ Killed b x) := by
      intro i b hb
      rw [hm.blkAt hb, killedD_dense hids (hnamed hb) hx, killed_iff]
    have hkillF : ∀ {i b}, At cfg i b → (killedD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x) = false ↔ ¬ Killed b x) := by
      intro i b hb
      rw [← hkillIff hb, Bool.not_eq_true]
    have hexpF : ∀ {i b}, At cfg i b → (exposesD (Bap.IR.DenseDce.blkAt blocks i) (idOf ids x) = false ↔ x ∉ blockIn b []) := by
      intro i b hb
      rw [hm.blkAt hb, ← exposesD_dense (effect := effect) hids (hnamed hb) hx, Bool.not_eq_true]
    have hcover : ∀ i b, At cfg i b → x ∈ liveIn old b.tid → i ∈ lost ∨ x ∈ liveIn cfg b.tid := by
      intro i b hb hlv
      refine removal_cover (R := fun i => row.contains i = true) hg hrm (fun t => t ∈ lost) hrow ?_ ?_ ?_ hb hlv
      · intro i b hb hr hn hs
        exact l4 i (List.mem_append_left _ hs) hr ((hexpF hb).2 hn)
      · intro s hs p hp b hb hr hn
        exact l4 p (List.mem_append_right _ (List.mem_flatMap.2 ⟨s, hs, hp⟩)) hr ((hexpF hb).2 hn)
      · intro t b hb hC hph p hp c hc hr hk hn
        exact l5 t hC ((hphiIff hb).2 hph) p hp hr ((hkillF hc).2 hk) ((hexpF hc).2 hn)
    cases hk : keptD g blocks row (idOf ids x) lost lostM seen2 with
    | none => rw [hk] at hr; cases hr
    | some keptPair =>
      rw [hk] at hr
      obtain ⟨kept, keptM⟩ := keptPair
      dsimp only at hr
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
      let live : Nat → Prop := fun t => ∃ b, At cfg t b ∧ x ∈ liveIn cfg b.tid
      obtain ⟨k1, k2, k3, k4, k5⟩ := keptD_spec (live := live) hpM (fun t ht => Nat.lt_of_lt_of_le (l3 t ht).1 hnM) hs2 (by
          intro t ht hsv
          obtain ⟨b, hb⟩ := hat (l3 t ht).1
          refine ⟨b, hb, ?_⟩
          simp only [survivesD, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.or_eq_true] at hsv
          obtain ⟨hkf, s, hs, hcase⟩ := hsv
          obtain ⟨c, hc⟩ := hat (hg.succs_in t s hs)
          have hreach : b.tid ∈ cfg.reachable := hrm.reach ▸ reachable_of_live ((hrow t b hb).1 (l3 t ht).2.1)
          have hsucc := (hg.succs t b s c hb hc).1 hs
          refine live_of_edge hreach (hg.block t b hb) ((hkillF hb).1 hkf) hsucc ⟨c, hg.block s c hc, ?_⟩
          rcases hcase with ⟨⟨h1, h2⟩, h3⟩ | h1
          · refine Or.inl ⟨?_, (hphiIff hc).1 h3⟩
            rcases hcover s c hc ((hrow s c hc).1 h1) with hC | hn
            · have : lostM.contains s = true := (l2 s).2 hC
              rw [h2] at this
              cases this
            · exact hn
          · refine Or.inr ?_
            rw [hm.blkAt hc, hg.tids t b hb] at h1
            exact (phiReadsD_dense hids (hnamed hc) _ hx).1 (by simpa using h1)) (by
          rintro t ⟨b, hb, hlv⟩ hph p hp _ hkf
          obtain ⟨c, hc⟩ := hat (hg.preds_in t p hp)
          obtain ⟨h1, h2⟩ := (hg.preds t b p c hb hc).1 hp
          exact ⟨c, hc, live_of_edge h1 (hg.block p c hc) ((hkillF hc).1 hkf) h2 ⟨b, hg.block t b hb, Or.inl ⟨hlv, (hphiIff hb).1 hph⟩⟩⟩) hk
      have hexact : ∀ {i b}, At cfg i b → ((row.contains i = true ∧ (i ∉ lost ∨ i ∈ kept)) ↔ x ∈ liveIn cfg b.tid) := by
        intro i b hb
        refine removal_exact (R := fun i => row.contains i = true) (C := fun t => t ∈ lost) (K := fun t => t ∈ kept) hg hrm hrow hcover ?_ ?_ ?_ ?_ hb
        · intro i b hb hC
          exact (hexpF hb).1 (l3 i hC).2.2
        · intro i b hb hK
          obtain ⟨c, hc, hl⟩ := k3 i hK
          have : c = b := by
            simp only [At] at hc hb
            rw [hc] at hb
            exact Option.some.inj hb
          exact this ▸ hl
        · intro i b hb hC hkn is bs his hsucc hcase
          refine k4 i hC ?_
          simp only [survivesD, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.or_eq_true]
          refine ⟨(hkillF hb).2 hkn, is, (hg.succs i b is bs hb his).2 hsucc, ?_⟩
          rcases hcase with ⟨h1, h2, h3⟩ | h1
          · refine Or.inl ⟨⟨h1, ?_⟩, (hphiIff his).2 h3⟩
            rw [Bool.eq_false_iff]
            exact fun hc => h2 ((l2 is).1 hc)
          · refine Or.inr ?_
            rw [hm.blkAt his, hg.tids i b hb]
            simpa using (phiReadsD_dense hids (hnamed his) _ hx).2 h1
        · intro t b hb hK hph p c hc hreach hsucc hC hkn
          exact k5 t hK ((hphiIff hb).2 hph) p ((hg.preds t b p c hb hc).2 ⟨hreach, hsucc⟩) ((l2 p).2 hC) ((hkillF hc).2 hkn)
      obtain ⟨a1, a2, a3⟩ := addKillers_spec (blocks := blocks) (g := g) (x := idOf ids x) ((lost.filter fun t => !keptM.contains t) ++ sites) dirty
      have hrowNew : ∀ i, ((rows.modify (idOf ids x) fun row => (lost.filter fun t => !keptM.contains t).foldl Row.erase row).getD (idOf ids x) (.short [])).contains i = true ↔
          row.contains i = true ∧ (i ∉ lost ∨ i ∈ kept) := by
        intro i
        rw [getD_modify_row, ite_eq_left ⟨rfl, hxs⟩, hrowv, Row.contains_eraseAll, List.mem_filter]
        rw [← k2 i]
        simp only [Bool.not_eq_true', not_and, Bool.not_eq_false]
        by_cases h1 : i ∈ lost <;> simp [h1]
      refine ⟨l1, k1, by simp, ?_, ?_, a1, ?_, ?_⟩
      · intro y hy
        rw [getD_modify_row, ite_eq_right fun h => hy h.1]
      · intro i b hb
        rw [hrowNew, hexact hb]
      · intro d hd
        rcases a3 d hd with h | ⟨t, _, h⟩
        · exact Or.inl h
        · exact Or.inr (hg.preds_in t d h)
      · intro t b hb hcase p hp hkp
        refine a2 t ?_ p hp hkp
        rcases hcase with hs | ⟨h1, h2⟩
        · exact List.mem_append_right _ hs
        · refine List.mem_append_left _ (List.mem_filter.2 ?_)
          rcases hcover t b hb h1 with hC | hn
          · refine ⟨hC, ?_⟩
            simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
            rw [Bool.eq_false_iff]
            intro hkm
            exact h2 ((hexact hb).1 ⟨(hrow t b hb).2 h1, Or.inr ((k2 t).1 hkm)⟩)
          · exact (h2 hn).elim

/-- A variable that has its row, and the blocks to look at again for it. -/
structure VarDone (g : Graphs) (blocks : Array DBlk) (ids : Ids) (old cfg : Cfg) (rows : Array Row) (dirty : List Nat) (x : Bap.Var) (sites : List Nat) : Prop where
  row : ∀ i b, At cfg i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn cfg b.tid)
  dirty : ∀ t b, At cfg t b → (t ∈ sites ∨ (x ∈ liveIn old b.tid ∧ x ∉ liveIn cfg b.tid)) →
    ∀ p ∈ g.preds.getD t [], killedD (Bap.IR.DenseDce.blkAt blocks p) (idOf ids x) = true → p ∈ dirty

private theorem getD_set_groups (a : Array (List Nat)) (y j : Nat) (v : List Nat) :
    (a.setIfInBounds y v).getD j [] = if y = j ∧ y < a.size then v else a.getD j [] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : y = j
  · subst h
    by_cases hs : y < a.size
    · simp [hs]
    · simp [hs]
  · simp [h]

/-- What `updateAll` leaves. -/
theorem updateAll_spec {g : Graphs} {ps : List Bap.Var} {n M : Nat} (orig : Nat → List Nat) (hm : Mirror effect ids blocks cfg) (hg : GraphsOK g ids cfg ps n) (hnM : n ≤ M)
    (hrm : ∀ x, ids.contains x = true → Removal old cfg x (orig (idOf ids x))) (hin : ∀ y, ∀ s ∈ orig y, s < n)
    (pairs : List (Nat × Nat)) (rows : Array Row) (groups : Array (List Nat)) (dirty : List Nat) (seen seen2 : Marks)
    (hsize : rows.size = ids.size) (hgsize : groups.size = ids.size) (hs1 : seen.WF M) (hs2 : seen2.WF M)
    (hnames : ∀ p ∈ pairs, ∃ x, ids.contains x = true ∧ idOf ids x = p.1)
    (hstate : ∀ x, ids.contains x = true → (VarDone g blocks ids old cfg rows dirty x (orig (idOf ids x)) ∧ groups.getD (idOf ids x) [] = []) ∨
      (groups.getD (idOf ids x) [] = orig (idOf ids x) ∧ orig (idOf ids x) ≠ [] ∧ (∀ i b, At cfg i b → ((rows.getD (idOf ids x) (.short [])).contains i = true ↔ x ∈ liveIn old b.tid))))
    (hleft : ∀ y, groups.getD y [] ≠ [] → ∃ p ∈ pairs, p.1 = y)
    {rows' : Array Row} {groups' : Array (List Nat)} {dirty' : List Nat} {s1 s2 : Marks}
    (hr : updateAll g blocks pairs rows groups dirty seen seen2 = some (rows', groups', dirty', s1, s2)) :
    s1.WF M ∧ s2.WF M ∧ rows'.size = ids.size ∧ groups'.size = ids.size ∧ (∀ y, groups'.getD y [] = []) ∧
      (∀ x, ids.contains x = true → VarDone g blocks ids old cfg rows' dirty' x (orig (idOf ids x))) ∧ (∀ d ∈ dirty', d ∈ dirty ∨ d < n) := by
  have hids := hm.wf
  induction pairs generalizing rows groups dirty seen seen2 with
  | nil =>
    simp only [updateAll, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr
    have hempty : ∀ y, groups.getD y [] = [] := by
      intro y
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨p, hp, _⟩ := hleft y hne
      cases hp
    refine ⟨hs1, hs2, hsize, hgsize, hempty, fun x hx => ?_, fun d hd => Or.inl hd⟩
    rcases hstate x hx with h | ⟨h1, h2, _⟩
    · exact h.1
    · exact (h2 (h1 ▸ hempty _)).elim
  | cons pair rest ih =>
    have hnamesRest := fun p hp => hnames p (List.mem_cons_of_mem _ hp)
    simp only [updateAll] at hr
    cases hg0 : groups.getD pair.1 [] with
    | nil =>
      rw [hg0] at hr
      refine ih rows groups dirty seen seen2 hsize hgsize hs1 hs2 hnamesRest hstate ?_ hr
      intro y hy
      obtain ⟨p, hp, hpy⟩ := hleft y hy
      rcases List.mem_cons.1 hp with rfl | hp
      · subst hpy
        exact (hy hg0).elim
      · exact ⟨p, hp, hpy⟩
    | cons first others =>
      rw [hg0] at hr
      dsimp only at hr
      rw [← hg0] at hr
      obtain ⟨x0, hx0, hid⟩ := hnames pair List.mem_cons_self
      rw [← hid] at hr hg0
      cases hu : updateVar g blocks (idOf ids x0) (groups.getD (idOf ids x0) []) rows dirty seen seen2 with
      | none => rw [hu] at hr; cases hr
      | some result =>
        rw [hu] at hr
        obtain ⟨r2, d2, m1, m2⟩ := result
        dsimp only at hr
        have hltx : idOf ids x0 < ids.size := hids.lt x0 hx0
        have hold : groups.getD (idOf ids x0) [] = orig (idOf ids x0) ∧
            ∀ i b, At cfg i b → ((rows.getD (idOf ids x0) (.short [])).contains i = true ↔ x0 ∈ liveIn old b.tid) := by
          rcases hstate x0 hx0 with h | ⟨h1, _, h3⟩
          · rw [h.2] at hg0
            cases hg0
          · exact ⟨h1, h3⟩
        obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := updateVar_spec (old := old) hm hg hnM hx0 (hsize ▸ hltx) (by rw [hold.1]; exact hrm x0 hx0)
          (by rw [hold.1]; exact hin _) hold.2 hs1 hs2 hu
        refine (fun hdone => ?_) (ih r2 (groups.setIfInBounds (idOf ids x0) []) d2 m1 m2 (u3.trans hsize) (by simpa using hgsize) u1 u2 hnamesRest ?_ ?_ hr)
        · obtain ⟨z1, z2, z3, z4, z5, z6, z7⟩ := hdone
          refine ⟨z1, z2, z3, z4, z5, z6, fun d hd => ?_⟩
          rcases z7 d hd with h | h
          · rcases u7 d h with h | h
            · exact Or.inl h
            · exact Or.inr h
          · exact Or.inr h
        · intro x hx
          by_cases hxe : idOf ids x = idOf ids x0
          · have hxx := hids.inj x x0 hx hx0 hxe
            subst hxx
            refine Or.inl ⟨⟨u5, ?_⟩, ?_⟩
            · intro t b hb hc p hp hk
              exact u8 t b hb (by rw [hold.1]; exact hc) p hp hk
            · rw [getD_set_groups, ite_eq_left ⟨rfl, hgsize ▸ hltx⟩]
          · have hne : ¬ (idOf ids x0 = idOf ids x ∧ idOf ids x0 < groups.size) := fun h => hxe h.1.symm
            rw [getD_set_groups, ite_eq_right hne, u4 _ hxe]
            rcases hstate x hx with h | h
            · refine Or.inl ⟨⟨?_, ?_⟩, h.2⟩
              · intro i b hb
                rw [u4 _ hxe]
                exact h.1.row i b hb
              · intro t b hb hc p hp hk
                exact u6 p (h.1.dirty t b hb hc p hp hk)
            · exact Or.inr h
        · intro y hy
          by_cases hye : y = idOf ids x0
          · subst hye
            rw [getD_set_groups, ite_eq_left ⟨rfl, hgsize ▸ hltx⟩] at hy
            exact (hy rfl).elim
          · have hne : ¬ (idOf ids x0 = y ∧ idOf ids x0 < groups.size) := fun h => hye h.1.symm
            rw [getD_set_groups, ite_eq_right hne] at hy
            obtain ⟨p, hp, hpy⟩ := hleft y hy
            rcases List.mem_cons.1 hp with rfl | hp
            · exact (hye (hpy.symm.trans hid.symm)).elim
            · exact ⟨p, hp, hpy⟩

/-- What `addGroups` builds. -/
theorem addGroups_spec (pairs : List (Nat × Nat)) (groups : Array (List Nat)) (hlt : ∀ p ∈ pairs, p.1 < groups.size) :
    (addGroups pairs groups).size = groups.size ∧
      ∀ y s, s ∈ (addGroups pairs groups).getD y [] ↔ s ∈ groups.getD y [] ∨ (y, s) ∈ pairs := by
  simp only [addGroups]
  induction pairs generalizing groups with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    obtain ⟨i1, i2⟩ := ih (groups.modify p.1 (p.2 :: ·)) (by
      intro q hq
      simpa using hlt q (List.mem_cons_of_mem _ hq))
    refine ⟨by simpa using i1, fun y s => ?_⟩
    rw [i2, getD_modify]
    have hp := hlt p List.mem_cons_self
    by_cases hy : y = p.1
    · subst hy
      simp only [hp, and_self, ↓reduceIte, List.mem_cons, Prod.ext_iff]
      grind
    · simp only [hy, false_and, ↓reduceIte, List.mem_cons]
      have : (y, s) ≠ p := fun e => hy (by rw [← e])
      simp [this]

end Losses

end Bap.IR.DenseDce
