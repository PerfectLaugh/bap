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

def visitPredsD (blocks : Array DBlk) (x : Nat) (preds : List Nat) (state : Marks × List Nat × List Nat) : Marks × List Nat × List Nat :=
  preds.foldl (init := state) fun state p =>
    if state.1.contains p then state
    else if killedD (blkAt blocks p) x then state
    else (state.1.add p, p :: state.2.1, p :: state.2.2)

/-- The blocks that `x` is live in, from what starts it. -/
def floodD (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) : Nat → Marks → List Nat → List Nat → Option (List Nat × Marks)
  | 0, _, _, _ => none
  | _ + 1, seen, row, [] => some (row, seen)
  | fuel + 1, seen, row, t :: work =>
    if hasPhiD (blkAt blocks t) x then
      floodD blocks preds x fuel seen row work
    else
      let next := visitPredsD blocks x (preds.getD t []) (seen, row, work)
      floodD blocks preds x fuel next.1 next.2.1 next.2.2

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
      match floodD blocks preds x (start.length + blocks.size + 1) (start.foldl Marks.add seen.clear) start start with
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

/-- The blocks of the dirty list, scanned, and what the definitions they removed mention. -/
def scanAll (g : Graphs) (blocks : Array DBlk) (rows : Array Row) (dirty : List Nat) (reads live : Marks) :
    Array DBlk × List Nat × Marks × Marks :=
  dirty.foldl (init := (blocks, [], reads, live)) fun state i =>
    let r := scanD g blocks rows i (blkAt blocks i) state.2.2.1 state.2.2.2
    (state.1.setIfInBounds i r.1, r.2.1 ++ state.2.1, r.2.2.1, r.2.2.2)

def loopD (g : Graphs) (fallback : Array DBlk → Nat → Cfg) (ofBlocks : Array DBlk → Cfg) :
    Nat → Array DBlk → Array Row → List Nat → List Nat → Marks → Marks → Marks → Marks → Cfg
  | 0, blocks, _, _, _, _, _, _, _ => ofBlocks blocks
  | fuel + 1, blocks, rows, affected, dirty, kills, seen, reads, live =>
    match refreshD g blocks rows affected kills seen with
    | none => fallback blocks (fuel + 1)
    | some (rows, kills, seen) =>
      let result := scanAll g blocks rows dirty reads live
      match result.2.1 with
      | [] => ofBlocks blocks
      | dropped =>
        let affected := nodup seen dropped
        let dirtyList := nodup affected.2 (affected.1.flatMap fun x => g.definers.getD x [])
        loopD g fallback ofBlocks fuel result.1 rows affected.1 dirtyList.1 kills dirtyList.2 result.2.2.1 result.2.2.2

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
  let ofBlocks (blocks : Array DBlk) : Cfg := { cfg with blocks := blocks.toList.map DBlk.toBlk }
  loopD (graphsOf ids protectedVars cfg index) (fun blocks fuel => fallback (ofBlocks blocks) fuel) ofBlocks fuel blocks
    (Array.replicate nVars (.short [])) (List.range nVars) (List.range n)
    (Marks.empty nVars) (Marks.empty (max nVars n)) (Marks.empty nVars) (Marks.empty nVars)

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

variable {blocks : Array DBlk} {preds : Array (List Nat)} {x : Nat}

/-- The blocks where a variable is live, as far as `floodD` goes. -/
structure FloodSpec (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) (live : Nat → Prop) : Prop where
  step : ∀ t, live t → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [], killedD (blkAt blocks p) x = false → live p

private structure FloodInv (blocks : Array DBlk) (preds : Array (List Nat)) (x : Nat) (live : Nat → Prop) (seen : Marks) (row work : List Nat) : Prop where
  sound : ∀ t ∈ row, live t
  marked : ∀ t, seen.contains t = true → t ∈ row
  closed : ∀ t ∈ row, t ∉ work → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [],
    killedD (blkAt blocks p) x = false → p ∈ row
  work : ∀ t ∈ work, t ∈ row

private theorem visitPreds_inv {live : Nat → Prop} {n : Nat} (ps : List Nat) (hlive : ∀ p ∈ ps, killedD (blkAt blocks p) x = false → live p)
    (state : Marks × List Nat × List Nat) (hw : state.1.WF n) (hsound : ∀ t ∈ state.2.1, live t)
    (hmarked : ∀ t, state.1.contains t = true → t ∈ state.2.1) (hwork : ∀ t ∈ state.2.2, t ∈ state.2.1) :
    let next := visitPredsD blocks x ps state
    next.1.WF n ∧ (∀ t ∈ next.2.1, live t) ∧ (∀ t, next.1.contains t = true → t ∈ next.2.1) ∧ (∀ t ∈ next.2.2, t ∈ next.2.1) ∧
      (∀ t ∈ state.2.1, t ∈ next.2.1) ∧ (∀ t ∈ state.2.2, t ∈ next.2.2) ∧ (∀ t ∈ next.2.1, t ∈ state.2.1 ∨ t ∈ next.2.2) ∧
      ∀ p ∈ ps, killedD (blkAt blocks p) x = false → p ∈ next.2.1 := by
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
        have hk' : killedD (blkAt blocks p) x = false := by simpa using hk
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

private theorem floodD_inv {live : Nat → Prop} {n : Nat} (hspec : FloodSpec blocks preds x live) (fuel : Nat) (seen : Marks) (row work : List Nat)
    (result : List Nat) (seen' : Marks) (hw : seen.WF n) (hinv : FloodInv blocks preds x live seen row work)
    (hr : floodD blocks preds x fuel seen row work = some (result, seen')) :
    seen'.WF n ∧ FloodInv blocks preds x live seen' result [] ∧ ∀ t ∈ row, t ∈ result := by
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
        obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := visitPreds_inv (blocks := blocks) (x := x) (live := live) (n := n) (preds.getD t [])
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
theorem floodD_spec {live : Nat → Prop} {n : Nat} (hspec : FloodSpec blocks preds x live) {fuel : Nat} {seen seen' : Marks} {start result : List Nat}
    (hw : seen.WF n) (hmarked : ∀ t, seen.contains t = true → t ∈ start) (hstart : ∀ t ∈ start, live t)
    (hleast : ∀ Row : Nat → Prop, (∀ t ∈ start, Row t) →
      (∀ t, Row t → hasPhiD (blkAt blocks t) x = false → ∀ p ∈ preds.getD t [], killedD (blkAt blocks p) x = false → Row p) → ∀ t, live t → Row t)
    (hr : floodD blocks preds x fuel seen start start = some (result, seen')) :
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

private theorem getD_modify (a : Array (List Nat)) (y j : Nat) (f : List Nat → List Nat) :
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
    (xs : List Nat) (hflood : ∀ y ∈ xs, FloodSpec blocks preds y (L y)) (hsound : ∀ y ∈ xs, ∀ i, i ∈ seeds.getD y [] → L y i)
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
      cases hf : floodD blocks preds x ((seeds.getD x []).length + blocks.size + 1) ((seeds.getD x []).foldl Marks.add seen.clear) (seeds.getD x []) (seeds.getD x []) with
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
    have hstep : ∀ y ∈ affected, FloodSpec blocks g.preds y (L y) := by
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

end Bap.IR.DenseDce
