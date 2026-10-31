import Bap.IR.Transform
import Std.Data.HashSet

namespace Bap.IR

private def union (left right : List Bap.Var) : List Bap.Var := (left ++ right).eraseDups
private def subtract (left right : List Bap.Var) : List Bap.Var := left.filter fun var => var ∉ right

private def blockOut (cfg : Cfg) (ins : List (Tid × List Bap.Var)) (tid : Tid) : List Bap.Var :=
  (cfg.successors tid).foldl (init := []) fun out successor =>
    match cfg.block successor with
    | none => out
    | some block =>
      let phiVars := block.phis.map Phi.var
      let successorIn := (Assoc.get successor ins).getD []
      let out := union out (subtract successorIn phiVars)
      block.phis.foldl (init := out) fun out phi =>
        match Assoc.get tid phi.values with
        | some value => union out (Bil.freeVars value)
        | none => out

/-- Live-in, measured before the phis run: what the definitions and jumps read and what is live out,
minus everything the block assigns first. A phi's inputs are live out of the predecessor instead. -/
private def blockIn (blk : Blk) (out : List Bap.Var) : List Bap.Var :=
  let step := blk.defs.foldl (init := ([], blk.phis.map Phi.var)) fun state defn =>
    let input := state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2
    (input, defn.var :: state.2)
  let input := blk.jmps.foldl (init := step.1) fun input jmp =>
    union input (subtract jmp.freeVars step.2)
  union input (subtract out step.2)

/-- Live-out of a block: what its successors need, plus the seed if it is the seeded exit. -/
private def seedOut (initial : Option (Tid × List Bap.Var)) (tid : Tid) (out : List Bap.Var) : List Bap.Var :=
  match initial with
  | some (exit, vars) => if exit = tid then union out vars else out
  | none => out

private def livenessStep (cfg : Cfg) (initial : Option (Tid × List Bap.Var))
    (ins outs : List (Tid × List Bap.Var)) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  cfg.reachable.reverse.foldl (init := (ins, outs)) fun state tid =>
    match cfg.block tid with
    | none => state
    | some blk =>
      let out := seedOut initial tid (blockOut cfg state.1 tid)
      let input := blockIn blk out
      (Assoc.put tid input state.1, Assoc.put tid out state.2)

section Fast

open Bap.Graph.Fast (dedup dedup_eq)

private def subtractFast (left right : List Bap.Var) : List Bap.Var :=
  let removed : Std.HashSet Bap.Var := Std.HashSet.ofList right
  left.filter fun var => !removed.contains var

private theorem subtract_eq_fast (left right : List Bap.Var) : subtract left right = subtractFast left right := by
  simp only [subtract, subtractFast]
  apply List.filter_congr
  intro x _
  simp [Std.HashSet.contains_ofList]

private theorem eraseDups_union (left right : List Bap.Var) :
    (left.eraseDups ++ right).eraseDups = (left ++ right).eraseDups := by
  rw [List.eraseDups_append, List.eraseDups_append]
  have hnd : left.eraseDups.Nodup := Bap.Proofs.Graph.nodup_eraseDups left
  have hself : left.eraseDups.eraseDups = left.eraseDups := Bap.Proofs.Graph.eraseDups_of_nodup hnd
  rw [hself]
  congr 2
  apply List.filter_congr
  intro x _
  simp

/-- What a block needs from a successor, in the order `blockOut` meets it. -/
private def edgeNeeds (cfg : Cfg) (ins : List (Tid × List Bap.Var)) (tid successor : Tid) : List Bap.Var :=
  match cfg.block successor with
  | none => []
  | some block =>
    subtractFast ((Assoc.get successor ins).getD []) (block.phis.map Phi.var) ++
      block.phis.flatMap fun phi =>
        match Assoc.get tid phi.values with
        | some value => Bil.freeVars value
        | none => []

/-- `blockOut`, with its unions in one go. -/
private def blockOutFast (cfg : Cfg) (ins : List (Tid × List Bap.Var)) (tid : Tid) : List Bap.Var :=
  dedup ((cfg.successors tid).flatMap (edgeNeeds cfg ins tid))

private theorem foldl_phi_union (tid : Tid) (phis : List Phi) (acc : List Bap.Var) :
    phis.foldl (init := acc.eraseDups) (fun out phi =>
        match Assoc.get tid phi.values with
        | some value => union out (Bil.freeVars value)
        | none => out) =
      (acc ++ phis.flatMap fun phi =>
        match Assoc.get tid phi.values with
        | some value => Bil.freeVars value
        | none => []).eraseDups := by
  induction phis generalizing acc with
  | nil => simp
  | cons phi rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons]
    cases hg : Assoc.get tid phi.values with
    | none => simpa using ih acc
    | some value =>
      have hu : union acc.eraseDups (Bil.freeVars value) = (acc ++ Bil.freeVars value).eraseDups := eraseDups_union _ _
      simp only [hu]
      rw [ih, List.append_assoc]

@[csimp] private theorem blockOut_eq_fast : @blockOut = @blockOutFast := by
  funext cfg ins tid
  simp only [blockOut, blockOutFast, dedup_eq]
  have key : ∀ (l : List Tid) (acc : List Bap.Var), l.foldl (init := acc.eraseDups) (fun out successor =>
        match cfg.block successor with
        | none => out
        | some block =>
          let phiVars := block.phis.map Phi.var
          let successorIn := (Assoc.get successor ins).getD []
          let out := union out (subtract successorIn phiVars)
          block.phis.foldl (init := out) fun out phi =>
            match Assoc.get tid phi.values with
            | some value => union out (Bil.freeVars value)
            | none => out) = (acc ++ l.flatMap (edgeNeeds cfg ins tid)).eraseDups := by
    intro l
    induction l with
    | nil => simp
    | cons s rest ih =>
      intro acc
      simp only [List.foldl_cons, List.flatMap_cons, edgeNeeds]
      cases hb : cfg.block s with
      | none => simpa using ih acc
      | some block =>
        have hu : union acc.eraseDups (subtract ((Assoc.get s ins).getD []) (block.phis.map Phi.var)) =
            (acc ++ subtractFast ((Assoc.get s ins).getD []) (block.phis.map Phi.var)).eraseDups := by
          rw [subtract_eq_fast]
          exact eraseDups_union _ _
        simp only [hu]
        rw [foldl_phi_union, ih]
        simp only [List.append_assoc]
  simpa using key (cfg.successors tid) []

/-- `blockIn`, with its unions in one go. -/
private def blockInFast (blk : Blk) (out : List Bap.Var) : List Bap.Var :=
  let step := blk.defs.foldl (init := ([], blk.phis.map Phi.var)) fun state defn =>
    let input := state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2
    (input, defn.var :: state.2)
  let killed : Std.HashSet Bap.Var := Std.HashSet.ofList step.2
  let reads := blk.jmps.flatMap fun jmp => jmp.freeVars.filter fun var => !killed.contains var
  dedup (step.1 ++ reads ++ out.filter fun var => !killed.contains var)

@[csimp] private theorem blockIn_eq_fast : @blockIn = @blockInFast := by
  funext blk out
  simp only [blockIn, blockInFast, dedup_eq]
  generalize blk.defs.foldl (init := ([], blk.phis.map Phi.var)) (fun state defn =>
    let input := state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2
    (input, defn.var :: state.2)) = step
  have hsub : ∀ l : List Bap.Var, subtract l step.2 = l.filter fun var => !(Std.HashSet.ofList step.2).contains var := fun l =>
    subtract_eq_fast l step.2
  have key : ∀ (jmps : List Jmp) (input : List Bap.Var), (jmps.foldl (init := input) fun input jmp =>
        union input (subtract jmp.freeVars step.2)) =
      if jmps = [] then input else (input ++ jmps.flatMap fun jmp => subtract jmp.freeVars step.2).eraseDups := by
    intro jmps
    induction jmps with
    | nil => simp
    | cons j rest ih =>
      intro input
      rw [List.foldl_cons, ih, List.flatMap_cons]
      by_cases hrest : rest = []
      · subst hrest
        simp [union]
      · have hu : (union input (subtract j.freeVars step.2) ++ rest.flatMap fun jmp => subtract jmp.freeVars step.2).eraseDups =
            (input ++ (subtract j.freeVars step.2 ++ rest.flatMap fun jmp => subtract jmp.freeVars step.2)).eraseDups := by
          rw [← List.append_assoc]
          exact eraseDups_union _ _
        simp [hrest, hu]
  rw [key]
  by_cases hj : blk.jmps = []
  · simp [hj, union, hsub]
  · have hu : (union ((step.1 ++ blk.jmps.flatMap fun jmp => subtract jmp.freeVars step.2).eraseDups) (subtract out step.2)) =
        (step.1 ++ (blk.jmps.flatMap fun jmp => subtract jmp.freeVars step.2) ++ subtract out step.2).eraseDups :=
      eraseDups_union _ _
    simp only [hj, ↓reduceIte, hsub]
    exact eraseDups_union _ _

/-- `sameSets`, without comparing every pair of a row. -/
private def sameSetsFast (keys : List Tid) (left right : List (Tid × List Bap.Var)) : Bool :=
  keys.all fun tid =>
    let leftRow := (Assoc.get tid left).getD []
    let rightRow := (Assoc.get tid right).getD []
    let leftSet : Std.HashSet Bap.Var := Std.HashSet.ofList leftRow
    let rightSet : Std.HashSet Bap.Var := Std.HashSet.ofList rightRow
    leftRow.all rightSet.contains && rightRow.all leftSet.contains

end Fast

/-- Tables are compared as sets per key: rebuilding a set may reorder it without changing it. -/
private def sameSets (keys : List Tid) (left right : List (Tid × List Bap.Var)) : Bool :=
  keys.all fun tid => Bap.Graph.setEq ((Assoc.get tid left).getD []) ((Assoc.get tid right).getD [])

private def livenessAux (cfg : Cfg) (initial : Option (Tid × List Bap.Var)) :
    Nat → List (Tid × List Bap.Var) → List (Tid × List Bap.Var) →
      List (Tid × List Bap.Var) × List (Tid × List Bap.Var)
  | 0, ins, outs => (ins, outs)
  | fuel + 1, ins, outs =>
    let (nextIns, nextOuts) := livenessStep cfg initial ins outs
    if sameSets cfg.reachable nextIns ins && sameSets cfg.reachable nextOuts outs then
      (ins, outs)
    else
      livenessAux cfg initial fuel nextIns nextOuts

@[csimp] private theorem sameSets_eq_fast : @sameSets = @sameSetsFast := by
  funext keys left right
  simp only [sameSets, sameSetsFast, Bap.Graph.setEq, Bap.Graph.subset]
  apply congrArg (fun f => keys.all f)
  funext tid
  have hrow : ∀ l r : List Bap.Var, (l.all fun value => decide (value ∈ r)) = l.all (Std.HashSet.ofList r).contains := by
    intro l r
    apply congrArg (fun f => l.all f)
    funext x
    rw [Bool.eq_iff_iff]
    simp [Std.HashSet.contains_ofList]
  simp only [hrow]

/-- Each pass that changes a table adds a variable to a row of one of the two tables. -/
private def livenessFuel (cfg : Cfg) (vars : List Bap.Var) : Nat :=
  let varCount := (cfg.blocks.flatMap (fun blk => blk.definedVars ++ blk.freeVars) ++ vars).eraseDups.length
  2 * varCount * cfg.reachable.length + 1

private def livenessFuelFast (cfg : Cfg) (vars : List Bap.Var) : Nat :=
  let varCount := (Bap.Graph.Fast.dedup (cfg.blocks.flatMap (fun blk => blk.definedVars ++ blk.freeVars) ++ vars)).length
  2 * varCount * cfg.reachable.length + 1

@[csimp] private theorem livenessFuel_eq_fast : @livenessFuel = @livenessFuelFast := by
  funext cfg vars
  simp only [livenessFuel, livenessFuelFast, Bap.Graph.Fast.dedup_eq]

/-- A table by key, in their order, however the solver left it. -/
private def rowsOf (keys : List Tid) (tables : List (Tid × List Bap.Var) × List (Tid × List Bap.Var)) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  (keys.map fun tid => (tid, (Assoc.get tid tables.1).getD []), keys.map fun tid => (tid, (Assoc.get tid tables.2).getD []))

private def livenessFromRaw (cfg : Cfg) (exit : Tid) (vars : List Bap.Var) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  let outs := Assoc.put exit vars ins
  livenessAux cfg (some (exit, vars)) (livenessFuel cfg vars) ins outs

private def livenessRaw (cfg : Cfg) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let ins := cfg.reachable.map fun tid => (tid, [])
  livenessAux cfg none (livenessFuel cfg []) ins ins

def Cfg.livenessFrom (cfg : Cfg) (exit : Tid) (vars : List Bap.Var) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  rowsOf cfg.reachable (livenessFromRaw cfg exit vars)

def Cfg.liveness (cfg : Cfg) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  rowsOf cfg.reachable (livenessRaw cfg)

/-! The solver with its tables in hash maps, and one list of reachable blocks. Every pass of the list
solver looks up blocks and rows in lists, and scans the edges for successors. -/

section FastSolver

open Bap.Graph.Fast (assocTable assocTable_get groupBy groupBy_getD dedup dedup_eq)

private abbrev Rows := Std.HashMap Tid (List Bap.Var)

private structure Tables where
  blocks : Std.HashMap Tid Blk
  edges : Std.HashMap Tid (List Tid)

private def tablesOf (cfg : Cfg) : Tables :=
  { blocks := assocTable (cfg.blocks.map fun blk => (blk.tid, blk)), edges := groupBy cfg.graph.edges }

private def edgeNeedsT (tables : Tables) (ins : Rows) (tid successor : Tid) : List Bap.Var :=
  match tables.blocks.get? successor with
  | none => []
  | some block =>
    subtractFast (ins.getD successor []) (block.phis.map Phi.var) ++
      block.phis.flatMap fun phi =>
        match Assoc.get tid phi.values with
        | some value => Bil.freeVars value
        | none => []

private def blockOutT (tables : Tables) (ins : Rows) (tid : Tid) : List Bap.Var :=
  dedup ((dedup (tables.edges.getD tid [])).flatMap (edgeNeedsT tables ins tid))

private def livenessStepT (tables : Tables) (order : List Tid) (initial : Option (Tid × List Bap.Var))
    (ins outs : Rows) : Rows × Rows :=
  order.foldl (init := (ins, outs)) fun state tid =>
    match tables.blocks.get? tid with
    | none => state
    | some blk =>
      let out := seedOut initial tid (blockOutT tables state.1 tid)
      (state.1.insert tid (blockIn blk out), state.2.insert tid out)

private def sameRows (keys : List Tid) (left right : Rows) : Bool :=
  keys.all fun tid =>
    let leftRow := left.getD tid []
    let rightRow := right.getD tid []
    let leftSet : Std.HashSet Bap.Var := Std.HashSet.ofList leftRow
    let rightSet : Std.HashSet Bap.Var := Std.HashSet.ofList rightRow
    leftRow.all rightSet.contains && rightRow.all leftSet.contains

private def livenessAuxT (tables : Tables) (keys order : List Tid) (initial : Option (Tid × List Bap.Var)) :
    Nat → Rows → Rows → Rows × Rows
  | 0, ins, outs => (ins, outs)
  | fuel + 1, ins, outs =>
    let (nextIns, nextOuts) := livenessStepT tables order initial ins outs
    if sameRows keys nextIns ins && sameRows keys nextOuts outs then
      (ins, outs)
    else
      livenessAuxT tables keys order initial fuel nextIns nextOuts

private abbrev Same (list : List (Tid × List Bap.Var)) (rows : Rows) : Prop :=
  ∀ tid, Assoc.get tid list = rows.get? tid

private theorem Same.getD {list : List (Tid × List Bap.Var)} {rows : Rows} (h : Same list rows) (tid : Tid) :
    (Assoc.get tid list).getD [] = rows.getD tid [] := by
  rw [h tid, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.get?_eq_getElem?]

private theorem Same.put {list : List (Tid × List Bap.Var)} {rows : Rows} (h : Same list rows) (tid : Tid)
    (value : List Bap.Var) : Same (Assoc.put tid value list) (rows.insert tid value) := by
  intro key
  have hg : Assoc.get key (Assoc.put tid value list) = if key = tid then some value else Assoc.get key list := by
    by_cases hk : key = tid
    · subst hk
      simp
    · simp only [hk, ite_false, Assoc.get, Assoc.put, List.lookup_cons]
      have hb : (key == tid) = false := by simpa using hk
      simp only [hb]
      have key2 : ∀ l : List (Tid × List Bap.Var), List.lookup key (l.filter fun e => e.1 != tid) = List.lookup key l := by
        intro l
        induction l with
        | nil => rfl
        | cons e es ih =>
          obtain ⟨a, b⟩ := e
          by_cases ha : a = tid
          · subst ha
            simp [List.lookup_cons, hb, ih]
          · have hk' : (a != tid) = true := by simpa using ha
            simp only [List.filter_cons, hk', ↓reduceIte, List.lookup_cons, ih]
      exact key2 list
  rw [hg, h key]
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hk : key = tid
  · subst hk
    simp
  · have hb : (tid == key) = false := by simpa using fun e : tid = key => hk e.symm
    simp [hk, hb]

private theorem tables_block (cfg : Cfg) (tid : Tid) : cfg.block tid = (tablesOf cfg).blocks.get? tid := by
  simp only [tablesOf, assocTable_get, Cfg.block]
  have key : ∀ l : List Blk, l.find? (fun blk => decide (blk.tid = tid)) = Assoc.get tid (l.map fun blk => (blk.tid, blk)) := by
    intro l
    induction l with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.find?_cons, List.map_cons, Assoc.get, List.lookup_cons]
      by_cases hb : b.tid = tid
      · subst hb
        simp
      · have h1 : (tid == b.tid) = false := by simpa using fun e : tid = b.tid => hb e.symm
        simp only [hb, decide_false, h1]
        exact ih
  exact key cfg.blocks

private theorem tables_successors (cfg : Cfg) (tid : Tid) :
    cfg.successors tid = dedup ((tablesOf cfg).edges.getD tid []) := by
  have := Bap.Graph.Fast.successors_eq cfg.graph tid
  exact this.symm

private theorem edgeNeeds_eq (cfg : Cfg) {ins : List (Tid × List Bap.Var)} {rows : Rows} (h : Same ins rows) (tid successor : Tid) :
    edgeNeeds cfg ins tid successor = edgeNeedsT (tablesOf cfg) rows tid successor := by
  simp only [edgeNeeds, edgeNeedsT, tables_block, h.getD]

private theorem blockOut_eq (cfg : Cfg) {ins : List (Tid × List Bap.Var)} {rows : Rows} (h : Same ins rows) (tid : Tid) :
    blockOut cfg ins tid = blockOutT (tablesOf cfg) rows tid := by
  rw [blockOut_eq_fast]
  simp only [blockOutFast, blockOutT, tables_successors]
  rw [show edgeNeeds cfg ins tid = edgeNeedsT (tablesOf cfg) rows tid from funext (edgeNeeds_eq cfg h tid)]

private theorem livenessStep_same (cfg : Cfg) (order : List Tid) (initial : Option (Tid × List Bap.Var))
    {ins outs : List (Tid × List Bap.Var)} {insT outsT : Rows} (hi : Same ins insT) (ho : Same outs outsT) :
    let list := order.foldl (init := (ins, outs)) fun state tid =>
      match cfg.block tid with
      | none => state
      | some blk =>
        let out := seedOut initial tid (blockOut cfg state.1 tid)
        let input := blockIn blk out
        (Assoc.put tid input state.1, Assoc.put tid out state.2)
    let table := livenessStepT (tablesOf cfg) order initial insT outsT
    Same list.1 table.1 ∧ Same list.2 table.2 := by
  induction order generalizing ins outs insT outsT with
  | nil => exact ⟨hi, ho⟩
  | cons tid rest ih =>
    simp only [List.foldl_cons, livenessStepT]
    cases hb : cfg.block tid with
    | none =>
      have ht : (tablesOf cfg).blocks.get? tid = none := by rw [← tables_block, hb]
      simp only [ht]
      exact ih hi ho
    | some blk =>
      have ht : (tablesOf cfg).blocks.get? tid = some blk := by rw [← tables_block, hb]
      simp only [ht]
      rw [← blockOut_eq cfg hi]
      exact ih (hi.put tid (blockIn blk (seedOut initial tid (blockOut cfg ins tid))))
        (ho.put tid (seedOut initial tid (blockOut cfg ins tid)))

private theorem sameSets_eq_rows {keys : List Tid} {a b : List (Tid × List Bap.Var)} {ta tb : Rows} (ha : Same a ta) (hb : Same b tb) :
    sameSets keys a b = sameRows keys ta tb := by
  rw [sameSets_eq_fast]
  simp only [sameSetsFast, sameRows, ha.getD, hb.getD]

private theorem livenessAux_same (cfg : Cfg) (initial : Option (Tid × List Bap.Var)) (fuel : Nat)
    {ins outs : List (Tid × List Bap.Var)} {insT outsT : Rows} (hi : Same ins insT) (ho : Same outs outsT) :
    let list := livenessAux cfg initial fuel ins outs
    let table := livenessAuxT (tablesOf cfg) cfg.reachable cfg.reachable.reverse initial fuel insT outsT
    Same list.1 table.1 ∧ Same list.2 table.2 := by
  induction fuel generalizing ins outs insT outsT with
  | zero => exact ⟨hi, ho⟩
  | succ fuel ih =>
    have h1 : Same (livenessStep cfg initial ins outs).1 (livenessStepT (tablesOf cfg) cfg.reachable.reverse initial insT outsT).1 :=
      (livenessStep_same cfg cfg.reachable.reverse initial hi ho).1
    have h2 : Same (livenessStep cfg initial ins outs).2 (livenessStepT (tablesOf cfg) cfg.reachable.reverse initial insT outsT).2 :=
      (livenessStep_same cfg cfg.reachable.reverse initial hi ho).2
    simp only [livenessAux, livenessAuxT]
    rw [sameSets_eq_rows h1 hi, sameSets_eq_rows h2 ho]
    split
    · exact ⟨hi, ho⟩
    · exact ih h1 h2

/-- `Cfg.liveness`, from the solver with hash maps. -/
private def livenessFast (cfg : Cfg) : List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let keys := cfg.reachable
  let ins : Rows := assocTable (keys.map fun tid => (tid, []))
  let table := livenessAuxT (tablesOf cfg) keys keys.reverse none (livenessFuel cfg []) ins ins
  (keys.map fun tid => (tid, table.1.getD tid []), keys.map fun tid => (tid, table.2.getD tid []))

@[csimp] private theorem liveness_eq_fast : @Cfg.liveness = @livenessFast := by
  funext cfg
  have hi : Same (cfg.reachable.map fun tid => (tid, [])) (assocTable (cfg.reachable.map fun tid => (tid, []))) :=
    fun tid => (assocTable_get _ tid).symm
  obtain ⟨h1, h2⟩ := livenessAux_same cfg none (livenessFuel cfg []) hi hi
  simp only [Cfg.liveness, livenessFast, rowsOf, livenessRaw, h1.getD, h2.getD]

private def livenessFromFast (cfg : Cfg) (exit : Tid) (vars : List Bap.Var) :
    List (Tid × List Bap.Var) × List (Tid × List Bap.Var) :=
  let keys := cfg.reachable
  let ins : Rows := assocTable (keys.map fun tid => (tid, []))
  let table := livenessAuxT (tablesOf cfg) keys keys.reverse (some (exit, vars)) (livenessFuel cfg vars) ins (ins.insert exit vars)
  (keys.map fun tid => (tid, table.1.getD tid []), keys.map fun tid => (tid, table.2.getD tid []))

@[csimp] private theorem livenessFrom_eq_fast : @Cfg.livenessFrom = @livenessFromFast := by
  funext cfg exit vars
  have hi : Same (cfg.reachable.map fun tid => (tid, [])) (assocTable (cfg.reachable.map fun tid => (tid, []))) :=
    fun tid => (assocTable_get _ tid).symm
  obtain ⟨h1, h2⟩ := livenessAux_same cfg (some (exit, vars)) (livenessFuel cfg vars) hi (hi.put exit vars)
  simp only [Cfg.livenessFrom, livenessFromFast, rowsOf, livenessFromRaw, h1.getD, h2.getD]

end FastSolver

@[simp] theorem liveness_empty : (Cfg.fromSub ⟨1, "empty", [], []⟩).liveness = ([], []) := by
  rfl

end Bap.IR
