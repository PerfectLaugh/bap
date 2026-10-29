import Bap.IR.Transform

namespace Bap.IR

def Blk.definesBase (blk : Blk) (var : Bap.Var) : Bool :=
  blk.definedVars.any fun defined => defined.base = var.base

private def insertPhisForVar (cfg : Cfg) (frontier : List (Tid × List Tid)) (var : Bap.Var) :
    Nat → List Tid → List Tid → Cfg
  | 0, _, _ => cfg
  | _fuel + 1, [], _ => cfg
  | fuel + 1, tid :: work, inserted =>
    let joins := (Assoc.get tid frontier).getD []
    let (cfg, inserted, work) := joins.foldl (init := (cfg, inserted, work)) fun state join =>
      let (cfg, inserted, work) := state
      if join ∈ inserted then
        (cfg, inserted, work)
      else
        let predecessors := cfg.predecessors join
        let phi : Phi := ⟨join, var, predecessors.map fun pred => (pred, .var var)⟩
        (cfg.updateBlock join fun blk => { blk with phis := blk.phis ++ [phi] }, join :: inserted, join :: work)
    insertPhisForVar cfg frontier var fuel work inserted

private def insertAllPhis (cfg : Cfg) (frontier : List (Tid × List Tid)) : List Bap.Var → Cfg
  | [] => cfg
  | var :: rest =>
    let definitions := cfg.blocks.filterMap fun blk => if blk.definesBase var then some blk.tid else none
    let fuel := cfg.blocks.length * 2 + 1
    let cfg := insertPhisForVar cfg frontier var fuel definitions []
    insertAllPhis cfg frontier rest

structure RenameState where
  stacks : List (Bap.Var × List Bap.Var) := []
  counters : List (Bap.Var × Nat) := []
  deriving Repr

private def newName (var : Bap.Var) (state : RenameState) : Bap.Var × RenameState :=
  let var := var.base
  let counter := (Assoc.get var state.counters).getD 1
  let renamed := var.version counter
  let stack := (Assoc.get var state.stacks).getD []
  (renamed, {
    stacks := Assoc.put var (stack ++ [renamed]) state.stacks
    counters := Assoc.put var (counter + 1) state.counters
  })

private def topName (var : Bap.Var) (state : RenameState) : Bap.Var :=
  let base := var.base
  match Assoc.get base state.stacks with
  | some stack => stack.getLast?.getD base
  | none => base

private def replacements (state : RenameState) : List (Bap.Var × Bil.Exp) :=
  state.stacks.filterMap fun entry => entry.2.getLast?.map fun var => (entry.1, .var var)

private def renameExp (state : RenameState) (exp : Bil.Exp) : Bil.Exp :=
  Bil.substitute (replacements state) exp

private def renamePhis : List Phi → RenameState → List Phi × RenameState
  | [], state => ([], state)
  | phi :: rest, state =>
    let (var, state) := newName phi.var state
    let (rest, state) := renamePhis rest state
    ({ phi with var := var } :: rest, state)

private def renameDefs : List Def → RenameState → List Def × RenameState
  | [], state => ([], state)
  | defn :: rest, state =>
    let rhs := renameExp state defn.rhs
    let (var, state) := newName defn.var state
    let (rest, state) := renameDefs rest state
    ({ defn with var := var, rhs := rhs } :: rest, state)

private def updatePhiInputs (source successor : Tid) (state : RenameState) (cfg : Cfg) : Cfg :=
  cfg.updateBlock successor fun blk =>
    { blk with phis := blk.phis.map fun phi =>
      { phi with values := phi.values.map fun input =>
        if input.1 = source then
          match input.2 with
          | .var var => (source, .var (topName var state))
          | _ => input
        else
          input
      }
    }

private def popVars (vars : List Bap.Var) (state : RenameState) : RenameState :=
  { state with stacks := state.stacks.map fun entry =>
    if entry.1 ∈ vars then (entry.1, entry.2.dropLast) else entry
  }

private def renameBlock (idom : List (Tid × Tid)) : Nat → Tid → Cfg → RenameState → Cfg × RenameState
  | 0, _, cfg, state => (cfg, state)
  | fuel + 1, tid, cfg, state =>
    match cfg.block tid with
    | none => (cfg, state)
    | some block =>
      let defined := block.definedVars.map Bap.Var.base
      let (phis, state) := renamePhis block.phis state
      let (defs, state) := renameDefs block.defs state
      let jmps := block.jmps.map (Jmp.mapExp (renameExp state))
      let cfg := cfg.updateBlock tid fun block => { block with phis := phis, defs := defs, jmps := jmps }
      let cfg := (cfg.successors tid).foldl (fun cfg successor => updatePhiInputs tid successor state cfg) cfg
      let children := (idom.filter fun entry => entry.2 = tid).map Prod.fst
      let (cfg, state) := children.foldl (init := (cfg, state)) fun current child =>
        renameBlock idom fuel child current.1 current.2
      (cfg, popVars defined state)

def toSsa (sub : Sub) : Sub :=
  let cfg := Cfg.connected sub
  let idom := cfg.immediateDominators
  let frontier := cfg.dominanceFrontier
  let vars := (cfg.blocks.flatMap fun blk =>
    (blk.definedVars ++ blk.freeVars).map Bap.Var.base).eraseDups
  let cfg := insertAllPhis cfg frontier vars
  let (cfg, _) := renameBlock idom (cfg.blocks.length + 1) cfg.start cfg {}
  { sub with blks := sub.blks.filterMap fun blk => cfg.block blk.tid }

@[simp] theorem toSsa_tid (sub : Sub) : (toSsa sub).tid = sub.tid := by
  rfl

@[simp] theorem toSsa_name (sub : Sub) : (toSsa sub).name = sub.name := by
  rfl

end Bap.IR
