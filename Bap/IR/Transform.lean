import Bap.IR.Cfg
import Bap.Bil.Transform

namespace Bap.IR

def Label.mapExp (f : Bil.Exp → Bil.Exp) : Label → Label
  | .direct tid => .direct tid
  | .indirect target => .indirect (f target)

def JmpKind.mapExp (f : Bil.Exp → Bil.Exp) : JmpKind → JmpKind
  | .goto target => .goto (target.mapExp f)
  | .ret target => .ret (target.mapExp f)
  | .call target returnTo => .call (target.mapExp f) (returnTo.map (Label.mapExp f))
  | .interrupt number returnTo => .interrupt number returnTo

def Jmp.mapExp (f : Bil.Exp → Bil.Exp) (jmp : Jmp) : Jmp :=
  { jmp with condition := jmp.condition.map f, kind := jmp.kind.mapExp f }

def Blk.mapExp (f : Bil.Exp → Bil.Exp) (blk : Blk) : Blk :=
  { blk with
    phis := blk.phis.map fun phi => { phi with values := phi.values.map fun input => (input.1, f input.2) }
    defs := blk.defs.map fun defn => { defn with rhs := f defn.rhs }
    jmps := blk.jmps.map (Jmp.mapExp f)
  }

def Sub.mapExp (f : Bil.Exp → Bil.Exp) (sub : Sub) : Sub :=
  { sub with blks := sub.blks.map (Blk.mapExp f) }

def simplifyBlk (blk : Blk) : Blk := blk.mapExp Bil.simplifyExp
def simplifySub (sub : Sub) : Sub := sub.mapExp Bil.simplifyExp

def Label.freeVars : Label → List Bap.Var
  | .direct _ => []
  | .indirect target => Bil.freeVars target

def JmpKind.freeVars : JmpKind → List Bap.Var
  | .goto target | .ret target => target.freeVars
  | .call target returnTo =>
    (target.freeVars ++ (returnTo.map Label.freeVars |>.getD [])).eraseDups
  | .interrupt _ _ => []

def Jmp.freeVars (jmp : Jmp) : List Bap.Var :=
  ((jmp.condition.map Bil.freeVars |>.getD []) ++ jmp.kind.freeVars).eraseDups

def Blk.definedVars (blk : Blk) : List Bap.Var :=
  ((blk.phis.map Phi.var) ++ (blk.defs.map Def.var)).eraseDups

def Blk.defines (blk : Blk) (var : Bap.Var) : Bool := blk.definedVars.contains var

/-- Variables a block reads before writing them. Phis assign on entry, so they and the definitions
kill what later definitions and the jumps read; a phi's inputs are read on the incoming edge. -/
def Blk.freeVars (blk : Blk) : List Bap.Var :=
  let step := blk.defs.foldl (init := ([], blk.phis.map Phi.var)) fun state defn =>
    let free := state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2
    (free, defn.var :: state.2)
  ((step.1 ++ blk.phis.flatMap (fun phi => phi.values.flatMap (Bil.freeVars ∘ Prod.snd)) ++
    (blk.jmps.flatMap Jmp.freeVars).filter fun var => var ∉ step.2)).eraseDups

/-- `Blk.definedVars`, without comparing every pair: a phi per variable makes for long lists. -/
private def Blk.definedVarsFast (blk : Blk) : List Bap.Var :=
  Bap.Graph.Fast.dedup ((blk.phis.map Phi.var) ++ (blk.defs.map Def.var))

@[csimp] private theorem Blk.definedVars_eq_fast : @Blk.definedVars = @Blk.definedVarsFast :=
  funext fun _blk => (Bap.Graph.Fast.dedup_eq _).symm

/-- What each definition reads that isn't written before it, the last first, and what all of them and the phis write, as a set. -/
private def Blk.freeStep (defs : List Def) (chunks : List (List Bap.Var)) (killed : Std.HashSet Bap.Var) :
    List (List Bap.Var) × Std.HashSet Bap.Var :=
  defs.foldl (init := (chunks, killed)) fun (chunks, killed) defn =>
    ((Bil.freeVars defn.rhs).filter (fun var => !killed.contains var) :: chunks, killed.insert defn.var)

private theorem Blk.freeStep_spec (defs : List Def) (chunks : List (List Bap.Var)) (killed : Std.HashSet Bap.Var)
    (free kills : List Bap.Var) (hf : chunks.reverse.flatten = free) (hk : ∀ var, killed.contains var = decide (var ∈ kills)) :
    let step := defs.foldl (init := (free, kills)) fun state defn =>
      (state.1 ++ (Bil.freeVars defn.rhs).filter fun var => var ∉ state.2, defn.var :: state.2)
    (Blk.freeStep defs chunks killed).1.reverse.flatten = step.1 ∧
      ∀ var, (Blk.freeStep defs chunks killed).2.contains var = decide (var ∈ step.2) := by
  induction defs generalizing chunks killed free kills with
  | nil => exact ⟨hf, hk⟩
  | cons defn rest ih =>
    simp only [Blk.freeStep, List.foldl_cons] at ih ⊢
    apply ih
    · simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, hf]
      congr 1
      apply List.filter_congr
      intro var _
      simp [hk]
    · intro var
      rw [Std.HashSet.contains_insert, hk]
      by_cases h : defn.var = var
      · subst h; simp
      · have h' : var ≠ defn.var := fun e => h e.symm
        simp [h, h']

/-- `Blk.freeVars`, without comparing every pair, nor going through what was read before for each definition. -/
private def Blk.freeVarsFast (blk : Blk) : List Bap.Var :=
  let step := Blk.freeStep blk.defs [] ((blk.phis.map Phi.var).foldl (init := {}) fun set var => set.insert var)
  Bap.Graph.Fast.dedup ((step.1.reverse.flatten ++ blk.phis.flatMap (fun phi => phi.values.flatMap (Bil.freeVars ∘ Prod.snd)) ++
    (blk.jmps.flatMap Jmp.freeVars).filter fun var => !step.2.contains var))

private theorem foldl_insert_contains (vars : List Bap.Var) (set : Std.HashSet Bap.Var) (var : Bap.Var) :
    (vars.foldl (init := set) fun set var => set.insert var).contains var = (set.contains var || decide (var ∈ vars)) := by
  induction vars generalizing set with
  | nil => simp
  | cons head tail ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    by_cases h : head = var
    · subst h; simp
    · have h' : (head == var) = false := beq_false_of_ne h
      have h'' : var ≠ head := fun e => h e.symm
      simp [h', h'']

@[csimp] private theorem Blk.freeVars_eq_fast : @Blk.freeVars = @Blk.freeVarsFast := by
  funext blk
  have ⟨hf, hk⟩ := Blk.freeStep_spec blk.defs [] ((blk.phis.map Phi.var).foldl (init := {}) fun set var => set.insert var)
    [] (blk.phis.map Phi.var) rfl (fun var => by rw [foldl_insert_contains]; simp)
  simp only [Blk.freeVars, Blk.freeVarsFast, Bap.Graph.Fast.dedup_eq]
  rw [hf]
  congr 2
  apply List.filter_congr
  intro var _
  simp [hk]

def pruneSub (sub : Sub) : Sub := (Cfg.fromSub sub).prune.intoSub sub

end Bap.IR
