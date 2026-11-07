import Bap.Analysis.Cff
import Bap.Linux.DynamicTaint

/-! A verdict of a program is what some registers and memory hold at some instruction: `captureVerdict` runs a machine there, notes them and
saves the machine, and `explain` says where each byte of them came from, by a tracker, and what of that can't be said: what was there before
anything was followed or the machine was put back, what tracking couldn't follow, what was let go of, and what only a branch or a pointer led
to. A transition of a flattened machine that went the wrong way is a verdict too, of its state where the dispatcher read it. -/

namespace Bap.Analysis.Verdict

open Bap.Emu (ThreadId)
open Bap.Analysis.DynamicTaint
open Bap.Linux (Machine)

inductive Criterion where
  | register (name : String) (size : Nat := 8)
  | memory (address size : Nat)
  /-- Where a state of `Cff` is, which is one of the others when it is captured. -/
  | location (location : Cff.StateLocation)
  deriving DecidableEq, Repr, Inhabited

structure Criteria where
  pc : Nat
  /-- In which thread, or in whichever comes there. -/
  thread : Option ThreadId := none
  /-- Which time it comes there that counts, from 1. -/
  hit : Nat := 1
  criteria : List Criterion
  quantum : Nat := 100000
  fuel : Nat := 1000000000

structure Checkpoint where
  pc : Nat
  thread : ThreadId
  group : Nat
  /-- Where the machine was in its history, if it keeps one. -/
  position : Option Nat
  /-- Each criterion as a register or memory, with what it held. -/
  values : List (Criterion × ByteArray)
  /-- The machine there, as `Machine.checkpoint` has it. -/
  data : ByteArray

/-- A criterion as a register or memory, for the thread that runs. -/
private def resolve (machine : Machine) : Criterion → IO Criterion
  | .location (.register name width) => pure (.register name ((width + 7) / 8))
  | .location (.memory address size) => pure (.memory address size)
  | .location (.relative name offset size) => do
    let width ← Bap.Emu.wordWidth machine.emu
    match Value.asBits (← Bap.Emu.reg machine.emu ⟨name, .imm width, 0, false⟩) with
    | .ok bits => pure (.memory ((Int.ofNat bits.2.toNat + offset) % (2 ^ width : Int)).toNat size)
    | .error error => throw <| IO.userError s!"{name}: {error}"
  | other => pure other

/-- What a criterion holds now: a register from its least significant byte, and memory from its address up. -/
private def valueOf (machine : Machine) : Criterion → IO ByteArray
  | .register name size => do
    match Value.asBits (← Bap.Emu.reg machine.emu ⟨name, .imm (size * 8), 0, false⟩) with
    | .ok bits => pure (ByteArray.mk ((Array.range size).map fun index => (bits.2.toNat >>> (8 * index)).toUInt8))
    | .error _ =>
      -- A register that is wider than asked: its low bytes.
      let width ← Bap.Emu.wordWidth machine.emu
      match Value.asBits (← Bap.Emu.reg machine.emu ⟨name, .imm width, 0, false⟩) with
      | .ok bits => pure (ByteArray.mk ((Array.range size).map fun index => (bits.2.toNat >>> (8 * index)).toUInt8))
      | .error error => throw <| IO.userError s!"{name}: {error}"
  | .memory address size => Bap.Emu.peek machine.emu address size
  | .location _ => pure ByteArray.empty

/-- Runs the machine to the `hit`th time that a thread of `criteria` comes to its instruction, as the program would get there, and there notes
what the criteria hold and saves the machine. It doesn't go on from there. -/
def captureVerdict (machine : Machine) (criteria : Criteria) : IO Checkpoint := do
  let emu := machine.emu
  let breakpoint ← Bap.Emu.addBreakpoint emu criteria.pc
  try
    let mut hits := 0
    let mut fuel := criteria.fuel
    while true do
      let outcome ← machine.run (quantum := criteria.quantum) (fuel := fuel) fun _ => pure ()
      match outcome with
      | .stopped id =>
        let thread ← Bap.Emu.thread emu
        if (← emu.pc.get) == criteria.pc && (criteria.thread.all (· == thread)) then
          hits := hits + 1
          if hits == criteria.hit then
            let values ← criteria.criteria.mapM fun criterion => do
              let concrete ← resolve machine criterion
              pure (concrete, ← valueOf machine concrete)
            let group := (((← emu.taskTable.get).find? thread).map (·.group)).getD thread
            let position ← match ← machine.history.get with
              | some history => pure (some history.position)
              | none => pure none
            return { pc := criteria.pc, thread, group, position, values, data := ← machine.checkpoint }
        Bap.Emu.resumeThread emu id
        fuel := fuel - 1
        if fuel == 0 then break
      | other => throw <| IO.userError s!"it never came to the verdict, which ended as {repr other}"
    throw <| IO.userError "it never came to the verdict"
  finally
    Bap.Emu.removeHook emu breakpoint

/-- Why a byte of a verdict can't be said to come from where its explanation says, or from anywhere. -/
inductive Reason where
  /-- Nothing followed wrote it: it was there when tracking started, or when the machine was put back, as these say. -/
  | untouched (restoredFrom : List (Nat × String))
  /-- What led to it has gone, as there was no room for it. -/
  | truncated
  /-- Tracking couldn't follow all of these instructions on the way. -/
  | gaps (pcs : List Nat)
  /-- It comes from what was marked only by what a branch chose or by a pointer, which is likely and not shown. -/
  | likely (edge : Edge)
  deriving Repr

structure Unresolved where
  criterion : Nat
  byte : Nat
  reason : Reason
  deriving Repr

structure Report where
  /-- Each byte of each criterion with where it came from. -/
  bytes : List (Nat × Nat × Tracker.Explanation)
  /-- What it all comes from, with the strongest edge that it does by. -/
  sources : List (String × Option Nat × Edge)
  unresolved : List Unresolved

private def edgeRank : Edge → Nat
  | .data => 0
  | .condition => 1
  | .guard => 2
  | .address => 3

/-- Where each byte of a verdict came from, by a tracker of the machine, which has to be where the verdict was: just after `captureVerdict`,
or on a machine that went on from its checkpoint. -/
def explain (tracker : Tracker) (machine : Machine) (checkpoint : Checkpoint) : IO Report := do
  let space ← Bap.Emu.spaceOf machine.emu checkpoint.thread
  let gaps : Std.HashSet Nat := (← tracker.gapsOf).foldl (fun gaps entry => gaps.insert entry.1) {}
  let mut bytes : Array (Nat × Nat × Tracker.Explanation) := #[]
  let mut unresolved : Array Unresolved := #[]
  -- Each source once, where it was first found, with the strongest edge that any byte reaches it by.
  let mut sources : Array (String × Option Nat × Edge) := #[]
  let mut where_ : Std.HashMap (String × Option Nat) Nat := {}
  for ((criterion, value), index) in checkpoint.values.zipIdx do
    for byte in List.range value.size do
      let explanation ← match criterion with
        | .register name _ => tracker.explainRegister name byte (some checkpoint.thread)
        | .memory address _ => tracker.explainMemory (address + byte) (some space)
        | .location _ => pure { origin := .untouched }
      bytes := bytes.push (index, byte, explanation)
      match explanation.origin with
      | .untouched => unresolved := unresolved.push { criterion := index, byte, reason := .untouched explanation.restoredFrom }
      | .clean _ => pure ()
      | .tainted .. =>
        if explanation.truncated then unresolved := unresolved.push { criterion := index, byte, reason := .truncated }
        let missed := (explanation.path.map (·.node.pc)).filter gaps.contains
        unless missed.isEmpty do unresolved := unresolved.push { criterion := index, byte, reason := .gaps missed.eraseDups }
        let found := explanation.sources.filterMap fun (node, at_, edge) => match node.kind with
          | .source label offset => some (label, offset.map (· + at_), edge)
          | _ => none
        if !found.isEmpty && found.all (fun (_, _, edge) => edgeRank edge ≥ 2) then
          let strongest := found.foldl (fun best (_, _, edge) => if edgeRank edge < edgeRank best then edge else best) .address
          unresolved := unresolved.push { criterion := index, byte, reason := .likely strongest }
        for (label, offset, edge) in found do
          match where_[(label, offset)]? with
          | some at_ =>
            if edgeRank edge < edgeRank sources[at_]!.2.2 then sources := sources.set! at_ (label, offset, edge)
          | none =>
            where_ := where_.insert (label, offset) sources.size
            sources := sources.push (label, offset, edge)
  pure { bytes := bytes.toList, sources := sources.toList, unresolved := unresolved.toList }

/-- The criteria of a transition, which is the state that the dispatcher read at the visit after it: where a slice back from a round that
went the wrong way starts. -/
def ofTransition (profile : Cff.Profile) (transition : Cff.Transition) : Criteria :=
  { pc := profile.dispatcher, thread := some transition.thread, hit := transition.index + 2, criteria := [.location profile.state] }

/-- The criteria to capture what a program did at the `index`th instruction of a trace of pcs, in the order it ran them: that
instruction's pc, at the occurrence of it that `index` is, with what `criteria` name — so that a verdict or a slice there needs no
recovered dispatcher, only the pcs a trace kept. For the occurrence to be the one a fresh run comes to, the pcs have to be of the whole
run so far, as a ring of every pc keeps them (`pcCapacity := 0`); of a ring that let some go, it is short by what it dropped before `index`.
It is `none` if `index` is past the end. -/
def ofTrace (pcs : List Nat) (index : Nat) (criteria : List Criterion) (thread : Option ThreadId := none) : Option Criteria :=
  match pcs[index]? with
  | none => none
  | some pc => some { pc, thread, hit := ((pcs.take (index + 1)).filter (· == pc)).length, criteria }

end Bap.Analysis.Verdict
