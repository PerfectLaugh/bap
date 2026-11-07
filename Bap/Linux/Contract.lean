import Bap.Analysis.Cff
import Bap.Linux.Machine

/-! What a handler of a flattened machine does, as a contract: from the state it was given to the state it leaves, the memory it changes,
and what it asks of the kernel and of the host on the way, but for its own frame below the stack pointer, which is gone when it is done. `capture` runs one round of a handler from where the machine is, at the
dispatcher, and puts the machine back as it was. `verify` checks something that is to do the same faster, such as a handler written on the
host, against the handler as it runs: both start from the same machine, and what each leaves is compared. Registers aren't in a contract, as
a handler's are its own until it gives its state back. -/

namespace Bap.Analysis.Contract

open Bap.Emu (ThreadId)
open Bap.Linux (Machine)

structure Contract where
  state : Nat
  next : Option Nat
  /-- What it changed, by where, as what it is after. -/
  writes : List (Nat × ByteArray)
  /-- What it asked, of the kernel and of the host, with what was answered. -/
  services : List (String × Option Nat)
  instructions : Nat
  /-- The status that the program ended with, where the round ended it rather than coming back to the dispatcher, which is the
  boundary that a replacement keeps too; there is no next state then. -/
  exit : Option Nat := none
  deriving DecidableEq, Repr

/-- What hears what a round does, which is attached once to a machine: it hears only while it is asked to, and only of one thread. -/
structure Recorder where
  machine : Machine
  active : IO.Ref (Option ThreadId)
  written : IO.Ref (Std.HashSet Nat)
  services : IO.Ref (Array (String × Option Nat))
  calling : IO.Ref (List String)

private def callName (machine : Machine) (number : Nat) : String :=
  match machine.architecture.call number with
  | some call => ((reprStr call).splitOn ".").getLast?.getD (reprStr call)
  | none => s!"syscall {number}"

def Recorder.attach (machine : Machine) : IO Recorder := do
  let recorder : Recorder := { machine, active := ← IO.mkRef none, written := ← IO.mkRef {}, services := ← IO.mkRef #[], calling := ← IO.mkRef [] }
  let emu := machine.emu
  let mine : IO Bool := do
    match ← recorder.active.get with
    | some thread => pure ((← Bap.Emu.thread emu) == thread)
    | none => pure false
  emu.memoryChanged.modify ((fun address size _ => do
    if ← mine then
      recorder.written.modify fun written => (List.range size).foldl (fun written offset => written.insert (address + offset)) written) :: ·)
  emu.syscallStarts.modify ((fun number _ => do if ← mine then recorder.calling.modify (callName machine number :: ·)) :: ·)
  emu.syscallEnds.modify ((fun result => do
    if ← mine then
      match ← recorder.calling.get with
      | label :: rest =>
        recorder.calling.set rest
        recorder.services.modify (·.push (label, result))
      | [] => pure ()) :: ·)
  -- What the host writes is what it does to memory, and not something asked of it.
  emu.hostStarts.modify ((fun label => do
    if ← mine then recorder.calling.modify ((if label.startsWith "Machine.write" then "" else label) :: ·)) :: ·)
  emu.hostEnds.modify ((fun _ => do
    if ← mine then
      match ← recorder.calling.get with
      | label :: rest =>
        recorder.calling.set rest
        unless label.isEmpty do recorder.services.modify (·.push (label, none))
      | [] => pure ()) :: ·)
  pure recorder

/-- Addresses as runs in a row, each with how many it has: a run goes on while the next address is the one after it. -/
def runsOf : List Nat → List (Nat × Nat)
  | [] => []
  | address :: rest =>
    match runsOf rest with
    | (start, count) :: more => if address + 1 == start then (address, count + 1) :: more else (address, 1) :: (start, count) :: more
    | [] => [(address, 1)]

/-- The addresses that changed, by what they were before and are after, as runs of what they are after. -/
def changes (before after : Nat → Option UInt8) (addresses : List Nat) : List (Nat × ByteArray) :=
  -- In order, each once, which after sorting is each that isn't the one before it.
  let sorted := (addresses.toArray.qsort (· < ·)).toList
  let unique := (sorted.zip (none :: sorted.map some)).filterMap fun (address, previous) => if previous == some address then none else some address
  let changed := unique.filter fun address => before address != after address
  (runsOf changed).map fun (start, count) => (start, ByteArray.mk ((List.range count).map fun offset => (after (start + offset)).getD 0).toArray)

private def byteAt (machine : Machine) (address : Nat) : IO (Option UInt8) := do
  match ← (Bap.Emu.peek machine.emu address 1).toBaseIO with
  | .ok bytes => pure bytes[0]?
  | .error _ => pure none

/-- The status that the process of a thread ended with, if it has. -/
private def exitOf (machine : Machine) (thread : ThreadId) : IO (Option Nat) := do
  let table ← machine.emu.taskTable.get
  let group := ((table.tasks.find? (·.tid == thread)).map (·.group)).getD thread
  pure ((table.tasks.find? (·.tid == group)).bind (·.status))

/-- What happens from here while `act` runs, for the thread that runs, which is then put back as it was. -/
private def observe (recorder : Recorder) (profile : Cff.Profile) (act : IO Nat) : IO Contract := do
  let machine := recorder.machine
  let emu := machine.emu
  if (← emu.pc.get) != profile.dispatcher then
    throw <| IO.userError "a contract starts at the dispatcher, where a round does"
  let thread ← Bap.Emu.thread emu
  let saved ← machine.save
  let state := profile.decode (← Cff.readState emu profile.state)
  recorder.written.set {}
  recorder.services.set #[]
  recorder.calling.set []
  let hook ← Bap.Emu.onWrite emu (0, 2 ^ (← Bap.Emu.wordWidth emu) - 1) fun current address size _ => do
    if (← Bap.Emu.thread current) == thread then
      recorder.written.modify fun written => (List.range size).foldl (fun written offset => written.insert (address + offset)) written
  recorder.active.set (some thread)
  let instructions ← try act finally
    recorder.active.set none
    Bap.Emu.removeHook emu hook
  let exit ← exitOf machine thread
  let next ← if exit.isSome then pure none else pure (some (profile.decode (← Cff.readState emu profile.state)))
  -- What is below the stack pointer when the round is over is no one's any more, as a handler's frame is.
  let width ← Bap.Emu.wordWidth emu
  let stack ← match Value.asBits (← Bap.Emu.reg emu ⟨(Bap.Emu.threadRegisters emu.config.syscallAbi).1, .imm width, 0, false⟩) with
    | .ok bits => pure bits.2.toNat
    | .error _ => pure 0
  let addresses := (← recorder.written.get).toList.filter fun address => !(address < stack && address + 8 * 1024 * 1024 ≥ stack)
  let after ← addresses.foldlM (init := ({} : Std.HashMap Nat (Option UInt8))) fun table address => do
    pure (table.insert address (← byteAt machine address))
  let services := (← recorder.services.get).toList
  machine.restore saved (label := "Contract")
  let before ← addresses.foldlM (init := ({} : Std.HashMap Nat (Option UInt8))) fun table address => do
    pure (table.insert address (← byteAt machine address))
  let look (table : Std.HashMap Nat (Option UInt8)) (address : Nat) : Option UInt8 := (table.get? address).join
  pure { state, next, writes := changes (look before) (look after) addresses, services, instructions, exit }

/-- One round of the handler of the state that the machine is in, which has to be at the dispatcher: what it did by the time its thread came
back to the dispatcher, or the program ended. The machine is then as it was. -/
def capture (recorder : Recorder) (profile : Cff.Profile) (fuel : Nat := 100000000) : IO Contract :=
  observe recorder profile do
    let machine := recorder.machine
    let emu := machine.emu
    let thread ← Bap.Emu.thread emu
    let started ← emu.executed.get
    -- A thread that a breakpoint stopped there goes on, and off the dispatcher first, as it is there.
    Bap.Emu.resumeThread emu thread
    let _ ← machine.run (fuel := 1) fun _ => pure ()
    let breakpoint ← Bap.Emu.addBreakpoint emu profile.dispatcher
    try
      let mut left := fuel
      while left > 0 do
        match ← machine.run (fuel := left) fun _ => pure () with
        | .stopped id =>
          if (← Bap.Emu.thread emu) == thread && (← emu.pc.get) == profile.dispatcher then
            return (← emu.executed.get) - started
          Bap.Emu.resumeThread emu id
          left := left - 1
        | .finished _ => return (← emu.executed.get) - started
        | other => throw <| IO.userError s!"the round never came back to the dispatcher, and ended as {repr other}"
      throw <| IO.userError "the round never came back to the dispatcher"
    finally
      Bap.Emu.removeHook emu breakpoint

/-- What something that is to do what a round does did, from the same machine: it changes the machine as it likes, by `Machine.write` and
the like, and leaves the next state where the state is. Its instructions are those of the guest that it ran, none where it is all of the
host. -/
def captureReplacement (recorder : Recorder) (profile : Cff.Profile) (replacement : Machine → IO Unit) : IO Contract :=
  observe recorder profile do
    let started ← recorder.machine.emu.executed.get
    replacement recorder.machine
    pure ((← recorder.machine.emu.executed.get) - started)

/-- How what two asked differ: each that one asked and the other didn't, as many times as it is short of, and of what both asked in the
same order, each that was answered otherwise. -/
def serviceDifferences (original replacement : List (String × Option Nat)) : List String :=
  let names (services : List (String × Option Nat)) := services.map (·.1)
  let removed := (names replacement).foldl (fun left name => left.erase name) (names original)
  let added := (names original).foldl (fun left name => left.erase name) (names replacement)
  let answers := if names original == names replacement then
      (original.zip replacement).filterMap fun ((name, answer), (_, other)) =>
        if answer != other then some s!"{name} answers it {answer} and the replacement {other}" else none
    else if removed.isEmpty && added.isEmpty then [s!"it asks {names original} in that order and not {names replacement}"]
    else []
  removed.map (s!"it asks {·}, which the replacement doesn't") ++ added.map (s!"the replacement asks {·}, which the handler doesn't") ++ answers

structure Verification where
  original : Contract
  replacement : Contract
  /-- How they differ, which is nothing when the replacement does what the handler does. -/
  differences : List String
  deriving Repr

/-- Whether `replacement` does what the handler of the state that the machine is in does, from here: the same next state, the same
memory changed to the same, the same asked of the kernel and the host, in the same order and answered the same, so that a service
that is gone, one that is new and one asked otherwise are each a difference, and the program ended the same where the handler ended it. How many instructions each ran is in its contract and isn't
one: the replacement is there to run fewer, or none of the guest. The machine is as it was afterwards. -/
def verify (recorder : Recorder) (profile : Cff.Profile) (replacement : Machine → IO Unit) : IO Verification := do
  let original ← capture recorder profile
  let replaced ← captureReplacement recorder profile replacement
  let mut differences : List String := []
  if original.exit != replaced.exit then
    differences := differences ++ [match original.exit, replaced.exit with
      | some status, some other => s!"it ends the program with {status} and the replacement with {other}"
      | some status, none => s!"it ends the program with {status}, which the replacement doesn't"
      | none, _ => s!"the replacement ends the program, which the handler doesn't"]
  if original.next != replaced.next then
    differences := differences ++ [s!"the next state is {original.next} and not {replaced.next}"]
  for (address, bytes) in original.writes do
    match replaced.writes.lookup address with
    | some other => if other != bytes then differences := differences ++ [s!"at {address} it leaves {bytes.toList} and not {other.toList}"]
    | none => differences := differences ++ [s!"at {address} it leaves {bytes.toList}, which the replacement doesn't"]
  for (address, bytes) in replaced.writes do
    if (original.writes.lookup address).isNone then
      differences := differences ++ [s!"the replacement leaves {bytes.toList} at {address}, which the handler doesn't"]
  differences := differences ++ serviceDifferences original.services replaced.services
  pure { original, replacement := replaced, differences }

end Bap.Analysis.Contract
