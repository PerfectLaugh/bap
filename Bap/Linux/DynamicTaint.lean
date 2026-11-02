import Bap.Analysis.DynamicTaint
import Bap.Analysis.Journal
import Bap.Linux.Machine

/-! What a Linux machine does and where its bytes come from, in the terms of what it runs: what a system call brings in is a source by what it is, a file
by its path, `/proc` too, and what a program sends to a file or a pipe goes through there. Both can be in a checkpoint, as models. -/

namespace Bap.Linux

open Bap.Analysis.DynamicTaint
open Bap.Analysis.Journal (Journal)

private def callName (call : Call) : String :=
  match (reprStr call).splitOn "." |>.getLast? with
  | some name => name
  | none => reprStr call

/-- Where memory went, what became of a descriptor and the like: nothing that a program finds out about the world by. -/
private def saysNothing : Call → Bool
  | .mmap | .mmap2 | .munmap | .mprotect | .madvise | .mremap | .brk | .succeeds | .close | .setThreadArea | .sigaltstack
  | .lseek | .llseek | .write | .pwrite | .writev | .fcntl | .dup | .dup2 | .dup3 | .umask | .pipe | .pipe2 => true
  | _ => false

/-- What was opened, by open file, as what it was opened as. A path says the same of most, and nothing of what `/proc` makes. -/
abbrev Opened := IO.Ref (Std.HashMap Nat String)

/-- What a descriptor reads from. -/
private def pathOf (machine : Machine) (opened : Opened) (group fd : Nat) : IO (Option String) := do
  let kernel ← machine.kernel.get
  match kernel.openFileOf group fd with
  | .error _ => pure none
  | .ok (id, file) =>
    if kernel.pipeOf group fd |>.isSome then return some s!"pipe {file.inode}"
    pure (((← opened.get).get? id).orElse fun _ => (kernel.paths.toList.find? (·.2 == file.inode)).map (·.1))

private def noteOpened (machine : Machine) (opened : Opened) (number : Nat) (args : List Nat) (result : Option Nat) : IO Unit := do
  -- The second argument of `openat`, and the first of `open`.
  let address := match machine.architecture.call number with
    | some .openat => some (args.getD 1 0)
    | some .open_ => some (args.getD 0 0)
    | _ => none
  match address, result with
  | some address, some fd =>
    if fd < 2 ^ 32 then
      if let .ok bytes := ← (Bap.Emu.peek machine.emu address 256).toBaseIO then
        let name := bytes.extract 0 ((bytes.data.findIdx? (· == 0)).getD bytes.size)
        let group := (← Bap.Emu.currentTask machine.emu).group
        if let .ok (id, _) := (← machine.kernel.get).openFileOf group fd then
          opened.modify (·.insert id (String.fromUTF8? name |>.getD ""))
  | _, _ => pure ()

/-- What a call is, with what it reads from if that means something. -/
private def callLabel (machine : Machine) (opened : Opened) (number : Nat) (args : List Nat) : IO String := do
  let group := (← Bap.Emu.currentTask machine.emu).group
  match machine.architecture.call number with
  | none => pure s!"syscall {number}"
  | some call =>
    match call with
    | .read | .readv | .pread | .write | .writev | .pwrite =>
      let path ← pathOf machine opened group (args.getD 0 0)
      pure s!"{callName call} {path.getD s!"fd {args.getD 0 0}"}"
    | _ => pure (callName call)

/-- Where a call is a read from what keeps tags, what that is and where it reads from, which is what has been read of a pipe. -/
private def readBacking (machine : Machine) (number : Nat) (args : List Nat) : IO (Option (Nat × Nat × Bool)) := do
  let group := (← Bap.Emu.currentTask machine.emu).group
  let kernel ← machine.kernel.get
  let offset := match machine.architecture.call number with
    | some .pread =>
      if machine.architecture.bits == 64 then some (args.getD 3 0)
      else
        let base := machine.architecture.pairBase
        let (low, high) := if machine.architecture.big then (args.getD (base + 1) 0, args.getD base 0) else (args.getD base 0, args.getD (base + 1) 0)
        some (high * 2 ^ 32 + low)
    | some .read | some .readv => none
    | _ => some 0
  match machine.architecture.call number with
  | some .read | some .readv | some .pread =>
    match kernel.openFileOf group (args.getD 0 0) with
    | .error _ => pure none
    | .ok (_, file) =>
      match kernel.inodes.get? file.inode with
      | some { content := .pipe _ _ consumed, .. } => pure (some (Kernel.fileSpace + file.inode, consumed, true))
      | some { content := .file _, .. } => pure (some (Kernel.fileSpace + file.inode, offset.getD file.offset, false))
      | _ => pure none
  | _ => pure none

/-- What a call is about to send somewhere that keeps tags. -/
private def callSends (machine : Machine) (opened : Opened) (number : Nat) (args : List Nat) : IO (List Send) := do
  let group := (← Bap.Emu.currentTask machine.emu).group
  let kernel ← machine.kernel.get
  let architecture := machine.architecture
  let some call := architecture.call number | return []
  let fd := args.getD 0 0
  let target : Option (Nat × Nat) ← match kernel.openFileOf group fd with
    | .error _ => pure none
    | .ok (_, file) =>
      match kernel.inodes.get? file.inode with
      | some { content := .pipe buffer head consumed, .. } => pure (some (file.inode, consumed + (buffer.size - head)))
      | some { content := .file data, .. } =>
        -- `O_APPEND` writes at the end.
        pure (some (file.inode, if file.flags &&& 0x400 != 0 then data.size else file.offset))
      | _ => pure none
  let some (inode, offset) := target | return []
  let label := s!"{callName call} {(← pathOf machine opened group fd).getD s!"fd {fd}"}"
  let send (address size at_ : Nat) : Send := { address, size, space := Kernel.fileSpace + inode, offset := at_, label }
  match call with
  | .write => pure [send (args.getD 1 0) (args.getD 2 0) offset]
  | .pwrite =>
    let at_ := if architecture.bits == 64 then args.getD 3 0
      else
        let base := architecture.pairBase
        let (low, high) := if architecture.big then (args.getD (base + 1) 0, args.getD base 0) else (args.getD base 0, args.getD (base + 1) 0)
        high * 2 ^ 32 + low
    pure [send (args.getD 1 0) (args.getD 2 0) at_]
  | .writev =>
    let word := architecture.bits / 8
    let count := args.getD 2 0
    let vector := args.getD 1 0
    let readWord (address : Nat) : IO Nat := do
      let bytes ← Bap.Emu.peek machine.emu address word
      let ordered := if architecture.big then bytes.toList else bytes.toList.reverse
      pure (ordered.foldl (fun value byte => value * 256 + byte.toNat) 0)
    let mut sends : List Send := []
    let mut at_ := offset
    for index in List.range count do
      let base ← readWord (vector + 2 * word * index)
      let size ← readWord (vector + 2 * word * index + word)
      sends := sends ++ [send base size at_]
      at_ := at_ + size
    pure sends
  | _ => pure []

/-- A `Tracker` of a machine, with what it knows of what was opened. What a checkpoint has is both. -/
private def attachTracker (machine : Machine) (config : Config) : IO (Tracker × Opened) := do
  let opened : Opened ← IO.mkRef {}
  let emu := machine.emu
  let started : IO.Ref (Option Tracker) ← IO.mkRef none
  let describe (number : Nat) (args : List Nat) : IO (Option (String × Option Nat)) := do
    if ← Bap.Emu.bookkeepingCall emu number then return none
    if let some call := machine.architecture.call number then
      if saysNothing call then return none
    let label ← callLabel machine opened number args
    pure (some (label, (← readBacking machine number args).map (·.2.1)))
  let backing (number : Nat) (args : List Nat) : IO (Option (Nat × Nat)) := do
    pure ((← readBacking machine number args).map fun (space, offset, _) => (space, offset))
  let called (number : Nat) (args : List Nat) (result : Option Nat) : IO Unit := do
    noteOpened machine opened number args result
    -- A private mapping of a file has a copy of what that came from. A shared one has it there.
    let isMap := match machine.architecture.call number with
      | some .mmap | some .mmap2 => true
      | _ => false
    if isMap && args.getD 3 0 &&& machine.architecture.mapAnonymous == 0 then
      if let (some start, some tracker) := (result, ← started.get) then
        let group := (← Bap.Emu.currentTask emu).group
        if let some mapping := ((← machine.kernel.get).process group).mappings.find? (·.start == start) then
          if !mapping.shared then
            tracker.mapped start mapping.size (Kernel.fileSpace + mapping.inode) mapping.offset none
  let tracker ← Tracker.start emu { config with describe, backing, sends := callSends machine opened, called }
  started.set (some tracker)
  pure (tracker, opened)

private def putOpened (out : ByteArray) (opened : Std.HashMap Nat String) : ByteArray :=
  let sorted := opened.toList.toArray.qsort (fun left right => left.1 < right.1) |>.toList
  Wire.putList (fun out entry => Wire.putText (Wire.putNat out entry.1) entry.2) out sorted

private def taintState (tracker : Tracker) (opened : Opened) : ModelState where
  save := do pure (putOpened (← tracker.save) (← opened.get))
  load := fun data => do
    let at_ ← tracker.load data
    let (entries, _) ← IO.ofExcept (Wire.getList (fun data at_ => do
      let (id, at_) ← Wire.getNat data at_
      let (path, at_) ← Wire.getText data at_
      .ok ((id, path), at_)) data at_)
    opened.set (entries.foldl (fun map entry => map.insert entry.1 entry.2) {})

/-- What a checkpoint knows a `Tracker` by. -/
def taintModelId : String := "bap.taint"

/-- A `Tracker` that goes on from a checkpoint, for `Machine.ofCheckpoint` or `start`, which leaves it in `cell`. -/
def taintModel (cell : IO.Ref (Option Tracker)) (config : Config := {}) : RuntimeModel where
  id := taintModelId
  attach := fun machine => do
    let (tracker, opened) ← attachTracker machine config
    cell.set (some tracker)
    pure (taintState tracker opened)

/-- Starts following where the bytes of a machine come from, from here on: what a system call returns or leaves in memory, other than what says nothing about the
world such as `mmap` and `futex`, what JNI gives, what `Machine.write` writes, and what the host gives `Machine.call`. What a program sends to a file or a pipe has what it came
from when it is read there. What was opened from before this was called goes by its path if it has one. It is in a checkpoint from then on, which then needs `taintModel` to go on from. -/
def Machine.track (machine : Machine) (config : Config := {}) : IO Tracker := do
  let (tracker, opened) ← attachTracker machine config
  machine.models.modify (· ++ [{ id := taintModelId, version := 1, state := taintState tracker opened }])
  pure tracker

/-! ### What a machine did -/

private def attachJournal (machine : Machine) (config : Bap.Analysis.Journal.Config) : IO (Journal × Opened) := do
  let opened : Opened ← IO.mkRef {}
  let journal ← Journal.start machine.emu { config with describe := callLabel machine opened }
  -- What it was opened as, which it needs to say what a read is of.
  let args : IO.Ref (Nat × List Nat) ← IO.mkRef (0, [])
  machine.emu.syscallStarts.modify ((fun number given => args.set (number, given)) :: ·)
  machine.emu.syscallEnds.modify ((fun result => do
    let (number, given) ← args.get
    noteOpened machine opened number given result) :: ·)
  pure (journal, opened)

private def journalState (journal : Journal) (opened : Opened) : ModelState where
  save := do pure (putOpened (← journal.save) (← opened.get))
  load := fun data => do
    let at_ ← journal.load data
    let (entries, _) ← IO.ofExcept (Wire.getList (fun data at_ => do
      let (id, at_) ← Wire.getNat data at_
      let (path, at_) ← Wire.getText data at_
      .ok ((id, path), at_)) data at_)
    opened.set (entries.foldl (fun map entry => map.insert entry.1 entry.2) {})

/-- What a checkpoint knows a `Journal` by. -/
def journalModelId : String := "bap.journal"

/-- A `Journal` that goes on from a checkpoint, which it leaves in `cell`. -/
def journalModel (cell : IO.Ref (Option Journal)) (config : Bap.Analysis.Journal.Config := {}) : RuntimeModel where
  id := journalModelId
  attach := fun machine => do
    let (journal, opened) ← attachJournal machine config
    cell.set (some journal)
    pure (journalState journal opened)

/-- Starts keeping what a machine does, from here on: each instruction of each thread, each call and return, and each system call and each call of JNI, with what it
answered and left. It is in a checkpoint from then on, which then needs `journalModel` to go on from. -/
def Machine.journal (machine : Machine) (config : Bap.Analysis.Journal.Config := {}) : IO Journal := do
  let (journal, opened) ← attachJournal machine config
  machine.models.modify (· ++ [{ id := journalModelId, version := 1, state := journalState journal opened }])
  pure journal

/-- Why a run first came to an address, as far as it can be said: how it got there, what had called what, and the last branch before that on anything marked, by way of
what that came from. Both have to have started together, as this goes by how many instructions each has seen. -/
structure WhyEntered where
  entry : Bap.Analysis.Journal.Journal.Entry
  branch : Option Node
  explanation : Option Tracker.Explanation

def whyEntered (journal : Journal) (tracker : Tracker) (address : Nat) : IO (Option WhyEntered) := do
  let some entry ← journal.firstEntry address | return none
  let ahead := (← tracker.insn.get) - (← journal.seq.get)
  let moment := entry.instruction.seq + ahead
  let branch := (← tracker.nodes.get).toList.reverse.find? fun node =>
    node.thread == entry.instruction.thread && node.insn < moment && node.kind matches .branch _
  let explanation ← match branch with
    | some node => pure (some (← tracker.explainTag (nodeTag node.id 0)))
    | none => pure none
  pure (some { entry, branch, explanation })

/-- Where two runs part, what they were given differently first, and the first file that they left different, by its path. -/
structure RunDifference where
  run : Bap.Analysis.Journal.Journal.Difference
  file : Option String

/-- Compares two runs that have journals. A file that only one of them has counts as different. -/
def compareRuns (left right : Machine) (leftJournal rightJournal : Journal) : IO RunDifference := do
  let run := Bap.Analysis.Journal.Journal.compare (← leftJournal.toRecord) (← rightJournal.toRecord)
  let leftKernel ← left.kernel.get
  let rightKernel ← right.kernel.get
  let bytesOf (kernel : Kernel) (path : String) : Option ByteArray := do
    let inode ← kernel.paths.get? path >>= kernel.inodes.get?
    match inode.content with
    | .file data => some data
    | _ => none
  let paths := (leftKernel.paths.toList.map (·.1) ++ rightKernel.paths.toList.map (·.1)).eraseDups.toArray.qsort (· < ·) |>.toList
  pure { run, file := paths.find? fun path => bytesOf leftKernel path != bytesOf rightKernel path }

end Bap.Linux
