import Bap.Analysis.DynamicTaint
import Bap.Linux.Machine

/-! Dynamic taint of a Linux machine: what a system call brings in is a source by what it is, and a file by its path, `/proc` too. -/

namespace Bap.Linux

open Bap.Analysis.DynamicTaint

private def callName (call : Call) : String :=
  match (reprStr call).splitOn "." |>.getLast? with
  | some name => name
  | none => reprStr call

/-- Where memory went, what became of a descriptor and the like: nothing that a program finds out about the world by. -/
private def saysNothing : Call → Bool
  | .mmap | .mmap2 | .munmap | .mprotect | .madvise | .mremap | .brk | .succeeds | .close | .setThreadArea | .sigaltstack
  | .lseek | .llseek | .write | .pwrite | .writev | .fcntl | .dup | .dup2 | .dup3 | .umask => true
  | _ => false

/-- What a descriptor reads from: what it was opened as, or else whichever path has its inode. -/
private def pathOf (machine : Machine) (opened : Std.HashMap Nat String) (group fd : Nat) : IO (Option String × Option Nat) := do
  let kernel ← machine.kernel.get
  match kernel.openFileOf group fd with
  | .error _ => pure (none, none)
  | .ok (id, file) =>
    let path := (opened.get? id).orElse fun _ =>
      (kernel.paths.toList.find? (·.2 == file.inode)).map (·.1)
    pure (path, some file.offset)

/-- Starts following where the bytes of a machine come from, from here on: what a system call returns or leaves in memory, other than what
says nothing about the world such as `mmap` and `futex`, and what JNI gives. What was opened from before this was called goes by its path if it has one. -/
def Machine.track (machine : Machine) (config : Config := {}) : IO Tracker := do
  let opened ← IO.mkRef ({} : Std.HashMap Nat String)
  let emu := machine.emu
  let describe (number : Nat) (args : List Nat) : IO (Option (String × Option Nat)) := do
    if ← Emu.bookkeepingCall emu number then return none
    let group := (← Emu.currentTask emu).group
    match machine.architecture.call number with
    | none => pure (some (s!"syscall {number}", none))
    | some call =>
      if saysNothing call then return none
      let name := callName call
      match call with
      | .read | .readv =>
        let (path, offset) ← pathOf machine (← opened.get) group (args.getD 0 0)
        pure (some (s!"{name} {path.getD s!"fd {args.getD 0 0}"}", offset))
      | .pread =>
        let (path, _) ← pathOf machine (← opened.get) group (args.getD 0 0)
        pure (some (s!"{name} {path.getD s!"fd {args.getD 0 0}"}", some (args.getD 3 0)))
      | _ => pure (some (name, none))
  let called (number : Nat) (args : List Nat) (result : Option Nat) : IO Unit := do
    -- What was opened: the second argument of `openat`, and the first of `open`.
    let address := match machine.architecture.call number with
      | some .openat => some (args.getD 1 0)
      | some .open_ => some (args.getD 0 0)
      | _ => none
    match address, result with
    | some address, some fd =>
      if fd < 2 ^ 32 then
        let bytes ← (Machine.read machine address 256).toBaseIO
        if let .ok bytes := bytes then
          let name := bytes.extract 0 ((bytes.data.findIdx? (· == 0)).getD bytes.size)
          let group := (← Emu.currentTask emu).group
          if let .ok (id, _) := (← machine.kernel.get).openFileOf group fd then
            opened.modify (·.insert id (String.fromUTF8? name |>.getD ""))
    | _, _ => pure ()
  Tracker.start emu { config with describe, called }

end Bap.Linux
