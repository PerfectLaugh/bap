import Bap.Linux.Poll
import Bap.Linux.Identity

/-! # Pseudo-terminals

`/dev/ptmx` makes a pseudo-terminal: its master, which the descriptor that it gives has, and its slave, `/dev/pts/N`, which
`unlockpt` lets be opened. What the master writes goes through the line discipline to what the slave reads, and what the slave writes
goes to what the master reads.

The line discipline has what Linux has of the flags that programs set: `ICRNL`, `INLCR` and `IGNCR` of what comes in, `OPOST` and
`ONLCR` of what goes out, `ECHO` with `ECHOE` and `ECHOCTL`, canonical lines with `VERASE`, `VKILL`, `VWERASE`, `VEOF`, `VEOL` and
`VEOL2`, and of `ISIG`, `VINTR`, `VQUIT` and `VSUSP`, which send SIGINT, SIGQUIT and SIGTSTP to the foreground process group. A raw
read waits for `VMIN` bytes, or as many as it asks for, but of `VTIME` no longer than that after the last came in; of `VMIN` of 0 it
waits as long as `VTIME` for a byte, and of `VTIME` of 0 too, or of `O_NONBLOCK`, it takes what there is.

A session leader with no terminal takes as its controlling terminal the slave that it opens, without `O_NOCTTY`, or `TIOCSCTTY`;
`/dev/tty` is that terminal. A process that isn't in the foreground of its controlling terminal and reads it is sent SIGTTIN, and of
`TOSTOP` one that writes is sent SIGTTOU, or the call gives `EIO` if that signal doesn't come to it. Once nothing has the master open, the
slave reads nothing more and can't be written; once nothing has the slave open, after it was, the master can't be read. Either is hung
up, then, as `poll` has it.

The ioctls are those of the layout of `termios` that x86, ARM, AArch64 and RISC-V have; MIPS and PowerPC, whose numbers and layouts
differ, have none of them, and their programs see no terminal. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Tty

private def control (byte : Nat) : Bool := byte < 32 || byte == 127

/-- What goes out of a terminal: of `OPOST` and `ONLCR`, a newline as a carriage return and a newline. -/
def post (terminal : Terminal) (bytes : ByteArray) : ByteArray :=
  if terminal.oflag &&& 1 != 0 && terminal.oflag &&& 4 != 0 then
    bytes.foldl (fun out byte => if byte == 10 then (out.push 13).push 10 else out.push byte) ByteArray.empty
  else bytes

/-- How a byte that comes in is shown, of `ECHOCTL`: a control as `^` and its letter, but for a tab and a newline. -/
private def shown (terminal : Terminal) (byte : Nat) : ByteArray :=
  if control byte && byte != 9 && byte != 10 && terminal.lflag &&& 0x200 != 0 then
    ByteArray.mk #[94, (byte ^^^ 0x40).toUInt8]
  else ByteArray.mk #[byte.toUInt8]

/-- What the master writes, through the line discipline: the terminal after, and the signals that it sends to the foreground, as 0 of
SIGINT, 1 of SIGQUIT and 2 of SIGTSTP. -/
def fromMaster (terminal : Terminal) (bytes : ByteArray) : Terminal × List Nat := Id.run do
  let mut terminal := terminal
  let mut signals := []
  let cc (index : Nat) : Nat := terminal.cc.getD index 0
  let echoing := terminal.lflag &&& 8 != 0
  for raw in bytes.toList do
    let mut byte := raw.toNat
    if terminal.iflag &&& 0x80 != 0 && byte == 13 then continue
    if terminal.iflag &&& 0x100 != 0 && byte == 13 then byte := 10
    else if terminal.iflag &&& 0x40 != 0 && byte == 10 then byte := 13
    let echo (terminal : Terminal) (out : ByteArray) : Terminal :=
      if echoing then { terminal with output := terminal.output ++ post terminal out } else terminal
    -- ISIG: what is in the line is gone, but of NOFLSH, and the signal goes to the foreground.
    if terminal.lflag &&& 1 != 0 && byte != 0 then
      let which := if byte == cc 0 then some 0 else if byte == cc 1 then some 1 else if byte == cc 10 then some 2 else none
      if let some which := which then
        terminal := echo terminal (shown terminal byte)
        if terminal.lflag &&& 0x80 == 0 then terminal := { terminal with input := [], line := ByteArray.empty }
        signals := signals ++ [which]
        continue
    if terminal.lflag &&& 2 != 0 then
      if byte == cc 2 && byte != 0 then
        if terminal.line.size > 0 then
          terminal := { terminal with line := terminal.line.extract 0 (terminal.line.size - 1) }
          if terminal.lflag &&& 0x10 != 0 then terminal := echo terminal (ByteArray.mk #[8, 32, 8])
        continue
      if byte == cc 3 && byte != 0 then
        terminal := { terminal with line := ByteArray.empty }
        continue
      if byte == cc 14 && byte != 0 && terminal.lflag &&& 0x8000 != 0 then
        let kept := terminal.line.toList.reverse.dropWhile (· == 32) |>.dropWhile (· != 32) |>.reverse
        terminal := { terminal with line := ByteArray.mk kept.toArray }
        continue
      if byte == cc 4 && byte != 0 then
        terminal := if terminal.line.size == 0 then { terminal with ends := terminal.ends + 1 }
          else { terminal with input := terminal.input ++ [terminal.line], line := ByteArray.empty }
        continue
      terminal := { echo terminal (shown terminal byte) with line := terminal.line.push byte.toUInt8 }
      if byte == 10 || (byte == cc 11 && byte != 0) || (byte == cc 16 && byte != 0) then
        terminal := { terminal with input := terminal.input ++ [terminal.line], line := ByteArray.empty }
    else
      terminal := { echo terminal (shown terminal byte) with input := terminal.input ++ [ByteArray.mk #[byte.toUInt8]] }
  pure (terminal, signals)

/-- What the slave reads, of `count` bytes at most: a line at a time, or nothing of an end of file, in canonical mode, and otherwise
what there is, once that is `least` bytes. None if it has to wait. -/
def toSlave (terminal : Terminal) (count least : Nat) : Option (Terminal × ByteArray) :=
  if terminal.lflag &&& 2 != 0 then
    match terminal.input with
    | first :: rest =>
      let taken := first.extract 0 count
      let left := first.extract count first.size
      some ({ terminal with input := if left.size == 0 then rest else left :: rest }, taken)
    | [] => if terminal.ends > 0 then some ({ terminal with ends := terminal.ends - 1 }, ByteArray.empty) else none
  else
    let all := terminal.input.foldl (· ++ ·) ByteArray.empty
    if all.size < least then none
    else
      let left := all.extract count all.size
      some ({ terminal with input := if left.size == 0 then [] else [left] }, all.extract 0 count)

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- The terminal of an inode of a pseudo-terminal, with the inode of its master. -/
def terminalOf (kernel : Kernel) (number : Nat) : Option (Nat × Terminal) :=
  match kernel.inodes.get? number with
  | some { content := .ptyMaster terminal, .. } => some (number, terminal)
  | some { content := .ptySlave master, .. } =>
    match kernel.inodes.get? master with
    | some { content := .ptyMaster terminal, .. } => some (master, terminal)
    | _ => none
  | _ => none

/-- Opens `/dev/ptmx`, which makes a pseudo-terminal, and `/dev/tty`, which is the controlling terminal, of the flags of the kernel. -/
def openDevice (poller : Poller) (emu : Emu) (path : String) (flags : Nat) : IO (Option SyscallAction) := do
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let succeed (value : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  if path == "/dev/ptmx" then
    let used := kernel.inodes.toList.filterMap fun (_, inode) => match inode.content with
      | .ptyMaster terminal => some terminal.index
      | _ => none
    let index := (List.range (used.length + 1)).find? (!used.contains ·) |>.getD used.length
    let (kernel, fd) := kernel.addObject group (.ptyMaster { index }) (flags &&& (Kernel.oCloexec ||| Kernel.oNonblock))
    let master := kernel.nextInode - 1
    let (kernel, _) := kernel.addDevice s!"/dev/pts/{index}" (.ptySlave master) 0o20620
    poller.kernel.set kernel
    succeed fd
  else if path == "/dev/tty" then
    match (kernel.process group).terminal with
    | none => pure (some (.returnValue (2 ^ 64 - 6)))
    | some number =>
      let openFile := kernel.nextOpenFile
      let kernel := { kernel with
        openFiles := kernel.openFiles.insert openFile { inode := number, flags := 2 ||| (flags &&& Kernel.oNonblock) }
        nextOpenFile := openFile + 1 }
      let (kernel, fd) := kernel.addDescriptor group openFile (flags &&& Kernel.oCloexec != 0)
      poller.kernel.set kernel
      succeed fd
  else pure none

/-- A slave was opened at `fd`: it may not be if it is locked, and a session leader that has no terminal takes it as its controlling
terminal, but of `O_NOCTTY`. Whatever else, if anything, the open gives. -/
def opened (poller : Poller) (emu : Emu) (fd flags : Nat) : IO (Option SyscallAction) := do
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let .ok (number, _, { content := .ptySlave master, .. }) := kernel.objectOf group fd | return none
  let some (_, terminal) := terminalOf kernel number | return none
  if terminal.locked then
    if let .ok closed := kernel.close group fd then poller.kernel.set closed
    return some (.returnValue (2 ^ 64 - 5))
  let leader := kernel.sidOf group == group
  let takes := flags &&& 0x100 == 0 && leader && (kernel.process group).terminal.isNone && terminal.session == 0
  let terminal := { terminal with opened := true, session := if takes then group else terminal.session
                                  foreground := if takes then kernel.pgidOf group else terminal.foreground }
  let kernel := kernel.setContent master (.ptyMaster terminal)
  poller.kernel.set (if takes then kernel.setProcess group { kernel.process group with terminal := some number } else kernel)
  pure none

/-- Of a process that isn't in the foreground of its controlling terminal: it is sent `signal`, and the call is made again once it goes
on. If the signal doesn't come to it, as it ignores or blocks it, a read (`reading`, of SIGTTIN) gives `EIO`, and anything else goes
ahead, as Linux's `__tty_check_change` has it. None if it is in the foreground, or this isn't its controlling terminal. -/
private def background (poller : Poller) (emu : Emu) (number : Nat) (terminal : Terminal) (signal : Nat) (reading : Bool) :
    IO (Option SyscallAction) := do
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  if (kernel.process group).terminal != some number || terminal.foreground == kernel.pgidOf group || terminal.foreground == 0 then
    return none
  if !(← poller.signals.comesTo (← thread emu) group signal) then return if reading then some (.returnValue (2 ^ 64 - 5)) else none
  for member in Identity.members kernel (← poller.live) (kernel.pgidOf group) do
    poller.signals.send emu none member ⟨signal, 0x80, .sent 0 0 0⟩
  pure (some (← Ptrace.again emu))

/-- What hangs up as the last of a master is closed, as Linux's `__tty_hangup` has it: the leader of the session of its terminal hears
SIGHUP and SIGCONT, and the terminal is of no session and its processes of no terminal from then on. Of each terminal that still has a
session but not a master that anything holds, which is after a `close` and as a process ends. -/
def hangUp (poller : Poller) (emu : Emu) : IO Unit := do
  let kernel ← poller.kernel.get
  let live ← poller.live
  let masters := kernel.inodes.fold (init := ([] : List (Nat × Terminal))) fun found number inode =>
    match inode.content with
    | .ptyMaster terminal => if terminal.session != 0 then (number, terminal) :: found else found
    | _ => found
  for (number, terminal) in masters do
    if kernel.inodeHeld live number then continue
    let leader := terminal.session
    let slave := kernel.paths.getD s!"/dev/pts/{terminal.index}" 0
    poller.kernel.modify fun kernel =>
      let kernel := kernel.setContent number (.ptyMaster { terminal with session := 0, foreground := 0 })
      live.foldl (init := kernel) fun kernel group =>
        if (kernel.process group).terminal == some slave then kernel.setProcess group { kernel.process group with terminal := none }
        else kernel
    if live.contains leader then
      let cont := if poller.architecture matches .mips .. then 25 else 18
      for signal in [1, cont] do
        poller.signals.send emu none leader ⟨signal, 0x80, .sent 0 0 0⟩

/-- `read`, `write` and the ioctls of a pseudo-terminal, if the descriptor is of one. -/
def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let mips := architecture matches .mips ..
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let .ok (number, opened_, inode) := kernel.objectOf group (arg 0) | return none
  let some (master, terminal) := terminalOf kernel number | return none
  let isMaster := match inode.content with
    | .ptyMaster _ => true
    | _ => false
  let live ← poller.live
  let now ← poller.timers.now
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let save (terminal : Terminal) : IO Unit := poller.kernel.modify (·.setContent master (.ptyMaster terminal))
  let nonblocking := opened_.flags &&& Kernel.oNonblock != 0
  let wait (due : Option Nat) : IO (Option SyscallAction) := do
    if nonblocking then fail 11 else pure (some (← poller.timers.waitUntil emu readySpace 0 due true))
  -- Whether the other end is open: the master always until it isn't, and the slave once it was opened. They go through each descriptor
  -- of each process, which is only when a read has nothing or of what is written.
  let slaveHeld : Unit → Bool := fun _ => kernel.inodeHeld live (kernel.paths.getD s!"/dev/pts/{terminal.index}" 0)
  let masterHeld : Unit → Bool := fun _ => kernel.inodeHeld live master
  let (tstp, ttin, ttou) := if mips then (24, 26, 27) else (20, 21, 22)
  try
    match call, isMaster with
    | .read, true =>
      if terminal.output.size == 0 then
        if terminal.opened && !slaveHeld () then return ← fail 5
        return ← wait none
      let taken := terminal.output.extract 0 (arg 2)
      write emu (arg 1) taken
      save { terminal with output := terminal.output.extract taken.size terminal.output.size }
      poller.wake emu
      succeed taken.size
    | .write, true =>
      let bytes ← read emu (arg 1) (arg 2)
      let (next, effects) := fromMaster terminal bytes
      save (if next.waiting > terminal.waiting then { next with arrived := now } else next)
      for effect in effects do
        let signal := match effect with
          | 0 => 2
          | 1 => 3
          | _ => tstp
        for member in Identity.members (← poller.kernel.get) live terminal.foreground do
          poller.signals.send emu none member ⟨signal, 0x80, .sent 0 0 0⟩
      poller.wake emu
      succeed bytes.size
    | .read, false =>
      if let some action ← background poller emu number terminal ttin true then return some action
      let tid ← thread emu
      let least := terminal.cc.getD 6 1
      let span := terminal.cc.getD 5 0 * 100000000
      -- Of `VTIME`, a raw read waits that long from when it began, of `VMIN` of 0, and otherwise from when the last byte came in, once
      -- one did.
      let due ← if terminal.lflag &&& 2 != 0 || span == 0 || nonblocking then pure none
        else if least == 0 then some <$> poller.timers.deadlineOf tid (pure (now + span))
        else pure (if terminal.waiting > 0 then some (terminal.arrived + span) else none)
      -- It takes `VMIN` bytes, or as many as it asks for, but one of `O_NONBLOCK` or `VMIN` of 0, and what there is of `VMIN` and `VTIME`
      -- of 0 or once its time is over.
      let wanted := if due.any (· ≤ now) || (least == 0 && span == 0) then 0
        else if least == 0 || nonblocking then 1 else min least (arg 2)
      match toSlave terminal (arg 2) wanted with
      | some (next, taken) =>
        poller.timers.finish tid
        write emu (arg 1) taken
        save next
        poller.wake emu
        succeed taken.size
      | none => if !masterHeld () then succeed 0 else wait due
    | .write, false =>
      if !masterHeld () then return ← fail 5
      if terminal.lflag &&& 0x100 != 0 then
        if let some action ← background poller emu number terminal ttou false then return some action
      let bytes ← read emu (arg 1) (arg 2)
      save { terminal with output := terminal.output ++ post terminal bytes }
      poller.wake emu
      succeed bytes.size
    | .ioctl, _ =>
      -- Of the layout of x86, ARM, AArch64 and RISC-V only.
      if mips || architecture matches .powerpc .. then return ← fail 25
      let request := arg 1 % 2 ^ 32
      let int (value : Nat) : IO (Option SyscallAction) := do
        write emu (arg 2) (numberBytes big 4 value)
        succeed
      let readInt : IO Nat := do pure (numberOf big (← read emu (arg 2) 4))
      let termios : ByteArray := numberBytes big 4 terminal.iflag ++ numberBytes big 4 terminal.oflag ++
        numberBytes big 4 terminal.cflag ++ numberBytes big 4 terminal.lflag ++ ByteArray.mk #[0] ++
        ByteArray.mk ((terminal.cc.take 19).map (·.toUInt8)).toArray
      let isSlave := !isMaster
      let slaveNumber := kernel.paths.getD s!"/dev/pts/{terminal.index}" 0
      match request with
      | 0x5401 =>
        write emu (arg 2) termios
        succeed
      | 0x5402 | 0x5403 | 0x5404 =>
        -- What sets a terminal, of the background, as of `TOSTOP` or not: SIGTTOU, as Linux's `tty_check_change` has it.
        if let some action ← background poller emu number terminal ttou false then return some action
        let bytes ← read emu (arg 2) 36
        let word (at_ : Nat) : Nat := numberOf big (bytes.extract at_ (at_ + 4))
        save { terminal with iflag := word 0, oflag := word 4, cflag := word 8, lflag := word 12
                             cc := (bytes.extract 17 36).toList.map (·.toNat)
                             input := if request == 0x5404 then [] else terminal.input }
        poller.wake emu
        succeed
      | 0x5413 =>
        write emu (arg 2) (numberBytes big 2 terminal.rows ++ numberBytes big 2 terminal.cols ++ numberBytes big 4 0)
        succeed
      | 0x5414 =>
        let bytes ← read emu (arg 2) 4
        let (rows, cols) := (numberOf big (bytes.extract 0 2), numberOf big (bytes.extract 2 4))
        save { terminal with rows, cols }
        -- SIGWINCH, to the foreground, if the size is another.
        if (rows, cols) != (terminal.rows, terminal.cols) then
          for member in Identity.members kernel live terminal.foreground do
            poller.signals.send emu none member ⟨28, 0x80, .sent 0 0 0⟩
        succeed
      | 0x540F => if terminal.session == 0 then fail 25 else int terminal.foreground
      | 0x5429 => if terminal.session == 0 then fail 25 else int terminal.session
      | 0x5410 =>
        if let some action ← background poller emu number terminal ttou false then return some action
        let pgid ← readInt
        if (kernel.process group).terminal != some slaveNumber then return ← fail 25
        if !live.any fun other => kernel.pgidOf other == pgid && kernel.sidOf other == terminal.session then return ← fail 1
        save { terminal with foreground := pgid }
        succeed
      | 0x540E =>
        -- TIOCSCTTY: of a session leader with no terminal, of a terminal of no session.
        if kernel.sidOf group != group || (kernel.process group).terminal.isSome then return ← fail 1
        if terminal.session != 0 && terminal.session != group then return ← fail 1
        save { terminal with session := group, foreground := kernel.pgidOf group }
        poller.kernel.modify fun kernel => kernel.setProcess group { kernel.process group with terminal := some slaveNumber }
        succeed
      | 0x5422 =>
        if (kernel.process group).terminal != some slaveNumber then return ← fail 25
        poller.kernel.modify fun kernel => kernel.setProcess group { kernel.process group with terminal := none }
        if kernel.sidOf group == group then save { terminal with session := 0, foreground := 0 }
        succeed
      | 0x541B => int (if isSlave then terminal.waiting else terminal.output.size)
      | 0x5411 => int (if isSlave then terminal.output.size else 0)
      | 0x540B | 0x5409 | 0x540A | 0x5425 => succeed
      | 0x80045430 => if isSlave then fail 25 else int terminal.index
      | 0x40045431 =>
        if isSlave then return ← fail 25
        save { terminal with locked := (← readInt) != 0 }
        succeed
      | _ => fail 25
    | _, _ => pure none
  catch _ => fail 14

end Tty

end Bap.Linux
