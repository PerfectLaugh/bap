import Bap.Linux.Files

/-! # POSIX message queues

`mq_open`, `mq_unlink`, `mq_timedsend`, `mq_timedreceive`, `mq_notify` and `mq_getsetattr`.

A queue is an inode, under `queueRoot`, which no listing of a directory shows, and a descriptor of `mq_open` is an open file of it. Its
messages are of the highest priority first and, of the same priority, in the order they came. A send waits for room and a receive for a
message, until a deadline of `CLOCK_REALTIME` if there is one, and after a handler of `SA_RESTART`, again. What `mq_notify` asks for is
a signal, of `SI_MESGQ`, when a message comes to the queue empty, once; `SIGEV_THREAD`, which needs netlink, isn't there. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Mqueue

/-- Where queues are, which no listing of `/` shows. -/
def queueRoot : String := "/\x01mqueue"

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Where a thread waits that receives from the queue of an inode, which `Poller.wake` wakes as it wakes what waits to read, and which
says that a receiver waits. -/
private def receiveSpace (number : Nat) : Nat := readySpace + 2 ^ 56 + number

/-- The calls of POSIX message queues, if the call is one of them. -/
def serve (poller : Poller) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := poller.architecture
  let big := architecture.big
  let word := architecture.bits / 8
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let kernel ← poller.kernel.get
  let now := kernel.clock
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let number (address size : Nat) : IO Nat := do pure (numberOf big (← read emu address size))
  let (emsgsize, etimedout) := (90, 110)
  -- A queue of a name, which comes without its `/`, or why it can't be one.
  let pathOf (address : Nat) : IO (Except Nat String) := do
    let name ← Files.readString emu address
    if name.isEmpty then return .error Errno.enoent
    if name.contains '/' then return .error Errno.eacces
    if name.utf8ByteSize > 255 then return .error 36
    pure (.ok (queueRoot ++ "/" ++ name))
  -- The queue of a descriptor.
  let queueOf (fd : Nat) : Except Nat (Nat × OpenFile × List (Nat × ByteArray) × Nat × Nat × Option (Nat × Nat × Nat × Nat)) :=
    match kernel.objectOf group fd with
    | .ok (number, file, { content := .mqueue messages capacity size notify, .. }) => .ok (number, file, messages, capacity, size, notify)
    | _ => .error Errno.ebadf
  -- A deadline of an absolute `timespec` of fields of `size` bytes, or none of one that Linux doesn't take, which a call fails with
  -- before anything else, whether it would wait or not.
  let deadlineAt (address size : Nat) : IO (Option (Option Nat)) := do
    if address == 0 then return some none
    pure ((← readSpan emu address size).map some)
  let wait (due : Option Nat) (space : Nat := readySpace) : IO (Option SyscallAction) := do
    if due.any (· ≤ now) then fail etimedout
    else pure (some (← poller.timers.waitUntil emu space 0 due true))
  -- A registration of `mq_notify` is of a process while it has the queue open, as `mqueue_flush_file` lets it go when it closes it,
  -- which it does as it ends.
  let live ← poller.live
  let registered (number_ : Nat) (notify : Option (Nat × Nat × Nat × Nat)) : Option (Nat × Nat × Nat × Nat) :=
    notify.filter fun (owner, _) => live.contains owner && (kernel.process owner).descriptors.toList.any fun (_, descriptor) =>
      (kernel.openFiles.get? descriptor.openFile).any (·.inode == number_)
  let send (fd address size priority timeout timeSize : Nat) : IO (Option SyscallAction) := do
    let some due ← deadlineAt timeout timeSize | fail Errno.einval
    let .ok (number_, file, messages, capacity, limit, notify) := queueOf fd | fail Errno.ebadf
    if file.flags &&& 3 == 0 then return ← fail Errno.ebadf
    if size > limit then return ← fail emsgsize
    if priority ≥ 32768 then return ← fail Errno.einval
    if messages.length ≥ capacity then
      if file.flags &&& Kernel.oNonblock != 0 then return ← fail Errno.eagain
      return ← wait due
    let text ← read emu address size
    let (before, after) := messages.span (·.1 ≥ priority)
    -- A message to the queue empty is what `mq_notify` asked to hear of, once; but one that a receiver that waits takes is said to
    -- nobody, and what was asked stays, as `do_mq_timedsend` has it.
    let notify := registered number_ notify
    let receiving := (← emu.taskTable.get).futexes.any (·.space == receiveSpace number_)
    let (notify, told) := if messages.isEmpty && !receiving then (none, notify) else (notify, none)
    poller.kernel.set (kernel.setContent number_ (.mqueue (before ++ [(priority, text)] ++ after) capacity limit notify))
    if let some (owner, 0, signal, value) := told then
      poller.signals.send emu none owner ⟨signal, 2 ^ 32 - 3, .sent group (kernel.process group).credentials.uid value⟩
    poller.wake emu
    succeed
  let receive (fd address size priorityAt timeout timeSize : Nat) : IO (Option SyscallAction) := do
    let some due ← deadlineAt timeout timeSize | fail Errno.einval
    let .ok (number_, file, messages, capacity, limit, notify) := queueOf fd | fail Errno.ebadf
    if file.flags &&& 3 == 1 then return ← fail Errno.ebadf
    if size < limit then return ← fail emsgsize
    match messages with
    | [] =>
      if file.flags &&& Kernel.oNonblock != 0 then return ← fail Errno.eagain
      wait due (receiveSpace number_)
    | (priority, text) :: rest =>
      write emu address text
      if priorityAt != 0 then write emu priorityAt (Abi.field big 4 priority)
      poller.kernel.set (kernel.setContent number_ (.mqueue rest capacity limit notify))
      poller.wake emu
      succeed text.size
  try
    match call with
    | .mqOpen =>
      let path ← match ← pathOf (arg 0) with
        | .ok path => pure path
        | .error errno => return ← fail errno
      let flags := architecture.openFlags (arg 1)
      if flags &&& 3 == 3 then return ← fail Errno.einval
      let (kernel, number_) ← match kernel.paths.get? path with
        | some number_ =>
          if flags &&& Kernel.oCreat != 0 && flags &&& Kernel.oExcl != 0 then return ← fail Errno.eexist
          pure (kernel, number_)
        | none =>
          if flags &&& Kernel.oCreat == 0 then return ← fail Errno.enoent
          let (capacity, size) ← if arg 3 == 0 then pure (10, 8192) else do
            pure (← number (arg 3 + word) word, ← number (arg 3 + 2 * word) word)
          if capacity == 0 || size == 0 || capacity > 65536 || size > 16777216 then return ← fail Errno.einval
          let process := kernel.process group
          pure (kernel.addDevice path (.mqueue [] capacity size none) (0o100000 ||| (arg 2 &&& 0o777 &&& (0o7777 - process.umask)))
            process.credentials)
      let openFile := kernel.nextOpenFile
      let kernel := { kernel with
        openFiles := kernel.openFiles.insert openFile { inode := number_, flags := flags &&& (3 ||| Kernel.oNonblock) }
        nextOpenFile := openFile + 1 }
      let (kernel, fd) := kernel.addDescriptor group openFile (flags &&& Kernel.oCloexec != 0)
      poller.kernel.set kernel
      succeed fd
    | .mqUnlink =>
      match ← pathOf (arg 0) with
      | .error errno => fail errno
      | .ok path =>
        if !kernel.paths.contains path then return ← fail Errno.enoent
        poller.kernel.set (kernel.unbindPath path)
        succeed
    | .mqTimedsend => send (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) word
    | .mqTimedsend64 => send (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) 8
    | .mqTimedreceive => receive (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) word
    | .mqTimedreceive64 => receive (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) 8
    | .mqNotify =>
      let .ok (number_, _, messages, capacity, limit, notify) := queueOf (arg 0) | fail Errno.ebadf
      if arg 1 == 0 then
        if notify.any (·.1 == group) then poller.kernel.set (kernel.setContent number_ (.mqueue messages capacity limit none))
        return ← succeed
      -- `struct sigevent`: its value, of a word, its signal and how it tells.
      let value ← number (arg 1) word
      let signal ← number (arg 1 + word) 4
      let how ← number (arg 1 + word + 4) 4
      if how > 1 || (how == 0 && (signal == 0 || signal > 64)) then return ← fail Errno.einval
      if (registered number_ notify).isSome then return ← fail 16
      poller.kernel.set (kernel.setContent number_ (.mqueue messages capacity limit (some (group, how, signal, value))))
      succeed
    | .mqGetsetattr =>
      let .ok (_, _, messages, capacity, limit, _) := queueOf (arg 0) | fail Errno.ebadf
      let .ok (id, file) := kernel.openFileOf group (arg 0) | fail Errno.ebadf
      let nonblocking := architecture.guestFlags Kernel.oNonblock
      if arg 2 != 0 then
        let flags := if file.flags &&& Kernel.oNonblock != 0 then nonblocking else 0
        write emu (arg 2) ([flags, capacity, limit, messages.length, 0, 0, 0, 0].foldl (fun out value => out ++ Abi.field big word value)
          ByteArray.empty)
      if arg 1 != 0 then
        let given ← number (arg 1) word
        let flags := if given &&& nonblocking != 0 then file.flags ||| Kernel.oNonblock else file.flags - (file.flags &&& Kernel.oNonblock)
        poller.kernel.set { kernel with openFiles := kernel.openFiles.insert id { file with flags } }
      succeed
    | _ => pure none
  catch _ => fail Errno.efault

end Mqueue

end Bap.Linux
