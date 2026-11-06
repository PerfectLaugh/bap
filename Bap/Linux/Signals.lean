import Bap.Emu.Tasks
import Bap.Emu.Checkpoint
import Bap.Linux.Calls
import Bap.Linux.Wire

/-! Signals of a Linux machine: what each process does with them and what each of its threads blocks, what is pending, and the
frame on the stack of a guest that a handler runs on and returns from.

A thread takes a signal at the end of a system call of its own, which is how a signal of its own comes to it, and when it is switched
to, which is how that of another comes, as one thread runs at a time. A thread that waits is woken for it. What is on the stack is what
Linux has there, so that a handler can read and change its context: `sigreturn` goes by what it finds. What isn't in that layout, as the
registers of floating point and the flags are, is kept here and comes back all the same.

The offsets are those of the `ucontext_t` of musl, which are those of the kernel, as the compiler says them for each target, and what a
program sees of all this agrees with qemu on `testsuite/src/libc-signals.c`. A signal that stops a process, as `SIGSTOP`, is ignored, as
no process is ever stopped here. There are no timers, so nothing raises `SIGALRM`, and a fault of memory is the only exception that
raises anything: not `SIGFPE` or `SIGILL`. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

structure SignalAction where
  handler : Nat := 0
  flags : Nat := 0
  restorer : Nat := 0
  mask : Nat := 0
  deriving DecidableEq, Repr

/-- What `siginfo_t` says. -/
inductive SignalDetail where
  /-- From a program, with what it sent. -/
  | sent (pid uid value : Nat)
  | child (pid uid status : Nat)
  | fault (address : Nat)
  /-- Of a system call that a filter of seccomp trapped: where it was made, its number, the architecture as `AUDIT_ARCH_*` says it,
  and what the filter gave with `SECCOMP_RET_TRAP`, which is `si_errno`. -/
  | seccomp (address syscall arch data : Nat)
  /-- Of a timer of `timer_create`: its id, how many times it expired that this doesn't say, and its `sigev_value`. -/
  | timer (id overrun value : Nat)
  deriving DecidableEq, Repr

structure SignalInfo where
  signal : Nat
  code : Nat
  detail : SignalDetail
  deriving DecidableEq, Repr

/-- All that goes back on `sigreturn` and that isn't in the context on the stack. -/
structure SignalFrame where
  /-- Where the stack was when the handler started, which tells a frame that is over from one that isn't. -/
  entry : Nat
  context : Nat
  onAlternate : Bool
  env : List (Bap.Var × Bap.Value)
  pc : Nat
  skip : Option Nat
  mask : Nat

/-- A system call as it began, for one that a signal is to start again. -/
structure LastCall where
  pc : Nat
  result : Nat
  restartable : Bool
  deriving DecidableEq, Repr

structure ThreadSignals where
  mask : Nat := 0
  pending : List SignalInfo := []
  frames : List SignalFrame := []
  /-- `sigaltstack`: where, how much, and the flags it was given, which are `SS_DISABLE` for none, as it then has no size. -/
  alternate : Nat × Nat × Nat := (0, 0, 2)
  /-- The mask to go back to after the handler of `sigsuspend`. -/
  suspended : Option Nat := none
  /-- What `sigtimedwait` waits for, where its information goes, and whether it may run out. -/
  waiting : Option (Nat × Nat) := none
  /-- Where a `waitid` that blocked has its `siginfo_t`, in which what it waits for leaves a status. -/
  waitingChild : Option Nat := none
  last : Option LastCall := none

structure SignalTable where
  /-- By process and signal, where it isn't the default. -/
  actions : Std.HashMap (Nat × Nat) SignalAction := {}
  /-- What is for a process and that all of its threads block. -/
  groupPending : Std.HashMap Nat (List SignalInfo) := {}
  threads : Std.HashMap Nat ThreadSignals := {}

/-- How a target has it. -/
private structure Layout where
  word : Nat
  /-- The registers in a context: their names and where they are. -/
  registers : List (String × Nat)
  /-- How much a register takes there. -/
  slot : Nat
  pc : Nat
  mask : Nat
  stack : Nat
  stackFlags : Nat
  stackSize : Nat
  size : Nat
  /-- On 32-bit ARM, where the mode is. -/
  cpsr : Option Nat := none
  /-- Where a pointer to the registers goes, and what it points to. -/
  pointer : Option (Nat × Nat) := none

private def isMipsArchitecture : Architecture → Bool
  | .mips .. => true
  | _ => false

private def numbered (base step : Nat) (registers : List String) : List (String × Nat) :=
  registers.zipIdx.map fun (name, index) => (name, base + index * step)

private def named (prefix_ : String) (first count : Nat) : List String :=
  (List.range count).map fun index => s!"{prefix_}{first + index}"

private def layoutOf : Architecture → Layout
  | .x86_64 =>
    { word := 8, slot := 8, pc := 40 + 16 * 8, mask := 296, stack := 16, stackFlags := 24, stackSize := 32, size := 936,
      registers := numbered 40 8 ["R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15", "RDI", "RSI", "RBP", "RBX", "RDX", "RAX", "RCX", "RSP"] }
  | .i686 =>
    { word := 4, slot := 4, pc := 20 + 14 * 4, mask := 108, stack := 8, stackFlags := 12, stackSize := 16, size := 348,
      registers := numbered (20 + 4 * 4) 4 ["EDI", "ESI", "EBP", "ESP", "EBX", "EDX", "ECX", "EAX"] }
  | .aarch64 =>
    { word := 8, slot := 8, pc := 440, mask := 40, stack := 16, stackFlags := 24, stackSize := 32, size := 4560,
      registers := numbered 184 8 (named "X" 0 31) ++ [("SP", 432)] }
  | .riscv64 =>
    { word := 8, slot := 8, pc := 176, mask := 40, stack := 16, stackFlags := 24, stackSize := 32, size := 960,
      registers := numbered (176 + 8) 8 (named "X" 1 31) }
  | .riscv32 =>
    { word := 4, slot := 4, pc := 160, mask := 20, stack := 8, stackFlags := 12, stackSize := 16, size := 816,
      registers := numbered (160 + 4) 4 (named "X" 1 31) }
  | .arm =>
    { word := 4, slot := 4, pc := 92, mask := 104, stack := 8, stackFlags := 12, stackSize := 16, size := 744, cpsr := some 96,
      registers := numbered 32 4 (named "R" 0 13) ++ [("SP", 84), ("LR", 88)] }
  | .mips 32 _ _ =>
    { word := 4, slot := 8, pc := 32, mask := 616, stack := 8, stackFlags := 16, stackSize := 12, size := 744,
      registers := numbered 40 8 (named "R" 0 32) }
  | .mips _ _ _ =>
    { word := 8, slot := 8, pc := 616, mask := 640, stack := 16, stackFlags := 32, stackSize := 24, size := 768,
      registers := numbered 40 8 (named "R" 0 32) }
  | .powerpc 32 _ =>
    { word := 4, slot := 4, pc := 192 + 32 * 4, mask := 52, stack := 8, stackFlags := 12, stackSize := 16, size := 1184,
      pointer := some (48, 192),
      registers := numbered 192 4 (named "R" 0 32) ++ [("CTR", 192 + 35 * 4), ("LR", 192 + 36 * 4)] }
  | .powerpc _ _ =>
    { word := 8, slot := 8, pc := 232 + 32 * 8, mask := 40, stack := 16, stackFlags := 24, stackSize := 32, size := 1696,
      pointer := some (224, 232),
      registers := numbered 232 8 (named "R" 0 32) ++ [("CTR", 232 + 35 * 8), ("LR", 232 + 36 * 8)] }

/-- Where a kernel's `sigaction` has each of its fields: flags and how wide, handler, restorer, mask. -/
private def actionOffsets (architecture : Architecture) : Nat × Nat × Nat × Option Nat × Nat :=
  let word := architecture.bits / 8
  match architecture with
  | .mips .. => (0, 4, word, none, 2 * word)
  | .riscv64 | .riscv32 => (word, word, 0, none, 2 * word)
  | _ => (word, word, 0, some (2 * word), 3 * word)

private def maskBytes (architecture : Architecture) : Nat := if isMipsArchitecture architecture then 16 else 8

private structure SignalNumbers where
  kill : Nat
  stop : Nat
  segv : Nat
  chld : Nat
  /-- What does nothing by default, of which those that stop are here too, as nothing is stopped. -/
  ignored : List Nat
  /-- `SA_SIGINFO`, and for `rt_sigprocmask` what blocks, unblocks and sets. -/
  saInfo : Nat
  /-- `SA_NOCLDWAIT`. -/
  saNoCldWait : Nat
  howBlock : Nat
  howUnblock : Nat
  howSet : Nat
  eintr : Nat
  eagain : Nat
  einval : Nat
  esrch : Nat
  efault : Nat
  eperm : Nat
  count : Nat
  /-- What stops a process by default, and what lets it go on. -/
  stops : List Nat
  cont : Nat

private def numbersOf (architecture : Architecture) : SignalNumbers :=
  if isMipsArchitecture architecture then
    { kill := 9, stop := 23, segv := 11, chld := 18, ignored := [18, 20, 21, 23, 24, 25, 26, 27], saInfo := 8, saNoCldWait := 0x10000, howBlock := 1, howUnblock := 2,
      howSet := 3, eintr := 4, eagain := 11, einval := 22, esrch := 3, efault := 14, eperm := 1, count := 128, stops := [23, 24, 26, 27],
      cont := 25 }
  else
    { kill := 9, stop := 19, segv := 11, chld := 17, ignored := [17, 18, 19, 20, 21, 22, 23, 28], saInfo := 4, saNoCldWait := 2, howBlock := 0, howUnblock := 1,
      howSet := 2, eintr := 4, eagain := 11, einval := 22, esrch := 3, efault := 14, eperm := 1, count := 64, stops := [19, 20, 21, 22],
      cont := 18 }

private def saOnStack : Nat := 0x08000000
private def saRestart : Nat := 0x10000000
private def saNoDefer : Nat := 0x40000000
private def saResetHand : Nat := 0x80000000
private def ssOnStack : Nat := 1
private def ssDisable : Nat := 2
private def ssAutoDisarm : Nat := 2 ^ 31

private def hasFlag (flags flag : Nat) : Bool := flags &&& flag != 0

/-- No alternate stack. -/
private def noAlternate : Nat × Nat × Nat := (0, 0, ssDisable)

/-- Whether a stack pointer is on the alternate stack, which, as Linux has it, one that `SS_AUTODISARM` takes away in a handler never is. -/
private def onAlternateStack (alternate : Nat × Nat × Nat) (sp : Nat) : Bool :=
  let (base, size, flags) := alternate
  !hasFlag flags ssAutoDisarm && base ≤ sp && sp < base + size

/-- The alternate stack that a `stack_t` sets, if Linux takes its flags: `SS_DISABLE`, or 0 or `SS_ONSTACK`, which is an old way to say
0, with `SS_AUTODISARM` or not. -/
private def givenAlternate (base size flags : Nat) : Option (Nat × Nat × Nat) :=
  let mode := flags &&& (ssAutoDisarm ^^^ (2 ^ 32 - 1))
  if mode == ssDisable then some (0, 0, flags)
  else if mode == 0 || mode == ssOnStack then some (base, size, flags)
  else none

private def bitOf (signal : Nat) : Nat := 1 <<< (signal - 1)

/-- The system calls of signals of a target. -/
private structure SignalCalls where
  sigaction : Nat
  sigprocmask : Nat
  returns : List Nat
  kill : Nat
  tkill : Nat
  tgkill : Nat
  pending : Nat
  timedwait : List Nat
  suspend : Nat
  queueinfo : Nat
  altstack : Nat
  waitid : Nat
  pause : Option Nat := none
  creates : List Nat
  restartable : List Nat

private def callsOf : Architecture → SignalCalls
  | .x86_64 =>
    { sigaction := 13, sigprocmask := 14, returns := [15], kill := 62, tkill := 200, tgkill := 234, pending := 127, timedwait := [128],
      suspend := 130, queueinfo := 129, waitid := 247, altstack := 131, pause := some 34, creates := [56, 57, 58], restartable := [61, 202, 247] }
  | .i686 =>
    { sigaction := 174, sigprocmask := 175, returns := [119, 173], kill := 37, tkill := 238, tgkill := 270, pending := 176,
      timedwait := [177, 421], suspend := 179, queueinfo := 178, waitid := 284, altstack := 186, pause := some 29, creates := [2, 120, 190],
      restartable := [7, 114, 240, 284, 422] }
  | .aarch64 | .riscv64 | .riscv32 =>
    { sigaction := 134, sigprocmask := 135, returns := [139], kill := 129, tkill := 130, tgkill := 131, pending := 136, timedwait := [137, 421],
      suspend := 133, queueinfo := 138, waitid := 95, altstack := 132, creates := [220], restartable := [95, 98, 260, 422] }
  | .arm =>
    { sigaction := 174, sigprocmask := 175, returns := [119, 173], kill := 37, tkill := 238, tgkill := 268, pending := 176,
      timedwait := [177, 421], suspend := 179, queueinfo := 178, waitid := 280, altstack := 186, pause := some 29, creates := [2, 120, 190],
      restartable := [114, 240, 280, 422] }
  | .powerpc 32 _ =>
    { sigaction := 173, sigprocmask := 174, returns := [119, 172], kill := 37, tkill := 208, tgkill := 250, pending := 175,
      timedwait := [176, 421], suspend := 178, queueinfo := 177, waitid := 272, altstack := 185, pause := some 29, creates := [2, 120, 189],
      restartable := [7, 114, 221, 272, 422] }
  | .powerpc _ _ =>
    { sigaction := 173, sigprocmask := 174, returns := [172], kill := 37, tkill := 208, tgkill := 250, pending := 175, timedwait := [176],
      suspend := 178, queueinfo := 177, waitid := 272, altstack := 185, pause := some 29, creates := [2, 120, 189], restartable := [7, 114, 221, 272] }
  | .mips 32 _ _ =>
    { sigaction := 4194, sigprocmask := 4195, returns := [4119, 4193], kill := 4037, tkill := 4236, tgkill := 4266, pending := 4196,
      timedwait := [4197, 4421], suspend := 4199, queueinfo := 4198, waitid := 4278, altstack := 4206, pause := some 4029, creates := [4002, 4120],
      restartable := [4007, 4114, 4238, 4278, 4422] }
  | .mips _ _ _ =>
    { sigaction := 5013, sigprocmask := 5014, returns := [5211], kill := 5060, tkill := 5192, tgkill := 5225, pending := 5125,
      timedwait := [5126], suspend := 5128, queueinfo := 5127, waitid := 5237, altstack := 5129, pause := some 5033, creates := [5055, 5056, 5057],
      restartable := [5059, 5194, 5237] }

/-- What a thread does to return from a handler that has no restorer, as a kernel keeps for it: the system call that ends one. It is
in a page of its own that every process has if it needs it. -/
private def returnCode (architecture : Architecture) : ByteArray :=
  let littleWords (words : List Nat) (big : Bool) : ByteArray :=
    ByteArray.mk (words.flatMap fun word =>
      let bytes := (List.range 4).map fun index => (word >>> (8 * index)).toUInt8
      if big then bytes.reverse else bytes).toArray
  match architecture with
  | .x86_64 => ByteArray.mk #[0xB8, 15, 0, 0, 0, 0x0F, 0x05]
  | .i686 => ByteArray.mk #[0xB8, 173, 0, 0, 0, 0xCD, 0x80]
  | .aarch64 => littleWords [0xD2801168, 0xD4000001] false
  | .arm => littleWords [0xE3A070AD, 0xEF000000] false
  | .riscv64 | .riscv32 => littleWords [0x08B00893, 0x00000073] false
  | .mips 32 big _ => littleWords [0x24021061, 0x0000000C] big
  | .mips _ big _ => littleWords [0x2402145B, 0x0000000C] big
  | .powerpc _ big => littleWords [0x380000AC, 0x44000002] big

namespace Encoding

open Wire

private def putValue (out : ByteArray) (binding : Bap.Var × Bap.Value) : ByteArray :=
  let (var, value) := binding
  let out := putFlag (putNat (putText out var.name) var.index) var.isVirtual
  match value with
  | @Value.bits width bits => putNat (putNat (putNat out 1) width) bits.toNat
  | _ => putNat out 0

private def getValue : Decoder (Bap.Var × Bap.Value) := fun data at_ => do
  let (name, at_) ← getText data at_
  let (index, at_) ← getNat data at_
  let (isVirtual, at_) ← getFlag data at_
  let (tag, at_) ← getNat data at_
  match tag with
  | 1 =>
    let (width, at_) ← getNat data at_
    let (value, at_) ← getNat data at_
    .ok ((⟨name, .imm width, index, isVirtual⟩, .bits (BitVec.ofNat width value)), at_)
  | _ => .ok ((⟨name, .imm 0, index, isVirtual⟩, .undefined), at_)

private def putInfo (out : ByteArray) (info : SignalInfo) : ByteArray :=
  let out := putNat (putNat out info.signal) info.code
  match info.detail with
  | .sent pid uid value => putNat (putNat (putNat (putNat out 0) pid) uid) value
  | .child pid uid status => putNat (putNat (putNat (putNat out 1) pid) uid) status
  | .fault address => putNat (putNat out 2) address
  | .seccomp address syscall arch data => putNat (putNat (putNat (putNat (putNat out 3) address) syscall) arch) data
  | .timer id overrun value => putNat (putNat (putNat (putNat out 4) id) overrun) value

private def getInfo : Decoder SignalInfo := fun data at_ => do
  let (signal, at_) ← getNat data at_
  let (code, at_) ← getNat data at_
  let (tag, at_) ← getNat data at_
  match tag with
  | 2 =>
    let (address, at_) ← getNat data at_
    .ok (⟨signal, code, .fault address⟩, at_)
  | 3 =>
    let (address, at_) ← getNat data at_
    let (syscall, at_) ← getNat data at_
    let (arch, at_) ← getNat data at_
    let (value, at_) ← getNat data at_
    .ok (⟨signal, code, .seccomp address syscall arch value⟩, at_)
  | 4 =>
    let (id, at_) ← getNat data at_
    let (overrun, at_) ← getNat data at_
    let (value, at_) ← getNat data at_
    .ok (⟨signal, code, .timer id overrun value⟩, at_)
  | _ =>
    let (first, at_) ← getNat data at_
    let (second, at_) ← getNat data at_
    let (third, at_) ← getNat data at_
    .ok (⟨signal, code, if tag == 0 then .sent first second third else .child first second third⟩, at_)

private def putFrame (out : ByteArray) (frame : SignalFrame) : ByteArray :=
  let out := putFlag (putNat (putNat out frame.entry) frame.context) frame.onAlternate
  let out := putList putValue out frame.env
  let out := putNat out frame.pc
  let out := putOption putNat out frame.skip
  putNat out frame.mask

private def getFrame : Decoder SignalFrame := fun data at_ => do
  let (entry, at_) ← getNat data at_
  let (context, at_) ← getNat data at_
  let (onAlternate, at_) ← getFlag data at_
  let (env, at_) ← getList getValue data at_
  let (pc, at_) ← getNat data at_
  let (skip, at_) ← getOption getNat data at_
  let (mask, at_) ← getNat data at_
  .ok ({ entry, context, onAlternate, env, pc, skip, mask }, at_)

private def putLast (out : ByteArray) (last : LastCall) : ByteArray :=
  putFlag (putNat (putNat out last.pc) last.result) last.restartable

private def getLast : Decoder LastCall := fun data at_ => do
  let (pc, at_) ← getNat data at_
  let (result, at_) ← getNat data at_
  let (restartable, at_) ← getFlag data at_
  .ok ({ pc, result, restartable }, at_)

private def putThread (out : ByteArray) (entry : Nat × ThreadSignals) : ByteArray :=
  let (tid, thread) := entry
  let out := putNat (putNat out tid) thread.mask
  let out := putList putInfo out thread.pending
  let out := putList putFrame out thread.frames
  let out := putNat (putNat (putNat out thread.alternate.1) thread.alternate.2.1) thread.alternate.2.2
  let out := putOption putNat out thread.suspended
  let out := putOption (fun out wait => putNat (putNat out wait.1) wait.2) out thread.waiting
  let out := putOption putNat out thread.waitingChild
  putOption putLast out thread.last

private def getThread : Decoder (Nat × ThreadSignals) := fun data at_ => do
  let (tid, at_) ← getNat data at_
  let (mask, at_) ← getNat data at_
  let (pending, at_) ← getList getInfo data at_
  let (frames, at_) ← getList getFrame data at_
  let (alternateStack, at_) ← getNat data at_
  let (alternateSize, at_) ← getNat data at_
  let (alternateFlags, at_) ← getNat data at_
  let (suspended, at_) ← getOption getNat data at_
  let (waiting, at_) ← getOption (fun data at_ => do
    let (set, at_) ← getNat data at_
    let (address, at_) ← getNat data at_
    .ok ((set, address), at_)) data at_
  let (waitingChild, at_) ← getOption getNat data at_
  let (last, at_) ← getOption getLast data at_
  .ok ((tid, { mask, pending, frames, alternate := (alternateStack, alternateSize, alternateFlags), suspended, waiting, waitingChild, last }), at_)

private def putAction (out : ByteArray) (entry : (Nat × Nat) × SignalAction) : ByteArray :=
  let ((group, signal), action) := entry
  putNat (putNat (putNat (putNat (putNat (putNat out group) signal) action.handler) action.flags) action.restorer) action.mask

private def getAction : Decoder ((Nat × Nat) × SignalAction) := fun data at_ => do
  let (group, at_) ← getNat data at_
  let (signal, at_) ← getNat data at_
  let (handler, at_) ← getNat data at_
  let (flags, at_) ← getNat data at_
  let (restorer, at_) ← getNat data at_
  let (mask, at_) ← getNat data at_
  .ok (((group, signal), { handler, flags, restorer, mask }), at_)

private def putGroup (out : ByteArray) (entry : Nat × List SignalInfo) : ByteArray :=
  putList putInfo (putNat out entry.1) entry.2

private def getGroup : Decoder (Nat × List SignalInfo) := fun data at_ => do
  let (group, at_) ← getNat data at_
  let (pending, at_) ← getList getInfo data at_
  .ok ((group, pending), at_)

def encode (table : SignalTable) : ByteArray :=
  let out := putSorted putAction ByteArray.empty table.actions.toList
  let out := putSorted putGroup out table.groupPending.toList
  putSorted putThread out table.threads.toList

def decode (data : ByteArray) : Except String SignalTable := do
  let (actions, at_) ← getList getAction data 0
  let (groups, at_) ← getList getGroup data at_
  let (threads, at_) ← getList getThread data at_
  expectEnd data at_
  .ok { actions := Std.HashMap.ofList actions, groupPending := Std.HashMap.ofList groups, threads := Std.HashMap.ofList threads }

end Encoding

/-- Why a signal ended a process, or would have: a fault that nothing handles, with where it was, a handler that couldn't be entered,
as for no stack to run it on, and a `sigreturn` that had nothing to go back to. They are apart, as the first is the program's and the
others are of how it was run. -/
inductive SignalFailure where
  | unhandled (thread pc address : Nat) (why : String)
  | handlerEntry (thread signal : Nat) (error : String)
  | sigreturn (thread : Nat) (why : String)
  /-- An ignored fault that was gone on from, past the instruction, as `skipIgnoredFaults` has it. -/
  | skipped (thread pc address : Nat)
  deriving DecidableEq, Repr

/-- The signals of a machine. -/
structure Signals where
  architecture : Architecture
  /-- Where the page of `returnCode` goes. -/
  returnPage : Nat
  table : IO.Ref SignalTable
  /-- What ended a process, or would have, as it happened. -/
  failures : IO.Ref (Array SignalFailure)
  /-- Whether a fault that a process ignores goes on past the instruction that faulted. Linux ends the process for it, as an
  instruction that faults again each time it runs can't be ignored, which is what this does unless it is asked not to. -/
  skipIgnoredFaults : IO.Ref Bool
  /-- What a signal that is to be delivered to a thread, or a fault of one, comes to first: whether it stopped the thread instead, as
  `Bap.Linux.Ptrace` has a tracee stop. -/
  intercept : IO.Ref (Emu → Nat → SignalInfo → IO Bool)
  /-- The process tracing a thread, if it is traced: a signal of a traced thread is kept to be delivered, and stops it, even if it
  is ignored. -/
  tracer : IO.Ref (Nat → IO (Option Nat))
  /-- A process that a signal stops, by what does that by default, or that SIGCONT lets go on: the process and the signal. -/
  jobControl : IO.Ref (Emu → Nat → Nat → IO Unit)
  /-- A thread that a signal woke from what it waited in: the thread, whether its handler has `SA_RESTART`, and the spaces that it
  waited in, as a call that runs again when it is woken has to hear of it. -/
  interrupted : IO.Ref (Emu → Nat → Bool → List Nat → IO Unit)
  /-- A signal was sent, as what waits to read one, as of `signalfd`, has to look again. -/
  sent : IO.Ref (Emu → IO Unit)
  /-- A signal of a process was taken from what was pending, as delivery or a wait takes it, as a timer of `timer_create` has to hear
  of what its signal said. -/
  taken : IO.Ref (Nat → SignalInfo → IO Unit)
  /-- The process group of a process, and the processes of a process group that aren't reaped, as the kernel has them, for `kill` of a group. -/
  pgidOf : IO.Ref (Nat → IO Nat)
  members : IO.Ref (Nat → IO (List Nat))

namespace Signals

private def numbers (signals : Signals) : SignalNumbers := numbersOf signals.architecture

private def threadOf (signals : Signals) (tid : Nat) : IO ThreadSignals := do
  pure ((← signals.table.get).threads.getD tid {})

private def modifyThread (signals : Signals) (tid : Nat) (change : ThreadSignals → ThreadSignals) : IO Unit :=
  signals.table.modify fun table =>
    { table with threads := table.threads.insert tid (change (table.threads.getD tid {})) }

private def actionOf (signals : Signals) (group signal : Nat) : IO SignalAction := do
  pure ((← signals.table.get).actions.getD (group, signal) {})

/-- What can't be blocked, caught or ignored. -/
private def unblockable (signals : Signals) : Nat :=
  bitOf (signals.numbers).kill ||| bitOf (signals.numbers).stop

private def blockable (signals : Signals) (mask : Nat) : Nat :=
  mask &&& ((2 ^ (signals.numbers).count - 1) ^^^ unblockable signals)

/-- What a signal comes to in a process where it isn't blocked. -/
private inductive Disposition where
  | ignore | handle (action : SignalAction) | terminate
  /-- It stops the process, which SIGCONT lets go on. -/
  | stop

private def dispositionOf (signals : Signals) (group signal : Nat) : IO Disposition := do
  let numbers := signals.numbers
  if signal == numbers.kill then return .terminate
  if signal == numbers.stop then return .stop
  let action ← actionOf signals group signal
  match action.handler with
  | 0 => pure (if numbers.stops.contains signal then .stop else if numbers.ignored.contains signal then .ignore else .terminate)
  | 1 => pure .ignore
  | _ => pure (.handle action)

/-- Whether a signal comes to a thread, rather than being blocked or ignored, as a terminal asks before it sends `SIGTTIN` or
`SIGTTOU` to a process that isn't in its foreground: `EIO` otherwise. -/
def comesTo (signals : Signals) (tid group signal : Nat) : IO Bool := do
  if bitOf signal &&& (← threadOf signals tid).mask != 0 then return false
  match ← dispositionOf signals group signal with
  | .ignore => pure false
  | _ => pure true

private def wordOfWidth (width value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)

private def registerValue (emu : Emu) (width : Nat) (name : String) : IO Nat := do
  match Bil.lookup (← emu.state.get).env ⟨name, .imm width, 0, false⟩ with
  | .ok (.bits value) => pure value.toNat
  | _ => pure 0

/-- `bytes` many, in the order of the target. -/
private def encodeNumber (emu : Emu) (bytes value : Nat) : ByteArray :=
  let little := (List.range bytes).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if emu.config.endian == .big then little.reverse else little).toArray

private def decodeNumber (emu : Emu) (data : ByteArray) : Nat :=
  let little := if emu.config.endian == .big then data.toList.reverse else data.toList
  little.foldr (fun byte value => value * 256 + byte.toNat) 0

private def readNumber (emu : Emu) (address bytes : Nat) : IO Nat := do
  pure (decodeNumber emu (← read emu address bytes))

/-- A mask as it is in memory: a word at a time, the low one first. -/
private def encodeMask (signals : Signals) (emu : Emu) (mask size : Nat) : ByteArray :=
  let word := signals.architecture.bits / 8
  (List.range (size / word)).foldl (init := ByteArray.empty) fun out index =>
    out ++ encodeNumber emu word (mask >>> (index * word * 8))

def readMask (signals : Signals) (emu : Emu) (address size : Nat) : IO Nat := do
  let word := signals.architecture.bits / 8
  (List.range (size / word)).foldlM (init := 0) fun mask index => do
    pure (mask ||| ((← readNumber emu (address + index * word) word) <<< (index * word * 8)))

private def writeInfo (signals : Signals) (emu : Emu) (address : Nat) (info : SignalInfo) : IO Unit := do
  let word := signals.architecture.bits / 8
  let mips := isMipsArchitecture signals.architecture
  let base := if word == 8 then 16 else 12
  let int (offset value : Nat) : IO Unit := write emu (address + offset) (encodeNumber emu 4 value)
  int 0 info.signal
  int (if mips then 4 else 8) info.code
  match info.detail with
  | .sent pid uid value =>
    int base pid
    int (base + 4) uid
    write emu (address + base + 8) (encodeNumber emu word value)
  | .child pid uid status =>
    int base pid
    int (base + 4) uid
    int (base + 8) status
  | .fault faulting => write emu (address + base) (encodeNumber emu word faulting)
  | .seccomp callAddress syscall arch data =>
    int (if mips then 8 else 4) data
    write emu (address + base) (encodeNumber emu word callAddress)
    int (base + word) syscall
    int (base + word + 4) arch
  | .timer id overrun value =>
    int base id
    int (base + 4) overrun
    write emu (address + base + 8) (encodeNumber emu word value)

/-- The way back for a handler without a restorer: the page is put there the first time that it is wanted. -/
private def returnAddress (signals : Signals) (emu : Emu) : IO Nat := do
  match lookupRegion (← emu.regions.get) signals.returnPage with
  | some _ => pure ()
  | none =>
    let code := returnCode signals.architecture
    map emu ⟨signals.returnPage, code ++ ByteArray.mk (Array.replicate (4096 - code.size) 0), ⟨true, false, true⟩⟩
  pure signals.returnPage

private def stackRegister (architecture : Architecture) : String :=
  match architecture with
  | .x86_64 => "RSP"
  | .i686 => "ESP"
  | .aarch64 | .arm => "SP"
  | .riscv64 | .riscv32 => "X2"
  | .mips .. => "R29"
  | .powerpc .. => "R1"

/-- Runs a handler, on the frame that it needs. `resume` is where the thread goes when it returns. -/
private def enterHandler (signals : Signals) (emu : Emu) (tid : Nat) (info : SignalInfo) (action : SignalAction) (resume : Nat)
    (skip : Option Nat) : IO Nat := do
  let architecture := signals.architecture
  let layout := layoutOf architecture
  let width := architecture.bits
  let word := width / 8
  let thread ← threadOf signals tid
  let sp ← registerValue emu width (stackRegister architecture)
  let (alternateBase, alternateSize, alternateFlags) := thread.alternate
  let alternateOff := alternateSize == 0
  let inAlternate := onAlternateStack thread.alternate sp
  let top :=
    if hasFlag action.flags saOnStack && !alternateOff && !inAlternate then alternateBase + alternateSize
    else
      -- What a function may use below its stack without saying so.
      match architecture with
      | .x86_64 => sp - 128
      | .powerpc 64 _ => sp - 288
      | _ => sp
  let onAlternate := hasFlag action.flags saOnStack && !alternateOff || inAlternate
  let contextSize := (layout.size + 15) / 16 * 16
  let infoAddress := (top - contextSize - 128) / 16 * 16
  let contextAddress := infoAddress + 128
  -- What the calling convention wants below it.
  let entry := match architecture with
    | .x86_64 => infoAddress - 8
    | .i686 => infoAddress - 16 - 4 + 0
    | .mips .. => infoAddress - 32
    | .powerpc 32 _ => infoAddress - 64
    | .powerpc _ _ => infoAddress - 112
    | _ => infoAddress
  let oldMask := thread.suspended.getD thread.mask
  write emu infoAddress (ByteArray.mk (Array.replicate (128 + contextSize) 0))
  writeInfo signals emu infoAddress info
  -- The context.
  let slot (value : Nat) : ByteArray := encodeNumber emu layout.slot (value % 2 ^ width)
  for (name, offset) in layout.registers do
    write emu (contextAddress + offset) (slot (← registerValue emu width name))
  write emu (contextAddress + layout.pc) (slot resume)
  write emu (contextAddress + layout.stack) (encodeNumber emu word alternateBase)
  write emu (contextAddress + layout.stackFlags) (encodeNumber emu 4 alternateFlags)
  write emu (contextAddress + layout.stackSize) (encodeNumber emu word alternateSize)
  write emu (contextAddress + layout.mask) (encodeMask signals emu oldMask (maskBytes architecture))
  if let some (at_, target) := layout.pointer then
    write emu (contextAddress + at_) (encodeNumber emu word (contextAddress + target))
  if let some at_ := layout.cpsr then
    write emu (contextAddress + at_) (encodeNumber emu 4 (if (← registerValue emu 1 "ISET") == 1 then 0x20 else 0))
  -- What goes back on `sigreturn`.
  let memoryVar := emu.config.memory
  let env := (← emu.state.get).env.filter fun binding => binding.1 != memoryVar
  let frame : SignalFrame := { entry, context := contextAddress, onAlternate, env, pc := resume, skip, mask := oldMask }
  let withoutStale := thread.frames.filter fun other => other.onAlternate != onAlternate || other.entry + 64 ≥ entry
  let addedMask := action.mask ||| (if hasFlag action.flags saNoDefer then 0 else bitOf info.signal)
  modifyThread signals tid fun thread =>
    { thread with
      frames := frame :: withoutStale
      mask := blockable signals (oldMask ||| addedMask)
      -- `SS_AUTODISARM` takes it away until `sigreturn` sets what the context has again.
      alternate := if hasFlag alternateFlags ssAutoDisarm then noAlternate else thread.alternate
      suspended := none }
  if hasFlag action.flags saResetHand then
    let group := (← emu.taskTable.get).find? tid |>.map (·.group) |>.getD tid
    signals.table.modify fun table => { table with actions := table.actions.erase (group, info.signal) }
  -- The registers of the handler.
  let set (name : String) (value : Nat) : IO Unit := setReg emu ⟨name, .imm width, 0, false⟩ (wordOfWidth width value)
  let returning ← match actionOffsets architecture with
    | (_, _, _, some _, _) => if action.restorer != 0 then pure action.restorer else returnAddress signals emu
    | _ => returnAddress signals emu
  let handler := match architecture with
    | .arm => action.handler - action.handler % 2
    | _ => action.handler
  match architecture with
  | .x86_64 =>
    write emu entry (encodeNumber emu 8 returning)
    set "RSP" entry
    set "RDI" info.signal
    set "RSI" infoAddress
    set "RDX" contextAddress
    setReg emu ⟨"DF", .imm 1, 0, false⟩ (wordOfWidth 1 0)
  | .i686 =>
    write emu entry (encodeNumber emu 4 returning)
    write emu (entry + 4) (encodeNumber emu 4 info.signal)
    write emu (entry + 8) (encodeNumber emu 4 infoAddress)
    write emu (entry + 12) (encodeNumber emu 4 contextAddress)
    set "ESP" entry
    setReg emu ⟨"DF", .imm 1, 0, false⟩ (wordOfWidth 1 0)
  | .aarch64 =>
    set "SP" entry
    set "X0" info.signal
    set "X1" infoAddress
    set "X2" contextAddress
    set "X30" returning
  | .arm =>
    set "SP" entry
    set "R0" info.signal
    set "R1" infoAddress
    set "R2" contextAddress
    set "LR" returning
    setReg emu ⟨"ISET", .imm 1, 0, false⟩ (wordOfWidth 1 (action.handler % 2))
  | .riscv64 | .riscv32 =>
    set "X2" entry
    set "X10" info.signal
    set "X11" infoAddress
    set "X12" contextAddress
    set "X1" returning
  | .mips .. =>
    set "R29" entry
    set "R4" info.signal
    set "R5" infoAddress
    set "R6" contextAddress
    set "R31" returning
    -- A function of MIPS finds what it needs from where it was called.
    set "R25" handler
  | .powerpc .. =>
    write emu entry (encodeNumber emu word 0)
    set "R1" entry
    set "R3" info.signal
    set "R4" infoAddress
    set "R5" contextAddress
    set "LR" returning
    -- As ELFv2 has a function find its data.
    set "R12" handler
  pure handler

/-- The next signal for a thread that doesn't block it: the lowest, and of one number the first. -/
private def nextSignal (signals : Signals) (tid group : Nat) : IO (Option SignalInfo) := do
  let table ← signals.table.get
  let thread := table.threads.getD tid {}
  let shared := table.groupPending.getD group []
  let candidates := (thread.pending ++ shared).filter fun info => bitOf info.signal &&& thread.mask == 0
  match candidates with
  | [] => pure none
  | first :: rest =>
    let lowest := rest.foldl (fun best info => if info.signal < best.signal then info else best) first
    let remove (list : List SignalInfo) : List SignalInfo := list.eraseP fun info => info.signal == lowest.signal
    if thread.pending.any (·.signal == lowest.signal) then
      modifyThread signals tid fun thread => { thread with pending := remove thread.pending }
    else
      signals.table.modify fun table => { table with groupPending := table.groupPending.insert group (remove shared) }
    (← signals.taken.get) group lowest
    pure (some lowest)

/-- The thread that runs takes what it has. `inCall` is whether a system call of its own is ending, which decides where it goes. -/
private partial def deliver (signals : Signals) (emu : Emu) (inCall : Bool) : IO Unit := do
  if ← stopped emu then return
  let tid ← thread emu
  let task ← currentTask emu
  if task.status.isSome then return
  if !inCall && (← emu.pendingRef.get).isSome then return
  match ← nextSignal signals tid task.group with
  | none => pure ()
  | some info =>
    -- A tracee stops for it instead, and its tracer says what becomes of it.
    if ← (← signals.intercept.get) emu tid info then return
    match ← dispositionOf signals task.group info.signal with
    | .ignore => deliver signals emu inCall
    | .stop => (← signals.jobControl.get) emu task.group info.signal
    | .terminate => kill emu task.group info.signal
    | .handle action =>
      let resume ← if inCall then
          match ← emu.redirect.get with
          | some target => pure target
          | none => emu.nextPc.get
        else emu.pc.get
      let skip ← if inCall then pure none else emu.skipCode.get
      match ← (enterHandler signals emu tid info action resume skip).toBaseIO with
      | .ok handler =>
        if inCall then emu.redirect.set (some handler)
        else
          emu.pc.set handler
          emu.skipCode.set none
        deliver signals emu inCall
      | .error error =>
        -- No stack to run it on: Linux has a process end for that.
        signals.failures.modify (·.push (.handlerEntry tid info.signal (toString error)))
        kill emu task.group (signals.numbers).segv

/-- What `rt_sigprocmask` does to the mask of a thread, of the numbers of the architecture for `how`: `set`, if it isn't 0, changes the
mask, and the mask that was before goes to `old`, if it isn't 0. The error number of the call if it fails. -/
def changeMask (signals : Signals) (emu : Emu) (tid how set old : Nat) : IO (Option Nat) := do
  let numbers := signals.numbers
  let size := maskBytes signals.architecture
  let previous := (← threadOf signals tid).mask
  try
    if set != 0 then
      let given ← readMask signals emu set size
      let mask ←
        if how == numbers.howBlock then pure (previous ||| given)
        else if how == numbers.howUnblock then pure (previous &&& (given ^^^ (2 ^ 128 - 1)))
        else if how == numbers.howSet then pure given
        else return some numbers.einval
      modifyThread signals tid fun state => { state with mask := blockable signals mask }
    if old != 0 then write emu old (encodeMask signals emu previous size)
    pure none
  catch _ => pure (some numbers.efault)

/-- The thread that runs takes what it may have now, from where it is, as after a function of the host, which it called, that
unblocked a signal returns. -/
def deliverPending (signals : Signals) (emu : Emu) : IO Unit :=
  deliver signals emu false

/-- A thread that has to wake for a signal: it isn't waiting any longer, and what it was doing says so, or starts again if it may. A
stop of its tracer and the wait of the parent of `vfork` aren't for a signal to end, and it goes on once nothing else holds it. -/
private def interrupt (signals : Signals) (emu : Emu) (tid : Nat) (restart : Bool) : IO Unit := do
  let table ← emu.taskTable.get
  let interruptible (waiter : FutexWaiter) : Bool := waiter.thread == tid && !uninterruptible waiter.space
  if !table.futexes.any interruptible && !table.waiters.any (·.thread == tid) then return
  emu.taskTable.set { table with futexes := table.futexes.filter (!interruptible ·), waiters := table.waiters.filter (·.thread != tid) }
  let spaces := (table.futexes.filter interruptible).map (·.space)
  let state ← threadOf signals tid
  match state.last, restart && (state.last.map (·.restartable)).getD false with
  | some last, true =>
    let width := signals.architecture.bits
    let (_, _, result) := syscallRegisters emu.config.syscallAbi
    -- It runs again with its arguments as they were, of which `a3` is one on MIPS, rather than what a result would make of it.
    setThreadReg emu tid ⟨result, .imm width, 0, false⟩ (wordOfWidth width last.result)
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == tid then { context with pc := last.pc, pending := none, skip := none } else context
  | _, _ =>
    setSyscallResult emu tid (.error (signals.numbers).eintr)
    -- A `sigtimedwait` ends with that too, unless what it waits for is pending.
    if let some (set, _) := state.waiting then
      let group := (table.find? tid).map (·.group) |>.getD tid
      let shared := (← signals.table.get).groupPending.getD group []
      unless (state.pending ++ shared).any fun info => bitOf info.signal &&& set != 0 do
        modifyThread signals tid fun state => { state with waiting := none }
  (← signals.interrupted.get) emu tid restart spaces
  wakeThread emu tid

/-- A signal is sent to a thread. -/
private def sendToThread (signals : Signals) (emu : Emu) (tid group : Nat) (info : SignalInfo) : IO Unit := do
  -- SIGCONT lets a stopped process go on as it is sent, whatever becomes of it after.
  if info.signal == (signals.numbers).cont then (← signals.jobControl.get) emu group info.signal
  let state ← threadOf signals tid
  let bit := bitOf info.signal
  -- What is sent to a tracee waits to be delivered, as that stops it, whatever it would have come to.
  if info.signal != (signals.numbers).kill && ((← (← signals.tracer.get) tid).isSome) then
    modifyThread signals tid fun state => { state with pending := state.pending ++ [info] }
    if (← thread emu) != tid || (← emu.taskTable.get).blocked tid then interrupt signals emu tid true
    return
  let realTime := info.signal ≥ 32
  -- Of one that isn't of real time one at most is pending.
  let already := !realTime && state.pending.any (·.signal == info.signal)
  let waitingFor := match state.waiting with
    | some (set, _) => set &&& bit != 0
    | none => false
  if bit &&& state.mask != 0 || waitingFor then
    unless already do modifyThread signals tid fun state => { state with pending := state.pending ++ [info] }
    if waitingFor then
      let table ← emu.taskTable.get
      emu.taskTable.set { table with futexes := table.futexes.filter fun waiter => waiter.thread != tid || uninterruptible waiter.space }
      wakeThread emu tid
    return
  match ← dispositionOf signals group info.signal with
  | .ignore => pure ()
  | .stop => (← signals.jobControl.get) emu group info.signal
  | .terminate => kill emu group info.signal
  | .handle action =>
    unless already do modifyThread signals tid fun state => { state with pending := state.pending ++ [info] }
    -- The thread that is current may wait too, as a timer comes while nothing can run: what woke it has it take what came, as a switch
    -- to it would.
    if (← thread emu) != tid || (← emu.taskTable.get).blocked tid then interrupt signals emu tid (hasFlag action.flags saRestart)

/-- A signal is sent to a process: to a thread of it that doesn't block it, its first if that one doesn't. A process that has exited, a
zombie, takes nothing. -/
private def sendToGroup (signals : Signals) (emu : Emu) (group : Nat) (info : SignalInfo) : IO Unit := do
  let tasks := (← emu.taskTable.get).tasks.filter fun task => task.group == group && task.status.isNone
  if tasks.isEmpty then return
  let bit := bitOf info.signal
  let leaderFirst := (tasks.filter (·.tid == group)) ++ tasks.filter (·.tid != group)
  let table ← signals.table.get
  let takes (tid : Nat) : Bool :=
    let state := table.threads.getD tid {}
    bit &&& state.mask == 0 || match state.waiting with
      | some (set, _) => set &&& bit != 0
      | none => false
  match leaderFirst.find? (fun task => takes task.tid) with
  | some task => sendToThread signals emu task.tid group info
  | none =>
    if info.signal == (signals.numbers).cont then (← signals.jobControl.get) emu group info.signal
    let realTime := info.signal ≥ 32
    let shared := table.groupPending.getD group []
    unless !realTime && shared.any (·.signal == info.signal) do
      signals.table.modify fun table => { table with groupPending := table.groupPending.insert group (shared ++ [info]) }

/-- Sends a signal to a thread of a process, or to the process, as `tgkill` and `kill` do. -/
def send (signals : Signals) (emu : Emu) (tid : Option Nat) (group : Nat) (info : SignalInfo) : IO Unit := do
  match tid with
  | some tid => sendToThread signals emu tid group info
  | none => sendToGroup signals emu group info
  (← signals.sent.get) emu

/-- Sends a signal to a thread that it can't keep from itself, as Linux has `force_sig_info_to_task` do for `SECCOMP_RET_TRAP`: if the
thread blocks it or its process ignores it, the thread no longer blocks it and the process has the default action for it. -/
def force (signals : Signals) (emu : Emu) (tid group : Nat) (info : SignalInfo) : IO Unit := do
  let blocked := bitOf info.signal &&& (← threadOf signals tid).mask != 0
  if blocked || (← actionOf signals group info.signal).handler == 1 then
    signals.table.modify fun table => { table with actions := table.actions.erase (group, info.signal) }
    if blocked then modifyThread signals tid fun state => { state with mask := state.mask ^^^ bitOf info.signal }
  signals.send emu (some tid) group info

/-- A timer of `timer_create` of a process expired `more` times again: if its signal is still pending, for the process or a thread of
it, that signal says so, as Linux has one signal of a timer pending at most. Whether it was pending. -/
def addOverrun (signals : Signals) (emu : Emu) (group signal id more : Nat) : IO Bool := do
  let ofTimer (info : SignalInfo) : Bool := info.signal == signal && match info.detail with
    | .timer which _ _ => which == id
    | _ => false
  let add (info : SignalInfo) : SignalInfo := match info.detail with
    | .timer which overrun value => if ofTimer info then { info with detail := .timer which (overrun + more) value } else info
    | _ => info
  let table ← signals.table.get
  let shared := table.groupPending.getD group []
  if shared.any ofTimer then
    signals.table.modify fun table => { table with groupPending := table.groupPending.insert group (shared.map add) }
    return true
  let tids := ((← emu.taskTable.get).tasks.filter fun task => task.group == group && task.status.isNone).map (·.tid)
  let some tid := tids.find? fun tid => (table.threads.getD tid {}).pending.any ofTimer | return false
  modifyThread signals tid fun state => { state with pending := state.pending.map add }
  pure true

/-- The signals that are pending for a thread, of its own and of its process, as bits. -/
def pendingBits (signals : Signals) (tid group : Nat) : IO Nat := do
  let table ← signals.table.get
  let own := (table.threads.getD tid {}).pending
  let shared := table.groupPending.getD group []
  pure ((own ++ shared).foldl (fun bits info => bits ||| bitOf info.signal) 0)

/-- Takes the lowest signal of `mask` that is pending for a thread, of its own first and then of its process, as `signalfd` reads it. -/
def takePending (signals : Signals) (tid group mask : Nat) : IO (Option SignalInfo) := do
  let table ← signals.table.get
  let own := (table.threads.getD tid {}).pending
  let shared := table.groupPending.getD group []
  let lowest (list : List SignalInfo) : Option SignalInfo :=
    (list.filter fun info => bitOf info.signal &&& mask != 0).foldl (fun best info =>
      match best with
      | some found => if info.signal < found.signal then some info else best
      | none => some info) none
  match lowest own, lowest shared with
  | some info, _ =>
    modifyThread signals tid fun state => { state with pending := state.pending.eraseP (·.signal == info.signal) }
    (← signals.taken.get) group info
    pure (some info)
  | none, some info =>
    signals.table.modify fun table => { table with groupPending := table.groupPending.insert group (shared.eraseP (·.signal == info.signal)) }
    (← signals.taken.get) group info
    pure (some info)
  | none, none => pure none

/-- A thread has `mask` while it waits in a call, as `ppoll`, `pselect6` and `epoll_pwait` have it, and its own again once the call is
over, as `sigsuspend` has it. -/
def suspendWith (signals : Signals) (tid mask : Nat) : IO Unit :=
  modifyThread signals tid fun state =>
    if state.suspended.isSome then state else { state with suspended := some state.mask, mask := blockable signals mask }

/-- What is pending for a thread that its mask lets through and that its process ignores is gone, as delivery would have it, unless
a tracer has it stop for that. -/
private def dropIgnored (signals : Signals) (tid group : Nat) : IO Unit := do
  if (← (← signals.tracer.get) tid).isSome then return
  let mask := (← threadOf signals tid).mask
  let kept (info : SignalInfo) : IO Bool := do
    if bitOf info.signal &&& mask != 0 then return true
    match ← dispositionOf signals group info.signal with
    | .ignore => pure false
    | _ => pure true
  let table ← signals.table.get
  let own ← (table.threads.getD tid {}).pending.filterM kept
  let shared ← (table.groupPending.getD group []).filterM kept
  modifyThread signals tid fun state => { state with pending := own }
  signals.table.modify fun table => { table with groupPending := table.groupPending.insert group shared }

/-- Whether a signal is pending for a thread that its mask lets through, which a call that waits with a mask of its own, as `ppoll`
does, ends with `EINTR` for rather than waiting. What it ignores is gone first, and doesn't end the call. -/
def unblockedPending (signals : Signals) (tid group : Nat) : IO Bool := do
  dropIgnored signals tid group
  let pending ← signals.pendingBits tid group
  pure (pending - (pending &&& (← threadOf signals tid).mask) != 0)

/-- Where a thread blocks that waits for no address: no guest can wake it, as this isn't memory that it has. -/
private def waitAddress (tid : Nat) : Nat := 2 ^ 64 - 8 * (tid + 1)

private def blockOnSignal (emu : Emu) (tid space : Nat) (timed : Bool) (deadline : Option Nat := none) : IO Unit := do
  emu.taskTable.modify (·.futexWait { thread := tid, space, address := waitAddress tid, bitset := 2 ^ 32 - 1, timed, deadline })
  emu.stopped.set true

/-- What a `sigtimedwait` that was woken comes to, when it runs again: the lowest signal that it waits for, of the thread's own
first, as Linux takes it. -/
private def finishWait (signals : Signals) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  let state ← threadOf signals tid
  let some (set, address) := state.waiting | return
  let task ← currentTask emu
  modifyThread signals tid fun state => { state with waiting := none }
  match ← takePending signals tid task.group set with
  | none => setSyscallResult emu tid (.error (signals.numbers).eagain)
  | some info =>
    if address != 0 then
      try
        write emu address (ByteArray.mk (Array.replicate 128 0))
        writeInfo signals emu address info
      catch _ => pure ()
    setSyscallResult emu tid (.ok info.signal)

/-- Fills in a `siginfo_t` from what `waitpid` reports of a child. -/
private def writeChildInfo (signals : Signals) (emu : Emu) (address child status : Nat) : IO Unit := do
  let signaled := status % 128 != 0
  write emu address (ByteArray.mk (Array.replicate 128 0))
  writeInfo signals emu address
    ⟨(signals.numbers).chld, if signaled then 2 else 1, .child child 0 (if signaled then status % 128 else status / 256 % 256)⟩

/-- A `waitid` that blocked has been woken, with what a `wait4` is given: it is what it says that it is. -/
private def finishChildWait (signals : Signals) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  let some address := (← threadOf signals tid).waitingChild | return
  modifyThread signals tid fun state => { state with waitingChild := none }
  let width := signals.architecture.bits
  let (_, _, resultRegister) := syscallRegisters emu.config.syscallAbi
  let result ← registerValue emu width resultRegister
  -- What it has if something interrupted it is an error, which stays. A child has an id much less than an error.
  if result ≥ 2 ^ (width - 1) || result == 0 then return
  -- And where an error is flagged, the result is only a number.
  let flagged ← match signals.architecture with
    | .mips .. => registerValue emu width "R7"
    | .powerpc .. => registerValue emu 1 "CR0UN"
    | _ => pure 0
  if flagged != 0 then return
  let status ← readNumber emu (address + (if width == 64 then 16 else 12) + 8) 4
  writeChildInfo signals emu address result status
  setSyscallResult emu tid (.ok 0)

/-- A `sigsuspend` that is over and that no handler ran for has the mask that it had. -/
private def endSuspend (signals : Signals) (emu : Emu) : IO Unit := do
  if ← stopped emu then return
  let tid ← thread emu
  if let some mask := (← threadOf signals tid).suspended then
    modifyThread signals tid fun state => { state with mask, suspended := none }

/-- A thread that runs now takes what came for it in the meantime. -/
def switchedIn (signals : Signals) (emu : Emu) : IO Unit := do
  finishWait signals emu
  finishChildWait signals emu
  deliver signals emu false
  endSuspend signals emu

/-- A system call ends. -/
def afterCall (signals : Signals) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  -- What was just made has the mask of what made it.
  let table ← emu.taskTable.get
  let known := (← signals.table.get).threads
  let unknown := table.tasks.filter fun task => !known.contains task.tid
  if !unknown.isEmpty then
    let mask := (known.getD tid {}).mask
    for task in unknown do
      modifyThread signals task.tid fun state => { state with mask }
  deliver signals emu true
  endSuspend signals emu

/-- A guest faulted, and it may have a handler for that. Whether it does. -/
def faulted (signals : Signals) (emu : Emu) (fault : MemoryFault) : IO Bool := do
  let task ← currentTask emu
  let numbers := signals.numbers
  let tid ← thread emu
  let state ← threadOf signals tid
  let code := if (lookupRegion (← emu.regions.get) fault.address).isSome then 2 else 1
  let info : SignalInfo := ⟨numbers.segv, code, .fault fault.address⟩
  let fail (why : String) : IO Bool := do
    signals.failures.modify (·.push (.unhandled tid fault.pc fault.address why))
    pure false
  -- A tracee stops for it, before anything is made of it.
  if ← (← signals.intercept.get) emu tid info then return true
  if bitOf numbers.segv &&& state.mask != 0 then return ← fail "SIGSEGV is blocked"
  match ← dispositionOf signals task.group numbers.segv with
  | .handle action =>
    let resume ← emu.pc.get
    let skip ← emu.skipCode.get
    match ← (enterHandler signals emu tid info action resume skip).toBaseIO with
    | .ok handler =>
      emu.pc.set handler
      emu.pendingRef.set none
      emu.skipCode.set none
      pure true
    | .error error =>
      signals.failures.modify (·.push (.handlerEntry tid numbers.segv (toString error)))
      pure false
  | .ignore =>
    if ← signals.skipIgnoredFaults.get then
      match ← nextInstruction emu fault.pc with
      | some next =>
        signals.failures.modify (·.push (.skipped tid fault.pc fault.address))
        emu.pc.set next
        emu.pendingRef.set none
        emu.skipCode.set none
        emu.stopped.set false
        pure true
      | none => fail "SIGSEGV is ignored, and what faulted can't be decoded to go past it"
    else fail "SIGSEGV is ignored"
  -- SIGSEGV doesn't stop by default.
  | .terminate | .stop => fail "nothing handles SIGSEGV"

/-- The parent of a process that is over hears of it, as Linux's `do_notify_parent` has it: it is sent the exit signal of the process,
which is SIGCHLD unless `clone` asked for another, or for none. -/
def notifyParent (signals : Signals) (emu : Emu) (group status : Nat) : IO Unit := do
  let table ← emu.taskTable.get
  let some task := table.find? group | return
  if task.parent == 0 then return
  let signal := task.exitSignal.getD (signals.numbers).chld
  if signal == 0 || signal > (signals.numbers).count then return
  -- A parent that ignores SIGCHLD isn't sent it, as Linux has it.
  if signal == (signals.numbers).chld && (← actionOf signals task.parent signal).handler == 1 then return
  let signaled := status % 128 != 0
  let info : SignalInfo :=
    ⟨signal, if signaled then 2 else 1, .child group 0 (if signaled then status % 128 else status / 256 % 256)⟩
  -- One that waits for it is woken by that, and hears of it when it runs.
  let parents := (table.tasks.filter fun other => other.group == task.parent && other.status.isNone)
  let waiting := parents.any fun other => table.waiters.any (·.thread == other.tid)
  if waiting then
    match parents.find? (·.tid == task.parent) with
    | some leader => modifyThread signals leader.tid fun state => { state with pending := state.pending ++ [info] }
    | none => pure ()
  else sendToGroup signals emu task.parent info

/-- A process is over, which its parent hears of now, unless a process other than its parent traces it: that one hears of it first,
and `Bap.Linux.Ptrace` tells the parent once it has waited for it. -/
def processExited (signals : Signals) (emu : Emu) (group status : Nat) : IO Unit := do
  if let some tracer := ← (← signals.tracer.get) group then
    if ((← emu.taskTable.get).find? group).all (·.parent != tracer) then return
  notifyParent signals emu group status

/-- Whether a process doesn't wait for its children, which go as they end without a wait, as Linux has it: it ignores `SIGCHLD`, or its
action has `SA_NOCLDWAIT`. What it does by default is to ignore it, which isn't this. -/
def reapsChildren (signals : Signals) (group : Nat) : IO Bool := do
  let action ← actionOf signals group (signals.numbers).chld
  pure (action.handler == 1 || action.flags &&& (signals.numbers).saNoCldWait != 0)

/-- A new process has what its parent has, and its thread what the thread that made it has, with nothing pending: in a copy of the memory
it goes back from the handlers that thread is in. As Linux has it, one that shares the memory has no alternate stack, which would be
that of its parent, unless it is a child of `vfork`, which runs on the stacks of its parent until it runs a program. -/
def forked (signals : Signals) (emu : Emu) (parent child : Nat) : IO Unit := do
  let tid ← thread emu
  let state ← threadOf signals tid
  let table ← emu.taskTable.get
  let shared := (table.tasks.find? (·.tid == child)).map (·.space) == some (← currentTask emu).space
  let vforked := table.futexes.any fun waiter => waiter.thread == tid && waiter.space == vforkSpace && waiter.address == child
  let alternate := if shared && !vforked then noAlternate else state.alternate
  signals.table.modify fun table =>
    { table with
      actions := table.actions.fold (init := table.actions) fun actions key action =>
        if key.1 == parent then actions.insert (child, key.2) action else actions
      threads := table.threads.insert child { state with pending := [], alternate, waiting := none, waitingChild := none } }

/-- `execve`: what had a handler goes back to the default, as the handler isn't there any more, and what was ignored stays so. -/
def executed (signals : Signals) (group tid : Nat) : IO Unit := do
  signals.table.modify fun table =>
    { table with
      actions := table.actions.filter fun key action => key.1 != group || action.handler == 1 }
  modifyThread signals tid fun state => { state with frames := [], alternate := noAlternate, suspended := none, waiting := none, waitingChild := none }

private def readAction (signals : Signals) (emu : Emu) (address : Nat) : IO SignalAction := do
  let word := signals.architecture.bits / 8
  let (flagsAt, flagsSize, handlerAt, restorerAt, maskAt) := actionOffsets signals.architecture
  let handler ← readNumber emu (address + handlerAt) word
  let flags ← readNumber emu (address + flagsAt) (if flagsSize == 0 then word else flagsSize)
  let restorer ← match restorerAt with
    | some at_ => readNumber emu (address + at_) word
    | none => pure 0
  pure { handler, flags, restorer, mask := ← readMask signals emu (address + maskAt) (maskBytes signals.architecture) }

private def writeAction (signals : Signals) (emu : Emu) (address : Nat) (action : SignalAction) : IO Unit := do
  let word := signals.architecture.bits / 8
  let (flagsAt, flagsSize, handlerAt, restorerAt, maskAt) := actionOffsets signals.architecture
  write emu (address + handlerAt) (encodeNumber emu word action.handler)
  write emu (address + flagsAt) (encodeNumber emu (if flagsSize == 0 then word else flagsSize) action.flags)
  if let some at_ := restorerAt then write emu (address + at_) (encodeNumber emu word action.restorer)
  write emu (address + maskAt) (encodeMask signals emu action.mask (maskBytes signals.architecture))

/-- Back from a handler, by what its frame and its context say. -/
private def sigreturn (signals : Signals) (emu : Emu) : IO SyscallAction := do
  let architecture := signals.architecture
  let layout := layoutOf architecture
  let width := architecture.bits
  let tid ← thread emu
  let state ← threadOf signals tid
  let sp ← registerValue emu width (stackRegister architecture)
  let inAlternate := onAlternateStack state.alternate sp
  -- A handler that left by `longjmp` left its frame, which is further down this stack.
  let live := state.frames.dropWhile fun frame => frame.onAlternate == inAlternate && frame.entry + 64 < sp
  match live with
  | [] =>
    signals.failures.modify (·.push (.sigreturn tid "no frame of a handler to go back to"))
    kill emu (← currentTask emu).group (signals.numbers).segv
    pure (.returnValue 0)
  | frame :: rest =>
    let memoryVar := emu.config.memory
    let current ← emu.state.get
    let memoryBinding := current.env.filter fun binding => binding.1 == memoryVar
    emu.state.set { env := frame.env ++ memoryBinding }
    let slotValue (at_ : Nat) : IO Nat := do
      pure ((← readNumber emu (frame.context + at_) layout.slot) % 2 ^ width)
    let mut failed := false
    try
      for (name, offset) in layout.registers do
        setReg emu ⟨name, .imm width, 0, false⟩ (wordOfWidth width (← slotValue offset))
      if let some at_ := layout.cpsr then
        let cpsr ← readNumber emu (frame.context + at_) 4
        setReg emu ⟨"ISET", .imm 1, 0, false⟩ (wordOfWidth 1 ((cpsr >>> 5) &&& 1))
      let pc ← slotValue layout.pc
      let mask ← readMask signals emu (frame.context + layout.mask) (maskBytes architecture)
      -- As Linux does, the alternate stack of the context, unless the stack it goes back to is on the one there is now, or its flags
      -- aren't taken.
      let word := width / 8
      let given := givenAlternate (← readNumber emu (frame.context + layout.stack) word)
        (← readNumber emu (frame.context + layout.stackSize) word) (← readNumber emu (frame.context + layout.stackFlags) 4)
      let back ← registerValue emu width (stackRegister architecture)
      modifyThread signals tid fun state =>
        { state with
          mask := blockable signals mask, frames := rest
          alternate := match given with
            | some alternate => if onAlternateStack state.alternate back then state.alternate else alternate
            | none => state.alternate }
      emu.redirect.set (some (match architecture with | .arm => pc - pc % 2 | _ => pc))
      emu.skipCode.set frame.skip
    catch error =>
      signals.failures.modify (·.push (.sigreturn tid s!"its context can't be read: {error}"))
      failed := true
    if failed then
      kill emu (← currentTask emu).group (signals.numbers).segv
      return .returnValue 0
    -- As a kernel does: what was loaded exclusively isn't held across this.
    if (Bil.lookup (← emu.state.get).env (exclusiveMonitor width)).toOption.isSome then
      setReg emu (exclusiveMonitor width) (wordOfWidth width 0)
    let (_, _, result) := syscallRegisters emu.config.syscallAbi
    pure (.returnValue (← registerValue emu width result))

/-- A system call starts, which a signal that interrupts it starts again from, of one that may be: what serves a call before `serve` does
says so. -/
def noteCall (signals : Signals) (emu : Emu) (number : Nat) : IO Unit := do
  if (callsOf signals.architecture).restartable.contains number then
    let (_, _, resultRegister) := syscallRegisters emu.config.syscallAbi
    let result ← registerValue emu signals.architecture.bits resultRegister
    let pc ← emu.pc.get
    modifyThread signals (← thread emu) fun state => { state with last := some { pc, result, restartable := true } }

/-- What serves the system calls of signals, before those of the kernel and of tasks. -/
def serve (signals : Signals) (emu : Emu) : IO Unit := do
  let architecture := signals.architecture
  let calls := callsOf architecture
  let numbers := numbersOf architecture
  let width := architecture.bits
  let (_, _, resultRegister) := syscallRegisters emu.config.syscallAbi
  let fail (current : Emu) (errno : Nat) : IO SyscallAction := syscallReturn current (.error errno)
  let valid (signal : Nat) : Bool := signal ≥ 1 && signal ≤ numbers.count
  let selfInfo (current : Emu) (signal code value : Nat) : IO SignalInfo := do
    pure ⟨signal, code, .sent (← currentTask current).group 0 value⟩
  let _ ← onSyscall emu fun current number args => do
    let arg (index : Nat) : Nat := args.getD index 0
    let signedCode (value : Nat) : Nat := 2 ^ 32 - value
    let tid ← thread current
    let task ← currentTask current
    if calls.restartable.contains number then
      let result ← registerValue current width resultRegister
      let pc ← current.pc.get
      modifyThread signals tid fun state => { state with last := some { pc, result, restartable := true } }
    -- What started a call before this isn't where this one starts again.
    else if (← threadOf signals tid).last.isSome then modifyThread signals tid fun state => { state with last := none }
    if number == calls.sigaction then
      let signal := arg 0
      let (act, old, size) := (arg 1, arg 2, arg 3)
      if !valid signal || size != maskBytes architecture then return ← fail current numbers.einval
      if signal == numbers.kill || signal == numbers.stop then
        if act != 0 then return ← fail current numbers.einval
      try
        if old != 0 then writeAction signals current old (← actionOf signals task.group signal)
        if act != 0 then
          let action ← readAction signals current act
          let action := { action with mask := blockable signals action.mask }
          signals.table.modify fun table =>
            { table with
              actions := if action.handler == 0 then table.actions.erase (task.group, signal)
                else table.actions.insert (task.group, signal) action }
          -- What is ignored now isn't pending any more.
          if ((action.handler == 1) || (action.handler == 0 && numbers.ignored.contains signal)) then
            let notThis (info : SignalInfo) : Bool := info.signal != signal
            signals.table.modify fun table =>
              { table with
                groupPending := table.groupPending.insert task.group ((table.groupPending.getD task.group []).filter notThis) }
            for other in (← current.taskTable.get).tasks do
              if other.group == task.group then
                modifyThread signals other.tid fun state => { state with pending := state.pending.filter notThis }
        syscallReturn current (.ok 0)
      catch _ => fail current numbers.efault
    else if number == calls.sigprocmask then
      if arg 3 != maskBytes architecture then return ← fail current numbers.einval
      match ← signals.changeMask current tid (arg 0) (arg 1) (arg 2) with
      | none => syscallReturn current (.ok 0)
      | some error => fail current error
    else if calls.returns.contains number then
      sigreturn signals current
    else if number == calls.kill then
      -- A `pid_t`: a process, its own process group of 0, every process but the first and itself of -1, and a group of the rest.
      let target := arg 0 % 2 ^ 32
      let signal := arg 1 % 2 ^ 32
      if signal != 0 && !valid signal then return ← fail current numbers.einval
      -- A process that has exited is there until it is reaped, a zombie, which takes nothing that is sent.
      let present := (← current.taskTable.get).present
      let groups ← if target == 0 then (← signals.members.get) ((← (← signals.pgidOf.get) task.group))
        else if target == 2 ^ 32 - 1 then pure (((present.map (·.group)).eraseDups).filter fun group => group != task.group && group != 1)
        else if target ≥ 2 ^ 31 then (← signals.members.get) (2 ^ 32 - target)
        -- A thread's id is its process's, as Linux has it.
        else pure ((present.find? (·.tid == target)).map (·.group)).toList
      if groups.isEmpty then return ← fail current numbers.esrch
      if signal != 0 then
        for group in groups do sendToGroup signals current group (← selfInfo current signal 0 0)
      syscallReturn current (.ok 0)
    else if number == calls.tkill || number == calls.tgkill then
      let (expected, target, signal) := if number == calls.tkill then (none, arg 0, arg 1) else (some (arg 0), arg 1, arg 2)
      if signal != 0 && !valid signal then return ← fail current numbers.einval
      -- A leader that has exited is there until it is reaped, and takes nothing that is sent.
      match (← current.taskTable.get).present.find? (·.tid == target) with
      | some { status, group, .. } =>
        if expected.isSome && expected != some group then return ← fail current numbers.esrch
        if signal != 0 && status.isNone then sendToThread signals current target group (← selfInfo current signal (signedCode 6) 0)
        syscallReturn current (.ok 0)
      | none => fail current numbers.esrch
    else if number == calls.queueinfo then
      let (target, signal, address) := (arg 0, arg 1, arg 2)
      if !valid signal then return ← fail current numbers.einval
      let word := width / 8
      let base := if word == 8 then 16 else 12
      try
        let code ← readNumber current (address + (if isMipsArchitecture architecture then 4 else 8)) 4
        let value ← readNumber current (address + base + 8) word
        match (← current.taskTable.get).present.find? (·.tid == target) with
        | some { group, .. } =>
          sendToGroup signals current group ⟨signal, code, .sent task.group 0 value⟩
          syscallReturn current (.ok 0)
        | none => fail current numbers.esrch
      catch _ => fail current numbers.efault
    else if number == calls.pending then
      let state ← threadOf signals tid
      let shared := (← signals.table.get).groupPending.getD task.group []
      let bits := (state.pending ++ shared).foldl (fun mask info => mask ||| bitOf info.signal) 0
      try
        write current (arg 0) (encodeMask signals current (bits &&& state.mask) (arg 1))
        syscallReturn current (.ok 0)
      catch _ => fail current numbers.efault
    else if calls.timedwait.contains number then
      let (set, infoAddress, timeout, size) := (arg 0, arg 1, arg 2, arg 3)
      if size != maskBytes architecture then return ← fail current numbers.einval
      try
        let wanted := blockable signals (← readMask signals current set size)
        -- The size of the fields of its timeout is that of a word, or 64 bits by the numbers of time64. One that Linux doesn't take
        -- fails before what is pending is looked at.
        let span ← if timeout == 0 then pure none else do
          let some span ← readSpan current timeout (if number == 421 || number == 4421 then 8 else width / 8)
            | return ← fail current numbers.einval
          pure (some span)
        modifyThread signals tid fun state => { state with waiting := some (wanted, infoAddress) }
        let state ← threadOf signals tid
        let shared := (← signals.table.get).groupPending.getD task.group []
        if (state.pending ++ shared).any fun info => bitOf info.signal &&& wanted != 0 then
          finishWait signals current
          pure (.returnValue (← registerValue current width resultRegister))
        else
          if span == some 0 then
            modifyThread signals tid fun state => { state with waiting := none }
            fail current numbers.eagain
          else
            -- Until its time, by the clock of the machine, after which it has nothing: `EAGAIN`.
            let now ← match ← current.now.get with
              | some clock => clock
              | none => pure 0
            blockOnSignal current tid task.space (timeout != 0) (span.map (now + ·))
            fail current numbers.eagain
      catch _ =>
        modifyThread signals tid fun state => { state with waiting := none }
        fail current numbers.efault
    else if number == calls.suspend then
      let (set, size) := (arg 0, arg 1)
      if size != maskBytes architecture then return ← fail current numbers.einval
      try
        let given ← readMask signals current set size
        modifyThread signals tid fun state =>
          { state with suspended := some state.mask, mask := blockable signals given }
        unless ← signals.unblockedPending tid task.group do blockOnSignal current tid task.space false
        fail current numbers.eintr
      catch _ => fail current numbers.efault
    else if some number == calls.pause then
      unless ← signals.unblockedPending tid task.group do blockOnSignal current tid task.space false
      fail current numbers.eintr
    else if number == calls.waitid then
      let (kind, id, infoAddress, options) := (arg 0, arg 1, arg 2, arg 3)
      -- By any, or by one, of what it can tell: there are no groups of processes. It reports what has exited, as nothing stops.
      let wnohang := 1
      let wexited := 4
      if options &&& wexited == 0 || kind > 1 then return ← fail current numbers.einval
      let wanted := if kind == 1 then some id else none
      let table ← current.taskTable.get
      match table.poll task.group wanted with
      | .noChild => fail current 10
      | .exited child status =>
        try
          if infoAddress != 0 then writeChildInfo signals current infoAddress child status
          current.taskTable.set (table.reap child)
          syscallReturn current (.ok 0)
        catch _ => fail current numbers.efault
      | .running =>
        if options &&& wnohang != 0 then
          try
            if infoAddress != 0 then write current infoAddress (ByteArray.mk (Array.replicate 128 0))
            syscallReturn current (.ok 0)
          catch _ => fail current numbers.efault
        else if infoAddress == 0 then
          -- It wants nothing back, and this has nowhere to keep what it is given.
          fail current numbers.einval
        else
          -- As a `wait4` waits: its status goes where a `siginfo_t` has one, from where `finishChildWait` makes the rest of that.
          let statusAt := infoAddress + (if width == 64 then 16 else 12) + 8
          current.taskTable.set { table with waiters := table.waiters ++ [{ thread := tid, target := wanted, statusAddress := some statusAt }] }
          current.stopped.set true
          modifyThread signals tid fun state => { state with waitingChild := some infoAddress }
          syscallReturn current (.ok 0)
    else if number == calls.altstack then
      let (given, old) := (arg 0, arg 1)
      let layout := layoutOf architecture
      let stackFlags := layout.stackFlags - layout.stack
      let stackSize := layout.stackSize - layout.stack
      let word := width / 8
      let state ← threadOf signals tid
      let sp ← registerValue current width (stackRegister architecture)
      let (base, size, flags) := state.alternate
      let inside := onAlternateStack state.alternate sp
      try
        if old != 0 then
          write current old (encodeNumber current word base)
          let oldFlags := (if size == 0 then ssDisable else if inside then ssOnStack else 0) ||| flags &&& ssAutoDisarm
          write current (old + stackFlags) (encodeNumber current 4 oldFlags)
          write current (old + stackSize) (encodeNumber current word size)
        if given != 0 then
          if inside then return ← fail current numbers.eperm
          let newBase ← readNumber current given word
          let newFlags ← readNumber current (given + stackFlags) 4
          let newSize ← readNumber current (given + stackSize) word
          match givenAlternate newBase newSize newFlags with
          | some alternate => modifyThread signals tid fun state => { state with alternate }
          | none => return ← fail current numbers.einval
        syscallReturn current (.ok 0)
      catch _ => fail current numbers.efault
    else
      pure .default
  emu.afterSyscall.set (some (afterCall signals emu))
  emu.switchedIn.set (some (switchedIn signals emu))
  emu.faultHandler.set (some (faulted signals emu))
  emu.processExited.set (some (processExited signals emu))
  emu.processHooks.modify ((fun parent child => forked signals emu parent child) :: ·)
  emu.leaderTaken.modify (· ++ [fun former leader =>
    signals.table.modify fun table => { table with threads := moveThread table.threads former leader }])

/-- What a checkpoint knows it by. -/
def modelId : String := "bap.signals"

def save (signals : Signals) : IO ByteArray := do
  pure (Encoding.encode (← signals.table.get))

def load (signals : Signals) (data : ByteArray) : IO Unit := do
  signals.table.set (← IO.ofExcept (Encoding.decode data))

end Signals

end Bap.Linux
