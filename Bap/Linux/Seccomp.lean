import Bap.Linux.Ptrace
import Bap.Linux.Calls

/-! # seccomp

What a thread may call, as `seccomp(2)` and `prctl(PR_SET_SECCOMP)` say: strict mode, in which only `read`, `write`, `exit` and
`sigreturn` are let through and anything else kills the process with `SIGKILL`, and filters of classic BPF, which each call of the
thread runs over its `struct seccomp_data` before anything serves it, once its tracer saw it start, and whose result says what becomes
of the call. Of all the filters of a thread, the result that comes first comes of it: `SECCOMP_RET_KILL_PROCESS`, `KILL_THREAD`,
`TRAP`, which sends `SIGSYS` with what the call was, `ERRNO`, `USER_NOTIF`, `TRACE`, which stops a tracee for its tracer as
`PTRACE_EVENT_SECCOMP`, `LOG` and `ALLOW`. A thread that is made has the filters, the mode and `no_new_privs` of the one that made it, and
they stay over `execve`.

There is no listener of `SECCOMP_FILTER_FLAG_NEW_LISTENER`, so that `USER_NOTIF` gives `ENOSYS` as it does without one. Everyone is root
here, so that a filter doesn't need `no_new_privs`. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

namespace Seccomp

/-- An instruction of classic BPF, as `struct sock_filter` has it. -/
structure Insn where
  code : Nat
  jt : Nat
  jf : Nat
  k : Nat
  deriving DecidableEq, Repr

/-- What seccomp keeps: each filter that was installed, which the threads that have it share, and of each thread, the filters that it
has, the newest first, whether it is in strict mode, whether it set `no_new_privs`, and whether its call was decided as
`SECCOMP_RET_TRACE` and its tracer let it go on, of which it is decided again. -/
structure State where
  programs : Array (Array Insn) := #[]
  filters : Std.HashMap Nat (List Nat) := {}
  strict : Std.HashSet Nat := {}
  noNewPrivs : Std.HashSet Nat := {}
  traced : Std.HashSet Nat := {}

def modelId : String := "bap.seccomp"

/-! ### Classic BPF -/

/-- Whether a filter is one that seccomp takes: of 1 to 4096 instructions, each of those that it allows, with its loads in
`struct seccomp_data` and aligned, its scratch in the 16 words, its jumps forward and inside, no division by a constant 0 nor a shift by
32 or more, and a return at its end. -/
def valid (program : Array Insn) : Bool :=
  let size := program.size
  let fits (pc offset : Nat) : Bool := pc + 1 + offset < size
  let ok (insn : Insn) (pc : Nat) : Bool :=
    match insn.code with
    | 0x20 => insn.k < 64 && insn.k % 4 == 0
    | 0x80 | 0x81 | 0x00 | 0x01 | 0x07 | 0x87 | 0x06 | 0x16 => true
    | 0x60 | 0x61 | 0x02 | 0x03 => insn.k < 16
    | 0x04 | 0x0c | 0x14 | 0x1c | 0x24 | 0x2c | 0x3c | 0x44 | 0x4c | 0x54 | 0x5c | 0x6c | 0x7c | 0x84 | 0xa4 | 0xac => true
    | 0x34 => insn.k != 0
    | 0x64 | 0x74 => insn.k < 32
    | 0x05 => fits pc insn.k
    | 0x15 | 0x1d | 0x25 | 0x2d | 0x35 | 0x3d | 0x45 | 0x4d => fits pc insn.jt && fits pc insn.jf
    | _ => false
  0 < size && size ≤ 4096 && (program.back?.any fun insn => insn.code == 0x06 || insn.code == 0x16) &&
    program.zipIdx.all fun (insn, pc) => ok insn pc

/-- What a filter returns of the words of `struct seccomp_data`, by their offsets. It is `valid`, so that each jump goes forward, and it
ends within as many steps as it has instructions; a division by 0 that `X` has returns 0, as Linux has it. -/
def run (program : Array Insn) (word : Nat → Nat) : Nat := Id.run do
  let mut pc := 0
  let mut a := 0
  let mut x := 0
  let mut scratch : Array Nat := Array.replicate 16 0
  let wrap (value : Nat) : Nat := value % 2 ^ 32
  for _ in [0:program.size] do
    let some insn := program[pc]? | return 0
    let source := if insn.code &&& 0x08 != 0 then x else insn.k
    let next := pc + 1
    match insn.code with
    | 0x20 => a := word insn.k
    | 0x80 => a := 64
    | 0x81 => x := 64
    | 0x00 => a := insn.k
    | 0x01 => x := insn.k
    | 0x60 => a := scratch[insn.k]!
    | 0x61 => x := scratch[insn.k]!
    | 0x02 => scratch := scratch.set! insn.k a
    | 0x03 => scratch := scratch.set! insn.k x
    | 0x07 => x := a
    | 0x87 => a := x
    | 0x06 => return insn.k
    | 0x16 => return a
    | 0x04 | 0x0c => a := wrap (a + source)
    | 0x14 | 0x1c => a := wrap (a + 2 ^ 32 - source)
    | 0x24 | 0x2c => a := wrap (a * source)
    | 0x34 | 0x3c => if source == 0 then return 0 else a := a / source
    | 0x44 | 0x4c => a := a ||| source
    | 0x54 | 0x5c => a := a &&& source
    | 0x64 | 0x6c => a := wrap (a <<< (source % 32))
    | 0x74 | 0x7c => a := a >>> (source % 32)
    | 0x84 => a := wrap (2 ^ 32 - a)
    | 0xa4 | 0xac => a := a ^^^ source
    | _ => pure ()
    pc := match insn.code with
      | 0x05 => next + insn.k
      | 0x15 | 0x1d => next + if a == source then insn.jt else insn.jf
      | 0x25 | 0x2d => next + if a > source then insn.jt else insn.jf
      | 0x35 | 0x3d => next + if a ≥ source then insn.jt else insn.jf
      | 0x45 | 0x4d => next + if a &&& source != 0 then insn.jt else insn.jf
      | _ => next
  return 0

/-- Of the results of a call's filters, the one that comes first, as Linux has it: by its action as a signed number, the least first, and
of two of the same action the first. -/
def combine (results : List Nat) : Nat :=
  let rank (result : Nat) : Int :=
    let action := result &&& 0xffff0000
    if action ≥ 2 ^ 31 then Int.ofNat action - 2 ^ 32 else Int.ofNat action
  results.foldl (fun best result => if rank result < rank best then result else best) 0x7fff0000

/-! ### The machine's side -/

/-- `AUDIT_ARCH_*` of an architecture, which `struct seccomp_data` has. -/
def auditArch : Architecture → Nat
  | .x86_64 => 0xC000003E
  | .i686 => 0x40000003
  | .aarch64 => 0xC00000B7
  | .arm => 0x40000028
  | .riscv64 => 0xC00000F3
  | .riscv32 => 0x400000F3
  | .mips 32 big _ => if big then 0x00000008 else 0x40000008
  | .mips _ big _ => if big then 0x80000008 else 0xC0000008
  | .powerpc 32 big => if big then 0x00000014 else 0x40000014
  | .powerpc _ big => if big then 0x80000015 else 0xC0000015

/-- `exit` and the `sigreturn`s, which strict mode lets through with `read` and `write`. -/
private def strictCalls : Architecture → List Nat
  | .x86_64 => [60, 15]
  | .aarch64 | .riscv64 | .riscv32 => [93, 139]
  | .arm | .i686 => [1, 119, 173]
  | .mips 32 _ _ => [4001, 4119, 4193]
  | .mips _ _ _ => [5058, 5211]
  | .powerpc 32 _ => [1, 119, 172]
  | .powerpc _ _ => [1, 172]

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- `struct seccomp_data` of a call, in the order of the target's bytes: its number, the architecture, where it was made from, and its
six arguments. -/
def callData (architecture : Architecture) (number ip : Nat) (args : List Nat) : ByteArray :=
  let big := architecture.big
  let out := numberBytes big 4 number ++ numberBytes big 4 (auditArch architecture) ++ numberBytes big 8 ip
  (List.range 6).foldl (fun out index => out ++ numberBytes big 8 (args.getD index 0)) out

/-- The 32 bits of `struct seccomp_data` at an offset, as a load of a filter reads them. -/
def wordAt (architecture : Architecture) (data : ByteArray) (offset : Nat) : Nat :=
  numberOf architecture.big (data.extract offset (offset + 4))

/-- The instructions of `struct sock_fprog` at an address, if it is there to read. -/
private def readProgram (emu : Emu) (architecture : Architecture) (address : Nat) : IO (Array Insn) := do
  let big := architecture.big
  let word := architecture.bits / 8
  let length := numberOf big (← read emu address 2)
  let filter := numberOf big (← read emu (address + word) word)
  let bytes ← read emu filter (length * 8)
  pure ((Array.range length).map fun index =>
    let at_ := index * 8
    { code := numberOf big (bytes.extract at_ (at_ + 2)), jt := (bytes.get! (at_ + 2)).toNat, jf := (bytes.get! (at_ + 3)).toNat
      k := numberOf big (bytes.extract (at_ + 4) (at_ + 8)) })

/-- What seccomp of a machine has, and the architecture that it is of. -/
structure Seccomp where
  architecture : Architecture
  /-- The numbers of what it serves, `seccomp` and `prctl`, and of what strict mode lets through, `read` and `write`, by which a call
  of a thread with nothing of seccomp is passed on at once. -/
  calls : Std.HashMap Nat Call
  signals : Signals
  ptrace : Ptrace
  state : IO.Ref State
  /-- Of each thread with anything of seccomp in a call, the first id that the call can give a thread that it makes, which has what
  it has. Nothing is in the middle of a call when a checkpoint is made. -/
  spawning : IO.Ref (Std.HashMap Nat Nat)

namespace Seccomp

private def errno (seccomp : Seccomp) (number : Nat) : Nat :=
  match seccomp.architecture, number with
  | .mips .., 38 => 89
  | .mips .., 95 => 122
  | _, _ => number

private def fail (seccomp : Seccomp) (emu : Emu) (number : Nat) : IO (Option SyscallAction) := do
  pure (some (← syscallReturn emu (.error (seccomp.errno number))))

private def succeed (emu : Emu) (value : Nat := 0) : IO (Option SyscallAction) := do
  pure (some (← syscallReturn emu (.ok value)))

/-- The signal that a filter's `KILL` and `TRAP` send. -/
private def sigsys (seccomp : Seccomp) : Nat := if seccomp.architecture matches .mips .. then 12 else 31

/-- A filter for a thread, and of `TSYNC` for each of its process too, as long as what each has is what the thread had before, as
Linux asks: the thread that has something else otherwise, which `TSYNC_ESRCH` makes `ESRCH`. -/
private def install (seccomp : Seccomp) (emu : Emu) (tid flags : Nat) (program : Array Insn) : IO (Option SyscallAction) := do
  let state ← seccomp.state.get
  let before := state.filters.getD tid []
  let index := state.programs.size
  let chain := index :: before
  let threads ← if flags &&& 1 != 0 then do
      let table ← emu.taskTable.get
      let group ← match table.find? tid with
        | some task => pure task.group
        | none => pure tid
      pure ((table.tasks.filter fun task => task.group == group && task.status.isNone).map (·.tid))
    else pure [tid]
  -- Each has what the thread had, or what it had before that.
  if let some other := threads.find? fun thread => !(state.filters.getD thread []).isSuffixOf before then
    return ← if flags &&& 16 != 0 then seccomp.fail emu 3 else succeed emu other
  seccomp.state.set { state with
    programs := state.programs.push program
    filters := threads.foldl (fun filters thread => filters.insert thread chain) state.filters }
  succeed emu

/-- `seccomp(2)` and the options of `prctl` that are of it: `PR_GET_SECCOMP`, `PR_SET_SECCOMP`, `PR_SET_NO_NEW_PRIVS` and
`PR_GET_NO_NEW_PRIVS`. -/
private def serveCall (seccomp : Seccomp) (emu : Emu) (tid : Nat) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let arg (index : Nat) : Nat := args.getD index 0
  let architecture := seccomp.architecture
  let filter (flags address : Nat) : IO (Option SyscallAction) := do
    if flags &&& (1 ||| 2 ||| 4 ||| 16) != flags then return ← seccomp.fail emu 22
    match ← (readProgram emu architecture address).toBaseIO with
    | .error _ => seccomp.fail emu 14
    | .ok program => if valid program then seccomp.install emu tid flags program else seccomp.fail emu 22
  let strict : IO (Option SyscallAction) := do
    seccomp.state.modify fun state => { state with strict := state.strict.insert tid }
    succeed emu
  match call with
  | .seccomp =>
    match arg 0 with
    | 0 => if arg 1 != 0 || arg 2 != 0 then seccomp.fail emu 22 else strict
    | 1 => filter (arg 1) (arg 2)
    | 2 =>
      -- SECCOMP_GET_ACTION_AVAIL, of all but `USER_NOTIF`, which has no listener here.
      if arg 1 != 0 then return ← seccomp.fail emu 22
      match ← (read emu (arg 2) 4).toBaseIO with
      | .error _ => seccomp.fail emu 14
      | .ok bytes =>
        let action := numberOf architecture.big bytes
        if [0x80000000, 0, 0x00030000, 0x00050000, 0x7ff00000, 0x7ffc0000, 0x7fff0000].contains action then succeed emu
        else seccomp.fail emu 95
    | 3 =>
      -- SECCOMP_GET_NOTIF_SIZES: of `struct seccomp_notif`, `seccomp_notif_resp` and `seccomp_data`.
      if arg 1 != 0 then return ← seccomp.fail emu 22
      let sizes := numberBytes architecture.big 2 80 ++ numberBytes architecture.big 2 24 ++ numberBytes architecture.big 2 64
      match ← (write emu (arg 2) sizes).toBaseIO with
      | .error _ => seccomp.fail emu 14
      | .ok () => succeed emu
    | _ => seccomp.fail emu 22
  | .prctl =>
    let state ← seccomp.state.get
    match arg 0 with
    | 21 => succeed emu (if state.strict.contains tid then 1 else if state.filters.contains tid then 2 else 0)
    | 22 =>
      match arg 1 with
      | 1 => strict
      | 2 => filter 0 (arg 2)
      | _ => seccomp.fail emu 22
    | 38 =>
      if arg 1 != 1 || arg 2 != 0 || arg 3 != 0 || arg 4 != 0 then return ← seccomp.fail emu 22
      seccomp.state.modify fun state => { state with noNewPrivs := state.noNewPrivs.insert tid }
      succeed emu
    | 39 =>
      if arg 1 != 0 || arg 2 != 0 || arg 3 != 0 || arg 4 != 0 then return ← seccomp.fail emu 22
      succeed emu (if state.noNewPrivs.contains tid then 1 else 0)
    | _ => pure none
  | _ => pure none

/-- The thread ends, as `SECCOMP_RET_KILL_THREAD` has it: the process with it if it is the last of it. -/
private def killThread (seccomp : Seccomp) (emu : Emu) (tid : Nat) : IO Unit := do
  let table ← emu.taskTable.get
  let group := (table.find? tid).map (·.group) |>.getD tid
  let live := table.tasks.filter fun task => task.group == group && task.status.isNone
  if live.length ≤ 1 then kill emu tid seccomp.sigsys else exitThread emu 0

/-- What becomes of a call of a thread, by its filters or its strict mode, before anything serves it; and `seccomp` and `prctl`
themselves, once they are let through. -/
def screen (seccomp : Seccomp) (emu : Emu) (tid number : Nat) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := seccomp.architecture
  let state ← seccomp.state.get
  let call := seccomp.calls.get? number
  let has := state.strict.contains tid || state.filters.contains tid || state.noNewPrivs.contains tid
  if !has && call.isNone then return none
  -- What a call makes has what this thread has.
  if has then seccomp.spawning.modify (·.insert tid (← emu.nextThreadRef.get))
  if state.strict.contains tid then
    unless call == some .read || call == some .write || (strictCalls architecture).contains number do
      kill emu tid 9
      return some (.returnValue 0)
  if let some chain := state.filters.get? tid then
    let resumed := state.traced.contains tid
    if resumed then seccomp.state.modify fun state => { state with traced := state.traced.erase tid }
    -- A call that its tracer took away, by making its number -1, isn't made, and has what the tracer left.
    if resumed && number == 2 ^ architecture.bits - 1 then return some (← Ptrace.unmade emu)
    let data := callData architecture number (← emu.nextPc.get) args
    let result := combine (chain.map fun index => run (state.programs[index]!) (wordAt architecture data))
    let value := result &&& 0xffff
    match result &&& 0xffff0000 with
    | 0x7fff0000 | 0x7ffc0000 => pure ()
    | 0x00050000 => return some (← syscallReturn emu (if value == 0 then .ok 0 else .error (min value 4095)))
    | 0x00030000 =>
      let group := ((← emu.taskTable.get).find? tid).map (·.group) |>.getD tid
      seccomp.signals.force emu tid group ⟨seccomp.sigsys, 1, .seccomp (← emu.nextPc.get) number (auditArch architecture) value⟩
      return some (← Ptrace.unmade emu)
    | 0x7ff00000 =>
      -- Once its tracer let it go on, the call goes through.
      unless resumed do
        if ← seccomp.ptrace.seccompStop emu tid value then
          seccomp.state.modify fun state => { state with traced := state.traced.insert tid }
          return some (← Ptrace.again emu)
        return ← seccomp.fail emu 38
    | 0x7fc00000 => return ← seccomp.fail emu 38
    | 0x00000000 =>
      seccomp.killThread emu tid
      return some (.returnValue 0)
    | _ =>
      kill emu tid seccomp.sigsys
      return some (.returnValue 0)
  match call with
  | some call => seccomp.serveCall emu tid call args
  | none => pure none

/-- A call of a thread with anything of seccomp ended: a thread or a process that it made has what it has. -/
def spawned (seccomp : Seccomp) (emu : Emu) : IO Unit := do
  let tid ← thread emu
  let some first := (← seccomp.spawning.get).get? tid | return
  seccomp.spawning.modify (·.erase tid)
  let last ← emu.nextThreadRef.get
  if first == last then return
  seccomp.state.modify fun state =>
    (List.range (last - first)).foldl (init := state) fun state offset =>
      let child := first + offset
      { state with
        filters := match state.filters.get? tid with
          | some chain => state.filters.insert child chain
          | none => state.filters
        strict := if state.strict.contains tid then state.strict.insert child else state.strict
        noNewPrivs := if state.noNewPrivs.contains tid then state.noNewPrivs.insert child else state.noNewPrivs }

end Seccomp

open Wire in
private def putInsn (out : ByteArray) (insn : Insn) : ByteArray :=
  putNat (putNat (putNat (putNat out insn.code) insn.jt) insn.jf) insn.k

open Wire in
private def getInsn : Decoder Insn := fun data at_ => do
  let (code, at_) ← getNat data at_
  let (jt, at_) ← getNat data at_
  let (jf, at_) ← getNat data at_
  let (k, at_) ← getNat data at_
  .ok ({ code, jt, jf, k }, at_)

open Wire in
/-- What seccomp has, as bytes, of the threads that there are: the same state makes the same bytes. -/
def encode (state : State) (live : Nat → Bool) : ByteArray :=
  let out := putList (fun out program => putList putInsn out program.toList) ByteArray.empty state.programs.toList
  let out := putSorted (fun out (tid, chain) => putList putNat (putNat out tid) chain) out
    (state.filters.toList.filter fun (tid, _) => live tid)
  let set (out : ByteArray) (threads : Std.HashSet Nat) : ByteArray := putSorted putNat out (threads.toList.filter live)
  set (set (set out state.strict) state.noNewPrivs) state.traced

open Wire in
def decode (data : ByteArray) : Except String State := do
  let (programs, at_) ← getList (getList getInsn) data 0
  let (filters, at_) ← getList (fun data at_ => do
    let (tid, at_) ← getNat data at_
    let (chain, at_) ← getList getNat data at_
    .ok ((tid, chain), at_)) data at_
  let (strict, at_) ← getList getNat data at_
  let (noNewPrivs, at_) ← getList getNat data at_
  let (traced, at_) ← getList getNat data at_
  expectEnd data at_
  if filters.any fun (_, chain) => chain.any (· ≥ programs.length) then .error "a checkpoint of seccomp with a filter that it hasn't"
  pure { programs := (programs.map List.toArray).toArray, filters := Std.HashMap.ofList filters, strict := Std.HashSet.ofList strict
         noNewPrivs := Std.HashSet.ofList noNewPrivs, traced := Std.HashSet.ofList traced }

/-- Seccomp of a machine, which `ptrace` asks of each call, after its tracer saw it start. -/
def attach (architecture : Architecture) (signals : Signals) (ptrace : Ptrace) (emu : Emu) : IO Seccomp := do
  let calls := architecture.calls.filter fun (_, call) => call == .seccomp || call == .prctl || call == .read || call == .write
  let seccomp : Seccomp := { architecture, calls := Std.HashMap.ofList calls, signals, ptrace, state := ← IO.mkRef {}
                             spawning := ← IO.mkRef {} }
  ptrace.screen.set (seccomp.screen)
  emu.syscallEnds.modify ((fun _ => seccomp.spawned emu) :: ·)
  pure seccomp

/-- What a checkpoint has of it. -/
def Seccomp.modelState (seccomp : Seccomp) (emu : Emu) : ModelState where
  save := do
    let table ← emu.taskTable.get
    pure (encode (← seccomp.state.get) fun tid => (table.find? tid).isSome)
  load := fun data => do seccomp.state.set (← IO.ofExcept (decode data))

end Seccomp

end Bap.Linux
