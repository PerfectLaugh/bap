import Bap.Linux.Kernel
import Bap.Linux.Calls
import Bap.Emu.Tasks

/-! # Who a process is

Process groups and sessions (`setpgid`, `getpgid`, `getpgrp`, `setsid`, `getsid`), the ids of users and groups (`setuid` and its kin,
`getgroups`, `setgroups`, `capget`, `capset`), the limits of resources (`getrlimit`, `setrlimit`, `prlimit64`), and what a process asks
of its accounting and scheduling (`getrusage`, `times`, `getpriority`, `setpriority`, the `sched_*` calls).

Everyone starts as root, with every capability. A process has those that it keeps when its ids change as Linux has it, those that
`capset` leaves it, and those that `execve` gives a program: what root may do goes by them. The limits are kept as
they are set, and `RLIMIT_NOFILE` is kept to by what makes a descriptor. Time that a process spent isn't counted: it is 0. There is
one processor. -/

namespace Bap.Linux

open Bap.Emu Bap.Tasks

structure Identity where
  architecture : Architecture
  kernel : IO.Ref Kernel

namespace Identity

private def numberOf (big : Bool) (bytes : ByteArray) : Nat :=
  let ordered := if big then bytes.toList else bytes.toList.reverse
  ordered.foldl (fun value byte => value * 256 + byte.toNat) 0

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- A resource of `setrlimit` as the others number it, of the number that MIPS has. -/
private def resourceOf (architecture : Architecture) (resource : Nat) : Nat :=
  match architecture, resource with
  | .mips .., 5 => 7
  | .mips .., 6 => 9
  | .mips .., 7 => 5
  | .mips .., 8 => 6
  | .mips .., 9 => 8
  | _, _ => resource

/-- The processes of a process group that are alive. -/
def members (kernel : Kernel) (live : List Nat) (pgid : Nat) : List Nat :=
  live.filter fun group => kernel.pgidOf group == pgid

/-- The calls of this module, if the call is one of them. -/
def serve (identity : Identity) (emu : Emu) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let architecture := identity.architecture
  let big := architecture.big
  let width := architecture.bits
  let word := width / 8
  let arg (index : Nat) : Nat := args.getD index 0
  let id32 (index : Nat) : Nat := arg index % 2 ^ 32
  let unset := 2 ^ 32 - 1
  let task ← currentTask emu
  let (group, tid) := (task.group, task.tid)
  let fail (errno : Nat) : IO (Option SyscallAction) := do pure (some (.returnValue (2 ^ 64 - errno)))
  let succeed (value : Nat := 0) : IO (Option SyscallAction) := do pure (some (.returnValue value))
  let (esrch, eperm, einval, eacces) := (3, 1, 22, 13)
  let tasks := (← emu.taskTable.get).tasks
  let live := ((tasks.filter (·.status.isNone)).map (·.group)).eraseDups
  -- The process of a `pid_t`, of which 0 is the one that calls: a thread's id is its process's.
  let processOf (pid : Nat) : Option Nat :=
    let pid := pid % 2 ^ 32
    if pid == 0 then some group else (tasks.find? fun task => task.tid == pid && task.status.isNone).map (·.group)
  let kernel ← identity.kernel.get
  let update (target : Nat) (change : Process → Process) : IO Unit :=
    identity.kernel.modify fun kernel => kernel.setProcess target (change (kernel.process target))
  let credentials := (kernel.process group).credentials
  let (mayUsers, mayGroups) := (credentials.capable Capability.setuid, credentials.capable Capability.setgid)
  let setCredentials (next : Credentials) : IO (Option SyscallAction) := do
    update group fun process => { process with credentials := next }
    succeed
  let setUsers (next : Credentials) : IO (Option SyscallAction) := setCredentials (next.ofUsers credentials)
  -- Of `setreuid` and its kin: what a process without the capability may take of what it has.
  let among (privileged : Bool) (value : Nat) (allowed : List Nat) : Bool := value == unset || privileged || allowed.contains value
  let words (address count : Nat) : IO (List Nat) := (List.range count).mapM fun index => do
    pure (numberOf big (← read emu (address + index * 4) 4))
  let writeWords (address : Nat) (values : List Nat) : IO Unit :=
    write emu address (values.foldl (fun out value => out ++ numberBytes big 4 value) ByteArray.empty)
  let limitBytes (size : Nat) (limit : Nat × Nat) : ByteArray :=
    let clamp (value : Nat) : Nat := if value ≥ 2 ^ (8 * size) - 1 then 2 ^ (8 * size) - 1 else value
    numberBytes big size (clamp limit.1) ++ numberBytes big size (clamp limit.2)
  let setLimit (target resource soft hard : Nat) : IO (Option SyscallAction) := do
    let (_, current) := kernel.limitOf target resource
    if soft > hard then return ← fail einval
    if hard > current && !credentials.capable Capability.sysResource then return ← fail eperm
    -- Of descriptors, no more than `/proc/sys/fs/nr_open` says, even with the capability, as `do_prlimit` has it.
    if resource == 7 && hard > 1048576 then return ← fail eperm
    update target fun process => { process with limits := (resource, soft, hard) :: process.limits.filter (·.1 != resource) }
    succeed
  try
    match call with
    | .getpgid =>
      let some target := processOf (arg 0) | return ← fail esrch
      succeed (kernel.pgidOf target)
    | .getpgrp => succeed (kernel.pgidOf group)
    | .getsid =>
      let some target := processOf (arg 0) | return ← fail esrch
      succeed (kernel.sidOf target)
    | .setpgid =>
      let some target := processOf (arg 0) | return ← fail esrch
      let isChild := tasks.any fun task => task.tid == target && task.parent == group
      if target != group && !isChild then return ← fail esrch
      let pgid := if arg 1 % 2 ^ 32 == 0 then target else arg 1 % 2 ^ 32
      if pgid ≥ 2 ^ 31 then return ← fail einval
      if kernel.sidOf target == target || kernel.sidOf target != kernel.sidOf group then return ← fail eperm
      -- Another group that it goes to is one of its session.
      if pgid != target && !live.any fun other => kernel.pgidOf other == pgid && kernel.sidOf other == kernel.sidOf group then
        return ← fail eperm
      update target fun process => { process with pgid }
      succeed
    | .setsid =>
      if kernel.pgidOf group == group then return ← fail eperm
      update group fun process => { process with pgid := group, sid := group, terminal := none }
      succeed group
    | .getuid => succeed credentials.uid
    | .geteuid => succeed credentials.euid
    | .getgid => succeed credentials.gid
    | .getegid => succeed credentials.egid
    | .setuid =>
      let uid := id32 0
      if uid == unset then return ← fail einval
      if mayUsers then setUsers { credentials with uid, euid := uid, suid := uid, fsuid := uid }
      else if uid == credentials.uid || uid == credentials.suid then setUsers { credentials with euid := uid, fsuid := uid }
      else fail eperm
    | .setgid =>
      let gid := id32 0
      if gid == unset then return ← fail einval
      if mayGroups then setCredentials { credentials with gid, egid := gid, sgid := gid, fsgid := gid }
      else if gid == credentials.gid || gid == credentials.sgid then setCredentials { credentials with egid := gid, fsgid := gid }
      else fail eperm
    | .setreuid =>
      let (real, effective) := (id32 0, id32 1)
      if !among mayUsers real [credentials.uid, credentials.euid] ||
          !among mayUsers effective [credentials.uid, credentials.euid, credentials.suid] then
        return ← fail eperm
      let uid := if real == unset then credentials.uid else real
      let euid := if effective == unset then credentials.euid else effective
      let suid := if real != unset || (effective != unset && effective != credentials.uid) then euid else credentials.suid
      setUsers { credentials with uid, euid, suid, fsuid := euid }
    | .setregid =>
      let (real, effective) := (id32 0, id32 1)
      if !among mayGroups real [credentials.gid, credentials.egid] ||
          !among mayGroups effective [credentials.gid, credentials.egid, credentials.sgid] then
        return ← fail eperm
      let gid := if real == unset then credentials.gid else real
      let egid := if effective == unset then credentials.egid else effective
      let sgid := if real != unset || (effective != unset && effective != credentials.gid) then egid else credentials.sgid
      setCredentials { credentials with gid, egid, sgid, fsgid := egid }
    | .setresuid =>
      let held := [credentials.uid, credentials.euid, credentials.suid]
      if ![id32 0, id32 1, id32 2].all (among mayUsers · held) then return ← fail eperm
      let pick (value old : Nat) : Nat := if value == unset then old else value
      let euid := pick (id32 1) credentials.euid
      setUsers { credentials with uid := pick (id32 0) credentials.uid, euid, suid := pick (id32 2) credentials.suid, fsuid := euid }
    | .setresgid =>
      let held := [credentials.gid, credentials.egid, credentials.sgid]
      if ![id32 0, id32 1, id32 2].all (among mayGroups · held) then return ← fail eperm
      let pick (value old : Nat) : Nat := if value == unset then old else value
      let egid := pick (id32 1) credentials.egid
      setCredentials { credentials with gid := pick (id32 0) credentials.gid, egid, sgid := pick (id32 2) credentials.sgid, fsgid := egid }
    | .getresuid =>
      for (address, value) in [(arg 0, credentials.uid), (arg 1, credentials.euid), (arg 2, credentials.suid)] do
        writeWords address [value]
      succeed
    | .getresgid =>
      for (address, value) in [(arg 0, credentials.gid), (arg 1, credentials.egid), (arg 2, credentials.sgid)] do
        writeWords address [value]
      succeed
    -- Of these, -1 isn't an id, and changes nothing: it is how one asks what there is.
    | .setfsuid =>
      let uid := id32 0
      if uid != unset && (mayUsers || [credentials.uid, credentials.euid, credentials.suid, credentials.fsuid].contains uid) then
        update group fun process => { process with credentials := credentials.withFsuid uid }
      succeed credentials.fsuid
    | .setfsgid =>
      let gid := id32 0
      if gid != unset && (mayGroups || [credentials.gid, credentials.egid, credentials.sgid, credentials.fsgid].contains gid) then
        update group fun process => { process with credentials := { credentials with fsgid := gid } }
      succeed credentials.fsgid
    | .getgroups =>
      let count := credentials.groups.length
      if arg 0 % 2 ^ 32 ≥ 2 ^ 31 then return ← fail einval
      if arg 0 % 2 ^ 32 == 0 then return ← succeed count
      if arg 0 % 2 ^ 32 < count then return ← fail einval
      writeWords (arg 1) credentials.groups
      succeed count
    | .setgroups =>
      -- They are kept in order, as Linux sorts them.
      if !mayGroups then return ← fail eperm
      if arg 0 % 2 ^ 32 > 65536 then return ← fail einval
      setCredentials { credentials with groups := (← words (arg 1) (arg 0 % 2 ^ 32)).mergeSort }
    | .capget | .capset =>
      -- `_LINUX_CAPABILITY_VERSION_1`, `_2` and `_3`, of which the first has one set of 32 and the others two: each of those has the
      -- effective, the permitted and the inheritable capabilities. Another version is answered with the third, which `capget`
      -- with no data is how a program asks for.
      let version := numberOf big (← read emu (arg 0) 4)
      let sets := if version == 0x19980330 then 1 else 2
      if version != 0x19980330 && version != 0x20071026 && version != 0x20080522 then
        writeWords (arg 0) [0x20080522]
        return ← if call == .capget && arg 1 == 0 then succeed else fail einval
      if call == .capget && arg 1 == 0 then return ← succeed
      let pid := numberOf big (← read emu (arg 0 + 4) 4)
      if call == .capget then
        if pid ≥ 2 ^ 31 then return ← fail einval
        let some target := processOf pid | return ← fail esrch
        let ids := (kernel.process target).credentials
        writeWords (arg 1) ((List.range sets).flatMap fun index =>
          [ids.effective, ids.permitted, ids.inheritable].map fun set => (set >>> (32 * index)) % 2 ^ 32)
        return ← succeed
      -- Only those of the thread itself, and of what it has: it may not raise one.
      if pid != 0 && pid != tid then return ← fail eperm
      let given ← words (arg 1) (3 * sets)
      let set (index : Nat) : Nat :=
        (List.range sets).foldl (fun total part => total ||| given[3 * part + index]! <<< (32 * part)) 0 &&& Capability.all
      let (effective, permitted, inheritable) := (set 0, set 1, set 2)
      let within (part whole : Nat) : Bool := part &&& whole == part
      if !credentials.capable Capability.setpcap && !within inheritable (credentials.inheritable ||| credentials.permitted) ||
          !within inheritable (credentials.inheritable ||| credentials.bounding) || !within permitted credentials.permitted ||
          !within effective permitted then
        return ← fail eperm
      setCredentials { credentials with effective, permitted, inheritable }
    | .getrlimit =>
      write emu (arg 1) (limitBytes word (kernel.limitOf group (resourceOf architecture (arg 0))))
      succeed
    | .setrlimit =>
      let read (offset : Nat) : IO Nat := do
        let value := numberOf big (← Bap.Emu.read emu (arg 1 + offset) word)
        pure (if value == 2 ^ width - 1 then 2 ^ 64 - 1 else value)
      setLimit group (resourceOf architecture (arg 0)) (← read 0) (← read word)
    | .prlimit =>
      let some target := processOf (arg 0) | return ← fail esrch
      let resource := resourceOf architecture (arg 1)
      if arg 3 != 0 then write emu (arg 3) (limitBytes 8 (kernel.limitOf target resource))
      if arg 2 == 0 then return ← succeed
      setLimit target resource (numberOf big (← read emu (arg 2) 8)) (numberOf big (← read emu (arg 2 + 8) 8))
    | .getrusage =>
      write emu (arg 1) (ByteArray.mk (Array.replicate (18 * word) 0))
      succeed
    | .times =>
      if arg 0 != 0 then write emu (arg 0) (ByteArray.mk (Array.replicate (4 * word) 0))
      succeed ((kernel.clock - 1700000000 * 1000000000) / 10000000 % 2 ^ (width - 1))
    | .getpriority | .setpriority =>
      -- PRIO_PROCESS, PRIO_PGRP and PRIO_USER, of which 0 is that of the one that calls.
      let who := arg 1 % 2 ^ 32
      let targets : List Nat := match arg 0 with
        | 0 => (processOf who).toList
        | 1 => members kernel live (if who == 0 then kernel.pgidOf group else who)
        | 2 => live.filter fun process => (kernel.process process).credentials.uid == (if who == 0 then credentials.uid else who)
        | _ => []
      if arg 0 > 2 then return ← fail einval
      if targets.isEmpty then return ← fail esrch
      if call == .getpriority then
        succeed (40 - (targets.map fun target => (kernel.process target).nice).foldl min 39)
      else
        let given : Int := if arg 2 % 2 ^ 32 ≥ 2 ^ 31 then Int.ofNat (arg 2 % 2 ^ 32) - 2 ^ 32 else Int.ofNat (arg 2 % 2 ^ 32)
        let nice := (max (-20) (min 19 given) + 20).toNat
        -- As `set_one_prio` has it: of a process of another user, as it goes by its effective one, `EPERM`.
        let others := targets.any fun target =>
          let ids := (kernel.process target).credentials
          ids.uid != credentials.euid && ids.euid != credentials.euid
        if !credentials.capable Capability.sysNice && others then return ← fail Errno.eperm
        if !credentials.capable Capability.sysNice && targets.any fun target => nice < (kernel.process target).nice then
          return ← fail eacces
        for target in targets do update target fun process => { process with nice }
        succeed
    | .schedSetaffinity =>
      if (processOf (arg 0)).isNone then return ← fail esrch
      let first ← read emu (arg 2) 1
      if (first.get! 0).toNat &&& 1 == 0 then fail einval else succeed
    | .schedGetparam =>
      if (processOf (arg 0)).isNone then return ← fail esrch
      writeWords (arg 1) [0]
      succeed
    | .schedSetparam | .schedSetscheduler =>
      let some target := processOf (arg 0) | return ← fail esrch
      if call == .schedSetscheduler && ![0, 1, 2, 3, 5].contains (arg 1 % 2 ^ 32 &&& 0xbfffffff) then return ← fail einval
      -- What it is set to it is, with `SCHED_RESET_ON_FORK`, as `sched_getscheduler` says.
      if call == .schedSetscheduler then update target fun process => { process with policy := arg 1 % 2 ^ 32 }
      succeed
    | .schedGetscheduler =>
      match processOf (arg 0) with
      | some target => succeed (kernel.process target).policy
      | none => fail esrch
    | .schedGetPriorityMax | .schedGetPriorityMin =>
      match arg 0 % 2 ^ 32 with
      | 1 | 2 => succeed (if call == .schedGetPriorityMax then 99 else 1)
      | 0 | 3 | 5 => succeed 0
      | _ => fail einval
    | .schedRrGetInterval | .schedRrGetInterval64 =>
      let field := if call == .schedRrGetInterval64 then 8 else word
      write emu (arg 1) (numberBytes big field 0 ++ numberBytes big field 100000000)
      succeed
    | _ => pure none
  catch _ => fail 14

end Identity

end Bap.Linux
