import Bap.Linux.Kernel

/-! # `/proc`, and what little of `/sys` libc reads

Files of `/proc` are generated files of the kernel, whose bytes these pure functions make when they are opened, so that a program
gets what a process is at that moment, and nothing comes from the machine that this runs on. `Kernel.addGenerated` puts another
in the place of any of them. What a process has under `/proc/PID` is made when a path there is looked at. -/

namespace Bap.Linux.Proc

private def text (value : String) : ByteArray := value.toUTF8

private def hex (digits value : Nat) : String :=
  let shown := String.ofList (Nat.toDigits 16 value)
  String.ofList (List.replicate (digits - shown.length) '0') ++ shown

/-- `/proc/PID/maps`, in order of address, with the names of the stack and the heap. -/
def maps (view : ProcessView) : ByteArray :=
  let sorted := view.ranges.toArray.qsort fun left right => left.start < right.start
  let digits := if view.bits == 64 then 12 else 8
  text <| String.join (sorted.toList.map fun range =>
    let flag (on : Bool) (letter : Char) : String := String.singleton (if on then letter else '-')
    let name :=
      if range.start == view.stackStart then " [stack]"
      else if view.breakStart ≤ range.start && range.start < view.breakEnd then " [heap]"
      else ""
    s!"{hex digits range.start}-{hex digits (range.start + range.size)} {flag range.readable 'r'}{flag range.writable 'w'}{flag range.executable 'x'}p 00000000 00:00 0{name}\n")

/-- The last part of a path. -/
private def baseName (path : String) : String := Path.name path

/-- A number in octal of four digits, as `Umask` is. -/
private def octal4 (value : Nat) : String :=
  String.ofList ((List.range 4).reverse.map fun place => Char.ofNat (48 + value / 8 ^ place % 8))

/-- Strings with a zero after each, as `cmdline` and `environ` have them. -/
def zeroEnded (items : List String) : ByteArray :=
  text (String.join (items.map (· ++ "\x00")))

def status (view : ProcessView) : ByteArray :=
  let memory := view.ranges.foldl (fun total range => total + range.size) 0
  let ids := view.credentials
  let groups := " ".intercalate (ids.groups.map toString)
  text s!"Name:\t{baseName view.program}\nUmask:\t{octal4 view.umask}\nState:\tR (running)\nTgid:\t{view.pid}\nNgid:\t0\nPid:\t{view.pid}\nPPid:\t{view.parent}\nTracerPid:\t0\nUid:\t{ids.uid}\t{ids.euid}\t{ids.suid}\t{ids.fsuid}\nGid:\t{ids.gid}\t{ids.egid}\t{ids.sgid}\t{ids.fsgid}\nFDSize:\t64\nGroups:\t{groups}\nVmSize:\t{memory / 1024} kB\nVmRSS:\t{memory / 1024} kB\nThreads:\t{view.threads.length}\nCpus_allowed:\t1\nCpus_allowed_list:\t0\n"

/-- `/proc/PID/stat`, with what isn't modelled at zero. -/
def stat (view : ProcessView) : ByteArray :=
  let memory := view.ranges.foldl (fun total range => total + range.size) 0
  text s!"{view.pid} ({baseName view.program}) R {view.parent} {view.pgid} {view.sid} 0 -1 4194304 0 0 0 0 0 0 0 0 20 0 {view.threads.length} 0 0 {memory} {memory / 4096} 18446744073709551615 0 0 {view.stackStart} 0 0 0 0 0 0 0 0 0 17 0 0 0 0 0 0 0 0 {view.breakStart} 0 0 0 0 0\n"

def statm (view : ProcessView) : ByteArray :=
  let pages := view.ranges.foldl (fun total range => total + range.size) 0 / 4096
  text s!"{pages} {pages} 0 0 0 0 0\n"

def limits (view : ProcessView) : ByteArray :=
  let shown (value : Nat) : String :=
    let value := if value ≥ 2 ^ 64 - 1 then "unlimited" else toString value
    value ++ String.ofList (List.replicate (21 - value.length) ' ')
  text s!"Limit                     Soft Limit           Hard Limit           Units     \nMax stack size            {shown view.stack.1}{shown view.stack.2}bytes     \nMax open files            {shown view.files.1}{shown view.files.2}files     \n"

/-- `/proc/PID/fdinfo/N`, of a descriptor that it has. -/
def fdinfo (view : ProcessView) (fd : Nat) : ByteArray :=
  match view.descriptors.find? (·.1 == fd) with
  | some (_, offset, flags) => text s!"pos:\t{offset}\nflags:\t0{String.ofList (Nat.toDigits 8 flags)}\nmnt_id:\t1\n"
  | none => ByteArray.empty

/-- What a process has mounted, the first first, after `/`, `/proc` and `/sys`: where, of what file system, what was mounted, and what
of `MS_RDONLY`, `MS_NOSUID`, `MS_NODEV` and `MS_NOEXEC` it was mounted with. -/
private def mounted (view : ProcessView) : List (String × String × String × String) :=
  [("/", "rootfs", "rootfs", "rw"), ("/proc", "proc", "proc", "rw,nosuid,nodev,noexec,relatime"),
   ("/sys", "sysfs", "sysfs", "rw,nosuid,nodev,noexec,relatime")] ++
  view.mounts.reverse.map fun (target, fstype, device, flags) =>
    let options := [(1, "ro"), (2, "nosuid"), (4, "nodev"), (8, "noexec")].filterMap fun (bit, name) =>
      if flags &&& bit != 0 then some name else none
    (target, fstype, if device.isEmpty then "none" else device, ",".intercalate ((if flags &&& 1 != 0 then [] else ["rw"]) ++ options))

/-- `/proc/PID/mountinfo`, of what `mounts` says. -/
def mountinfo (view : ProcessView) : ByteArray :=
  text (String.join ((mounted view).zipIdx.map fun ((target, fstype, device, options), index) =>
    s!"{index + 1} {if index == 0 then 0 else 1} 0:{index + 1} / {target} {options} - {fstype} {device} {if options.startsWith "ro" then "ro" else "rw"}\n"))

def mounts (view : ProcessView) : ByteArray :=
  text (String.join ((mounted view).map fun (target, fstype, device, options) => s!"{device} {target} {fstype} {options} 0 0\n"))

def cpuinfo (view : ProcessView) : ByteArray :=
  text s!"processor\t: 0\nmodel name\t: bap virtual {view.machine}\ncpu MHz\t\t: 1000.000\nbogomips\t: 2000.00\n\n"

def meminfo : ByteArray :=
  text "MemTotal:        1048576 kB\nMemFree:          524288 kB\nMemAvailable:     524288 kB\nBuffers:               0 kB\nCached:                0 kB\nSwapTotal:             0 kB\nSwapFree:              0 kB\n"

def uptime (view : ProcessView) : ByteArray :=
  let hundredths := view.uptime / 10000000
  let fraction := hundredths % 100
  let shown := s!"{hundredths / 100}.{if fraction < 10 then "0" else ""}{fraction}"
  text s!"{shown} {shown}\n"

/-- `/proc/stat`, of the one processor. -/
def kernelStat (view : ProcessView) : ByteArray :=
  let ticks := view.uptime / 10000000
  text s!"cpu  {ticks} 0 0 0 0 0 0 0 0 0\ncpu0 {ticks} 0 0 0 0 0 0 0 0 0\nctxt 0\nbtime {(view.clock - view.uptime) / 1000000000}\nprocesses {view.processes.length}\nprocs_running 1\nprocs_blocked 0\n"

/-- The generators of the kernel's own, by the name that an inode has. -/
def builtin : String → Option Generator
  | "maps" => some maps
  | "status" => some status
  | "stat" => some stat
  | "statm" => some statm
  | "cmdline" => some fun view => zeroEnded view.command
  | "auxv" => some fun view =>
    let size := view.bits / 8
    (view.auxiliary ++ [0, 0]).foldl (init := ByteArray.empty) fun bytes word =>
      let word := (List.range size).map fun index => (word >>> (8 * index)).toUInt8
      bytes ++ ByteArray.mk (if view.big then word.reverse else word).toArray
  | "environ" => some fun view => zeroEnded view.environment
  | "comm" => some fun view => text (baseName view.program ++ "\n")
  | "limits" => some limits
  | "mountinfo" => some mountinfo
  | "cgroup" => some fun _ => text "0::/\n"
  | "oom_score_adj" => some fun _ => text "0\n"
  | "random-uuid" => some fun view => text s!"{hex 8 (view.clock / 1000 % 2 ^ 32)}-0000-4000-8000-000000000000\n"
  | "boot-id" => some fun view => text s!"{hex 8 ((view.clock - view.uptime) / 1000000000 % 2 ^ 32)}-0000-4000-8000-000000000000\n"
  | "nr-open" => some fun _ => text "1048576\n"
  | "file-max" => some fun _ => text "9223372036854775807\n"
  | "somaxconn" => some fun _ => text "4096\n"
  | "transparent-hugepage" => some fun _ => text "always [madvise] never\n"
  | "mounts" => some mounts
  | "cpuinfo" => some cpuinfo
  | "meminfo" => some fun _ => meminfo
  | "uptime" => some uptime
  | "kernel-stat" => some kernelStat
  | "version" => some fun view => text s!"Linux version 6.1.0 (bap@bap) #1 SMP {view.machine}\n"
  | "loadavg" => some fun view => text s!"0.00 0.00 0.00 1/{view.processes.length} {view.pid}\n"
  | "filesystems" => some fun _ => text "nodev\tproc\nnodev\tsysfs\n\trootfs\n"
  | "osrelease" => some fun _ => text "6.1.0\n"
  | "ostype" => some fun _ => text "Linux\n"
  | "kernel-version" => some fun _ => text "#1 SMP\n"
  | "hostname" => some fun _ => text "bap\n"
  | "pid-max" => some fun _ => text "4194304\n"
  | "overcommit" => some fun _ => text "0\n"
  | "max-map-count" => some fun _ => text "65530\n"
  | "cpus" => some fun _ => text "0\n"
  -- A descriptor of `/proc/PID/fdinfo`, by its number.
  | name =>
    match name.splitOn ":" with
    | ["fdinfo", fd] => fd.toNat?.map fun fd view => fdinfo view fd
    | _ => none

/-- The files of `/proc` and `/sys` of anything that runs, and what makes them. -/
def systemFiles : List (String × String) :=
  [("/proc/cpuinfo", "cpuinfo"), ("/proc/meminfo", "meminfo"), ("/proc/uptime", "uptime"), ("/proc/stat", "kernel-stat"),
   ("/proc/version", "version"), ("/proc/loadavg", "loadavg"), ("/proc/filesystems", "filesystems"), ("/proc/mounts", "mounts"),
   ("/proc/sys/kernel/osrelease", "osrelease"), ("/proc/sys/kernel/ostype", "ostype"), ("/proc/sys/kernel/version", "kernel-version"),
   ("/proc/sys/kernel/hostname", "hostname"), ("/proc/sys/kernel/pid_max", "pid-max"), ("/proc/sys/vm/overcommit_memory", "overcommit"),
   ("/proc/sys/vm/max_map_count", "max-map-count"), ("/sys/devices/system/cpu/online", "cpus"),
   ("/sys/devices/system/cpu/possible", "cpus"), ("/sys/devices/system/cpu/present", "cpus"),
   ("/proc/sys/kernel/random/uuid", "random-uuid"), ("/proc/sys/kernel/random/boot_id", "boot-id"), ("/proc/sys/fs/nr_open", "nr-open"),
   ("/proc/sys/fs/file-max", "file-max"), ("/proc/sys/net/core/somaxconn", "somaxconn"),
   ("/sys/kernel/mm/transparent_hugepage/enabled", "transparent-hugepage")]

/-- The files of each process, under `/proc/PID`, by the names of what makes them. -/
def processFiles : List String :=
  ["maps", "status", "stat", "statm", "cmdline", "environ", "comm", "limits", "mounts", "auxv", "mountinfo", "cgroup", "oom_score_adj"]

/-- Puts in what is in `/proc` and `/sys` of anything that runs. Nothing replaces what is already there. -/
def install (kernel : Kernel) : Kernel :=
  systemFiles.foldl (init := kernel) fun kernel entry => kernel.addBuiltin entry.1 entry.2

/-- What a descriptor is, as `/proc/PID/fd/N` says: where its file is, or a terminal. -/
private def linkOfDescriptor (kernel : Kernel) (number : Nat) : String :=
  match kernel.inodes.get? number with
  | some { content := .console _, .. } => "/dev/console"
  | _ =>
    match kernel.paths.toList.find? (·.2 == number) with
    | some entry => entry.1
    | none => s!"anon_inode:[{number}]"

/-- `/proc` as it has to be for `group` and its task `thread` to look at it, with `/proc/self` being it, for these processes. -/
def refresh (kernel : Kernel) (group thread : Nat) (live : List Nat) (threadsOf : Nat → List Nat) : Kernel :=
  -- What was there for what has gone, and what may have changed.
  let stale := kernel.paths.toList.filterMap fun entry =>
    match (entry.1.splitOn "/") with
    | ["", "proc", number] =>
      match number.toNat? with
      | some pid => if live.contains pid then none else some pid
      | none => none
    | _ => none
  let kernel := stale.foldl (init := kernel) fun kernel pid =>
    let directory := s!"/proc/{pid}"
    let kernel := kernel.removeUnder directory
    match kernel.paths.get? directory with
    | some number => { kernel with paths := kernel.paths.erase directory, inodes := kernel.inodes.erase number }
    | none => kernel
  let kernel := kernel.setSymlink "/proc/self" (toString group)
  let kernel := kernel.setSymlink "/proc/thread-self" s!"{group}/task/{thread}"
  live.foldl (init := kernel) fun kernel pid =>
    let directory := s!"/proc/{pid}"
    let process := kernel.process pid
    let kernel := processFiles.foldl (init := kernel)
      fun kernel name => kernel.addBuiltin s!"{directory}/{name}" name
    let kernel := kernel.addDirectories s!"{directory}/fd"
    let kernel := kernel.removeUnder s!"{directory}/fd"
    let kernel := kernel.addDirectories s!"{directory}/fdinfo"
    let kernel := kernel.removeUnder s!"{directory}/fdinfo"
    let kernel := (kernel.process pid).descriptors.toList.foldl (init := kernel) fun kernel entry =>
      kernel.addBuiltin s!"{directory}/fdinfo/{entry.1}" s!"fdinfo:{entry.1}"
    let kernel := kernel.addDirectories s!"{directory}/task"
    let kernel := kernel.removeUnder s!"{directory}/task"
    let kernel := (threadsOf pid).foldl (init := kernel) fun kernel task =>
      ["comm", "status", "stat"].foldl (init := kernel) fun kernel name =>
        kernel.addBuiltin s!"{directory}/task/{task}/{name}" name
    let kernel := kernel.setSymlink s!"{directory}/exe" process.program
    let kernel := kernel.setSymlink s!"{directory}/cwd" process.cwd
    let kernel := kernel.setSymlink s!"{directory}/root" "/"
    (kernel.process pid).descriptors.toList.foldl (init := kernel) fun kernel entry =>
      let link := match kernel.openFiles.get? entry.2.openFile with
        | some file => linkOfDescriptor kernel file.inode
        | none => s!"anon_inode:[{entry.1}]"
      kernel.setSymlink s!"{directory}/fd/{entry.1}" link

end Bap.Linux.Proc
