import Bap.Linux.Kernel

/-! What differs between the architectures of Linux, as far as the kernel is concerned: which number is which system call, the
layout of `struct stat`, and the bits of the flags of `open`. The kernel itself has one set of these, which is that of x86-64. -/

namespace Bap.Linux

inductive Architecture where
  | x86_64 | aarch64 | riscv64
  deriving DecidableEq, Repr

/-- The architecture of the value of `e_machine`, if a machine can run it. -/
def Architecture.ofElf : Nat → Option Architecture
  | 62 => some .x86_64
  | 183 => some .aarch64
  | 243 => some .riscv64
  | _ => none

/-- The value of `e_machine` of an architecture. -/
def Architecture.elfMachine : Architecture → Nat
  | .x86_64 => 62
  | .aarch64 => 183
  | .riscv64 => 243

/-- The system calls that the kernel serves, whatever their numbers. Those of tasks are for `Bap.Emu.serveTaskCalls`. -/
inductive Call where
  | read | write | open_ | openat | close | stat | lstat | fstat | fstatat | statx | lseek | pread | pwrite | readv | writev
  | access | faccessat | dup | dup2 | dup3 | fcntl | ioctl | getdents | getcwd | chdir | fchdir | mkdir | mkdirat | rmdir
  | unlink | unlinkat | rename | renameat | symlink | symlinkat | readlink | readlinkat | chmod | fchmodat | truncate
  | ftruncate | umask | mmap | mremap | brk | gettimeofday | time | clockGettime | clockGetres | uname | getrlimit | prlimit
  | getrandom | sigaltstack | schedGetaffinity
  /-- What has nothing to do here: everyone is root, nothing has to reach a disk and sleeping takes no time. -/
  | succeeds
  deriving DecidableEq, Repr

/-- The numbers of x86-64. -/
def x86_64Calls : List (Nat × Call) :=
  [(0, .read), (1, .write), (2, .open_), (257, .openat), (3, .close), (4, .stat), (6, .lstat), (5, .fstat), (262, .fstatat),
   (332, .statx), (8, .lseek), (17, .pread), (18, .pwrite), (19, .readv), (20, .writev), (21, .access), (269, .faccessat),
   (439, .faccessat), (32, .dup), (33, .dup2), (292, .dup3), (72, .fcntl), (16, .ioctl), (217, .getdents), (79, .getcwd),
   (80, .chdir), (81, .fchdir), (83, .mkdir), (258, .mkdirat), (84, .rmdir), (87, .unlink), (263, .unlinkat), (82, .rename),
   (264, .renameat), (316, .renameat), (88, .symlink), (266, .symlinkat), (89, .readlink), (267, .readlinkat), (90, .chmod),
   (268, .fchmodat), (76, .truncate), (77, .ftruncate), (95, .umask), (9, .mmap), (25, .mremap), (12, .brk),
   (96, .gettimeofday), (201, .time), (228, .clockGettime), (229, .clockGetres), (63, .uname), (97, .getrlimit),
   (302, .prlimit), (318, .getrandom), (131, .sigaltstack), (204, .schedGetaffinity), (74, .succeeds), (75, .succeeds),
   (91, .succeeds), (92, .succeeds), (93, .succeeds), (94, .succeeds), (260, .succeeds), (280, .succeeds), (35, .succeeds),
   (230, .succeeds), (102, .succeeds), (104, .succeeds), (107, .succeeds), (108, .succeeds)]

/-- The numbers of the architectures that came after the old calls went: `asm-generic/unistd.h`. -/
def genericCalls : List (Nat × Call) :=
  [(63, .read), (64, .write), (56, .openat), (57, .close), (80, .fstat), (79, .fstatat), (291, .statx), (62, .lseek),
   (67, .pread), (68, .pwrite), (65, .readv), (66, .writev), (48, .faccessat), (439, .faccessat), (23, .dup), (24, .dup3),
   (25, .fcntl), (29, .ioctl), (61, .getdents), (17, .getcwd), (49, .chdir), (50, .fchdir), (34, .mkdirat), (35, .unlinkat),
   (38, .renameat), (276, .renameat), (36, .symlinkat), (78, .readlinkat), (53, .fchmodat), (45, .truncate), (46, .ftruncate),
   (166, .umask), (222, .mmap), (216, .mremap), (214, .brk), (169, .gettimeofday), (113, .clockGettime), (114, .clockGetres),
   (160, .uname), (163, .getrlimit), (261, .prlimit), (278, .getrandom), (132, .sigaltstack), (123, .schedGetaffinity),
   (82, .succeeds), (83, .succeeds), (52, .succeeds), (54, .succeeds), (55, .succeeds), (88, .succeeds), (101, .succeeds),
   (115, .succeeds), (174, .succeeds), (175, .succeeds), (176, .succeeds), (177, .succeeds)]

def Architecture.calls : Architecture → List (Nat × Call)
  | .x86_64 => x86_64Calls
  | .aarch64 | .riscv64 => genericCalls

/-- The call of a number, if the kernel serves it. -/
def Architecture.call (architecture : Architecture) (number : Nat) : Option Call :=
  architecture.calls.lookup number

/-- The flags of `open` as the kernel has them, from those of a guest, or back: on AArch64, `O_DIRECTORY` and `O_NOFOLLOW` are
where x86-64 has `O_DIRECT` and `O_LARGEFILE`, and the other way round. -/
def Architecture.openFlags : Architecture → Nat → Nat
  | .x86_64, flags | .riscv64, flags => flags
  | .aarch64, flags =>
    let low := flags &&& 0xc000
    let high := flags &&& 0x30000
    (flags - low - high) ||| (low * 4) ||| (high / 4)

/-- `struct stat`. -/
def Architecture.stat : Architecture → Kernel.Stat → ByteArray
  | .x86_64, value => Abi.stat value
  | .aarch64, value | .riscv64, value => Abi.genericStat value

/-- What `uname` and `AT_PLATFORM` say. -/
def Architecture.name : Architecture → String
  | .x86_64 => "x86_64"
  | .aarch64 => "aarch64"
  | .riscv64 => "riscv64"

end Bap.Linux
