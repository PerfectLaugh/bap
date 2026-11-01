import Bap.Linux.Kernel

/-! What differs between the architectures of Linux, as far as the kernel is concerned: which number is which system call, the
layout of `struct stat`, and the bits of the flags of `open`. The kernel itself has one set of these, which is that of x86-64. -/

namespace Bap.Linux

inductive Architecture where
  | x86_64 | aarch64 | riscv64 | riscv32
  /-- Of 32 or 64 bits, big-endian or not, of release 6 or not. -/
  | mips (bits : Nat) (big release6 : Bool)
  /-- Of 32 or 64 bits and big-endian or not. 64 bits means ELFv2. -/
  | powerpc (bits : Nat) (big : Bool)
  deriving DecidableEq, Repr

/-- The architecture of what `e_machine`, the width, the order and the flags of a file say, if a machine can run it. -/
def Architecture.ofElf (machine bits : Nat) (big : Bool) (flags : Nat) : Option Architecture :=
  match machine, bits, big with
  | 62, 64, false => some .x86_64
  | 183, 64, false => some .aarch64
  | 243, 64, false => some .riscv64
  | 243, 32, false => some .riscv32
  -- EF_MIPS_ARCH, of which `EF_MIPS_ARCH_32R6` and `EF_MIPS_ARCH_64R6` are release 6.
  | 8, 32, big | 8, 64, big => some (.mips bits big (flags / 2 ^ 28 == 9 || flags / 2 ^ 28 == 10))
  | 20, 32, big => some (.powerpc 32 big)
  -- A file of ELFv1 starts at a descriptor, which isn't there to test against.
  | 21, 64, big => if flags % 4 == 2 then some (.powerpc 64 big) else none
  | _, _, _ => none

/-- What `ofElf` takes to give it back, which is what a checkpoint says. -/
def Architecture.elf : Architecture → Nat × Nat × Bool × Nat
  | .x86_64 => (62, 64, false, 0)
  | .aarch64 => (183, 64, false, 0)
  | .riscv64 => (243, 64, false, 0)
  | .riscv32 => (243, 32, false, 0)
  | .mips bits big release6 => (8, bits, big, if release6 then 10 * 2 ^ 28 else 0)
  | .powerpc 32 big => (20, 32, big, 0)
  | .powerpc bits big => (21, bits, big, 2)

def Architecture.bits : Architecture → Nat
  | .riscv32 => 32
  | .mips bits _ _ | .powerpc bits _ => bits
  | _ => 64

def Architecture.big : Architecture → Bool
  | .mips _ big _ | .powerpc _ big => big
  | _ => false

/-- The system calls that the kernel serves, whatever their numbers. Those of tasks are for `Bap.Emu.serveTaskCalls`. -/
inductive Call where
  | read | write | open_ | openat | close | stat | lstat | fstat | fstatat | statx | lseek | pread | pwrite | readv | writev
  | access | faccessat | dup | dup2 | dup3 | fcntl | ioctl | getdents | getcwd | chdir | fchdir | mkdir | mkdirat | rmdir
  | unlink | unlinkat | rename | renameat | symlink | symlinkat | readlink | readlinkat | chmod | fchmodat | truncate
  | ftruncate | umask | mmap | mremap | brk | gettimeofday | time | clockGettime | clockGetres | uname | getrlimit | prlimit
  | getrandom | sigaltstack | schedGetaffinity
  /-- What 32-bit systems have for numbers that don't fit a word: the offsets of `mmap2` are in pages and `truncate64`,
  `ftruncate64` and `_llseek` have them in two words. -/
  | mmap2 | truncate64 | ftruncate64 | llseek | clockGettime64 | clockGetres64
  | setThreadArea
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

/-- The numbers of `asm-generic` on 32 bits, where whatever has a time or an offset in a word has gone. -/
def generic32Calls : List (Nat × Call) :=
  [(63, .read), (64, .write), (56, .openat), (57, .close), (291, .statx), (62, .llseek),
   (67, .pread), (68, .pwrite), (65, .readv), (66, .writev), (48, .faccessat), (439, .faccessat), (23, .dup), (24, .dup3),
   (25, .fcntl), (29, .ioctl), (61, .getdents), (17, .getcwd), (49, .chdir), (50, .fchdir), (34, .mkdirat), (35, .unlinkat),
   (38, .renameat), (276, .renameat), (36, .symlinkat), (78, .readlinkat), (53, .fchmodat), (45, .truncate64), (46, .ftruncate64),
   (166, .umask), (222, .mmap2), (216, .mremap), (214, .brk), (403, .clockGettime64), (406, .clockGetres64),
   (160, .uname), (261, .prlimit), (278, .getrandom), (132, .sigaltstack), (123, .schedGetaffinity),
   (82, .succeeds), (83, .succeeds), (52, .succeeds), (54, .succeeds), (55, .succeeds), (412, .succeeds), (407, .succeeds),
   (174, .succeeds), (175, .succeeds), (176, .succeeds), (177, .succeeds)]

/-- The numbers of the o32 ABI of MIPS, without their 4000. -/
def o32Calls : List (Nat × Call) :=
  [(3, .read), (4, .write), (5, .open_), (288, .openat), (6, .close), (366, .statx), (19, .lseek), (140, .llseek),
   (200, .pread), (201, .pwrite), (145, .readv), (146, .writev), (33, .access), (300, .faccessat), (439, .faccessat),
   (41, .dup), (63, .dup2), (327, .dup3), (55, .fcntl), (220, .fcntl), (54, .ioctl), (219, .getdents), (203, .getcwd),
   (12, .chdir), (133, .fchdir), (39, .mkdir), (289, .mkdirat), (40, .rmdir), (10, .unlink), (294, .unlinkat), (38, .rename),
   (295, .renameat), (351, .renameat), (83, .symlink), (297, .symlinkat), (85, .readlink), (298, .readlinkat), (15, .chmod),
   (299, .fchmodat), (92, .truncate), (93, .ftruncate), (211, .truncate64), (212, .ftruncate64), (60, .umask), (210, .mmap2),
   (167, .mremap), (45, .brk), (78, .gettimeofday), (263, .clockGettime), (264, .clockGetres), (403, .clockGettime64),
   (406, .clockGetres64), (122, .uname), (76, .getrlimit), (338, .prlimit), (353, .getrandom), (206, .sigaltstack),
   (240, .schedGetaffinity), (283, .setThreadArea), (118, .succeeds), (152, .succeeds), (94, .succeeds), (16, .succeeds),
   (95, .succeeds), (291, .succeeds), (316, .succeeds), (412, .succeeds), (166, .succeeds), (265, .succeeds), (407, .succeeds),
   (24, .succeeds), (47, .succeeds), (49, .succeeds), (50, .succeeds)]

/-- The numbers of the n64 ABI of MIPS, without their 5000. -/
def n64Calls : List (Nat × Call) :=
  [(0, .read), (1, .write), (2, .open_), (247, .openat), (3, .close), (4, .stat), (6, .lstat), (5, .fstat), (252, .fstatat),
   (326, .statx), (8, .lseek), (16, .pread), (17, .pwrite), (18, .readv), (19, .writev), (20, .access), (259, .faccessat),
   (439, .faccessat), (31, .dup), (32, .dup2), (286, .dup3), (70, .fcntl), (15, .ioctl), (308, .getdents), (77, .getcwd),
   (78, .chdir), (79, .fchdir), (81, .mkdir), (248, .mkdirat), (82, .rmdir), (85, .unlink), (253, .unlinkat), (80, .rename),
   (254, .renameat), (311, .renameat), (86, .symlink), (256, .symlinkat), (87, .readlink), (257, .readlinkat), (88, .chmod),
   (258, .fchmodat), (74, .truncate), (75, .ftruncate), (93, .umask), (9, .mmap), (24, .mremap), (12, .brk),
   (94, .gettimeofday), (222, .clockGettime), (223, .clockGetres), (61, .uname), (95, .getrlimit), (297, .prlimit),
   (313, .getrandom), (129, .sigaltstack), (195, .schedGetaffinity), (242, .setThreadArea), (72, .succeeds), (73, .succeeds),
   (89, .succeeds), (90, .succeeds), (91, .succeeds), (92, .succeeds), (250, .succeeds), (275, .succeeds), (34, .succeeds),
   (224, .succeeds), (100, .succeeds), (102, .succeeds), (105, .succeeds), (106, .succeeds)]

/-- The numbers of PowerPC, where those of each width that the other doesn't have are left to it not asking for them. -/
def powerpcCalls : List (Nat × Call) :=
  [(3, .read), (4, .write), (5, .open_), (286, .openat), (6, .close), (106, .stat), (107, .lstat), (108, .fstat), (291, .fstatat),
   (383, .statx), (19, .lseek), (140, .llseek), (179, .pread), (180, .pwrite), (145, .readv), (146, .writev), (33, .access),
   (298, .faccessat), (439, .faccessat), (41, .dup), (63, .dup2), (316, .dup3), (55, .fcntl), (204, .fcntl), (54, .ioctl),
   (202, .getdents), (182, .getcwd), (12, .chdir), (133, .fchdir), (39, .mkdir), (287, .mkdirat), (40, .rmdir), (10, .unlink),
   (292, .unlinkat), (38, .rename), (293, .renameat), (357, .renameat), (83, .symlink), (295, .symlinkat), (85, .readlink),
   (296, .readlinkat), (15, .chmod), (297, .fchmodat), (92, .truncate), (93, .ftruncate), (193, .truncate64), (194, .ftruncate64),
   (60, .umask), (90, .mmap), (192, .mmap2), (163, .mremap), (45, .brk), (78, .gettimeofday), (246, .clockGettime),
   (247, .clockGetres), (403, .clockGettime64), (406, .clockGetres64), (122, .uname), (76, .getrlimit), (190, .getrlimit),
   (325, .prlimit), (359, .getrandom), (185, .sigaltstack), (223, .schedGetaffinity), (118, .succeeds), (148, .succeeds),
   (94, .succeeds), (16, .succeeds), (95, .succeeds), (289, .succeeds), (304, .succeeds), (412, .succeeds), (162, .succeeds),
   (248, .succeeds), (407, .succeeds), (24, .succeeds), (47, .succeeds), (49, .succeeds), (50, .succeeds)]

def Architecture.calls : Architecture → List (Nat × Call)
  | .x86_64 => x86_64Calls
  | .aarch64 | .riscv64 => genericCalls
  | .riscv32 => generic32Calls
  | .mips 32 _ _ => o32Calls.map fun entry => (entry.1 + 4000, entry.2)
  | .mips _ _ _ => n64Calls.map fun entry => (entry.1 + 5000, entry.2)
  | .powerpc _ _ => powerpcCalls

/-- The call of a number, if the kernel serves it. -/
def Architecture.call (architecture : Architecture) (number : Nat) : Option Call :=
  architecture.calls.lookup number

/-- Where MIPS has the flags of `open` that are elsewhere than on x86-64, the ones that a machine looks at: `O_APPEND`, `O_NONBLOCK`,
`O_CREAT`, `O_EXCL`, `O_NOCTTY` and `O_DSYNC`. -/
def mipsOpenBits : List (Nat × Nat) :=
  [(0x8, 0x400), (0x80, 0x800), (0x100, 0x40), (0x400, 0x80), (0x800, 0x100), (0x10, 0x1000)]

/-- Where PowerPC has `O_DIRECTORY`, `O_NOFOLLOW`, `O_LARGEFILE` and `O_DIRECT`. -/
def powerpcOpenBits : List (Nat × Nat) :=
  [(0x4000, 0x10000), (0x8000, 0x20000), (0x10000, 0x8000), (0x20000, 0x4000)]

/-- `flags` with each bit of the first of a pair moved to the second, and the rest left. -/
def moveBits (moves : List (Nat × Nat)) (flags : Nat) : Nat :=
  let moved := moves.foldl (fun out move => if flags &&& move.1 != 0 then out ||| move.2 else out) 0
  (moves.foldl (fun out move => out - (out &&& move.1)) flags) ||| moved

/-- The flags of `open` as the kernel has them, from those of a guest: on AArch64, `O_DIRECTORY` and `O_NOFOLLOW` are
where x86-64 has `O_DIRECT` and `O_LARGEFILE`, and the other way round. -/
def Architecture.openFlags : Architecture → Nat → Nat
  | .x86_64, flags | .riscv64, flags | .riscv32, flags => flags
  | .mips _ _ _, flags => moveBits mipsOpenBits flags
  | .powerpc _ _, flags => moveBits powerpcOpenBits flags
  | .aarch64, flags =>
    let low := flags &&& 0xc000
    let high := flags &&& 0x30000
    (flags - low - high) ||| (low * 4) ||| (high / 4)

/-- The flags of `open` of a guest, from those of the kernel. -/
def Architecture.guestFlags : Architecture → Nat → Nat
  | .mips _ _ _, flags => moveBits (mipsOpenBits.map fun move => (move.2, move.1)) flags
  | .powerpc _ _, flags => moveBits (powerpcOpenBits.map fun move => (move.2, move.1)) flags
  | architecture, flags => architecture.openFlags flags

/-- `struct stat`. 32-bit systems ask for `statx`, whose times are wide enough. -/
def Architecture.stat : Architecture → Kernel.Stat → ByteArray
  | .x86_64, value => Abi.stat value
  | .aarch64, value | .riscv64, value | .riscv32, value => Abi.genericStat value
  | .mips _ big _, value => Abi.mips64Stat value big
  | .powerpc _ big, value => Abi.stat value big

/-- The number of an error of a guest, which on MIPS isn't that of Linux elsewhere for those above 34. -/
def Architecture.errno : Architecture → Nat → Nat
  | .mips _ _ _, 36 => 78
  | .mips _ _ _, 38 => 89
  | .mips _ _ _, 39 => 93
  | .mips _ _ _, 40 => 90
  | _, errno => errno

/-- `MAP_ANONYMOUS`. -/
def Architecture.mapAnonymous : Architecture → Nat
  | .mips _ _ _ => 0x800
  | _ => 0x20

/-- Which argument the low or high word of the offset of `pread` starts at, on 32 bits: MIPS aligns a pair to an even register. -/
def Architecture.pairBase : Architecture → Nat
  | .mips _ _ _ | .powerpc _ _ => 4
  | _ => 3

/-- What `uname` and `AT_PLATFORM` say. -/
def Architecture.name : Architecture → String
  | .x86_64 => "x86_64"
  | .aarch64 => "aarch64"
  | .riscv64 => "riscv64"
  | .riscv32 => "riscv32"
  | .mips 32 _ _ => "mips"
  | .mips _ _ _ => "mips64"
  | .powerpc 32 _ => "ppc"
  | .powerpc _ true => "ppc64"
  | .powerpc _ false => "ppc64le"

end Bap.Linux
