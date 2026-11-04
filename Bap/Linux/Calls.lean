import Bap.Linux.Kernel

/-! What differs between the architectures of Linux, as far as the kernel is concerned: which number is which system call, the
layout of `struct stat`, and the bits of the flags of `open`. The kernel itself has one set of these, which is that of x86-64. -/

namespace Bap.Linux

/-- What a Linux machine runs, with what tells its kinds apart where a kernel has to: the calls, their numbers and errors, and the layout
of what they write. -/
inductive Architecture where
  | x86_64 | i686 | aarch64 | arm | riscv64 | riscv32
  /-- Of 32 or 64 bits, big-endian or not, of release 6 or not. -/
  | mips (bits : Nat) (big release6 : Bool)
  /-- Of 32 or 64 bits and big-endian or not. 64 bits means ELFv2. -/
  | powerpc (bits : Nat) (big : Bool)
  deriving DecidableEq, Repr

/-- The architecture of what `e_machine`, the width, the order and the flags of a file say, if a machine can run it. -/
def Architecture.ofElf (machine bits : Nat) (big : Bool) (flags : Nat) : Option Architecture :=
  match machine, bits, big with
  | 62, 64, false => some .x86_64
  | 3, 32, false => some .i686
  | 183, 64, false => some .aarch64
  | 40, 32, false => some .arm
  | 243, 64, false => some .riscv64
  | 243, 32, false => some .riscv32
  -- EF_MIPS_ARCH, of which `EF_MIPS_ARCH_32R6` and `EF_MIPS_ARCH_64R6` are release 6.
  | 8, 32, big | 8, 64, big => some (.mips bits big (flags / 2 ^ 28 == 9 || flags / 2 ^ 28 == 10))
  | 20, 32, big => some (.powerpc 32 big)
  -- A file of ELFv1 starts at a descriptor, which isn't there to test against.
  | 21, 64, big => if flags % 4 == 3 then none else some (.powerpc 64 big)
  | _, _, _ => none

/-- What `ofElf` takes to give it back, which is what a checkpoint says. -/
def Architecture.elf : Architecture → Nat × Nat × Bool × Nat
  | .x86_64 => (62, 64, false, 0)
  | .i686 => (3, 32, false, 0)
  | .aarch64 => (183, 64, false, 0)
  | .arm => (40, 32, false, 0)
  | .riscv64 => (243, 64, false, 0)
  | .riscv32 => (243, 32, false, 0)
  | .mips bits big release6 => (8, bits, big, if release6 then 10 * 2 ^ 28 else 0)
  | .powerpc 32 big => (20, 32, big, 0)
  | .powerpc bits big => (21, bits, big, 2)

/-- How wide its words and addresses are. -/
def Architecture.bits : Architecture → Nat
  | .riscv32 | .i686 | .arm => 32
  | .mips bits _ _ | .powerpc bits _ => bits
  | _ => 64

/-- Whether it has the most significant byte first. -/
def Architecture.big : Architecture → Bool
  | .mips _ big _ | .powerpc _ big => big
  | _ => false

/-- The system calls that the kernel serves, whatever their numbers. Those of tasks are for `Bap.Emu.serveTaskCalls`. -/
inductive Call where
  | read | write | open_ | openat | close | stat | lstat | fstat | fstatat | statx | lseek | pread | pwrite | readv | writev
  | access | faccessat | dup | dup2 | dup3 | fcntl | ioctl | getdents | getcwd | chdir | fchdir | mkdir | mkdirat | rmdir
  | unlink | unlinkat | rename | renameat | symlink | symlinkat | readlink | readlinkat | chmod | fchmodat | truncate
  | ftruncate | umask | pipe | pipe2 | mmap | munmap | mprotect | madvise | mremap | brk | gettimeofday | time | clockGettime | clockGetres | uname | getrlimit | prlimit
  | getrandom | sigaltstack | schedGetaffinity | statfs | fstatfs | sysinfo | execve
  /-- `statfs` and `fstatfs` with the size of the structure in the middle, as 32-bit systems and PowerPC have them. -/
  | statfs64 | fstatfs64
  /-- What 32-bit systems have for numbers that don't fit a word: the offsets of `mmap2` are in pages and `truncate64`,
  `ftruncate64` and `_llseek` have them in two words. -/
  | mmap2 | truncate64 | ftruncate64 | llseek | clockGettime64 | clockGetres64
  | setThreadArea
  /-- Sockets of the Unix domain. `send` and `recv` are `sendto` and `recvfrom` without an address, which some systems have of their
  own. -/
  | socket | socketpair | bind | listen | accept | accept4 | connect | getsockname | getpeername | sendto | recvfrom | send | recv
  | setsockopt | getsockopt | shutdown | sendmsg | recvmsg
  /-- What a process asks of itself, of which only what tagged addresses are on AArch64 is answered. -/
  | prctl
  /-- What `Bap.Linux.Seccomp` serves, in front of the kernel. -/
  | seccomp
  | nanosleep | clockNanosleep | clockNanosleep64 | setitimer | getitimer | alarm | timerCreate | timerSettime | timerSettime64 | timerGettime | timerGettime64 | timerGetoverrun | timerDelete
  | poll | ppoll | ppoll64 | select | pselect6 | pselect664 | epollCreate | epollCreate1 | epollCtl | epollWait | epollPwait | epollPwait2 | eventfd | eventfd2 | timerfdCreate | timerfdSettime | timerfdSettime64 | timerfdGettime | timerfdGettime64 | signalfd | signalfd4
  | getpgid | setpgid | getpgrp | setsid | getsid | getuid | geteuid | getgid | getegid | setuid | setgid | setreuid | setregid | setresuid | setresgid | getresuid | getresgid | setfsuid | setfsgid | getgroups | setgroups | capget | capset | setrlimit | getrusage | times | getpriority | setpriority | schedSetaffinity | schedGetparam | schedSetparam | schedGetscheduler | schedSetscheduler | schedGetPriorityMax | schedGetPriorityMin | schedRrGetInterval | schedRrGetInterval64
  | link | linkat | renameat2 | utimensat | utimensat64 | utimes | utime | futimesat | chown | lchown | fchown | fchownat | setxattr | lsetxattr | fsetxattr | getxattr | lgetxattr | fgetxattr | listxattr | llistxattr | flistxattr | removexattr | lremovexattr | fremovexattr
  | memfdCreate | sendfile | sendfile64 | splice | tee | copyFileRange
  | flock
  | inotifyInit | inotifyInit1 | inotifyAddWatch | inotifyRmWatch
  | mount | umount2 | chroot | pivotRoot
  | shmget | shmat | shmdt | shmctl | semget | semop | semtimedop | semtimedop64 | semctl | msgget | msgsnd | msgrcv | msgctl | ipc
  /-- What has nothing to do here: everyone is root and nothing has to reach a disk. -/
  | succeeds
  deriving DecidableEq, Repr

/-- The numbers of x86-64. -/
def x86_64Calls : List (Nat × Call) :=
  [(29, .shmget), (30, .shmat), (67, .shmdt), (31, .shmctl), (64, .semget), (65, .semop), (220, .semtimedop), (66, .semctl), (68, .msgget), (69, .msgsnd), (70, .msgrcv), (71, .msgctl),
   (165, .mount), (166, .umount2), (161, .chroot), (155, .pivotRoot),
   (253, .inotifyInit), (294, .inotifyInit1), (254, .inotifyAddWatch), (255, .inotifyRmWatch),
   (73, .flock),
   (319, .memfdCreate), (40, .sendfile), (275, .splice), (276, .tee), (326, .copyFileRange),
   (86, .link), (265, .linkat), (280, .utimensat), (235, .utimes), (132, .utime), (261, .futimesat), (92, .chown), (94, .lchown), (93, .fchown), (260, .fchownat), (188, .setxattr), (189, .lsetxattr), (190, .fsetxattr), (191, .getxattr), (192, .lgetxattr), (193, .fgetxattr), (194, .listxattr), (195, .llistxattr), (196, .flistxattr), (197, .removexattr), (198, .lremovexattr), (199, .fremovexattr),
   (121, .getpgid), (109, .setpgid), (111, .getpgrp), (112, .setsid), (124, .getsid), (102, .getuid), (107, .geteuid), (104, .getgid), (108, .getegid), (105, .setuid), (106, .setgid), (113, .setreuid), (114, .setregid), (117, .setresuid), (119, .setresgid), (118, .getresuid), (120, .getresgid), (122, .setfsuid), (123, .setfsgid), (115, .getgroups), (116, .setgroups), (125, .capget), (126, .capset), (160, .setrlimit), (98, .getrusage), (100, .times), (140, .getpriority), (141, .setpriority), (203, .schedSetaffinity), (143, .schedGetparam), (142, .schedSetparam), (145, .schedGetscheduler), (144, .schedSetscheduler), (146, .schedGetPriorityMax), (147, .schedGetPriorityMin), (148, .schedRrGetInterval),
   (7, .poll), (271, .ppoll), (23, .select), (270, .pselect6), (213, .epollCreate), (291, .epollCreate1), (233, .epollCtl), (232, .epollWait), (281, .epollPwait), (441, .epollPwait2), (284, .eventfd), (290, .eventfd2), (283, .timerfdCreate), (286, .timerfdSettime), (287, .timerfdGettime), (282, .signalfd), (289, .signalfd4),
   (35, .nanosleep), (230, .clockNanosleep), (38, .setitimer), (36, .getitimer), (37, .alarm), (222, .timerCreate), (223, .timerSettime), (224, .timerGettime), (225, .timerGetoverrun), (226, .timerDelete),
   (157, .prctl), (317, .seccomp), (41, .socket), (42, .connect), (43, .accept), (44, .sendto), (45, .recvfrom), (46, .sendmsg), (47, .recvmsg), (48, .shutdown), (49, .bind), (50, .listen), (51, .getsockname), (52, .getpeername), (53, .socketpair), (54, .setsockopt), (55, .getsockopt), (288, .accept4),
   (22, .pipe), (293, .pipe2),
   (11, .munmap), (10, .mprotect), (28, .madvise), (26, .succeeds),
   (59, .execve), (137, .statfs), (138, .fstatfs), (99, .sysinfo),
   (0, .read), (1, .write), (2, .open_), (257, .openat), (3, .close), (4, .stat), (6, .lstat), (5, .fstat), (262, .fstatat),
   (332, .statx), (8, .lseek), (17, .pread), (18, .pwrite), (19, .readv), (20, .writev), (21, .access), (269, .faccessat),
   (439, .faccessat), (32, .dup), (33, .dup2), (292, .dup3), (72, .fcntl), (16, .ioctl), (217, .getdents), (79, .getcwd),
   (80, .chdir), (81, .fchdir), (83, .mkdir), (258, .mkdirat), (84, .rmdir), (87, .unlink), (263, .unlinkat), (82, .rename),
   (264, .renameat), (316, .renameat2), (88, .symlink), (266, .symlinkat), (89, .readlink), (267, .readlinkat), (90, .chmod),
   (268, .fchmodat), (76, .truncate), (77, .ftruncate), (95, .umask), (9, .mmap), (25, .mremap), (12, .brk),
   (96, .gettimeofday), (201, .time), (228, .clockGettime), (229, .clockGetres), (63, .uname), (97, .getrlimit),
   (302, .prlimit), (318, .getrandom), (131, .sigaltstack), (204, .schedGetaffinity), (74, .succeeds), (75, .succeeds),
   (91, .succeeds),    ]

/-- The numbers of the architectures that came after the old calls went: `asm-generic/unistd.h`. -/
def genericCalls : List (Nat × Call) :=
  [(194, .shmget), (196, .shmat), (197, .shmdt), (195, .shmctl), (190, .semget), (193, .semop), (192, .semtimedop), (191, .semctl), (186, .msgget), (189, .msgsnd), (188, .msgrcv), (187, .msgctl),
   (40, .mount), (39, .umount2), (51, .chroot), (41, .pivotRoot),
   (26, .inotifyInit1), (27, .inotifyAddWatch), (28, .inotifyRmWatch),
   (32, .flock),
   (279, .memfdCreate), (71, .sendfile), (76, .splice), (77, .tee), (285, .copyFileRange),
   (37, .linkat), (88, .utimensat), (55, .fchown), (54, .fchownat), (5, .setxattr), (6, .lsetxattr), (7, .fsetxattr), (8, .getxattr), (9, .lgetxattr), (10, .fgetxattr), (11, .listxattr), (12, .llistxattr), (13, .flistxattr), (14, .removexattr), (15, .lremovexattr), (16, .fremovexattr),
   (155, .getpgid), (154, .setpgid), (157, .setsid), (156, .getsid), (174, .getuid), (175, .geteuid), (176, .getgid), (177, .getegid), (146, .setuid), (144, .setgid), (145, .setreuid), (143, .setregid), (147, .setresuid), (149, .setresgid), (148, .getresuid), (150, .getresgid), (151, .setfsuid), (152, .setfsgid), (158, .getgroups), (159, .setgroups), (90, .capget), (91, .capset), (164, .setrlimit), (165, .getrusage), (153, .times), (141, .getpriority), (140, .setpriority), (122, .schedSetaffinity), (121, .schedGetparam), (118, .schedSetparam), (120, .schedGetscheduler), (119, .schedSetscheduler), (125, .schedGetPriorityMax), (126, .schedGetPriorityMin), (127, .schedRrGetInterval),
   (73, .ppoll), (72, .pselect6), (20, .epollCreate1), (21, .epollCtl), (22, .epollPwait), (441, .epollPwait2), (19, .eventfd2), (85, .timerfdCreate), (86, .timerfdSettime), (87, .timerfdGettime), (74, .signalfd4),
   (101, .nanosleep), (115, .clockNanosleep), (103, .setitimer), (102, .getitimer), (107, .timerCreate), (110, .timerSettime), (108, .timerGettime), (109, .timerGetoverrun), (111, .timerDelete),
   (277, .seccomp), (198, .socket), (199, .socketpair), (200, .bind), (201, .listen), (202, .accept), (203, .connect), (204, .getsockname), (205, .getpeername), (206, .sendto), (207, .recvfrom), (208, .setsockopt), (209, .getsockopt), (210, .shutdown), (211, .sendmsg), (212, .recvmsg), (242, .accept4),
   (59, .pipe2), (167, .prctl),
   (215, .munmap), (226, .mprotect), (233, .madvise), (227, .succeeds),
   (221, .execve), (43, .statfs), (44, .fstatfs), (179, .sysinfo),
   (63, .read), (64, .write), (56, .openat), (57, .close), (80, .fstat), (79, .fstatat), (291, .statx), (62, .lseek),
   (67, .pread), (68, .pwrite), (65, .readv), (66, .writev), (48, .faccessat), (439, .faccessat), (23, .dup), (24, .dup3),
   (25, .fcntl), (29, .ioctl), (61, .getdents), (17, .getcwd), (49, .chdir), (50, .fchdir), (34, .mkdirat), (35, .unlinkat),
   (38, .renameat), (276, .renameat2), (36, .symlinkat), (78, .readlinkat), (53, .fchmodat), (45, .truncate), (46, .ftruncate),
   (166, .umask), (222, .mmap), (216, .mremap), (214, .brk), (169, .gettimeofday), (113, .clockGettime), (114, .clockGetres),
   (160, .uname), (163, .getrlimit), (261, .prlimit), (278, .getrandom), (132, .sigaltstack), (123, .schedGetaffinity),
   (82, .succeeds), (83, .succeeds), (52, .succeeds),    ]

/-- The numbers of `asm-generic` on 32 bits, where whatever has a time or an offset in a word has gone. -/
def generic32Calls : List (Nat × Call) :=
  [(194, .shmget), (196, .shmat), (197, .shmdt), (195, .shmctl), (190, .semget), (193, .semop), (420, .semtimedop64), (191, .semctl), (186, .msgget), (189, .msgsnd), (188, .msgrcv), (187, .msgctl),
   (40, .mount), (39, .umount2), (51, .chroot), (41, .pivotRoot),
   (26, .inotifyInit1), (27, .inotifyAddWatch), (28, .inotifyRmWatch),
   (32, .flock),
   (279, .memfdCreate), (71, .sendfile64), (76, .splice), (77, .tee), (285, .copyFileRange),
   (37, .linkat), (412, .utimensat64), (55, .fchown), (54, .fchownat), (5, .setxattr), (6, .lsetxattr), (7, .fsetxattr), (8, .getxattr), (9, .lgetxattr), (10, .fgetxattr), (11, .listxattr), (12, .llistxattr), (13, .flistxattr), (14, .removexattr), (15, .lremovexattr), (16, .fremovexattr),
   (155, .getpgid), (154, .setpgid), (157, .setsid), (156, .getsid), (174, .getuid), (175, .geteuid), (176, .getgid), (177, .getegid), (146, .setuid), (144, .setgid), (145, .setreuid), (143, .setregid), (147, .setresuid), (149, .setresgid), (148, .getresuid), (150, .getresgid), (151, .setfsuid), (152, .setfsgid), (158, .getgroups), (159, .setgroups), (90, .capget), (91, .capset), (165, .getrusage), (153, .times), (141, .getpriority), (140, .setpriority), (122, .schedSetaffinity), (121, .schedGetparam), (118, .schedSetparam), (120, .schedGetscheduler), (119, .schedSetscheduler), (125, .schedGetPriorityMax), (126, .schedGetPriorityMin), (423, .schedRrGetInterval64),
   (414, .ppoll64), (413, .pselect664), (20, .epollCreate1), (21, .epollCtl), (22, .epollPwait), (441, .epollPwait2), (19, .eventfd2), (85, .timerfdCreate), (411, .timerfdSettime64), (410, .timerfdGettime64), (74, .signalfd4),
   (101, .nanosleep), (407, .clockNanosleep64), (103, .setitimer), (102, .getitimer), (107, .timerCreate), (409, .timerSettime64), (408, .timerGettime64), (109, .timerGetoverrun), (111, .timerDelete),
   (277, .seccomp), (198, .socket), (199, .socketpair), (200, .bind), (201, .listen), (202, .accept), (203, .connect), (204, .getsockname), (205, .getpeername), (206, .sendto), (207, .recvfrom), (208, .setsockopt), (209, .getsockopt), (210, .shutdown), (211, .sendmsg), (212, .recvmsg), (242, .accept4),
   (59, .pipe2), (167, .prctl),
   (215, .munmap), (226, .mprotect), (233, .madvise), (227, .succeeds),
   (221, .execve), (43, .statfs64), (44, .fstatfs64), (179, .sysinfo),
   (63, .read), (64, .write), (56, .openat), (57, .close), (291, .statx), (62, .llseek),
   (67, .pread), (68, .pwrite), (65, .readv), (66, .writev), (48, .faccessat), (439, .faccessat), (23, .dup), (24, .dup3),
   (25, .fcntl), (29, .ioctl), (61, .getdents), (17, .getcwd), (49, .chdir), (50, .fchdir), (34, .mkdirat), (35, .unlinkat),
   (38, .renameat), (276, .renameat2), (36, .symlinkat), (78, .readlinkat), (53, .fchmodat), (45, .truncate64), (46, .ftruncate64),
   (166, .umask), (222, .mmap2), (216, .mremap), (214, .brk), (403, .clockGettime64), (406, .clockGetres64),
   (160, .uname), (261, .prlimit), (278, .getrandom), (132, .sigaltstack), (123, .schedGetaffinity),
   (82, .succeeds), (83, .succeeds), (52, .succeeds),    ]

/-- The numbers of the o32 ABI of MIPS, without their 4000. -/
def o32Calls : List (Nat × Call) :=
  [(395, .shmget), (397, .shmat), (398, .shmdt), (396, .shmctl), (393, .semget), (420, .semtimedop64), (394, .semctl), (399, .msgget), (400, .msgsnd), (401, .msgrcv), (402, .msgctl), (117, .ipc),
   (21, .mount), (52, .umount2), (61, .chroot), (216, .pivotRoot),
   (284, .inotifyInit), (329, .inotifyInit1), (285, .inotifyAddWatch), (286, .inotifyRmWatch),
   (143, .flock),
   (354, .memfdCreate), (207, .sendfile), (237, .sendfile64), (304, .splice), (306, .tee), (360, .copyFileRange),
   (9, .link), (296, .linkat), (316, .utimensat), (412, .utimensat64), (267, .utimes), (30, .utime), (292, .futimesat), (202, .chown), (16, .lchown), (95, .fchown), (291, .fchownat), (224, .setxattr), (225, .lsetxattr), (226, .fsetxattr), (227, .getxattr), (228, .lgetxattr), (229, .fgetxattr), (230, .listxattr), (231, .llistxattr), (232, .flistxattr), (233, .removexattr), (234, .lremovexattr), (235, .fremovexattr),
   (132, .getpgid), (57, .setpgid), (65, .getpgrp), (66, .setsid), (151, .getsid), (24, .getuid), (49, .geteuid), (47, .getgid), (50, .getegid), (23, .setuid), (46, .setgid), (70, .setreuid), (71, .setregid), (185, .setresuid), (190, .setresgid), (186, .getresuid), (191, .getresgid), (138, .setfsuid), (139, .setfsgid), (80, .getgroups), (81, .setgroups), (204, .capget), (205, .capset), (75, .setrlimit), (77, .getrusage), (43, .times), (96, .getpriority), (97, .setpriority), (239, .schedSetaffinity), (159, .schedGetparam), (158, .schedSetparam), (161, .schedGetscheduler), (160, .schedSetscheduler), (163, .schedGetPriorityMax), (164, .schedGetPriorityMin), (165, .schedRrGetInterval), (423, .schedRrGetInterval64),
   (188, .poll), (302, .ppoll), (414, .ppoll64), (142, .select), (301, .pselect6), (413, .pselect664), (248, .epollCreate), (326, .epollCreate1), (249, .epollCtl), (250, .epollWait), (313, .epollPwait), (441, .epollPwait2), (319, .eventfd), (325, .eventfd2), (321, .timerfdCreate), (323, .timerfdSettime), (411, .timerfdSettime64), (322, .timerfdGettime), (410, .timerfdGettime64), (317, .signalfd), (324, .signalfd4),
   (265, .clockNanosleep), (258, .timerSettime), (259, .timerGettime),
   (166, .nanosleep), (407, .clockNanosleep64), (104, .setitimer), (105, .getitimer), (27, .alarm), (257, .timerCreate), (409, .timerSettime64), (408, .timerGettime64), (260, .timerGetoverrun), (261, .timerDelete),
   (192, .prctl), (352, .seccomp), (168, .accept), (169, .bind), (170, .connect), (171, .getpeername), (172, .getsockname), (173, .getsockopt), (174, .listen), (175, .recv), (176, .recvfrom), (177, .recvmsg), (178, .send), (179, .sendmsg), (180, .sendto), (181, .setsockopt), (182, .shutdown), (183, .socket), (184, .socketpair), (334, .accept4),
   (42, .pipe), (328, .pipe2),
   (91, .munmap), (125, .mprotect), (218, .madvise), (144, .succeeds),
   (11, .execve), (213, .stat), (214, .lstat), (215, .fstat), (293, .fstatat), (255, .statfs64), (256, .fstatfs64), (116, .sysinfo),
   (3, .read), (4, .write), (5, .open_), (288, .openat), (6, .close), (366, .statx), (19, .lseek), (140, .llseek),
   (200, .pread), (201, .pwrite), (145, .readv), (146, .writev), (33, .access), (300, .faccessat), (439, .faccessat),
   (41, .dup), (63, .dup2), (327, .dup3), (55, .fcntl), (220, .fcntl), (54, .ioctl), (219, .getdents), (203, .getcwd),
   (12, .chdir), (133, .fchdir), (39, .mkdir), (289, .mkdirat), (40, .rmdir), (10, .unlink), (294, .unlinkat), (38, .rename),
   (295, .renameat), (351, .renameat2), (83, .symlink), (297, .symlinkat), (85, .readlink), (298, .readlinkat), (15, .chmod),
   (299, .fchmodat), (92, .truncate), (93, .ftruncate), (211, .truncate64), (212, .ftruncate64), (60, .umask), (210, .mmap2),
   (167, .mremap), (45, .brk), (78, .gettimeofday), (263, .clockGettime), (264, .clockGetres), (403, .clockGettime64),
   (406, .clockGetres64), (122, .uname), (76, .getrlimit), (338, .prlimit), (353, .getrandom), (206, .sigaltstack),
   (240, .schedGetaffinity), (283, .setThreadArea), (118, .succeeds), (152, .succeeds), (94, .succeeds),       ]

/-- The numbers of the n64 ABI of MIPS, without their 5000. -/
def n64Calls : List (Nat × Call) :=
  [(28, .shmget), (29, .shmat), (65, .shmdt), (30, .shmctl), (62, .semget), (63, .semop), (214, .semtimedop), (64, .semctl), (66, .msgget), (67, .msgsnd), (68, .msgrcv), (69, .msgctl),
   (160, .mount), (161, .umount2), (156, .chroot), (151, .pivotRoot),
   (243, .inotifyInit), (288, .inotifyInit1), (244, .inotifyAddWatch), (245, .inotifyRmWatch),
   (71, .flock),
   (314, .memfdCreate), (39, .sendfile), (263, .splice), (265, .tee), (320, .copyFileRange),
   (84, .link), (255, .linkat), (275, .utimensat), (226, .utimes), (130, .utime), (251, .futimesat), (90, .chown), (92, .lchown), (91, .fchown), (250, .fchownat), (180, .setxattr), (181, .lsetxattr), (182, .fsetxattr), (183, .getxattr), (184, .lgetxattr), (185, .fgetxattr), (186, .listxattr), (187, .llistxattr), (188, .flistxattr), (189, .removexattr), (190, .lremovexattr), (191, .fremovexattr),
   (119, .getpgid), (107, .setpgid), (109, .getpgrp), (110, .setsid), (122, .getsid), (100, .getuid), (105, .geteuid), (102, .getgid), (106, .getegid), (103, .setuid), (104, .setgid), (111, .setreuid), (112, .setregid), (115, .setresuid), (117, .setresgid), (116, .getresuid), (118, .getresgid), (120, .setfsuid), (121, .setfsgid), (113, .getgroups), (114, .setgroups), (123, .capget), (124, .capset), (155, .setrlimit), (96, .getrusage), (98, .times), (137, .getpriority), (138, .setpriority), (140, .schedGetparam), (139, .schedSetparam), (142, .schedGetscheduler), (141, .schedSetscheduler), (143, .schedGetPriorityMax), (144, .schedGetPriorityMin), (145, .schedRrGetInterval),
   (7, .poll), (261, .ppoll), (22, .select), (260, .pselect6), (207, .epollCreate), (285, .epollCreate1), (208, .epollCtl), (209, .epollWait), (272, .epollPwait), (441, .epollPwait2), (278, .eventfd), (284, .eventfd2), (280, .timerfdCreate), (282, .timerfdSettime), (281, .timerfdGettime), (276, .signalfd), (283, .signalfd4),
   (34, .nanosleep), (224, .clockNanosleep), (36, .setitimer), (35, .getitimer), (37, .alarm), (216, .timerCreate), (217, .timerSettime), (218, .timerGettime), (219, .timerGetoverrun), (220, .timerDelete),
   (153, .prctl), (312, .seccomp), (40, .socket), (41, .connect), (42, .accept), (43, .sendto), (44, .recvfrom), (45, .sendmsg), (46, .recvmsg), (47, .shutdown), (48, .bind), (49, .listen), (50, .getsockname), (51, .getpeername), (52, .socketpair), (53, .setsockopt), (54, .getsockopt), (293, .accept4),
   (21, .pipe), (287, .pipe2),
   (11, .munmap), (10, .mprotect), (27, .madvise), (25, .succeeds),
   (57, .execve), (134, .statfs), (135, .fstatfs), (97, .sysinfo),
   (0, .read), (1, .write), (2, .open_), (247, .openat), (3, .close), (4, .stat), (6, .lstat), (5, .fstat), (252, .fstatat),
   (326, .statx), (8, .lseek), (16, .pread), (17, .pwrite), (18, .readv), (19, .writev), (20, .access), (259, .faccessat),
   (439, .faccessat), (31, .dup), (32, .dup2), (286, .dup3), (70, .fcntl), (15, .ioctl), (308, .getdents), (77, .getcwd),
   (78, .chdir), (79, .fchdir), (81, .mkdir), (248, .mkdirat), (82, .rmdir), (85, .unlink), (253, .unlinkat), (80, .rename),
   (254, .renameat), (311, .renameat2), (86, .symlink), (256, .symlinkat), (87, .readlink), (257, .readlinkat), (88, .chmod),
   (258, .fchmodat), (74, .truncate), (75, .ftruncate), (93, .umask), (9, .mmap), (24, .mremap), (12, .brk),
   (94, .gettimeofday), (222, .clockGettime), (223, .clockGetres), (61, .uname), (95, .getrlimit), (297, .prlimit),
   (313, .getrandom), (129, .sigaltstack), (196, .schedGetaffinity), (195, .schedSetaffinity), (242, .setThreadArea), (72, .succeeds), (73, .succeeds),
   (89, .succeeds),    ]

/-- The numbers of 32-bit ARM, with EABI, and two of its own: `set_tls` and `cacheflush`. -/
def armCalls : List (Nat × Call) :=
  [(307, .shmget), (305, .shmat), (306, .shmdt), (308, .shmctl), (299, .semget), (298, .semop), (312, .semtimedop), (420, .semtimedop64), (300, .semctl), (303, .msgget), (301, .msgsnd), (302, .msgrcv), (304, .msgctl),
   (21, .mount), (52, .umount2), (61, .chroot), (218, .pivotRoot),
   (316, .inotifyInit), (360, .inotifyInit1), (317, .inotifyAddWatch), (318, .inotifyRmWatch),
   (143, .flock),
   (385, .memfdCreate), (187, .sendfile), (239, .sendfile64), (340, .splice), (342, .tee), (391, .copyFileRange),
   (182, .chown), (16, .lchown), (95, .fchown), (24, .getuid), (49, .geteuid), (47, .getgid), (50, .getegid), (23, .setuid), (46, .setgid), (70, .setreuid), (71, .setregid), (164, .setresuid), (170, .setresgid), (165, .getresuid), (171, .getresgid), (138, .setfsuid), (139, .setfsgid), (80, .getgroups), (81, .setgroups),
   (9, .link), (330, .linkat), (348, .utimensat), (412, .utimensat64), (269, .utimes), (326, .futimesat), (212, .chown), (198, .lchown), (207, .fchown), (325, .fchownat), (226, .setxattr), (227, .lsetxattr), (228, .fsetxattr), (229, .getxattr), (230, .lgetxattr), (231, .fgetxattr), (232, .listxattr), (233, .llistxattr), (234, .flistxattr), (235, .removexattr), (236, .lremovexattr), (237, .fremovexattr),
   (132, .getpgid), (57, .setpgid), (65, .getpgrp), (66, .setsid), (147, .getsid), (199, .getuid), (201, .geteuid), (200, .getgid), (202, .getegid), (213, .setuid), (214, .setgid), (203, .setreuid), (204, .setregid), (208, .setresuid), (210, .setresgid), (209, .getresuid), (211, .getresgid), (215, .setfsuid), (216, .setfsgid), (205, .getgroups), (206, .setgroups), (184, .capget), (185, .capset), (75, .setrlimit), (77, .getrusage), (43, .times), (96, .getpriority), (97, .setpriority), (241, .schedSetaffinity), (155, .schedGetparam), (154, .schedSetparam), (157, .schedGetscheduler), (156, .schedSetscheduler), (159, .schedGetPriorityMax), (160, .schedGetPriorityMin), (161, .schedRrGetInterval), (423, .schedRrGetInterval64),
   (168, .poll), (336, .ppoll), (414, .ppoll64), (142, .select), (335, .pselect6), (413, .pselect664), (250, .epollCreate), (357, .epollCreate1), (251, .epollCtl), (252, .epollWait), (346, .epollPwait), (441, .epollPwait2), (351, .eventfd), (356, .eventfd2), (350, .timerfdCreate), (353, .timerfdSettime), (411, .timerfdSettime64), (354, .timerfdGettime), (410, .timerfdGettime64), (349, .signalfd), (355, .signalfd4),
   (265, .clockNanosleep), (258, .timerSettime), (259, .timerGettime),
   (162, .nanosleep), (407, .clockNanosleep64), (104, .setitimer), (105, .getitimer), (257, .timerCreate), (409, .timerSettime64), (408, .timerGettime64), (260, .timerGetoverrun), (261, .timerDelete),
   (172, .prctl), (383, .seccomp), (281, .socket), (282, .bind), (283, .connect), (284, .listen), (285, .accept), (286, .getsockname), (287, .getpeername), (288, .socketpair), (289, .send), (290, .sendto), (291, .recv), (292, .recvfrom), (293, .shutdown), (294, .setsockopt), (295, .getsockopt), (296, .sendmsg), (297, .recvmsg), (366, .accept4),
   (42, .pipe), (359, .pipe2),
   (91, .munmap), (125, .mprotect), (220, .madvise), (144, .succeeds),
   (11, .execve), (195, .stat), (196, .lstat), (197, .fstat), (327, .fstatat), (266, .statfs64), (267, .fstatfs64), (116, .sysinfo),
   (3, .read), (4, .write), (5, .open_), (322, .openat), (6, .close), (397, .statx), (19, .lseek), (140, .llseek),
   (180, .pread), (181, .pwrite), (145, .readv), (146, .writev), (33, .access), (334, .faccessat), (439, .faccessat), (41, .dup),
   (63, .dup2), (358, .dup3), (55, .fcntl), (221, .fcntl), (54, .ioctl), (217, .getdents), (183, .getcwd), (12, .chdir),
   (133, .fchdir), (39, .mkdir), (323, .mkdirat), (40, .rmdir), (10, .unlink), (328, .unlinkat), (38, .rename), (329, .renameat),
   (382, .renameat2), (83, .symlink), (331, .symlinkat), (85, .readlink), (332, .readlinkat), (15, .chmod), (333, .fchmodat),
   (92, .truncate), (93, .ftruncate), (193, .truncate64), (194, .ftruncate64), (60, .umask), (192, .mmap2), (163, .mremap),
   (45, .brk), (78, .gettimeofday), (263, .clockGettime), (264, .clockGetres), (403, .clockGettime64), (406, .clockGetres64),
   (122, .uname), (191, .getrlimit), (369, .prlimit), (384, .getrandom), (186, .sigaltstack), (242, .schedGetaffinity),
   (0xf0005, .setThreadArea), (0xf0002, .succeeds), (118, .succeeds), (148, .succeeds), (94, .succeeds),       ]

/-- The numbers of i686. -/
def i686Calls : List (Nat × Call) :=
  [(395, .shmget), (397, .shmat), (398, .shmdt), (396, .shmctl), (393, .semget), (420, .semtimedop64), (394, .semctl), (399, .msgget), (400, .msgsnd), (401, .msgrcv), (402, .msgctl), (117, .ipc),
   (21, .mount), (52, .umount2), (61, .chroot), (217, .pivotRoot),
   (291, .inotifyInit), (332, .inotifyInit1), (292, .inotifyAddWatch), (293, .inotifyRmWatch),
   (143, .flock),
   (356, .memfdCreate), (187, .sendfile), (239, .sendfile64), (313, .splice), (315, .tee), (377, .copyFileRange),
   (182, .chown), (16, .lchown), (95, .fchown), (24, .getuid), (49, .geteuid), (47, .getgid), (50, .getegid), (23, .setuid), (46, .setgid), (70, .setreuid), (71, .setregid), (164, .setresuid), (170, .setresgid), (165, .getresuid), (171, .getresgid), (138, .setfsuid), (139, .setfsgid), (80, .getgroups), (81, .setgroups),
   (9, .link), (303, .linkat), (320, .utimensat), (412, .utimensat64), (271, .utimes), (30, .utime), (299, .futimesat), (212, .chown), (198, .lchown), (207, .fchown), (298, .fchownat), (226, .setxattr), (227, .lsetxattr), (228, .fsetxattr), (229, .getxattr), (230, .lgetxattr), (231, .fgetxattr), (232, .listxattr), (233, .llistxattr), (234, .flistxattr), (235, .removexattr), (236, .lremovexattr), (237, .fremovexattr),
   (132, .getpgid), (57, .setpgid), (65, .getpgrp), (66, .setsid), (147, .getsid), (199, .getuid), (201, .geteuid), (200, .getgid), (202, .getegid), (213, .setuid), (214, .setgid), (203, .setreuid), (204, .setregid), (208, .setresuid), (210, .setresgid), (209, .getresuid), (211, .getresgid), (215, .setfsuid), (216, .setfsgid), (205, .getgroups), (206, .setgroups), (184, .capget), (185, .capset), (75, .setrlimit), (77, .getrusage), (43, .times), (96, .getpriority), (97, .setpriority), (241, .schedSetaffinity), (155, .schedGetparam), (154, .schedSetparam), (157, .schedGetscheduler), (156, .schedSetscheduler), (159, .schedGetPriorityMax), (160, .schedGetPriorityMin), (161, .schedRrGetInterval), (423, .schedRrGetInterval64),
   (168, .poll), (309, .ppoll), (414, .ppoll64), (142, .select), (308, .pselect6), (413, .pselect664), (254, .epollCreate), (329, .epollCreate1), (255, .epollCtl), (256, .epollWait), (319, .epollPwait), (441, .epollPwait2), (323, .eventfd), (328, .eventfd2), (322, .timerfdCreate), (325, .timerfdSettime), (411, .timerfdSettime64), (326, .timerfdGettime), (410, .timerfdGettime64), (321, .signalfd), (327, .signalfd4),
   (162, .nanosleep), (407, .clockNanosleep64), (104, .setitimer), (105, .getitimer), (27, .alarm), (259, .timerCreate), (409, .timerSettime64), (408, .timerGettime64),
   (172, .prctl), (354, .seccomp), (359, .socket), (360, .socketpair), (361, .bind), (362, .connect), (363, .listen), (364, .accept4), (365, .getsockopt), (366, .setsockopt), (367, .getsockname), (368, .getpeername), (369, .sendto), (370, .sendmsg), (371, .recvfrom), (372, .recvmsg), (373, .shutdown),
   (42, .pipe), (331, .pipe2),
   (91, .munmap), (125, .mprotect), (219, .madvise), (144, .succeeds),
   (11, .execve), (195, .stat), (196, .lstat), (197, .fstat), (300, .fstatat), (268, .statfs64), (269, .fstatfs64), (116, .sysinfo),
   (3, .read), (4, .write), (5, .open_), (295, .openat), (6, .close), (383, .statx), (19, .lseek), (140, .llseek),
   (180, .pread), (181, .pwrite), (145, .readv), (146, .writev), (33, .access), (307, .faccessat), (439, .faccessat), (41, .dup),
   (63, .dup2), (330, .dup3), (55, .fcntl), (221, .fcntl), (54, .ioctl), (220, .getdents), (183, .getcwd), (12, .chdir),
   (133, .fchdir), (39, .mkdir), (296, .mkdirat), (40, .rmdir), (10, .unlink), (301, .unlinkat), (38, .rename), (302, .renameat),
   (353, .renameat2), (83, .symlink), (304, .symlinkat), (85, .readlink), (305, .readlinkat), (15, .chmod), (306, .fchmodat),
   (92, .truncate), (93, .ftruncate), (193, .truncate64), (194, .ftruncate64), (60, .umask), (192, .mmap2), (163, .mremap),
   (45, .brk), (78, .gettimeofday), (265, .clockGettime), (266, .clockGetres), (403, .clockGettime64), (406, .clockGetres64),
   (122, .uname), (191, .getrlimit), (340, .prlimit), (355, .getrandom), (186, .sigaltstack), (242, .schedGetaffinity),
   (243, .setThreadArea), (118, .succeeds), (148, .succeeds), (94, .succeeds),    (267, .succeeds),    ]

/-- The numbers of PowerPC, where those of each width that the other doesn't have are left to it not asking for them. -/
def powerpcCalls : List (Nat × Call) :=
  [(395, .shmget), (397, .shmat), (398, .shmdt), (396, .shmctl), (393, .semget), (420, .semtimedop64), (394, .semctl), (399, .msgget), (400, .msgsnd), (401, .msgrcv), (402, .msgctl), (117, .ipc),
   (21, .mount), (52, .umount2), (61, .chroot), (203, .pivotRoot),
   (275, .inotifyInit), (318, .inotifyInit1), (276, .inotifyAddWatch), (277, .inotifyRmWatch),
   (143, .flock),
   (360, .memfdCreate), (186, .sendfile), (226, .sendfile64), (283, .splice), (284, .tee), (379, .copyFileRange),
   (9, .link), (294, .linkat), (304, .utimensat), (412, .utimensat64), (251, .utimes), (30, .utime), (290, .futimesat), (181, .chown), (16, .lchown), (95, .fchown), (289, .fchownat), (209, .setxattr), (210, .lsetxattr), (211, .fsetxattr), (212, .getxattr), (213, .lgetxattr), (214, .fgetxattr), (215, .listxattr), (216, .llistxattr), (217, .flistxattr), (218, .removexattr), (219, .lremovexattr), (220, .fremovexattr),
   (132, .getpgid), (57, .setpgid), (65, .getpgrp), (66, .setsid), (147, .getsid), (24, .getuid), (49, .geteuid), (47, .getgid), (50, .getegid), (23, .setuid), (46, .setgid), (70, .setreuid), (71, .setregid), (164, .setresuid), (169, .setresgid), (165, .getresuid), (170, .getresgid), (138, .setfsuid), (139, .setfsgid), (80, .getgroups), (81, .setgroups), (183, .capget), (184, .capset), (75, .setrlimit), (77, .getrusage), (43, .times), (96, .getpriority), (97, .setpriority), (222, .schedSetaffinity), (155, .schedGetparam), (154, .schedSetparam), (157, .schedGetscheduler), (156, .schedSetscheduler), (159, .schedGetPriorityMax), (160, .schedGetPriorityMin), (161, .schedRrGetInterval), (423, .schedRrGetInterval64),
   (167, .poll), (281, .ppoll), (414, .ppoll64), (142, .select), (280, .pselect6), (413, .pselect664), (236, .epollCreate), (315, .epollCreate1), (237, .epollCtl), (238, .epollWait), (303, .epollPwait), (441, .epollPwait2), (307, .eventfd), (314, .eventfd2), (306, .timerfdCreate), (311, .timerfdSettime), (411, .timerfdSettime64), (312, .timerfdGettime), (410, .timerfdGettime64), (305, .signalfd), (313, .signalfd4),
   (248, .clockNanosleep), (241, .timerSettime), (242, .timerGettime),
   (162, .nanosleep), (407, .clockNanosleep64), (104, .setitimer), (105, .getitimer), (27, .alarm), (240, .timerCreate), (409, .timerSettime64), (408, .timerGettime64), (243, .timerGetoverrun), (244, .timerDelete),
   (171, .prctl), (358, .seccomp), (326, .socket), (327, .bind), (328, .connect), (329, .listen), (330, .accept), (331, .getsockname), (332, .getpeername), (333, .socketpair), (334, .send), (335, .sendto), (336, .recv), (337, .recvfrom), (338, .shutdown), (339, .setsockopt), (340, .getsockopt), (341, .sendmsg), (342, .recvmsg), (344, .accept4),
   (42, .pipe), (317, .pipe2),
   (91, .munmap), (125, .mprotect), (205, .madvise), (144, .succeeds),
   (11, .execve), (116, .sysinfo),
   (3, .read), (4, .write), (5, .open_), (286, .openat), (6, .close), (106, .stat), (107, .lstat), (108, .fstat), (291, .fstatat),
   (383, .statx), (19, .lseek), (140, .llseek), (179, .pread), (180, .pwrite), (145, .readv), (146, .writev), (33, .access),
   (298, .faccessat), (439, .faccessat), (41, .dup), (63, .dup2), (316, .dup3), (55, .fcntl), (204, .fcntl), (54, .ioctl),
   (202, .getdents), (182, .getcwd), (12, .chdir), (133, .fchdir), (39, .mkdir), (287, .mkdirat), (40, .rmdir), (10, .unlink),
   (292, .unlinkat), (38, .rename), (293, .renameat), (357, .renameat2), (83, .symlink), (295, .symlinkat), (85, .readlink),
   (296, .readlinkat), (15, .chmod), (297, .fchmodat), (92, .truncate), (93, .ftruncate), (193, .truncate64), (194, .ftruncate64),
   (60, .umask), (90, .mmap), (192, .mmap2), (163, .mremap), (45, .brk), (78, .gettimeofday), (246, .clockGettime),
   (247, .clockGetres), (403, .clockGettime64), (406, .clockGetres64), (122, .uname), (76, .getrlimit), (190, .getrlimit),
   (325, .prlimit), (359, .getrandom), (185, .sigaltstack), (223, .schedGetaffinity), (118, .succeeds), (148, .succeeds),
   (94, .succeeds),    ]

/-- The calls that the kernel serves, by their numbers on it. What isn't here is for `serveTaskCalls`, or isn't there. -/
def Architecture.calls : Architecture → List (Nat × Call)
  | .x86_64 => x86_64Calls
  | .i686 => i686Calls
  | .arm => armCalls
  | .aarch64 | .riscv64 => genericCalls
  | .riscv32 => generic32Calls
  | .mips 32 _ _ => o32Calls.map fun entry => (entry.1 + 4000, entry.2)
  | .mips _ _ _ => n64Calls.map fun entry => (entry.1 + 5000, entry.2)
  -- The same numbers have the wide `struct stat` on 64-bit systems and `stat64` on the others.
  | .powerpc 32 _ =>
    [(195, .stat), (196, .lstat), (197, .fstat), (252, .statfs64), (253, .fstatfs64)] ++
      powerpcCalls.filter fun entry => ![106, 107, 108].contains entry.1
  | .powerpc _ _ => [(99, .statfs), (100, .fstatfs), (252, .statfs64), (253, .fstatfs64)] ++ powerpcCalls

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
  | .x86_64, flags | .i686, flags | .riscv64, flags | .riscv32, flags => flags
  | .mips _ _ _, flags => moveBits mipsOpenBits flags
  | .powerpc _ _, flags => moveBits powerpcOpenBits flags
  | .aarch64, flags | .arm, flags =>
    let low := flags &&& 0xc000
    let high := flags &&& 0x30000
    (flags - low - high) ||| (low * 4) ||| (high / 4)

/-- The flags of `open` of a guest, from those of the kernel. -/
def Architecture.guestFlags : Architecture → Nat → Nat
  | .mips _ _ _, flags => moveBits (mipsOpenBits.map fun move => (move.2, move.1)) flags
  | .powerpc _ _, flags => moveBits (powerpcOpenBits.map fun move => (move.2, move.1)) flags
  | architecture, flags => architecture.openFlags flags

/-- `struct stat`, and of 32-bit systems `struct stat64`, whose times 2038 ends: what asks for them asks for `statx` first. -/
def Architecture.stat : Architecture → Kernel.Stat → ByteArray
  | .x86_64, value => Abi.stat value
  | .i686, value => Abi.stat64 value
  | .arm, value => Abi.armStat64 value
  | .aarch64, value | .riscv64, value | .riscv32, value => Abi.genericStat value
  | .mips 32 big _, value => Abi.mipsStat64 value big
  | .mips _ big _, value => Abi.mips64Stat value big
  | .powerpc 32 big, value => Abi.powerpcStat64 value big
  | .powerpc _ big, value => Abi.stat value big

/-- The number of an error of a guest, which on MIPS isn't that of Linux elsewhere for those above 34. -/
def Architecture.errno : Architecture → Nat → Nat
  | .mips _ _ _, errno =>
    match [(35, 45), (36, 78), (37, 46), (38, 89), (39, 93), (40, 90), (42, 35), (43, 36), (61, 96), (62, 62), (75, 79), (84, 88),
        (110, 145), (112, 147), (113, 148), (114, 149), (115, 150), (125, 158),
        -- Those of sockets.
        (88, 95), (89, 96), (90, 97), (91, 98), (92, 99), (93, 120), (94, 121), (95, 122), (97, 124), (98, 125), (100, 127),
        (103, 130), (104, 131), (105, 132), (106, 133), (107, 134), (108, 143), (111, 146), (99, 126), (101, 128)].lookup errno with
    | some number => number
    | none => errno
  | _, errno => errno

/-- `MAP_ANONYMOUS`. -/
def Architecture.mapAnonymous : Architecture → Nat
  | .mips _ _ _ => 0x800
  | _ => 0x20

/-- Which argument the low or high word of the offset of `pread` starts at, on 32 bits: MIPS aligns a pair to an even register. -/
def Architecture.pairBase : Architecture → Nat
  | .mips _ _ _ | .powerpc _ _ | .arm => 4
  | _ => 3

/-- What `uname` and `AT_PLATFORM` say. -/
def Architecture.name : Architecture → String
  | .x86_64 => "x86_64"
  | .i686 => "i686"
  | .aarch64 => "aarch64"
  | .arm => "armv7l"
  | .riscv64 => "riscv64"
  | .riscv32 => "riscv32"
  | .mips 32 _ _ => "mips"
  | .mips _ _ _ => "mips64"
  | .powerpc 32 _ => "ppc"
  | .powerpc _ true => "ppc64"
  | .powerpc _ false => "ppc64le"

end Bap.Linux
