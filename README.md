# BAP in Lean

A binary analysis platform written in [Lean 4](https://lean-lang.org): it loads
executables, lifts machine code to BIL, analyzes it, emulates it and executes it
symbolically, with machine-checked proofs about most of what it does.

This is a port of the [Binary Analysis Platform](https://github.com/BinaryAnalysisPlatform/bap).
The OCaml and Rust implementation it came from is on the
[`ocaml`](https://github.com/PerfectLaugh/bap/tree/ocaml) branch, with the history of both.

## What it does

- **Loads** ELF (including relocatable objects, which it links), PE, Mach-O and COFF.
- **Disassembles** with LLVM for x86, x86-64, AArch64, ARM, Thumb, RISC-V, MIPS and PowerPC,
  from the entry point, symbols, init arrays and unwind tables, following direct calls.
- **Lifts** to BIL through Primus Lisp semantics in `semantics/`.
- **Analyzes**: control flow, SSA, liveness, dead code, constant propagation, cross references,
  call graphs, backward slicing, taint, strings and decompilation to C-like text.
- **Emulates** with a JIT, hooks and checkpoints. Tasks follow the Linux model: a thread and a process are tasks that differ
  in what `clone` shares. `runProcesses` schedules them, and `serveTaskCalls` gives guests the system calls of processes and
  pthreads: `fork`, `clone`, `waitpid`, `exit`, `futex`, `mmap` and others.
- **Runs Linux programs** in a virtual kernel of pure Lean, static and dynamic, on x86-64, AArch64, i686 and ARM with Thumb, and static on RISC-V, MIPS and PowerPC of either width and order: files, descriptors and the
  clock are all in it, and nothing reaches the host. A program sees only what was copied in before it started, and can run others of it with `execve`, scripts too. It has `/proc` and what libc reads of `/sys`, made by pure functions when they
  are opened, and `Kernel.addGenerated` puts a file of any path in that way. A machine can be
  saved at any instruction and go on from the file alone, with its tasks, its memory, its files and its signals, and runs the same instructions
  in the same order as if it hadn't stopped. A model of a runtime outside the kernel (locks, a debugger, JNI, an allocator) is a
  `RuntimeModel`: a name and a version that a checkpoint knows it by, callbacks that it attaches again, and its state, which goes in
  the same file. A checkpoint says which format, BAP, semantics and program it is of, and one that can't go on as it would have is refused.
  Memory is as Linux has it, as far as `testsuite/src/libc-memory.c` goes, which agrees with Linux itself: `brk` that gives back, `MADV_DONTNEED`, `mremap`, and `MAP_SHARED`, of files and of anonymous memory, between processes too, with `futex` on what they share. What is written to a shared mapping reaches its file and other processes at each system call and when another process runs, which is not within a parallel round. There is no `SIGBUS` past the end of a file, and `MADV_DONTNEED` of a segment of a program gives zeros instead of the file.
  `Machine.track` says where each byte of a run came from, whichever thread or process ran it: what a system call returns or leaves in memory, a file by its path and offset, `/proc` too, what JNI gives, and whatever `markMemory` and `markRegister` say, through registers, memory, vectors, flattened control flow and copies, by the byte. `explainMemory` and `explainRegister` give the way from the source, with each instruction and value, and tell a data dependency from a selection, a pointer and a branch that chose a constant, which is likely and not proved. What a program writes to a file or a pipe keeps what it came from when it is read there, and a child has what its parent had. `Machine.journal` keeps each instruction of each thread, each call and return as they were seen, wherever in a block, so that `callStack` needs no frame pointer, and each system call and call of JNI with what it answered and left. `firstEntry` and `whyEntered` say how a run first came to an address and what decided it, and `compareRuns` where two runs part and what they were given differently first. Both run one instruction at a time, and are in a checkpoint as models, which `taintModel` and `journalModel` go on from. Pipes are there too, `pipe` and `pipe2`, which block and end as on Linux, with no limit to what they hold and no `SIGPIPE`. `testsuite/musl/build.py` builds what is tested against musl. `Machine.stepBack` undoes the last instructions, after `Machine.keepHistory`, by going back to what it kept and running the rest again. A state that `Machine.save` gave has the history it had, so that one put back with `Machine.restore` steps back from there. `Analysis.Cff` recovers a flattened machine as it ran, from where its dispatcher and its state are: each round's state and the next, where each handler starts and ends, what it asks of the kernel, the rounds that come round again, and with a tracker what decided each. `Analysis.Verdict` runs a machine to where a verdict is, saves it, and says where each byte of it came from and what of that can't be said, a round that went the wrong way among them; and `Analysis.Contract` says what a handler does, to check something faster against it. The journal says which process each instruction was of and when the machine was put back, and a tracker says that what no one wrote may have been there then. What `Machine.manifest` lists is what was loaded, by the digest of its file and whether its initializers ran, and `Machine.ofCheckpoint` can refuse a checkpoint without the libraries expected. `Machine.setExecutionMode` runs a machine in the interpreter, which never starts the compiler, or goes back to the JIT, at any point of a run, and either way it does the same things.
  Signals are as Linux has them on each of those, as far as `testsuite/src/libc-signals.c` goes, which agrees with qemu: handlers with their `siginfo_t` and a context that they can
  change, masks, `sigaltstack`, `sigsuspend`, `sigtimedwait`, `SIGCHLD`, a signal for a thread or a process, and faults that a handler takes. `pthread_cancel` works by them.
  `Machine.read` and `Machine.write` reach the memory of any of its processes by virtual address, without a program being able to tell, and `Machine.malloc`, `Machine.calloc`,
  `Machine.realloc` and `Machine.free` allocate in it from outside, in mappings of their own.
  `Machine.loadLibrary` loads a shared library into it from outside, as `dlopen` would, with all that it needs, with no libc or linker in the guest; what it imports can come from
  the host, `Machine.findSymbol` finds what it has and `Machine.call` calls that. Its thread-local storage is laid out and relocated for a libc to give threads their blocks by `LoadedLibrary.tls`,
  or `Machine.setupThreadTls` where there is none.
- **Executes symbolically**, solving path conditions with Z3.

## Building

You need [elan](https://github.com/leanprover/elan) (the toolchain comes from `lean-toolchain`),
Python 3, clang, CMake and Ninja. The first step downloads LLVM and Z3 and builds them into
`_deps/`, which takes a while.

```sh
python3 native/build-static.py
lake build
```

`build-static.py` generates the libc++ headers it needs from the LLVM sources, unless
`BAP_LIBCXX_INCLUDE` names a directory that has them. CI builds and tests on Linux and Windows.

With [just](https://github.com/casey/just), `just setup` is that first build, and `just` lists the rest: `just build`,
`just test`, and `just native` after a change to the C++ in `native/`, which compiles only that again, in seconds, and links it
into every executable, as Lake doesn't see it change (`build-static.py --objects`).

## Using it

```sh
lake exe bap analyze /usr/bin/bash      # functions, cross references and the call graph
lake exe bap disassemble /usr/bin/bash  # instructions and their BIL
lake exe bap image /usr/bin/bash        # what the loader sees
lake exe bap symbolic program.bil       # paths of a BIL program
lake exe bap mc c3                      # one instruction, from hex
lake exe bap run program args           # an x86, ARM, RISC-V, MIPS or PowerPC Linux program, in a virtual Linux
lake exe bap run --copy dir program     # the same, with a directory copied in first
lake exe bap run --root dir program     # the same, with its libraries from under a root of its architecture
lake exe bap run --strace program       # the same, saying each system call
lake exe bap run --stats program        # the same, saying at the end how many steps were taken back, and why
lake exe bap run --stop-after 1000000 file program  # the same, saved to a file after that many instructions
lake exe bap resume file                # goes on from it, in another process or on another machine
```

The Lisp semantics are read when a program starts, from `BAP_SEMANTICS_DIR`, else `semantics/` here, else the nearest
`semantics/` above the executable. Run `lake exe bap` for the other commands. Everything is also a library: `Bap.Runtime` has
the modules without the proofs.

## Testing

```sh
lake exe bap-tests      # or: just test
```

Two more tools are in `tools/`, and neither is part of the default build:

- `tools/difftest` runs each instruction on real execution, natively on x86-64 and i686 and under
  qemu-user for the other targets, and compares the registers, flags and memory with the lifted
  program. Linux only.
- `tools/smoke.py` counts the opcodes of each target that decode and lift. Linux only.

## What is proved

`Bap/Proofs/` and the modules next to the code hold about 6,200 theorems, checked by the Lean
kernel. No `sorry`, `native_decide` or `partial def` is in `Bap/`, and they use only the axioms
`propext`, `Classical.choice` and `Quot.sound`. For example:

- Lifting through the real, lazily compiled environment means what the Lisp source says
  (`thunked_instruction_means_source`).
- A JIT-compiled range ends as its blocks do one at a time in the interpreter
  (`lowerGraph_correct`), given the stated obligations of the C++.
- `toSsa` is an exact equivalence on runs (`toSsa_runs_iff`), and `optimize` is one where the input
  doesn't fail (`optimize_runs_iff`).
- A slice that reports `complete` reproduces its criteria (`slice_end_to_end`).
- Symbolic execution is sound against the concrete evaluator (`run_sound_loop_free`).
- `decryptBlock` is the InvCipher of a separate statement of FIPS-197
  (`decryptBlock_eq_specInvCipher`).
- The ELF linker writes the value of each relocation's ABI formula (`link_image`).

Fast implementations are proved equal to the plain definitions they replace, and swapped in with
`@[csimp]`, so the theorems speak of the code that runs.

### What is not proved

**Read the list at the top of [`Bap/Proofs.lean`](Bap/Proofs.lean)**: it has everything that is
trusted or only tested, with file and line. The main items are these:

- **That the Lisp semantics are what hardware does.** No proof can say so. `tools/difftest` tests
  it: 2,731 x86-64 and 2,449 i686 opcodes against a Ryzen 9 5950X, and the other targets against
  qemu, which is a second implementation and not silicon. Some PowerPC and legacy MIPS opcodes
  disagree on the edges of NaNs, as the list says. AVX-512 was checked only against a hand-written model,
  as that machine doesn't have it.
- **The C++ JIT, LLVM and Z3.** `Bap/Jit.lean` states the obligations the proofs rest on.
- **The Lean kernel, compiler and runtime**, and `IO.Ref`, tasks and mutexes behaving as modelled.
- **The specifications themselves**, such as FIPS-197, which are checked by reading.

## Layout

| Path | What is there |
|---|---|
| `Bap/Core`, `Bap/Bil`, `Bap/IR`, `Bap/Graph` | words, memory, BIL and its evaluator, IR and CFG |
| `Bap/Image`, `Bap/Disasm`, `Bap/Target`, `Bap/LLVM.lean` | loaders, disassembly, lifting |
| `Bap/Tasks.lean` | tasks, as the emulator and Primus share them |
| `Bap/Linux` | the virtual kernel, the ELF loader and the Linux machine |
| `Bap/Float.lean` | floating point in integers, which is what programs run on |
| `Bap/Primus`, `semantics/` | the Lisp evaluator, the lifted engine, the semantics of each target |
| `Bap/Emu.lean`, `Bap/Emu/`, `Bap/Jit.lean` | the emulator and the JIT interface |
| `Bap/Analysis`, `Bap/Decompile`, `Bap/Symbolic`, `Bap/Project` | analyses, decompiler, symbolic execution, projects |
| `Bap/Theory`, `Bap/Knowledge` | the core theory and the knowledge base |
| `Bap/Proofs/` | the proofs |
| `BapTests/`, `testsuite/` | tests and the binaries they use |
| `native/` | the C++ shims for LLVM, Z3 and the JIT, and their build |
| `tools/` | the differential and smoke tests |

## License

MIT. See [LICENSE](LICENSE).
