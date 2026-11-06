# BAP in Lean

A binary analysis platform written in [Lean 4](https://lean-lang.org): it loads executables, lifts machine code to BIL, analyzes,
emulates and symbolically executes it, with machine-checked proofs about most of what it does.

It is a port of the [Binary Analysis Platform](https://github.com/BinaryAnalysisPlatform/bap). The OCaml and Rust implementation it
came from is on the [`ocaml`](https://github.com/PerfectLaugh/bap/tree/ocaml) branch, with the history of both.

## What it does

- **Loads** ELF (linking relocatable objects), PE, Mach-O and COFF.
- **Disassembles** with LLVM for x86, x86-64, AArch64, ARM, Thumb, RISC-V, MIPS and PowerPC, from the entry point, symbols, init
  arrays and unwind tables.
- **Lifts** to BIL through the Primus Lisp semantics in `semantics/`.
- **Analyzes**: control flow, SSA, liveness, dead code, constant propagation, cross references, call graphs, slicing, taint, strings,
  and decompilation to C-like text.
- **Emulates** with a JIT, hooks, traces and checkpoints. Threads and processes are Linux-style tasks.
- **Executes symbolically**, solving path conditions with Z3.
- **Runs Linux programs** in a virtual kernel of pure Lean, where nothing reaches the host:
  - static and dynamic on x86-64, AArch64, i686 and ARM/Thumb; static on RISC-V, MIPS and PowerPC of either width and byte order;
  - files, descriptors, pipes, sockets, terminals, `/proc`, signals, timers, `ptrace`, seccomp, io_uring and SysV IPC, checked against
    Linux by the programs in `testsuite/src`;
  - checkpoints at any instruction, which go on from the file alone and run exactly as an uninterrupted run would;
  - byte-level taint (`Machine.track`), a journal of every instruction, call and system call (`Machine.journal`), stepping back
    (`Machine.stepBack`), and analyses of flattened control flow, verdicts and handler contracts (`Analysis.Cff`, `Verdict`, `Contract`);
  - access from the host: read and write guest memory, allocate in it, load libraries and call their functions (`Machine.read`,
    `Machine.malloc`, `Machine.loadLibrary`, `Machine.call` and the like);
  - runtime models outside the kernel (locks, a debugger, JNI, an allocator) as `RuntimeModel`s, which checkpoints keep.

## Building

You need [elan](https://github.com/leanprover/elan) (the toolchain comes from `lean-toolchain`), Python 3, clang, CMake and Ninja.
The first step downloads LLVM and Z3 and builds them into `_deps/`, which takes a while.

```sh
python3 native/build-static.py   # or: just setup
lake build                       # or: just build
```

After changing the C++ in `native/`, run `just native` (`build-static.py --objects`): Lake doesn't see that change by itself.
`build-static.py` generates the libc++ headers it needs unless `BAP_LIBCXX_INCLUDE` names a directory that has them. CI builds and
tests on Linux and Windows.

## Using it

```sh
lake exe bap analyze /usr/bin/bash      # functions, cross references and the call graph
lake exe bap disassemble /usr/bin/bash  # instructions and their BIL
lake exe bap image /usr/bin/bash        # what the loader sees
lake exe bap symbolic program.bil       # paths of a BIL program
lake exe bap mc c3                      # one instruction, from hex
lake exe bap run program args           # a Linux program in the virtual kernel
lake exe bap run --strace program       # ... printing each system call
lake exe bap run --copy dir program     # ... with a directory copied in (--root dir: libraries from a sysroot)
lake exe bap run --stop-after N file program && lake exe bap resume file   # checkpoint after N instructions, then go on
```

Run `lake exe bap` for the other commands and options. The Lisp semantics are read at startup from `BAP_SEMANTICS_DIR`, else
`semantics/` here, else the nearest `semantics/` above the executable. Everything is also a library; `Bap.Runtime` has the modules
without the proofs.

## Testing

```sh
lake exe bap-tests      # or: just test
```

Guest test programs are built against musl with `testsuite/musl/build.py`. Two more Linux-only tools in `tools/` are outside the
default build: `difftest` compares each lifted instruction with real execution (natively on x86-64 and i686, under qemu-user
elsewhere), and `smoke.py` counts the opcodes of each target that decode and lift.

## What is proved

`Bap/Proofs/` and the modules next to the code hold about 6,200 theorems checked by the Lean kernel, with no `sorry`,
`native_decide` or `partial def` in `Bap/`, and only the axioms `propext`, `Classical.choice` and `Quot.sound`. For example:

- Lifting through the real, lazily compiled environment means what the Lisp source says (`thunked_instruction_means_source`).
- A JIT-compiled range ends as its blocks do one at a time in the interpreter (`lowerGraph_correct`), given the C++'s stated obligations.
- `toSsa` is an exact equivalence on runs (`toSsa_runs_iff`), and `optimize` is one where the input doesn't fail (`optimize_runs_iff`).
- A slice that reports `complete` reproduces its criteria (`slice_end_to_end`).
- Symbolic execution is sound against the concrete evaluator (`run_sound_loop_free`).
- `decryptBlock` is the InvCipher of a separate statement of FIPS-197 (`decryptBlock_eq_specInvCipher`).
- The ELF linker writes the value of each relocation's ABI formula (`link_image`).

Fast implementations are proved equal to the plain definitions they replace and swapped in with `@[csimp]`, so the theorems are
about the code that runs.

### What is not proved

[`Bap/Proofs.lean`](Bap/Proofs.lean) lists everything that is trusted or only tested, with file and line. Mainly:

- **That the Lisp semantics match hardware.** `tools/difftest` tests 2,731 x86-64 and 2,449 i686 opcodes against a Ryzen 9 5950X,
  and the other targets against qemu (a second implementation, not silicon). Some PowerPC and legacy MIPS opcodes disagree on NaN
  edge cases, and AVX-512 is checked only against a hand-written model.
- **The C++ JIT, LLVM and Z3.** `Bap/Jit.lean` states the obligations the proofs rest on.
- **The Lean kernel, compiler and runtime**, including `IO.Ref`, tasks and mutexes behaving as modelled.
- **The specifications themselves**, such as FIPS-197, checked by reading.

## Layout

| Path | Contents |
|---|---|
| `Bap/Core`, `Bap/Bil`, `Bap/IR`, `Bap/Graph` | words, memory, BIL and its evaluator, IR and CFG |
| `Bap/Image`, `Bap/Disasm`, `Bap/Target`, `Bap/LLVM.lean` | loaders, disassembly, lifting |
| `Bap/Tasks.lean` | tasks, shared by the emulator and Primus |
| `Bap/Linux` | the virtual kernel, the ELF loader and the Linux machine |
| `Bap/Float.lean` | floating point in integers |
| `Bap/Primus`, `semantics/` | the Lisp evaluator, the lifted engine, the semantics of each target |
| `Bap/Emu.lean`, `Bap/Emu/`, `Bap/Jit.lean` | the emulator and the JIT interface |
| `Bap/Analysis`, `Bap/Decompile`, `Bap/Symbolic`, `Bap/Project` | analyses, decompiler, symbolic execution, projects |
| `Bap/Theory`, `Bap/Knowledge` | the core theory and the knowledge base |
| `Bap/Proofs/` | the proofs |
| `BapTests/`, `testsuite/` | tests and the binaries they use |
| `native/` | C++ shims for LLVM, Z3 and the JIT, and their build |
| `tools/` | the differential and smoke tests |

## License

MIT. See [LICENSE](LICENSE).
