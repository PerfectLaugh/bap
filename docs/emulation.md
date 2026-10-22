# Running programs: Primus, Unicorn, and scripts

BAP runs binary programs in three ways:

| Way | Entry point | Use it to |
|-----|-------------|-----------|
| The `run` pass | `bap FILE --passes=run --run-systems=SYSTEM` | run a program from the command line, with the analyses of a Primus system |
| Scripts | `bap script FILE.ml ARG...`, with the `Bap_script` library | combine projects, systems, and analyses in OCaml, without writing a plugin |
| The emulator | the `Bap_emu` library, in a script | drive a program step by step: pause it, read and write its state, hook it, snapshot it |

All three run the program in a Primus system. A system is a set of components, e.g., the loader, the Lisp machine, the taint tracker, see `bap primus-systems` and `bap primus-components`. The systems differ in how they run the code:

| System | The code runs in | Notes |
|--------|------------------|-------|
| `bap:legacy-main` | the Primus interpreter | the lifted program |
| `bap:stubbed-executor` | the Primus interpreter | the lifted program, with the Lisp stubs of libc |
| `bap:unicorn-executor` | Unicorn, natively | the default; the stubs and the system calls still run in Primus |
| `bap:terminating-unicorn-executor` | Unicorn | with `bap:limit`, so that the program always ends |

The `run` pass and the scripts run `bap:unicorn-executor`, unless they name another system, or the `primus-unicorn` plugin, which is licensed under GPL, isn't installed, then they run `bap:legacy-main`. The Unicorn executor is many times faster than the interpreter. It hands an instruction to the interpreter only when Primus has to see it, e.g., when it reads a tainted or symbolic value, when it traps, or when the program writes code.

## The `run` pass

```bash
bap ./echo --passes=run --run-argv=hello,world
```

`--run-systems=bap:legacy-main` interprets the whole program instead, as BAP did before.

The options of the Unicorn executor:

| Option | Meaning |
|--------|---------|
| `--primus-unicorn-timeout=SECONDS` | terminates a machine after it has run for so long in Unicorn and in the stubs |
| `--primus-unicorn-checkpoint=FILE` and `--primus-unicorn-checkpoint-at=ADDR\|NAME` | save the state of the machine to `FILE`, when the code at the address first runs; the machine then continues |
| `--primus-unicorn-restore=FILE` | continues from a saved checkpoint, instead of the entry point |
| `--primus-unicorn-native-stubs=NAME,...` | runs these functions of libc on the state of Unicorn, instead of their Lisp stubs |

`--run-components=NAME,...` adds components to the system, e.g., the debugger or the taint tracker:

```bash
bap ./prog --passes=run --run-systems=bap:unicorn-executor \
  --run-components=bap:taint-primitives,bap:propagate-taint-by-computation,bap:select-default-taint-policy
```

### The debugger

The `bap:debugger` component stops the machines at the breakpoints, or at the first instruction if there are none. It then reads commands from the terminal or from a file:

```bash
bap ./prog --passes=run --run-systems=bap:unicorn-executor \
  --run-components=bap:debugger --primus-debugger-break=main \
  --primus-debugger-commands=commands.txt
```

| Command | Action |
|---------|--------|
| `c`, `continue` | continue to the next breakpoint |
| `s`, `step` | stop at the next instruction |
| `b`, `break ADDR\|NAME` | stop at the address or the subroutine |
| `d`, `delete ADDR\|NAME` | remove the breakpoint |
| `breaks` | list the breakpoints |
| `pc` | show the program counter |
| `regs` | show the registers, without the aliases |
| `reg NAME` | show the register |
| `set NAME VALUE` | set the register |
| `x ADDR [LEN]` | dump `LEN` (64) bytes of the memory |
| `write ADDR BYTE...` | store the bytes to the memory |
| `call NAME ARG...` | call the Lisp function and show its result |
| `quit [CODE]` | exit bap with `CODE` (0) |
| `help` | show this help |

The debugger behaves the same in the interpreter and in Unicorn. It observes only the stops, see `Primus.Interpreter.stop_reached`, so Unicorn runs at full speed between the breakpoints.

## Scripts

`bap script` compiles an OCaml script to native code and runs it. The script links the libraries of BAP, plus those that its `#require` lines name:

```bash
bap script [--cache-dir=DIR] script.ml ARG...
```

With `--cache-dir`, the compiled script is cached, and the next run skips the compilation. `Bap_script.args ()` returns the arguments after the file.

A script configures the analyses with the arguments of the functions that it calls:

```ocaml
let () =
  let file = List.hd (Bap_script.args ()) in
  ignore
    (Bap_script.run ~args:[ "hello"; "cruel"; "world" ]
       (Bap_script.project file))
```

- `Bap_script.project file` loads the file, without its disassembly, see [Bare projects](#bare-projects), and runs the passes that run automatically, e.g., `api`. `~api` adds folders of api files, and `~lisp` adds a Primus Lisp program, e.g., `~lisp:{ paths = [ dir ]; features = [ "syscalls" ] }`.
- `Bap_script.run project` runs the program in a system, by default `bap:unicorn-executor`. Use `~components` to add components by name, and `~init` to add the script's own components. `~args`, `~envp`, and `~entry` set the arguments, the environment, and the entry point.

### Bare projects

`Bap_script.project` skips the disassembly and the lifting. These are the expensive parts of loading, and Unicorn doesn't need them. The program then has only the subroutines of the file's named symbols, plus those the user provides, e.g., with `--read-symbols-from`. A stripped file without either gets the subroutines that the knowledge base finds instead, which costs a scan of the whole code. Primus lifts the instructions that it needs on demand, e.g., the system calls.

`Bap_script.project ~disassemble:true` disassembles and lifts the file, as the `disassemble` command does, e.g., for `bap:legacy-main`, which interprets the whole program, or for the analyses of the whole program.

### The options of the plugins

A script starts bap without command-line options, so the options of the plugins come from the environment or from the configuration files. The environment variable of an option is its full name in upper case, with `BAP_` in front and the dashes replaced by underscores:

```bash
BAP_READ_SYMBOLS_FROM=prog.symbols bap script script.ml prog
```

### The debugger of the scripts

The `Bap_script_debugger` library (`#require "bap-frontend.script-debugger"`) calls the script's handlers at the stops:

```ocaml
#require "bap-primus, bap-frontend.script-debugger"

open Bap_primus.Std
module Debugger = Bap_script_debugger

module Show (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Eval = Primus.Interpreter.Make (Machine)
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let stopped addr =
    Eval.get (Bap.Std.Var.create "RAX" (Bap.Std.Type.imm 64)) >>= fun x ->
    Printf.printf "at %s RAX = %s\n%!" (Bap.Std.Addr.string_of_value addr)
      (Bap.Std.Word.string_of_value (Primus.Value.to_word x));
    Stops.set_stepping false
end

let () =
  Debugger.break "0x4004c0";
  Debugger.on_stop (module Show);
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor" ~init:[ Debugger.component ]
       (Bap_script.project (List.hd (Bap_script.args ()))))
```

- A handler steps with `Stops.set_stepping true`, and adds or removes breakpoints with `Stops.add` and `Stops.remove`.
- It changes registers with `Primus.Interpreter.Make.set` and memory with `Primus.Interpreter.Make.store`, so that Unicorn sees the changes.
- To watch only certain addresses, observe `Primus.Interpreter.stop_reached`, not `pc_change`. An observer of `pc_change` makes Unicorn stop at every instruction.

## The emulator: `Bap_emu`

`Bap_emu` (`#require "bap-primus-unicorn.emu"`) runs a program in Unicorn and lets the script drive it, much as one drives Unicorn itself. The program pauses before its first instruction:

```ocaml
#require "bap-primus-unicorn.emu"
module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
  match Emu.run emu ~until:0x40076bL with
  | Paused ->
      Printf.printf "paused at %Lx, argc = %Ld\n" (Emu.pc emu) (Emu.reg emu "RDI");
      ignore (Emu.run emu)
  | Exited code -> ignore code
  | Running | Failed _ -> ()
```

### Running and pausing

| Function | Action |
|----------|--------|
| `run ?until emu` | continue until the instruction at `until`, a `stop`, or the end |
| `step emu` | run one instruction |
| `stop emu` | pause before the next instruction, e.g., from a hook |
| `pc`, `set_pc` | the address of the next instruction; with the Thumb bit on ARM |
| `status`, `exit_code` | the state of the program |

### Registers, memory, and code

| Function | Action |
|----------|--------|
| `registers`, `reg`, `set_reg` | the registers of the target, by name, e.g., `RAX` |
| `read emu addr n`, `write emu addr data` | the bytes of the memory, also of the code, so that the change stays |
| `write_direct emu addr data` | the bytes of Unicorn's copy of the memory, also in the hooks |
| `bir emu addr` | the size and the BIR of the instruction at the address, lifted on demand from its current bytes, also in the hooks; Thumb on ARM by the lower bit of the address |
| `symbols`, `add_symbol` | the names of the functions; name new code, e.g., code that the program unpacked |
| `unstub emu name` | run the program's own code of a function, instead of its Lisp stub |

`write` stores the bytes to the memory of Primus, from which they go to Unicorn, so the change stays, also of a read-only page, e.g., of the code:

```ocaml
(* mov $0xa, %edi, which prints the newline, prints + instead *)
Emu.write emu 0x400727L "\xbf\x2b"
```

`write_direct` changes only Unicorn's copy of a read-only page, which is lost when Unicorn copies the page again, e.g., after a snapshot, and which the interpreter doesn't see, but it is the only write in the hooks.

The program has no disassembled BIR in a bare project, so `bir` lifts the instruction, as Primus does when it interprets it. The patched code is lifted from its new bytes:

```ocaml
match Emu.bir emu 0x400727L with
| Some (size, blks) -> List.iter blks ~f:(fun b -> print_endline (Blk.to_string b))
| None -> print_endline "not an instruction"
```

### Hooks

| Function | Calls `f` |
|----------|-----------|
| `on_code ?first ?last emu f` | before each instruction in the range |
| `on_read`, `on_write` | before each load or store in the range |
| `on_call emu name f` | when the program calls the function; `f` returns `Default` to run it, or `Return x` to return `x` at once |

`arg emu n` reads the arguments of the called function, as its prototype tells, e.g., from the api files. While the program runs, a hook may only `stop` it, or `read` and `write_direct` the memory:

```ocaml
Emu.on_call emu "putchar" (fun emu ->
    if Emu.arg emu 0 = Int64.of_int (Char.code 'l') then Return 108L else Default)
```

### Traces and slices

`on_code` calls its closure for each instruction, which makes the program run tens to hundreds of times slower. `Emu.Trace` records the program counters natively, in a ring in C, with no call to OCaml:

| Function | Action |
|----------|--------|
| `Trace.start ?size ?blocks ?every ?accesses ?first ?last emu` | record the last `size` instructions, by default 2^20, or only the blocks with `~blocks:true`, or every `every`-th instruction, and the last `accesses` loads and stores |
| `Trace.insns ?last trace` | the program counters of the last instructions, also of a trace of blocks, whose blocks are decoded once |
| `Trace.save ?last trace file` | write the recorded program counters, one in hex a line |
| `Trace.count`, `Trace.accesses`, `Trace.stop` | the number of records, the recorded accesses, and the end of recording |

The trace of the blocks costs the least, about three times the time of the program, and its `insns` are the instructions of the trace of each instruction, which costs tens of times the time, as Unicorn calls a hook for each instruction:

```ocaml
let trace = Emu.Trace.start ~blocks:true ~size:(1 lsl 20) emu in
ignore (Emu.run emu);
ignore (Emu.Trace.save trace "pcs.txt")
```

`slice trace locations` is the dynamic backward slice of the values, that the paused program has in the registers, e.g., `Reg "RAX"`, or the memory, e.g., `Mem (addr, 4)`, over the trace: the instructions, whose values flow to them, through the registers, and, if the trace records the accesses, through the memory, at the addresses, that they had. It is a slice of the data, and with `~addresses:true` it follows the addresses of the loads and the stores too. The code, that Primus runs, e.g., the Lisp stubs, isn't in the trace, so the slice marks the `gaps`, where the registers or the memory, that it follows, were written outside of the trace:

```ocaml
let trace = Emu.Trace.start ~blocks:true ~accesses:(1 lsl 20) emu in
ignore (Emu.run emu ~until:0x400494L);
let s = Emu.slice trace [ Emu.Reg "RAX" ] in
List.iter s.steps ~f:(fun { Emu.pc; _ } -> printf "%Lx\n" pc)
```

### Snapshots and checkpoints

`snapshot` saves the state of the paused program in memory, and `restore` returns to it, as many times as needed. The hooks stay:

```ocaml
let snap = Emu.snapshot emu in
ignore (Emu.run emu);
Emu.restore emu snap;
Emu.set_reg emu "RDI" 2L;
ignore (Emu.run emu)
```

`save` writes a checkpoint to a file, and `create ~restore` continues from it, also in another run of bap:

```ocaml
ignore (Emu.run emu ~until:after_unpack);
Emu.add_symbol emu "decrypt" 0x602000L;
Emu.save emu "unpacked.ckpt";
(* ... later, or in another script *)
let emu = Emu.create ~restore:"unpacked.ckpt" proj in
Emu.on_call emu "decrypt" (fun _ -> Default)
```

A checkpoint keeps:
- the registers and the memory, as the program and the script changed them
- the names from `add_symbol` and the functions from `unstub`
- the digest of the program's file, so that it isn't restored on another program
- the states of the components that extend the checkpoints, see `Primus.Checkpoint`, e.g., the channels of Primus Lisp, the taint, and the symbolic inputs

The program continues the innermost run of Unicorn. Afterwards, the stub that started it completes, if it is known, see `Emu.complete`; e.g., `__libc_start_main` exits with the result of `main`.

### Primus from the script

`primus emu component` runs a component in the paused program's machine. Through it, the script can use the whole API of Primus, e.g., the environment, the memory, the linker, Lisp, or the taint tracker.

### Taint

```ocaml
let emu = Emu.create ~components:Emu.Taint.components proj in
ignore (Emu.run emu ~until:after_read);
Emu.Taint.introduce emu ~kind:"input" (Mem (buf, 16));
Emu.Taint.on_jump emu (fun _ ~kinds dst -> (* a jump on a tainted condition *) ());
ignore (Emu.run emu)
```

`kinds`, `is_tainted`, and `sanitize` query and remove the taints of a register or of memory.

### Symbolic execution

```ocaml
module Sym = Emu.Symbolic

let emu = Emu.create ~components:Sym.components proj in
ignore (Emu.run emu ~until:after_getchar);
Sym.symbolize emu (Reg "RAX");
let branches = ref [] in
Sym.on_branch emu (fun _ b -> branches := b :: !branches);
ignore (Emu.run emu);
List.iter (fun b ->
    match Sym.flip b with
    | Some model -> (* the inputs that take the other side of the branch *) ()
    | None -> ()) !branches
```

`formula` shows the formulas of a register or of memory, and `solve` finds a model of the constraints of the path taken.

### Several emulators

The emulators of a script run side by side, e.g., programs of different targets. Each has its own Unicorn engine, Primus system, knowledge, hooks, stops, and snapshots:

```ocaml
let a = Emu.create (Bap_script.project x86_file) in
let b = Emu.create (Bap_script.project arm_file) in
ignore (Emu.step a);
ignore (Emu.step b)
```

The script runs one of them at a time. `Emu.knowledge emu` returns the knowledge of a system after its program ended, e.g., the instructions that it lifted.

## See also

- The API reference of `Bap_emu`, `Bap_script`, and `Bap_script_debugger`, in `dune build @doc`.
- `Primus.Interpreter.Stops`, `Primus.Interpreter.stop_reached`, and `Primus.Checkpoint`, in the API reference of `bap-primus`.
- The functional tests in `tools/testsuite/run_tests.ml`, whose `emu/` and `script/` cases run every feature above.
