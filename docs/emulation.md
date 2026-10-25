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
| `bap:lifted-executor` | the lifted engine, natively | the default; runs the semantics, that BAP lifts, see below; the stubs and the system calls still run in Primus |
| `bap:terminating-lifted-executor` | the lifted engine | with `bap:limit`, so that the program always ends |
| `bap:unicorn-executor` | Unicorn, natively | the stubs and the system calls still run in Primus |
| `bap:terminating-unicorn-executor` | Unicorn | with `bap:limit`, so that the program always ends |

The `run` pass, the scripts, and `Emu.create` run `bap:lifted-executor`, unless they name another system, or `bap:unicorn-executor`, if the `primus-lifted` plugin isn't loaded, or `bap:legacy-main`, if the plugins of the executors, which are licensed under GPL, aren't installed. The executors are many times faster than the interpreter, and Unicorn is the fastest, e.g., in the hot loops, see the lifted executor below. Each executor hands an instruction to the interpreter only when Primus has to see it, e.g., when it reads a tainted or symbolic value, when it traps, or when the program writes code.

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

### The lifted executor

The executors of the lifted engine, `bap:lifted-executor`, `bap:terminating-lifted-executor`, and `bap:lifted-binary-executor`, of the plugin `primus-lifted`, run the native code in the lifted engine, see `Bap_lifted`, rather than in Unicorn, which runs the semantics of the instructions, that BAP lifts, so that the program runs as the lifters see it. Their options are the ones of the Unicorn executor, `--primus-lifted-timeout`, `--primus-lifted-checkpoint`, `--primus-lifted-checkpoint-at`, `--primus-lifted-restore`, and `--primus-lifted-native-stubs`, and `--primus-lifted-jit=false`, which runs only the closures, see below. The executors share the loader of the program, `bap:load-binary-unicorn`, and the component `bap:lifted-emulator` of the lifted ones chooses the lifted engine. The lifted engine compiles each instruction, once, to the closures, and runs the intrinsics of the floats natively, as Primus Lisp runs them. The instructions, that it can't run, e.g., the system calls, or the traps, are interpreted in Primus. Its blocks, that run 32 times, are compiled by the JIT of LLVM to the native code of the host, from the instructions, that start them, to the one, that may jump, which ends the block, as in Unicorn, so that it runs about 70 million instructions per second in the loops, and about a million in the closures, e.g., while a hook of the memory, or a trace of the accesses, needs them. It records the traces, see `Emu.Trace`, as Unicorn does: the same instructions, blocks, and accesses, but on x86 without the reads of the descriptors of the segments, that Unicorn makes.

```bash
bap ./prog --passes=run --run-systems=bap:lifted-executor
```

`BAP_LIFTED_STATS=1` prints the numbers of the instructions, that the lifted engine ran, couldn't run, and ran in the compiled blocks, and `BAP_LIFTED_STATS=verbose` the ones, that it couldn't run, and the blocks, that it compiled, or couldn't, and why. The cases `lifted/TARGET/N` of the testsuite check the lifted engine against Unicorn, instruction by instruction, and `BAP_TESTSUITE_EXECUTOR=lifted` runs the other cases with its executors.

The changes of BAP to Unicorn, e.g., the restarted stores of its helpers, are the files of `plugins/primus_native/libunicorn/overlay`, see its README.

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
bap script [--cache-dir=DIR] [--check] script.ml ARG...
```

With `--cache-dir`, the compiled script is cached, and the next run skips the compilation. With `--check`, the script is compiled, but not run, so bap exits with 0, if it compiles, or prints the errors of the compiler, with the lines of the script, and exits with 1, e.g., in an editor or a hook of the commits; with `--cache-dir` too, the run, that follows, skips the compilation. `Bap_script.args ()` returns the arguments after the file.

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

`Bap_emu` (`#require "bap-primus-native.emu"`) runs a program in Unicorn and lets the script drive it, much as one drives Unicorn itself. The program pauses before its first instruction:

```ocaml
#require "bap-primus-native.emu"
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
| `insn_at emu pc`, `lifted_bytes emu addr n` | the instruction, that the lifted engine lifted at the address, to run it, with the bytes it was lifted from, and the bytes of the instructions from an address, as far as they were lifted, see below |
| `insns emu` | the addresses of the instructions, that `insn_at` has, in their order |
| `insns_since emu file`, `Checkpoint.insns_diff before after` | the instructions, that ran for the first time since the checkpoint, or between two checkpoints |
| `symbols`, `add_symbol` | the names of the functions; name new code, e.g., code that the program unpacked |
| `unstub emu name` | run the program's own code of a function, instead of its Lisp stub |
| `call emu addr ~args` | call a function with the arguments, on a zeroed stack, and get its result, see below |
| `regions`, `project` | the memory map, and the project of the memory, disassembled from the bytes, that the program has now, see below |

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

`read` and `bir` are of the bytes, that the memory has now. The lifted engine keeps each instruction, that it lifted to run it, with the bytes it was lifted from, until it lifts the instruction anew, when the bytes change before it runs again, so `insn_at` recovers the code, that ran, after the program overwrote or scrubbed it, e.g., the code it unpacked, and `lifted_bytes` reassembles a function from them, as far as its instructions were lifted:

```ocaml
(* after the run: the decrypted routine, as it executed, though the program zeroed it *)
match Emu.insn_at emu decrypted with
| Some { bytes; name; bir; _ } -> printf "%s %S\n" name bytes
| None -> print_endline "never lifted there";
Out_channel.write_all "decrypted.bin" ~data:(Emu.lifted_bytes emu decrypted 0x400)
```

The engine lifts the instructions of a block, that it compiles, a few ahead of the one, that runs, so an instruction right after a branch may be lifted without running. Unicorn translates the code in itself, where the script doesn't see it, so `insn_at` is `None` there: catch the writes with `on_write`, or read the code while it is in memory.

`insns` lists the addresses of the instructions, that ran, e.g., to dump the code, that the program unpacked, without knowing where it is. A checkpoint keeps the bytes of these instructions, so the program, that continues from it, in another run too, has the instructions, that ran before it, which `insn_at` lifts anew from their bytes, unless they ran again since:

```ocaml
let emu = Emu.create ~restore:"unpacked.ckpt" proj in
Emu.insns emu
|> List.filter ~f:(fun pc -> Option.is_none (Emu.function_at emu pc))
|> List.iter ~f:(fun pc ->
       let insn = Option.value_exn (Emu.insn_at emu pc) in
       printf "%Lx: %s\n" pc insn.name)
```

`insns_since emu file` tells the instructions, that ran for the first time since the checkpoint in the file was saved, e.g., to answer, what code an action ran, and `Checkpoint.insns_diff before after` the ones between two checkpoints, e.g., of a baseline and of the run after an experiment, without loading them; `Checkpoint.insns file` lists the ones of a checkpoint. An instruction, that ran before the checkpoint, and again since, isn't there, which a trace of the action tells, and the few, that the engine lifted after a branch, without running them, are:

```ocaml
Emu.save emu "before.ckpt";
ignore (Emu.call emu handler ~args:[ request ]);
Emu.insns_since emu "before.ckpt" |> List.iter ~f:(printf "%Lx\n")
```

### Hooks

| Function | Calls `f` |
|----------|-----------|
| `on_code ?first ?last emu f` | before each instruction in the range |
| `on_sites emu sites f` | before each instruction at one of the sites, with one hook, that the engine finds them natively with |
| `on_read`, `on_write` | before each load or store in the range; `on_write ~primus:true` also sees the stores of Primus and of the native functions of libc |
| `on_call emu name f` | when the program calls the function; `f` returns `Default` to run it, or `Return x` to return `x` at once |
| `on_syscall emu f` | at each system call, `f emu number args`, with the number and the six arguments, as the ABI of Linux passes them, e.g., `X8` and `X0`..`X5` of AArch64; `Return x` returns `x` from the call, and `Default` serves it as without the hook |
| `shell emu` | a prompt with the commands of the debugger on the paused program, see below |

A hook doesn't see again the instruction, before which it paused the program, when the program continues from there, so `on_code` may `stop` the program at an address unconditionally, and `run` stops there the next time the code reaches it.

The hooks of the engine don't see the stores, that it doesn't run: of the Lisp stubs, e.g., `fread` or `strcpy`, of the instructions, that Primus interprets, and of the native functions of libc, that replace their stubs, e.g., `memcpy`. `on_write ~primus:true` sees them too, the ones of Primus after each byte, and the ones of the native functions before them, in the pieces of at most 8 bytes, so a watch of a buffer sees, whoever fills it:

```ocaml
Emu.on_write emu ~first:buf ~last:Int64.(buf + 63L) ~primus:true (fun emu addr size _ ->
    printf "%d bytes at %Lx\n" size addr)
```

For several write predicates, `Emu.on_writes` shares one native hook per distinct range and gives every callback independent exact-once replay state. A subscription has optional `first`/`last`, `primus`, and `callback`; singleton `on_write` is the same API with one subscription. `write_profile emu` reports native dispatches, callback invocations, and callback seconds for that emulator, so grouped dispatch and per-callback costs are distinguishable.

A watch of many addresses, e.g., of a table of handlers, costs a hook of `on_code` each, which the lifted engine checks one by one at their instructions, and changes its hooks for, while `on_sites emu sites f` is one hook, which finds the sites in a set, or, in Unicorn, in C, so only the sites call OCaml.

The hooks stay, until the emulator is gone, unless a scope added them: `Emu.scoped emu f` removes the hooks of `on_code`, `on_sites`, `on_read`, `on_write`, `on_writes`, `on_call`, `on_syscall`, and `Trace.capture`, that `f` added, when it returns or raises, so an experiment, e.g., a `call` or a `drive`, doesn't leave them to the run after it:

```ocaml
Emu.scoped emu (fun () ->
    Emu.on_call emu "getuid" (fun _ -> Return 0L);
    Emu.drive emu handler ~args:[ request ] ~budget:100 ~service)
```

`arg emu n` reads the arguments of the called function, as its prototype tells, e.g., from the api files.

`on_syscall` serves the system calls, that no Lisp function of their intrinsic serves, e.g., `svc #0` of AArch64, without which the program fails with `unbound function intrinsic:svc`, wherever the program makes them, also in the code, that it writes later. `Default` leaves a call to the executor, which runs the calls of the threads natively, e.g., `clone`, `futex`, and `exit`, so a catch-all serves the others by their numbers:

```ocaml
Emu.on_syscall emu (fun emu number args ->
    match (number, args) with
    | 64L, [ _; buf; len; _; _; _ ] ->       (* write *)
        print_string (Emu.read emu buf (Int64.to_int_exn len));
        Return len
    | 172L, _ -> Return 1000L                 (* getpid *)
    | (93L | 94L | 96L | 98L | 124L | 178L | 220L | 435L), _ -> Default  (* the threads *)
    | _ -> Return (-38L))                     (* ENOSYS *)
```

A syscall handler chooses `Return` or `Default` immediately. If serving it needs a paused-only operation, such as `Emu.write`, allocation through `Emu.primus`, or another checkpoint, defer that operation before returning from the handler:

```ocaml
Emu.on_syscall emu (fun emu number args ->
    match (number, args) with
    | 222L, [ dst; src; len; _; _; _ ] ->
        Emu.defer emu (fun emu ->
            Emu.write emu dst (Emu.read emu src (Int64.to_int_exn len)));
        Return len
    | _ -> Default)
```

The instructions, that Primus interprets, e.g., that read the tainted registers, call the Lisp function without the hooks.

```ocaml
Emu.on_call emu "putchar" (fun emu ->
    if Emu.arg emu 0 = Int64.of_int (Char.code 'l') then Return 108L else Default)
```

While the program runs, the machine of Primus runs it, and serves no request of the script, so a hook may `stop` the program, read the registers, `read` the memory, that Unicorn has, i.e., the pages the program touched, and `write_direct` it, and `bir` and `insn_at` the code; the other functions raise `Invalid_argument`, which says the program is not paused, as it runs, and `read` raises for a page, that is not in Unicorn yet, rather than making bytes up. For the rest, `defer` an action to the pause, that the hook asks for, before the instruction it sees, or after the access, in `on_read` and `on_write`; the program continues after the action, unless the hook also stopped it, and an error of the action raises from `run`:

```ocaml
Emu.on_code emu ~first:unpacked ~last:unpacked (fun emu _ ->
    Emu.save emu "unpacked.ckpt";               (* saved at the pause, see below *)
    Emu.defer emu (fun emu ->
        let region = Emu.read emu base 0x540000 in   (* every page, as Primus has it *)
        Out_channel.write_all "region.bin" ~data:region;
        Emu.add_symbol emu "decrypt" (Emu.reg emu "X0")))
```

`save` from a hook defers itself, so a checkpoint is saved before the instruction the hook sees.

### The shell

`shell emu` turns a pause into a prompt: it reads the commands of the [debugger](#the-debugger) from the standard input, or from `~input`, runs them on the paused program, and returns the status of the program at `q`, or at the end of the input, so the script goes on:

```ocaml
match Emu.run emu ~until:suspicious with
| Paused -> ignore (Emu.shell emu)
| _ -> ()
```

```
(emu) pc
paused at 400596 in decrypt
(emu) x RDI 32
3f8ffea0: 4e 6f 77 20 77 65 20 77 69 6c 6c 20 70 72 69 6e  |Now we will prin|
3f8ffeb0: 74 20 73 6f 6d 65 20 72 61 6e 64 6f 6d 20 73 74  |t some random st|
(emu) b print_endline
breakpoint at 400726
(emu) c
paused at 400726 in print_endline
(emu) q
```

Besides the commands of the debugger, `c ADDR` continues to an address, `s N` steps `N` instructions, `insn ADDR` and `lifted ADDR LEN` show the code as the lifted engine ran it, `bir ADDR` lifts the instruction from its bytes, `call NAME ARG...` calls a function of the program, `sym PREFIX`, `regions`, and `origin ADDR` show the functions, the memory map, and where a byte comes from, `snap` and `restore N` take and restore snapshots, `save FILE` saves a checkpoint, `q` leaves the shell, and `exit CODE` exits bap. An address is a number, a function, or a register. The breakpoints stay, and stop the program when the script runs it too. From a hook, `shell` opens at the pause the hook asks for, see `defer`, so a breakpoint of the script becomes a prompt:

```ocaml
Emu.on_code emu ~first:decrypt ~last:decrypt (fun emu _ -> ignore (Emu.shell emu))
```

The script's own code doesn't run at the prompt, as the script is compiled to native code; for OCaml at a prompt, run the script in `baptop`, which loads `bap-primus-native.emu` like any library.

### Traces and slices

`on_code` calls its closure for each instruction, which makes the program run tens to hundreds of times slower. `Emu.Trace` records the program counters natively, in a ring in C, with no call to OCaml:

| Function | Action |
|----------|--------|
| `Trace.start ?size ?blocks ?every ?accesses ?first ?last emu` | record the last `size` instructions, by default 2^20, or only the blocks with `~blocks:true`, or every `every`-th instruction, and the last `accesses` loads and stores |
| `Trace.insns ?last trace` | the program counters of the last instructions, also of a trace of blocks, whose blocks are decoded once |
| `Trace.save ?last trace file` | write the recorded program counters, one in hex a line |
| `Trace.count`, `Trace.accesses`, `Trace.stop` | the number of records, the recorded accesses, and the end of recording |

`Trace.capture emu sites` records the registers at the sites, by default the registers, that the C ABI passes the arguments in, e.g., `X0` to `X7`, each time the program reaches one of them, in a ring of its own, so that a long run doesn't lose them, e.g., to map the arguments of a function from the sites of its calls, `Trace.calls`, in one run; `Trace.captured` lists them, the oldest first.

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

The slice handles these cases, see `testsuite/src/slice-weird.c` and the `emu/slice` case of the testsuite:

- The registers and the memory are followed by the byte, e.g., through the partial registers, the overlapping stores, and the bytes, that a later store overwrites, and through the repeated moves, each of whose iterations is a record.
- A def, that the instruction may skip, e.g., of a compare and exchange, keeps its register live, and its value depends on the conditions of the instruction, as of a conditional move. The stores, that the trace recorded, did happen, so their conditions, e.g., of a repeated move, are not followed. A conditional store to the bytes, that the instruction also reads, may be the write-back of a compare and exchange, that fails, so those bytes stay live.
- The registers or the memory, that a hook writes while the program runs, e.g., with `set_reg` in `on_code`, make a gap before the instruction, that the hook sees. The bytes, that the stubs or the script wrote, e.g., `memcpy` or `write`, come from the gap, so the slice doesn't follow them to the stores before it. The written registers are not known, so the slice goes on through them.
- The code, that the program patched after it ran, is lifted with the bytes, that it had then, which the trace keeps, as the writes to the executable pages keep the bytes, that they overwrite.
- When the ring of the accesses has wrapped, the slice stops at the first record, whose accesses are all kept.
- The loads and the stores of an instruction are its accesses, in their order, if their sizes are the same, so that a load or a store of multiple registers, e.g., `push` and `pop` of ARM, or `ldrd`, moves each register by its own bytes.
- On ARM, the traces record the mode of each record, A32 or Thumb, as the program counters of Thumb have no lower bit, and the instructions are lifted in it. The IT blocks of Thumb are lifted in their order, from the IT instruction, as the decoder gives their conditions; the instructions, whose conditions fail, have no records in a trace of the instructions. Unicorn enables VFP and NEON, as Linux does. On AArch64, Unicorn runs its maximal CPU, which has the LSE atomics of ARMv8.1 and later, that the default Cortex-A72 lacks.

The limits: the instructions of a trace of blocks are decoded with the bytes, that the code has now. The patches, that the stubs or the script made, aren't undone. The registers are followed whole, e.g., `AL` of `RAX`, or `S1` of `D0`. An IT block, that starts before the window, isn't known. The slice is of the data, not of the control.

### Calling a function

`call emu addr ~args` calls a function of the paused program with the given arguments, as the C ABI of the target passes `long`s, on a new stack of `~stack` bytes (64 KB by default), which `malloc` allocates and the call zeroes, and returns its result. The function runs as the program does, so the hooks see it, and after it returns the registers are as they were, the memory is as the function left it, and the program pauses where it was:

```ocaml
match Emu.call emu decrypt ~args:[ buf; 16L ] with
| Some n -> printf "decrypted %Ld bytes: %S\n" n (Emu.read emu buf 16)
| None -> (* the function paused, e.g., a hook stopped it, or the program ended *) ()
```

A function, that a hook pauses, continues with `run`, after which the program pauses where it was, with the result in `returned emu`. A snapshot before the call undoes its memory effects, and `diff emu snapshot` lists them, see below. `call` raises `Failure` if the function can't be called, e.g., the C ABI of the target is unknown, or if it fails, e.g., with a segmentation fault, after which the program is paused where it was.

`record emu (fun () -> Emu.call emu f ~args)` runs the call with a trace of its own, and gives its result, or the message of its failure, with the trace, whose `Trace.branches` are the conditional branches, that the callee took, in their order, with the address each went to, and whether it was taken, so one call tells, which check rejected its inputs:

```ocaml
let r = Emu.record emu (fun () -> Emu.call emu check ~args:[ stream ]) in
(match r.result with Ok x -> printf "returned %s\n" (Option.value_map x ~default:"nothing" ~f:Int64.to_string) | Error msg -> printf "failed: %s\n" msg);
List.iter (Emu.Trace.branches r.trace) ~f:(fun (site, dst, taken) ->
    printf "%Lx -> %Lx %s\n" site dst (if taken then "taken" else "fell through"))
```

`~service:(fun emu pc -> ...)` serves the pauses of the function instead: when a hook stops it, e.g., at a system call, or an import, that the script models, the service runs, and the function continues, until it returns, so that a routine, that does IO, runs end to end in one expression, with the script's own handlers.

`~regs:[ ("X8", ctx) ]` sets the registers, that the ABI doesn't pass, e.g., the context of a hand-written dispatcher, after the arguments, and `~thread:tid` runs the function in the context of another thread of the program, see `threads emu`, i.e., with its registers, e.g., its TLS, which a routine reads, when the program paused in a thread, that wouldn't call it:

```ocaml
let worker = List.find_exn (Emu.threads emu) ~f:(fun t -> t.tid <> Emu.thread emu) in
Emu.call emu routine ~args:[ ctx ] ~regs:[ ("X8", table) ] ~thread:worker.tid
```

`drive` calls a function as `call` does, and tells how the call came out: `Returned x`, `Parked { pc; thread }`, if the function still runs, paused at `pc`, or `Ended status`, if the program ended in it. It serves at most `~budget` of the pauses with `~service`, and runs the function for at most `~timeout` seconds, after which it parks. The other threads don't run in a call, so a function, that waits on a futex, e.g., of a condition variable, or on an object of Windows, pauses at the wait, and continues, as if it was woken spuriously, e.g., to wait again, and a function, that spins on a flag, runs out of its time:

```ocaml
match Emu.drive emu routine ~args:[ ctx ] ~budget:100 ~timeout:1.0 ~service with
| Returned x -> printf "returned %Ld\n" x
| Parked { pc; thread } ->
    printf "parked at %Lx in the thread %d, X0 = %Lx\n" pc thread
      (List.Assoc.find_exn (Emu.thread_regs emu thread) ~equal:String.equal "R0")
| Ended _ -> print_endline "the program ended"
```

### What changed, and where a byte comes from

`diff emu snapshot` is the list of the ranges of the memory, `(addr, bytes)`, that differ between a snapshot and the paused program, and `changed_since emu file` the same against a checkpoint in a file, e.g., the outputs of a routine, that `call` ran, in the static storage, without dumping the regions:

```ocaml
let snap = Emu.snapshot emu in
ignore (Emu.call emu decode ~args:[ input; output ]);
List.iter (Emu.diff emu snap) ~f:(fun (addr, n) -> printf "%Lx: %d bytes\n" addr n)
```

`changes emu snapshot` splits the ranges of the diff where the provenance of the bytes differs, and tells it on both sides, so a range from `Generated` to `Stored` is the first real write, e.g., an output, and one from `Stored` to `Stored` overwrote the data of the program. The bytes, that the program never stored, are not in the diff, nor the ones, that the loads generated, which a checkpoint keeps as stored, so `changed_since` compares them with the bytes, that the program has now. `provenance emu addr` tells where a byte comes from: `Stored` by the program, a stub, or the script, in this run; `Generated` by a load, as the region has no bytes, e.g., the uninitialized memory, or to be generated, when it is loaded; `Mapped` from the file, or the fill of a region, e.g., the zeros of BSS; or `Unmapped`. The generated bytes are deterministic in a run, as the generator is seeded, but not across runs, which load them in another order, so two runs from the same checkpoint differ in them, and a value, that looks like a pointer, may be the garbage of the uninitialized memory. A checkpoint keeps them as stored, as they were loaded.

### The project of the memory

A program, that writes its code as it runs, e.g., unpacks or decrypts it, executes bytes, that the file doesn't have. `project emu` builds a `Project.t` from the memory of the paused program, as it is now: its executable regions, see `regions emu`, the memory map with the protections, are disassembled and lifted from the bytes, that the program has there, from the symbols of the program, of `add_symbol`, and of `~symbols`, e.g., the entries, that the script found in a table, and its other regions are its data, as the program has it, e.g., the tables of pointers, that it built. The analyses of the whole program then work on the code, that runs:

```ocaml
ignore (Emu.run emu ~until:after_unpack);
Emu.add_symbol emu "decrypt" 0x602000L;
let proj = Emu.project emu in
let proj = Bap_script.run_pass "recompile-optimize" proj in
...
```

The project is in a unit of its own, named after the file with `#live` and a number, so that it isn't confused with the knowledge of the file, and the memory, that the program never stored, e.g., most of the stack, is zero, without being generated, as the loads generate it.

`~roots:[ addr; ... ]` adds the addresses of code, that the disassembler starts from too, e.g., the targets of the calls of a trace, `Trace.calls`, which it names by their addresses, so that the functions, that only a run found, are functions of the project, with `Xrefs.function_of` and `callers`.

For a focused query, `~regions:(fun r -> ...)` limits disassembly to the executable regions that the predicate selects. The other regions remain in `Project.memory`, so xrefs still read tables and pointers in them, but their symbols and roots do not start disassembly. For example, this disassembles only the region containing the discovered code:

```ocaml
let scope (r : Emu.region) =
  Int64.(r.executable && r.lower <= discovered && discovered <= r.upper) in
let proj = Emu.project emu ~regions:scope ~roots:[discovered]
    ~cache:"unpacked.proj"
```

The selected extents are part of the project digest, so one cache filename is safe across different scopes. Pass the same `~regions`, `~symbols`, and `~roots` to `code_digest` when checking a saved project manually. For repeated queries, keep using `~cache` and `Xrefs.save`/`Xrefs.load` rather than rebuilding the scoped project and index.

The disassembly of a large program takes minutes, so `project emu ~cache:"unpacked.proj"` loads the project from the file, if it is of the same code, and else builds it and saves it there. Underneath, `save_project proj file` saves the project, its program, with the addresses of its terms only, its memory, target, and the digest of the code, and `load_project file` loads it, without the disassembly; `code_digest emu` is the digest of the code of the paused program, its executable regions, symbols and roots, which tells, if a saved project is still of it:

```ocaml
let cached = "unpacked.proj" in
let proj =
  match Emu.load_project cached with
  | proj
    when Option.equal String.equal (Emu.project_digest proj)
           (Some (Emu.code_digest emu)) ->
      proj
  | _ | (exception Failure _) ->
      let proj = Emu.project emu in
      Emu.save_project proj cached;
      proj
```

`Xrefs.save` and `Xrefs.load` do the same for the cross references, see below.

### Cross references

`Emu.Xrefs` finds the addresses, that the instructions of a project refer to, e.g., of the project of the memory. The constants of each subroutine are folded, so that the addresses, that the code builds, e.g., with `adrp` and `add` of AArch64, or `mov` and `movk`, are found, and the targets of the indirect calls and jumps through the slots at constant addresses, e.g., GOT, or a table of pointers to functions, are read from the memory of the project:

```ocaml
let xrefs = Emu.Xrefs.create proj in
Emu.Xrefs.callers xrefs decrypt   (* the functions, that call decrypt, directly, or through a slot *)
|> List.iter ~f:(fun f -> printf "%s\n" (Option.value (Emu.Xrefs.name xrefs f) ~default:"?"));
Emu.Xrefs.find xrefs table        (* who loads, stores, or passes the address of the table *)
|> List.iter ~f:(fun x -> printf "%Lx %s\n" x.site (match x.kind with Store -> "stores" | Load -> "loads" | _ -> "refers"))
```

| Function | Result |
|----------|--------|
| `find xrefs addr` | the references to the address: the site, the kind (`Call`, `Jump`, `Load`, `Store`, `Address`), and the slot, that an indirect call went through |
| `of_insn`, `of_function` | the references of an instruction, or of a function |
| `callers`, `callees` | the call graph, by the addresses of the functions |
| `function_of`, `name`, `functions` | the function of a site, the name of a function, all functions |

A reference is to an address of the mapped memory, so a constant, that happens to be an address, is one too, e.g., in a program loaded at zero.

The targets of the calls through the slots, that the program fills at run time, aren't in the code, but a trace records them, see `Trace.calls`, and `Xrefs.add_calls xrefs (Emu.Trace.calls trace)` adds the recorded calls to the references, by their sites, so that `callers` and `find` answer with both the static and the dynamic edges. `Xrefs.save xrefs file` and `Xrefs.load file` keep the references between the scripts.

### Static slices

`Emu.Static.slice proj addr locations` is the backward slice of the values of the locations, e.g., `Reg "X0"`, or `Mem (addr, 8)`, as the instruction at `addr` has them, over the function, that the instruction is in, as BAP lifted it, e.g., from the memory of the program, and with `~forward:true` the forward slice of the values, that the instruction leaves in them. Without the locations, it is the slice of what the instruction reads, or, forward, writes, e.g., who reads the slot, that a store writes:

```ocaml
let s = Emu.Static.slice proj store [] in
List.iter s.sites ~f:(printf "%Lx\n");   (* how the stored value is computed *)
let s = Emu.Static.slice ~forward:true proj store [] in
List.iter s.sites ~f:(printf "%Lx\n");   (* who reads the stored bytes *)
```

The slice follows the registers, their aliases, e.g., `X0` of `R0` of AArch64, the slots of the frame at the offsets from the stack and the frame pointers, through their adjustments, e.g., the local variables of code compiled without optimizations, and the memory at the constant addresses, that the folded code computes, and, with `~addresses:true`, the addresses of the loads and the stores too. The loads and stores through pointers aren't followed through the memory, and `complete` is false, if their values may come from, or go to, the memory, that the slice follows. `live` are the locations, that come from before the function, e.g., its arguments, or go out of it, e.g., its results. The dynamic `slice` of a trace, see above, follows the values, that the program had, through any memory.

The calls are opaque by default: `calls` are the ones, whose results flow to the locations, or that the values flow to, as arguments, by the registers of the C ABI. With `~depth:n` the slice follows the values through the functions, that the direct calls call, `n` calls deep, e.g., from a context structure, that one routine builds, to the routine, that consumes it three calls later: backward, from the result of a call into the callee, to its arguments, and on in the caller; forward, from the arguments into the callee, to its results, and on after the call. The slots of the frame are of each function, so only the registers and the memory at constant addresses cross the calls, and the instructions of the callees are in `sites`.

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
- the states that script models register with `Emu.Checkpoint.register`, saved together with the guest state before the checkpoint file is replaced

A JNI model exports its handles, object and class identities, method and field IDs, arrays, allocator counters, and string contents. Register it in both the saving and restored runs, constructing it with the same declarations and callbacks each time:

```ocaml
let register_jni jni =
  Emu.Checkpoint.register "jni" ~required:true ~version:1
    ~save:(fun () -> Some (Emu.Jni.export_state jni))
    ~restore:(Emu.Jni.import_state jni)
```

Call `register_jni jni` before `Emu.create ~restore`, so checkpoint validation can see the model's policy. Native argument pointers are not saved in place of strings, whose original contents may outlive reused guest buffers. Other OCaml-side models, such as allocators, TLS mappings, file offsets, and clocks, must register their own state too; restoring guest memory alone cannot restore it. `register_ref` and `register_table` serialize references and hash tables through a `Binable` module, and decode the new value before changing the model.

Every checkpoint has a manifest of the registered model names, schema versions, and whether their state is required. A required model must have saved state, a registered restore handler, and a matching schema; otherwise restore fails before guest memory, model callbacks, or execution. An optional mismatch is skipped with a warning. A required save that returns `None` fails without replacing an existing checkpoint. Use `Checkpoint.models file` to inspect the manifest without loading the program. Callbacks and default handlers are not serialized: the restored script registers them under the same model name and schema.

Checkpoints written before the manifest format remain supported for optional models. Registering a required model rejects such a legacy checkpoint because its schema and producer-side requirement cannot be proved.

For divergence investigation and older checkpoints without `export_state`, the JNI model also records portable replay journals. Each event has the call ordinal, operation, raw arguments, string arguments by value, model-created argument identities, method/field details, result, and result identity:

```ocaml
Emu.Jni.start_recording jni;
(* serve JNI and JavaVM calls *)
Emu.Jni.stop_recording jni;
let data = Emu.Jni.export_journal (Emu.Jni.journal jni) in
let events = Emu.Jni.import_journal data in
let replayed = make_jni () in
Emu.Jni.replay replayed events
```

Replay injects the recorded string values instead of rereading native argument buffers, which may have been reused. It checks ordinals, operations, details, results, and identities, and raises an error naming the ordinal, operation, and expected and actual values on the first mismatch. Use a fresh or appropriately restored model with the same declarations and deterministic external models, such as allocators. Replay is not transactional and does not append journal events. New checkpoints should prefer `export_state`.

### Android models

JNI and Android models live in the separate `bap-primus-native-jni` package and plugin. `bap-primus-native.emu` depends on it and keeps the `Emu.Jni` and `Emu.Android` aliases, so existing scripts do not need changes; direct users may require `bap-primus-native-jni.jni`.

`Emu.Android` complements JNI with ServiceManager, IBinder, and stateful Parcel objects. Service declarations provide stable identities, return classes, and transaction handlers. Parcels support `obtain`, `writeInterfaceToken`, `writeInt`, `readInt`, `transact`, and `readException`:

```ocaml
let android = Android.create ~services:[demo_service] () in
let jni =
  Jni.create ~class_of:(Android.class_of android)
    ~classes:(Android.jni_classes android) ~read_string ~alloc_string ()
```

The declarations include ServiceManager.getService, Parcel.obtain/writeInterfaceToken/writeInt/readException, and IBinder.transact. Repeated calls share service and return-class identities but obtain distinct parcels, producing a consistent object graph rather than unrelated fresh objects.

`Android.export_state` and `import_state` preserve service metadata, live parcels, cursors, exceptions, return classes, and the identity cursor. Register them as a required model and recreate service declarations and handlers in the restored run; handlers are not serialized. Use `Android.find_parcel` to inspect restored parcels.

A checkpoint is untrusted input, as it may be crafted, so its restore checks it: the program must be of the same digest, and the channels of Primus Lisp reopen their files only if the restored run allows them. A channel, that only reads, e.g., of the redirected input, reopens a regular file, and a channel, that writes, and the redirections, that the program may open, only the files, that `--primus-lisp-channel-redirect`, or the `redirects` of the script, redirect in the restored run; the others are closed, with a warning.

The program continues the innermost run of Unicorn. Afterwards, the stub that started it completes, if it is known, see `Emu.complete`; e.g., `__libc_start_main` exits with the result of `main`.

The program, that failed, e.g., at an instruction, that faulted, is saved too, at the address, from which Unicorn would continue, i.e., of that instruction, so the restored program runs it again, e.g., after the script fixed the pointer or patched the code, in another run too:

```ocaml
match Emu.run emu with
| Failed _ -> Emu.save emu "crash.ckpt"
| _ -> ()
(* ... later *)
let emu = Emu.create ~restore:"crash.ckpt" proj in
Emu.set_reg emu "RAX" valid;
Emu.run emu
```

`Checkpoint.context file` describes a failure checkpoint without running it: the active thread, native frames, model manifest, last unrecoverable fault, and the last 32 model events. JNI and named import/syscall outcomes are recorded automatically. Allocator and other models add positions with `record_event emu "allocator" detail`. The journal is informational and bounded; the actual model state still comes from registered extensions, and missing or incompatible required state is rejected before guest execution.

While a function, that the script called, runs, e.g., paused in it by a hook, see `call`, the checkpoint is of the program at the call: the registers, the runs of Unicorn, and the threads, that the program had, when the script called the function, and the memory, as the function changed it, as the call is of the script, and not of the program, which continues from where it paused for the call.

A failure outside of a run of Unicorn, e.g., of a stub, that the program called before it started, has no checkpoint, and `save` raises `Failure`; the program, that exited, or whose emulator failed, e.g., with an exception of the script, raises `Invalid_argument`.

A signal, e.g., of `kill`, may save the checkpoint: its handler stops the program, which pauses, and the script saves it:

```ocaml
Sys.set_signal Sys.sigterm (Sys.Signal_handle (fun _ -> Emu.stop emu));
match Emu.run emu with
| Paused -> Emu.save emu "interrupted.ckpt"
| _ -> ()
```

The handler runs within about 20 ms, also while the program runs a loop without calls, as Unicorn is stopped, when a handler of OCaml is pending, at the start of a block, and continues, if the handler doesn't pause the program. On Windows, the handler runs, when the program next leaves Unicorn, e.g., calls a stub.

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

### Threads

The programs of Linux run their threads, that the system calls create, e.g., `clone` with `CLONE_VM`, as `pthread_create` does, one at a time, in the same memory, on x86-64, x86, AArch64, ARM, MIPS, MIPS64, PowerPC, and RISC-V64. A thread switches, when it waits on a futex, exits, or calls `sched_yield`, and else after 5 ms of the processor, while another thread is ready, so the interleavings may differ from run to run. The executor handles `clone`, with `CLONE_SETTLS` (FS_BASE of x86-64, the descriptor of GS of x86, TPIDR_EL0, TPIDRURO, UserLocal, R2 of PowerPC, and TP of RISC-V), `futex` (its waits and wakes), `set_tid_address`, `gettid`, `sched_yield`, `exit`, and `exit_group`, which exits with the Lisp `exit`, and `set_thread_area` of x86 and MIPS, and `set_tls` of ARM, with the errors of each target, e.g., A3 of MIPS, and SO of PowerPC; the other system calls go to `intrinsic:syscall`, `intrinsic:svc`, or `intrinsic:interrupt`, as before.

The programs of Windows, on x86-64 and x86, run their threads, that `CreateThread`, or `_beginthreadex` and `_beginthread` of msvcrt, create, with their objects, as the executor runs these functions of KERNEL32 instead of their stubs: `ExitThread`, `GetCurrentThreadId`, `GetThreadId`, `GetExitCodeThread`, `ResumeThread` (of `CREATE_SUSPENDED`), `CloseHandle`, `Sleep`, `SwitchToThread`, `WaitForSingleObject` and `WaitForMultipleObjects` (of the threads, the events, the mutexes, and the semaphores), `CreateEvent`, `SetEvent`, `ResetEvent`, `CreateMutex`, `ReleaseMutex`, `CreateSemaphore`, `ReleaseSemaphore`, the critical sections, the SRW locks, the condition variables, `WaitOnAddress` and `WakeByAddress*`, and the slots of `TlsAlloc` and `FlsAlloc`, in the TEBs of the threads. The handles are the addresses of the objects, that `malloc` allocates, as the stacks and the TEBs of the threads, so the checkpoints keep them. A thread, that waits, calls the function again, when it is woken, and a thread, whose function returns, exits with its result. The timeouts expire only when no thread is ready, as the time doesn't pass.

The programs of Linux, that import the functions of the threads of POSIX, without the libc, that has them, e.g., a payload of Android, whose bionic isn't loaded, run them in the executor, instead of their stubs: `pthread_create`, `pthread_join`, `pthread_detach`, `pthread_self`, `pthread_equal`, `pthread_exit`, and the detach state and the size of the stack of `pthread_attr_*`. The handle of a thread, `pthread_t`, is its TID, so the threads, that the program creates with `clone` itself, and the ones of `pthread_create`, are the same to them, as on Linux, e.g., `std::thread::detach` of a thread of `clone`, and `pthread_join` gives the result of the function, or the code of the `exit` of a thread of `clone`. A thread, that `pthread_create` creates, calls its function on a new stack, of 256 KB, or of its attributes, and exits with its result. The threads, that are detached, and the results of the ones, that exited, and aren't joined, are in the checkpoints. A program, whose libc runs, e.g., glibc, runs its own functions, and a hook of `on_call` replaces them too.

`Emu.threads` tells the threads, and the addresses, that they wait on, e.g., their futexes, as `waiting`, only for the waits, that the executor runs, and in which it parked them: of the futexes, and of the objects of Windows. A thread, that waits otherwise, e.g., spins on a flag, or in a `pthread_cond_wait` of a stub, that doesn't use a futex, runs, so it isn't `waiting`, and `Trace.hot` tells, where it spins.

`Emu.thread` tells the thread, that the paused program runs, and `Emu.thread_regs emu tid` the registers of a thread, without the aliases, e.g., of the one, that waits, to tell, which lock it holds, from its arguments. A thread, that doesn't run, keeps the values of its registers in the variables of Primus, `thread_<tid>_<register>`, so they keep their taint and their symbolic formulas, while the threads switch, and the checkpoints keep them, with the threads, e.g., to continue a program, that was saved in one thread, while the others wait. The futexes, the TIDs, and the objects of Windows may be in the tainted memory, which only Primus has, and the atomic sequences, e.g., `ldrex` and `strex`, `lwarx` and `stwcx.`, or `ll` and `sc`, which Primus interprets there, are interpreted whole.

`set_thread_reg emu tid name value` and `set_thread_pc emu tid addr` change an active or parked thread. `resume_thread emu tid` resumes a ready parked thread, or does nothing for the active thread; waiting and nonexistent threads are rejected. `failure emu` reports the last unrecoverable memory fault as `{thread; pc; addr; operation}`, where operation is `Read`, `Write`, or `Fetch`, without conflating recoverable page faults.

The limits: a `clone` of a process, without `CLONE_VM`, fails with `ENOSYS`, as does `clone3`, after which glibc calls `clone`. The threads switch only in the run, that created them, so a thread can't wait in a function of the program, that a Lisp stub called, and the checkpoint isn't saved there. A thread, that is preempted between a load-linked and its store-conditional in Unicorn, e.g., by the hooks of every instruction, may see the reservation of another thread.

### Several emulators

The emulators of a script run side by side, e.g., programs of different targets. Each has its own Unicorn engine, Primus system, knowledge, hooks, stops, and snapshots:

```ocaml
let a = Emu.create (Bap_script.project x86_file) in
let b = Emu.create (Bap_script.project arm_file) in
ignore (Emu.step a);
ignore (Emu.step b)
```

`Emu.create ~engine:`Lifted` runs the program in the lifted engine, e.g., beside the same program in Unicorn, `~engine:`Unicorn`, as `lifted/check.ml` of the testsuite compares them. Without `~engine`, the engine is the one of `~system`, e.g., of `bap:lifted-executor`, or, without it, `BAP_EMU_ENGINE=lifted` makes it the lifted engine.

The script runs one of them at a time. `Emu.knowledge emu` returns the knowledge of a system after its program ended, e.g., the instructions that it lifted.

### Long runs

A run, that executes much new code, grows: the lifted engine keeps the semantics of each instruction, that it lifted, for its engines and its cache, the memory of Primus keeps each byte, that the program stored, as a value of its own, which costs about a hundred bytes, and a snapshot keeps a machine, with the pages, that the engine holds for it. The heap of OCaml takes about twice the live data, by default, see `space_overhead`. A script, that runs for long, watches its footprint, and gives the memory back:

```ocaml
let check emu =
  let f = Emu.footprint () in
  if f.heap > 4_000_000_000 then begin
    Emu.forget_lifts emu;            (* the lifted instructions, saved first *)
    List.iter !old ~f:(Emu.drop_snapshot emu);  (* the snapshots, that are done *)
    Gc.compact ()
  end;
  if Option.exists f.rss ~f:(fun rss -> rss > 16_000_000_000) then begin
    Emu.save emu "resume.ckpt";      (* and start anew from the checkpoint *)
    exit 3
  end
```

- `footprint ()` is the heap of OCaml, the most it had, and the resident size of the process, which Linux tells.
- `forget_lifts emu` saves the lifted instructions to the cache, if bap has one, and drops them, with the ones, that `bir` lifted in the hooks; the code, that the engine compiled, stays, so the program runs on at full speed, and an instruction, that is lifted again, e.g., in a new engine, costs a lift, as at the start.
- `drop_snapshot emu snapshot` frees a snapshot, that the script doesn't restore anymore; `restore` of a dropped snapshot raises.
- The garbage collector of OCaml trades memory for time: `OCAMLRUNPARAM='o=40'` in the environment, or `Gc.set { (Gc.get ()) with space_overhead = 40 }` in the script, keeps the heap closer to the live data, at the cost of more collections; the default is 120.
- The bytes, that the program stores in Unicorn, go to Primus, when it reads them, e.g., at a snapshot, a checkpoint, or a `project`, as values; `peek` and the diffs read the pending pages without storing them.

A wrapper, that is killed, e.g., `timeout`, or a task runner, leaves bap running, so a long run installs its own watchdog: `Sys.set_signal Sys.sigalrm` with `Unix.alarm`, or a handler of `SIGTERM`, that stops the program, see the signals above, saves what it needs, and exits; the lifted engine saves its instructions on `SIGTERM` and `SIGINT` itself, unless the script handles them.

## See also

- The API reference of `Bap_emu`, `Bap_script`, and `Bap_script_debugger`, in `dune build @doc`.
- `Primus.Interpreter.Stops`, `Primus.Interpreter.stop_reached`, and `Primus.Checkpoint`, in the API reference of `bap-primus`.
- The functional tests in `tools/testsuite/run_tests.ml`, whose `emu/` and `script/` cases run every feature above.
