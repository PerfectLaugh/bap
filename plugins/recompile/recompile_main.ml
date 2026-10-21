let doc =
  {|
# DESCRIPTION

Recompiles the program of x86-64 to LLVM IR, which LLVM optimizes and
compiles to a native program, e.g.,

```
  bap ./prog --passes=recompile --recompile-output=prog.ll
  clang -O2 -fPIE -pie prog.ll prog.ll.rt.c -o prog.native
```

The pass writes the program to the output, and its runtime, a C file,
next to it. The native program must be PIE, so that it doesn't take the
addresses of the original one. The recompiled program works on the memory of the original
one, at its original addresses: the runtime maps the segments of the
original file, which must be an executable of ELF, that isn't PIE, and
applies its dynamic relocations, and the subroutines of the program are
the functions of LLVM, whose registers are local, so that LLVM keeps
them in the registers of the machine, and removes the flags that the
program doesn't read. The calls of the imported functions are native,
with their arguments in the registers, as the ABI of System V passes
them.

The prototype doesn't recompile the floating-point code, the system
calls, and the code, that the program jumps to, but that BAP didn't
disassemble.

The $(b,recompile-optimize) pass optimizes the subs of BIR with the
passes of LLVM, see $(b,--recompile-opt-passes), which $(b,opt) runs,
e.g., removes the flags, that the code doesn't read, and simplifies the
expressions and the control flow, and raises the functions back to BIR,
e.g.,

```
  bap ./prog --passes=recompile-optimize,run
```

Each sub is a function of LLVM, whose jumps, that leave it, e.g., the
calls, the returns, and the interrupts, are opaque to LLVM, so the
registers and the memory are the same at them, and the raised sub has
the same jumps. The values, that the code uses once, are substituted
into the expressions, that use them, and a sub, that can't be raised,
stays as it was. Only the entry of a raised sub, and the blocks, in
which the code continues after its calls, have their addresses, as the
other blocks use the values, that their dominators computed, so the
indirect jumps into the sub, e.g., of the tables of its switches, can't
enter them, and $(b,--recompile-opt-subs) excludes such subs.

The scripts and the other plugins optimize the subs on demand with the
library of the plugin, e.g.,

```
  #require "bap-recompile"
  let sub = Bap_recompile.optimize sub |> Or_error.ok_exn
```
|}

open Core
open Bap.Std
open Bap_main
open Extension.Syntax

let output =
  Extension.Configuration.parameter
    Extension.Type.(some string)
    "output" ~doc:"Writes the LLVM IR of the program to the $(docv)."

let entry =
  Extension.Configuration.parameter
    Extension.Type.(string =? "main")
    "entry" ~doc:"The subroutine, that the program starts from."

let opt =
  Extension.Configuration.parameter
    Extension.Type.(string =? "opt")
    "opt" ~doc:"The opt of LLVM, that optimizes the subs."

let pipeline =
  Extension.Configuration.parameter
    Extension.Type.(string =? Bap_recompile.default_passes)
    "opt-passes"
    ~doc:
      "The pipeline of the passes of LLVM, that optimize the subs, in the \
       syntax of $(b,opt -passes), without the vectorizers, whose vectors \
       aren't raised back to BIR."

let subs =
  Extension.Configuration.parameter
    Extension.Type.(list string)
    "opt-subs" ~doc:"Optimizes only the named subs, by default all of them."

let () =
  Extension.declare ~doc ~provides:[ "pass"; "llvm"; "recompile" ]
  @@ fun ctxt ->
  let entry = ctxt --> entry in
  let output = ctxt --> output in
  Project.register_pass (fun proj ->
      match output with
      | None -> invalid_arg "the recompile pass needs --recompile-output"
      | Some output ->
          let ir, runtime = Bap_recompile.recompile ~entry proj in
          Out_channel.write_all output ~data:ir;
          Out_channel.write_all (output ^ ".rt.c") ~data:runtime;
          proj);
  let opt = ctxt --> opt and passes = ctxt --> pipeline in
  let subs = ctxt --> subs in
  let select sub =
    List.is_empty subs || List.mem subs (Sub.name sub) ~equal:String.equal
  in
  Project.register_pass ~name:"optimize"
    (Project.map_program
       ~f:(Bap_recompile.optimize_program ~opt ~passes ~select));
  Ok ()
