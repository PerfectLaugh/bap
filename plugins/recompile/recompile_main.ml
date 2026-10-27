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

The slots of the frame of a sub, i.e., the memory at the constant offsets
from its stack pointer at the entry, are the variables of LLVM, e.g., the
local variables of the code, that is compiled without the optimizations,
if the address of the frame doesn't escape, and the dispatchers of the
state machines are threaded, so that $(b,--recompile-deflatten) undoes
the flattening of the control flow, e.g., of the obfuscators, whose
blocks go through a dispatcher, which switches on the state, that they
set, e.g.,

```
  bap ./prog --passes=recompile-optimize --recompile-deflatten -dbir
```

With $(b,--recompile-lean-deflatten), every constant expression used to
justify dispatcher threading is checked by Lean 4.35.0. Each constant-state
threaded edge is also compared with the original dispatcher path in a formal
CFG semantics: the destination and every final definition must be equal for
arbitrary unrelated inputs. Symbolic select splits are certified by the same
destination and definition checks for every condition value. This requires
$(b,elan) on $(b,PATH) or in
$(b,~/.elan/bin), and adds external proof-checking cost. A failed proof or Lean
process rejects the optimized candidate, so the original sub is kept.
Unchecked, expression-checked, and CFG-checked results use separate cache
entries. The option has no effect without $(b,--recompile-deflatten).

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

let deflatten =
  Extension.Configuration.flag "deflatten"
    ~doc:
      "Undoes the flattening of the control flow of the subs, e.g., of the \
       obfuscators, whose blocks go through a dispatcher, which switches on \
       the state, that the blocks set, so that the blocks jump to each other, \
       in the rounds of the optimization, see $(b,--recompile-opt-passes), \
       whose default is the pipeline of the deflattening then."

let lean_deflatten =
  Extension.Configuration.flag "lean-deflatten"
    ~doc:
      "Uses Lean to check dispatcher expressions and certify constant-state \
       threaded CFG edges. Requires --recompile-deflatten and Lean 4.35.0."

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
  let deflatten = ctxt --> deflatten in
  let validate, validate_thread, validate_split =
    if ctxt --> lean_deflatten then
      ( Some
          (fun before after ->
            match Bap_bil_plugin.Bil_lean.validate_exp before after with
            | Ok () -> true
            | Error message -> failwith message),
        Some
          (fun witness ->
            match Bap_recompile.validate_thread witness with
            | Ok () -> true
            | Error message -> failwith message),
        Some
          (fun witness ->
            match Bap_recompile.validate_split witness with
            | Ok () -> true
            | Error message -> failwith message) )
    else (None, None, None)
  in
  Project.register_pass ~name:"optimize" (fun proj ->
      let target = Project.target proj in
      if deflatten then
        let passes =
          if String.equal passes Bap_recompile.default_passes then
            Bap_recompile.deflatten_passes
          else passes
        in
        Project.map_program proj ~f:(fun prog ->
            Term.map sub_t prog ~f:(fun sub ->
                if
                  Term.length blk_t sub = 0
                  || String.is_prefix (Sub.name sub) ~prefix:"intrinsic:"
                  || not (select sub)
                then sub
                else
                  match
                    Bap_recompile.deflatten ~target ~opt ~passes ?validate
                      ?validate_thread ?validate_split sub
                  with
                  | Ok sub -> sub
                  | Error err ->
                      eprintf "bap-recompile: can't deflatten %s: %s\n%!"
                        (Sub.name sub) (Error.to_string_hum err);
                      sub))
      else
        Project.map_program proj
          ~f:(Bap_recompile.optimize_program ~target ~opt ~passes ~select));
  Ok ()
