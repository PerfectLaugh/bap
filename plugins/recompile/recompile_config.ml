open Core
open Bap.Std
open Bap_main

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

let mba =
  Extension.Configuration.flag "mba"
    ~doc:
      "Canonicalizes and simplifies mixed Boolean-arithmetic expressions \
       before LLVM optimization and every deflattening round."

let lean_mba =
  Extension.Configuration.flag "lean-mba"
    ~doc:
      "Applies MBA simplification only when Lean proves every changed \
       expression equivalent. Implies --recompile-mba and requires Lean \
       4.35.0."

let lean_deflatten =
  Extension.Configuration.flag "lean-deflatten"
    ~doc:
      "Uses Lean to check dispatcher expressions and certify constant-state \
       threaded CFG edges. Requires --recompile-deflatten and Lean 4.35.0."

let mba_mode ctxt =
  let open Extension.Syntax in
  if ctxt --> lean_mba then Bap_recompile.Checked
  else if ctxt --> mba then Bap_recompile.Unchecked
  else Bap_recompile.Disabled
