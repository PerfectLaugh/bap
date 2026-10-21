(** Recompiles BIR with LLVM.

    The subs of BIR are the functions of LLVM, which LLVM optimizes, and which
    are raised back to BIR, see {!optimize}, or which clang compiles to a native
    program, see {!recompile}, e.g., in a script,

    {[
    #require "bap-recompile"

    let sub = Bap_recompile.optimize sub |> Or_error.ok_exn
    ]}

    The recompile plugin runs them as the [recompile] and the
    [recompile-optimize] passes. *)

open Core
open Bap.Std

val default_passes : string
(** the pipeline of the passes of LLVM, that {!optimize} runs by default, in the
    syntax of [opt -passes], without the vectorizers, whose vectors aren't
    raised back to BIR *)

val optimize : ?opt:string -> ?passes:string -> sub term -> sub term Or_error.t
(** [optimize sub] is the [sub] optimized by the [passes] of LLVM, which [opt]
    runs, by default the opt in PATH, e.g., without the flags, that the code
    doesn't read, and with the simpler expressions and control flow.

    The jumps of [sub], that leave it, e.g., the calls, the returns, and the
    interrupts, are opaque to LLVM, so the registers and the memory are the same
    at them, and the optimized sub has the same jumps, with the same attributes.
    Only its entry, and the blocks, in which the code continues after its calls,
    have their addresses, as the other blocks use the values, that their
    dominators computed, so the indirect jumps into the sub, e.g., of the tables
    of its switches, can't enter them.

    The results are cached, so the same sub, with the same [passes], is
    optimized once. Fails, if LLVM IR can't express the code of [sub], e.g., a
    block without a jump, if the optimized code can't be raised back to BIR, or
    if opt fails. *)

(** The code, that is optimized: its blocks, the first of which is its only
    entry, whose jumps to its blocks stay inside of it, while its other jumps,
    e.g., to the blocks outside of it, the calls, and the returns, leave it, so
    the registers and the memory are the same at them, e.g.,

    {[
      match Bap_emu.bir emu pc with
      | Some (size, blks) ->
          let next = Addr.of_int64 Int64.(pc + of_int size) in
          Region.of_blks ~next blks |> Or_error.ok_exn
          |> Bap_recompile.optimize_region
      | None -> ...
    ]} *)
module Region : sig
  type t

  val of_sub : sub term -> t Or_error.t
  (** [of_sub sub] is the region of the blocks of [sub], from its first one *)

  val of_blks : ?next:addr -> blk term list -> t Or_error.t
  (** [of_blks blks] is the region of the blocks, e.g., of an instruction, see
      [Bap_emu.bir], whose blocks, that fall through, continue in the next
      block, and the last one at the address [next]. Fails, if the last block
      falls through without [next], or if there are no blocks. *)

  val of_range : sub term -> lo:addr -> hi:addr -> t Or_error.t
  (** [of_range sub ~lo ~hi] is the region of the blocks of the instructions of
      [sub] from [lo] to [hi], [hi] excluded, in their order, whose last block,
      if it falls through, continues in the next block of [sub]. Fails, if the
      code of [sub] outside of the range jumps into it, but to its first block,
      as the other blocks of the optimized region have no entry. *)

  val entry : t -> blk term
  (** [entry region] is the first block, which keeps its identity, when the
      region is optimized *)

  val blks : t -> blk term list
  (** [blks region] are the blocks, from the entry *)

  val update : sub term -> t -> sub term
  (** [update sub region] replaces the blocks of [sub], that the region was made
      of, with the blocks of [region], e.g., after it is optimized *)
end

val optimize_region :
  ?opt:string -> ?passes:string -> Region.t -> Region.t Or_error.t
(** [optimize_region region] optimizes the code of [region], as {!optimize}
    does, which has the same entry, and the same jumps, that leave it. *)

val optimize_program :
  ?opt:string ->
  ?passes:string ->
  ?select:(sub term -> bool) ->
  ?report:(sub term -> Error.t -> unit) ->
  program term ->
  program term
(** [optimize_program prog] optimizes the subs of [prog], that [select] selects,
    by default the ones with code, see {!optimize}, in one run of opt, and keeps
    the subs, that can't be optimized, as they were, after it calls [report] for
    them, which prints the error by default. *)

val recompile : ?entry:string -> project -> string * string
(** [recompile project] is the LLVM IR of the program of x86-64 of the
    [project], which starts from the [entry], [main] by default, and the C
    source of its runtime, which clang compiles to a native program, e.g.,
    [clang -O2 -fPIE -pie prog.ll prog.ll.rt.c], see the recompile plugin. *)
