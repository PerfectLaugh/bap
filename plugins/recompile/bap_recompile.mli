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
open Bap_core_theory
module Recompile_optimize = Recompile_optimize
module Recompile_mba = Recompile_mba

type mba = Disabled | Unchecked | Checked

val simplify_exp :
  ?max_iterations:int -> ?max_rewrites:int -> exp -> exp Or_error.t

val simplify_exp_checked :
  ?max_iterations:int -> ?max_rewrites:int -> exp -> exp Or_error.t

val simplify_mba :
  ?max_iterations:int -> ?max_rewrites:int -> sub term -> sub term Or_error.t

val simplify_mba_checked :
  ?max_iterations:int -> ?max_rewrites:int -> sub term -> sub term Or_error.t
(** [simplify_mba sub] canonicalizes and simplifies pure expressions and
    performs bounded copy propagation without changing BIR structure or term
    identifiers. [simplify_mba_checked] accepts the result only when Lean proves
    every rewrite, using prior definitions as premises for propagation. Both
    functions fail on budget exhaustion; checked mode also fails on every
    rejected or unsupported proof. *)

val default_passes : string
(** the pipeline of the passes of LLVM, that {!optimize} runs by default, in the
    syntax of [opt -passes], without the vectorizers, whose vectors aren't
    raised back to BIR *)

val deflatten_passes : string
(** the pipeline of {!deflatten}, which simplifies the conditions of the
    dispatchers, and removes them, after they are threaded *)

val optimize :
  ?target:Theory.Target.t ->
  ?opt:string ->
  ?passes:string ->
  ?mba:mba ->
  ?validate:(exp -> exp -> bool) ->
  ?validate_thread:(Recompile_optimize.thread_witness -> bool) ->
  ?validate_split:(Recompile_optimize.split_witness -> bool) ->
  sub term ->
  sub term Or_error.t
(** [optimize sub] is the [sub] optimized by the [passes] of LLVM, which [opt]
    runs, by default the opt in PATH, e.g., without the flags, that the code
    doesn't read, and with the simpler expressions and control flow.

    The [mba] mode applies native MBA simplification before LLVM. [Checked]
    requires a Lean proof of every changed expression and keeps the three modes
    in separate cache entries. MBA errors reject the candidate.

    With the [target], the slots of the frame of [sub], i.e., the memory at the
    constant offsets from its stack pointer at the entry, are the variables of
    LLVM, e.g., the local variables of the code, compiled without the
    optimizations, as the registers are, if the address of the frame doesn't
    escape: it isn't stored, or passed to a callee, but in the stack and the
    frame pointers, and the memory isn't accessed at an unknown address in the
    frame. The slots are in the memory at the jumps, that leave the sub.

    The jumps of [sub], that leave it, e.g., the calls, the returns, and the
    interrupts, are opaque to LLVM, so the registers and the memory are the same
    at them, and the optimized sub has the same jumps, with the same attributes.
    Only its entry, and the blocks, in which the code continues after its calls,
    have their addresses, as the other blocks use the values, that their
    dominators computed, so the indirect jumps into the sub, e.g., of the tables
    of its switches, can't enter them.

    The results are cached, so the same sub, with the same [passes], is
    optimized once. Fails, if LLVM IR can't express the code of [sub], e.g., a
    block without a jump, if the optimized code can't be raised back to BIR, if
    opt fails, or if the result has an invalid destination or changes the
    multiset of opaque exits, their stable targets, or their attributes. These
    checks validate the external control-flow boundary, not full trace
    equivalence or preservation of internal stores. *)

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
  ?target:Theory.Target.t ->
  ?opt:string ->
  ?passes:string ->
  ?mba:mba ->
  Region.t ->
  Region.t Or_error.t
(** [optimize_region region] optimizes the code of [region], as {!optimize}
    does, which has the same entry, and the same jumps, that leave it. *)

val thread_proof : Recompile_optimize.thread_witness -> (string, string) result
(** Generates the Lean artifact for a dispatcher-threading witness. *)

val validate_thread : Recompile_optimize.thread_witness -> (unit, string) result
(** Checks a complete dispatcher-threading witness with Lean. *)

val split_proof : Recompile_optimize.split_witness -> (string, string) result
(** Generates the Lean artifact for a symbolic dispatcher split. *)

val validate_split : Recompile_optimize.split_witness -> (unit, string) result
(** Checks a symbolic dispatcher split with Lean. *)

val deflatten :
  ?target:Theory.Target.t ->
  ?opt:string ->
  ?passes:string ->
  ?mba:mba ->
  ?validate:(exp -> exp -> bool) ->
  ?validate_thread:(Recompile_optimize.thread_witness -> bool) ->
  ?validate_split:(Recompile_optimize.split_witness -> bool) ->
  ?rounds:int ->
  sub term ->
  sub term Or_error.t
(** [deflatten sub] undoes the flattening of the control flow of [sub], e.g., of
    the obfuscators, whose blocks go through the dispatcher, which finds the
    next block from the state, that the blocks set, e.g., by the binary search
    of the cases of a switch, so that the blocks jump to each other, and the
    dispatcher is removed, e.g., for the analyses, that need the control flow.

    Each of the [rounds], 4 by default, optimizes [sub], see {!optimize}, until
    the number of its blocks doesn't change. As the state must be a value, that
    LLVM sees, the [target], that promotes the slots of the frame, is needed, if
    the state is on the stack, e.g., of the code, that is compiled without the
    optimizations. Each round, the dispatcher is evaluated for each state, that
    a block passes to it, a constant, or a select of the constants, as long as
    its blocks have no effects, and the block jumps to the block, that the
    dispatcher leads to, with the variables, that the dispatcher defined on the
    way. Each round applies the destination and opaque-exit validation of
    {!optimize} before caching or returning the result.

    When [validate] is supplied, every original/folded expression pair that
    guides dispatcher evaluation must be accepted by it. Rejected folds are not
    used for threading, and validator exceptions become optimization errors.

    When [validate_thread] is supplied, it is called with each complete proposed
    edge before redirection. {!validate_thread} checks in a formal CFG semantics
    that the original and threaded paths reach the same destination and produce
    the same final definitions for arbitrary unrelated inputs. When
    [validate_split] is supplied, symbolic select splits receive the same
    destination and definition checks for every condition value; otherwise they
    are left untransformed. Unchecked, expression-checked, thread-checked, and
    split-checked results use different cache entries, so a less checked result
    is never returned for a more checked request. *)

val optimize_program :
  ?target:Theory.Target.t ->
  ?opt:string ->
  ?passes:string ->
  ?mba:mba ->
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
