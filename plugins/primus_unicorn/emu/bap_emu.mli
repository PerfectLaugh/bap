(** Runs a program in Unicorn, as the script drives it.

    The emulator runs the program of a project, e.g., of a bare project, see
    [Bap_script.project ~bare], in a Primus system, by default the
    [bap:unicorn-executor], in which the code runs in Unicorn, and Primus runs
    the stubs, e.g., of libc, and the system calls. The script pauses and
    continues the program, reads and writes its registers and memory, and hooks
    its instructions, its memory accesses and the calls of its functions, as it
    would with Unicorn, e.g.,

    {[
      let emu = Bap_emu.create (Bap_script.project ~bare:true file) in
      Bap_emu.on_call emu "getuid" (fun _ -> Return 0L);
      match Bap_emu.run emu ~until:0x401000L with
      | Paused -> Bap_emu.set_reg emu "RAX" 42L
      | Exited code -> ...
    ]}

    The program runs in the fiber of the script, which it leaves, when it
    pauses, and the script continues it with {!run}. The emulator is one at a
    time, as Unicorn is. *)

open Bap.Std

type t
(** the emulator *)

(** the state of the program *)
type status =
  | Paused  (** the program pauses, e.g., at the address of [until] *)
  | Exited of int option  (** the program exited, with the code, if known *)
  | Failed of string  (** the program or the emulator failed *)

(** what a hook of a call does *)
type action =
  | Default  (** the function runs, e.g., its stub *)
  | Return of int64  (** the function returns the value at once *)

val create :
  ?system:string ->
  ?components:string list ->
  ?args:string list ->
  ?envp:string list ->
  ?entry:string ->
  project ->
  t
(** [create project] starts the program of [project], from [entry], by default
    its entry point, or [_start], in the [system], by default
    [bap:unicorn-executor], with the [components], e.g., [bap:debugger], the
    program arguments [args], without the name of the program, and the
    environment [envp], and pauses it before its first instruction runs in
    Unicorn. *)

val run : ?until:int64 -> t -> status
(** [run emu] continues the program, until it pauses, e.g., before the
    instruction at [until], or by {!stop}, or exits. *)

val step : t -> status
(** [step emu] runs one instruction in Unicorn. *)

val status : t -> status
(** the state of the program *)

val stop : t -> unit
(** [stop emu] pauses the program, e.g., in a hook, before the next instruction.
*)

val pc : t -> int64
(** the address of the next instruction, with the lower bit set in the Thumb
    state of ARM *)

val set_pc : t -> int64 -> unit
(** [set_pc emu addr] continues the program from [addr], when it is paused *)

val registers : t -> string list
(** the names of the registers of the target, e.g., [RAX] *)

val reg : t -> string -> int64
(** [reg emu name] the value of the register, at most 64 bits wide, raises
    [Invalid_argument] for the unknown register. *)

val set_reg : t -> string -> int64 -> unit
(** [set_reg emu name x] writes [x] to the register. *)

val read : t -> int64 -> int -> string
(** [read emu addr n] reads [n] bytes from [addr], raises [Invalid_argument], if
    Primus would fault on any of them, or, in a hook, if their page is not in
    Unicorn yet, which a paused program copies. *)

val write : t -> int64 -> string -> unit
(** [write emu addr data] writes the bytes, also to the code, as the debuggers
    do, raises [Invalid_argument] as {!read} does.

    {b Warning:} the bytes of a read-only page, e.g., of the code, go only to
    the copy of the page in Unicorn, not to the memory of the machine in Primus,
    so they are lost, when Unicorn copies the page anew, e.g., after
    {!snapshot}, which forks the machine, or after the protection of the page
    changes, and Primus doesn't see them, e.g., when it interprets the code of
    the page, see the taint and the symbolic execution. Use {!patch} for the
    code, that must stay patched. It is the only write in the hooks.

    The writable pages have no such problem, as their changes go to Primus. *)

val patch : t -> int64 -> string -> unit
(** [patch emu addr data] stores the bytes to the memory of the machine in
    Primus, also to the read-only pages, e.g., to the code, from which they go
    to Unicorn, which translates the changed code anew, so that they stay, as
    the program changed them, e.g., after {!snapshot} or {!restore} of a later
    snapshot, and the instructions, that Primus interprets, or whose registers
    the executor tracks, are decoded and lifted anew from them.

    Raises [Invalid_argument] as {!read} does, or if the program is not paused,
    e.g., in a hook. *)

val primus : t -> Bap_primus.Std.Primus.Machine.component -> unit
(** [primus emu component] runs the [init] of the [component] in the Primus
    machine of the program, which is paused, or ended, so that the script uses
    the whole API of Primus, e.g., its environment, memory, linker, Lisp, or the
    taint tracker, whose results the script gets, e.g., with references, and
    whose changes, e.g., of the registers and the memory, the program sees, when
    it continues, e.g.,

    {[
    let rax = ref Word.b0 in
    Bap_emu.primus emu
      (module functor
                (Machine : Primus.Machine.S)
                ->
                struct
                  module Env = Primus.Env.Make (Machine)
                  open Machine.Syntax

                  let init () =
                    Env.get (Var.create "RAX" reg64_t) >>| fun x ->
                    rax := Primus.Value.to_word x
                end)
    ]}

    The [init] may observe the program, e.g., with
    [Machine.Observation.observe], as the components do, and its observers stay.
    Raises [Invalid_argument], if the program is not paused, e.g., in a hook. *)

val on_code : ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> unit) -> unit
(** [on_code emu f] calls [f emu addr] before each instruction from [first] to
    [last], inclusive, by default of all. *)

val on_read :
  ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> int -> unit) -> unit
(** [on_read emu f] calls [f emu addr size] before each load. *)

val on_write :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  (t -> int64 -> int -> int64 -> unit) ->
  unit
(** [on_write emu f] calls [f emu addr size value] before each store. *)

val on_call : t -> string -> (t -> action) -> unit
(** [on_call emu name f] calls [f emu] when the program calls the function,
    e.g., an external one, before its stub, or one of the program, which [f] may
    replace, see {!action}, and whose arguments {!arg} reads. *)

val arg : t -> int -> int64
(** [arg emu n] the [n]th argument of the function, which is called, from 0, as
    its prototype tells, e.g., from the api files. *)

val exit_code : t -> int option
(** the code, with which the program exited *)

type snapshot
(** the saved state of the paused program, its registers and its memory *)

val snapshot : t -> snapshot
(** [snapshot emu] saves the state of the paused program, which the program
    continues from, when it is restored, as many times, as the script restores
    it. *)

val restore : t -> snapshot -> unit
(** [restore emu snapshot] drops the state of the paused program, which
    continues from the [snapshot], paused at its address. The hooks of the
    script stay. *)

(** The taint of the values, that the program computes.

    Primus tracks the taint, see the [bap-taint] library, as the program runs in
    Unicorn, which leaves the instructions, that use the tainted values, to
    Primus, so that the taint propagates through the computations, the loads and
    the stores, e.g.,

    {[
      let emu = Bap_emu.create ~components:Bap_emu.Taint.components proj in
      ignore (Bap_emu.run emu ~until:after_read);
      Bap_emu.Taint.introduce emu ~kind:"input" (Mem (buf, len));
      Bap_emu.Taint.on_jump emu (fun _ ~kinds dst -> ...);
      Bap_emu.run emu
    ]}

    The functions, except the callbacks, run, when the program is paused, or
    ended, see {!primus}. *)
module Taint : sig
  (** the place of the values, whose taint is introduced or queried *)
  type place =
    | Reg of string  (** the value of the register, e.g., [RAX] *)
    | Mem of int64 * int
        (** the values of the bytes of the memory from the address *)

  val components : string list
  (** the components of the system, that propagate the taint, by the
      computations, which {!create} needs *)

  val introduce : t -> kind:string -> place -> unit
  (** [introduce emu ~kind place] taints the values of the [place] with a new
      taint of the [kind], e.g., ["input"], the value of the register directly,
      and the bytes of the memory indirectly, i.e., the values, that the program
      loads from them. *)

  val kinds : t -> place -> string list
  (** [kinds emu place] the kinds of the taints of the values of the [place],
      i.e., of the value of the register, or of the locations of the memory. *)

  val is_tainted : t -> kind:string -> place -> bool
  (** [is_tainted emu ~kind place] if the [place] has a taint of the [kind] *)

  val sanitize : t -> kind:string -> place -> unit
  (** [sanitize emu ~kind place] removes the taints of the [kind] of the
      [place], from all values, that they taint. *)

  val on_jump : t -> (t -> kinds:string list -> int64 -> unit) -> unit
  (** [on_jump emu f] calls [f emu ~kinds dst] when the program jumps to [dst]
      on a condition, that the taints of the [kinds] taint. The callback runs,
      when the program runs, so it may only {!stop} it. *)
end
