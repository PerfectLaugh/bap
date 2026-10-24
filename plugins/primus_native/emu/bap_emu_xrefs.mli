(** The cross references of a program: the addresses, that its instructions
    refer to, e.g., of the memory of the paused program, see [Bap_emu.project],
    whose code the program built, e.g.,

    {[
    let xrefs = Emu.Xrefs.create (Emu.project emu) in
    List.iter (Emu.Xrefs.find xrefs table) ~f:(fun x ->
        printf "%Lx %s %Lx\n" x.site
          (match x.kind with Store -> "stores to" | _ -> "refers to")
          x.target)
    ]}

    The references are of the BIR of the program, whose constants are folded in
    each subroutine, so that the addresses, that the code builds, e.g., with
    [adrp] and [add] of AArch64, or [mov] and [movk], are found, and the targets
    of the indirect calls and jumps, whose addresses are constants, or the words
    of the slots at the constant addresses, e.g., of the tables of the pointers
    to the functions, are read from the memory of the project, as the program
    has it. A reference is to an address of the mapped memory, so the constants,
    that aren't addresses, are references, if they are in it. The references of
    an instruction are at its address, the site, and the instructions are of the
    subroutines of the program, by whose addresses the functions are named. *)

open Bap.Std

type t

(** what the instruction does with the address *)
type kind =
  | Call  (** calls the function, directly, or through a slot *)
  | Jump  (** jumps there indirectly, e.g., through a table *)
  | Load  (** loads from the address *)
  | Store  (** stores to the address *)
  | Address  (** computes the address, e.g., passes it *)
[@@deriving compare, equal, sexp]

type xref = {
  site : int64;  (** the address of the instruction *)
  target : int64;  (** the address, that it refers to *)
  kind : kind;
  slot : int64 option;
      (** the slot, from which the target of a call, or a jump, was loaded,
          e.g., of GOT, or of a table of pointers to the functions *)
}
[@@deriving compare, equal, sexp]

val create : project -> t
(** [create proj] the references of the program of [proj], which is
    disassembled, e.g., of [Bap_emu.project], or of
    [Bap_script.project ~disassemble:true] *)

val find : t -> int64 -> xref list
(** [find xrefs addr] the references to [addr], in the order of their sites,
    e.g., who calls the function, who stores to the slot, who refers to the
    string *)

val of_insn : t -> int64 -> xref list
(** [of_insn xrefs addr] the references of the instruction at [addr] *)

val of_function : t -> int64 -> xref list
(** [of_function xrefs addr] the references of the instructions of the function
    at [addr], in the order of their sites *)

val callers : t -> int64 -> int64 list
(** [callers xrefs addr] the functions, that call the function at [addr], by
    their addresses, in their order, each once *)

val callees : t -> int64 -> int64 list
(** [callees xrefs addr] the functions, that the function at [addr] calls, by
    their addresses, in their order, each once *)

val function_of : t -> int64 -> int64 option
(** [function_of xrefs addr] the function, whose instruction is at [addr] *)

val name : t -> int64 -> string option
(** [name xrefs addr] the name of the function at [addr] *)

val functions : t -> int64 list
(** the functions of the program, by their addresses, in their order *)

val all : t -> xref list
(** all references, in the order of their sites *)
