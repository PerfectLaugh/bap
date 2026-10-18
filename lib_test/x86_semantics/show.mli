(* prints the lifted x86 instructions as bap mc prints them *)

val x86_64 : Lifter_test.mode
(** the x86-64 instructions at the address 0 *)

val i686 : Lifter_test.mode
(** the i686 instructions at the address 0 *)

val show : Lifter_test.mode -> string -> unit
(** [show mode code] prints the assembly and the BIL of the instruction with the
    encoding [code], the bytes in hex separated by spaces, as bap mc
    --show-insn=asm --show-bil does, but with the temporaries and the let-bound
    variables numbered in the order of their occurrences. *)
