(** The modes of the tests of the PowerPC lifters, see {!Lifter_test}.

    The instructions are at [0x20000], where lib_test/cross/runner.c executes
    them. The locations are the variables of the targets, e.g., [R3], [LR], the
    bits of the condition register, e.g., [CR0EQ], the flags of XER, e.g., [CA],
    and the memory words. *)

val ppc32 : Lifter_test.mode
(** the 32-bit big-endian instructions *)

val ppc64eb : Lifter_test.mode
(** the 64-bit big-endian instructions *)

val ppc64le : Lifter_test.mode
(** the 64-bit little-endian instructions *)
