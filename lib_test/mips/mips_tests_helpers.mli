(** The modes of the tests of the MIPS lifters, see {!Lifter_test}.

    The instructions are at [0x20000], where lib_test/cross/runner.c executes
    them. The locations are the variables of the targets, e.g., [R2], [HI] or
    [LO], and the memory words. *)

val mips32eb : Lifter_test.mode
(** the 32-bit big-endian instructions *)

val mips32le : Lifter_test.mode
(** the 32-bit little-endian instructions *)

val mips64eb : Lifter_test.mode
(** the 64-bit big-endian instructions *)

val mips64le : Lifter_test.mode
(** the 64-bit little-endian instructions *)
