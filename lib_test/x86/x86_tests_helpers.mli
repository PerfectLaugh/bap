(** The modes of the tests of the x86 lifters, see {!Lifter_test}.

    The locations are the variables of the targets, e.g., [RAX], [CF] or [YMM0],
    and the memory words. *)

val x86_64 : Lifter_test.mode
(** the 64-bit instructions *)

val i686 : Lifter_test.mode
(** the 32-bit instructions *)
