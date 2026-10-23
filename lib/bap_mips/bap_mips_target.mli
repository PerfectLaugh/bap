open Bap_core_theory
(** Declares some of the MIPS targets.

    More targets could be added without modifying this module. It is advised to
    inherit from one of the targets defined here to include the newly defined
    target into the mips family, though it is not strictly required. *)

val parent : Theory.Target.t
(** [parent] it the parent of all MIPS.

    No properties are set. *)

(** {3 The MIPS 32 family}*)

val mips32bi : Theory.Target.t
(** The bi-endian MIPS32 (the parent) *)

val mips32eb : Theory.Target.t
(** The big endian MIPS32 *)

val mips32le : Theory.Target.t
(** The little endian MIPS32 *)

(** {3 The MIPS 64 family}*)

val mips64bi : Theory.Target.t
(** The bi-endian MIPS64 (the parent) *)

val mips64eb : Theory.Target.t
(** The big endian MIPS64 *)

val mips64le : Theory.Target.t
(** The little endian MIPS64 *)

(** {3 The release 6}

    The targets of the release 6, whose encodings differ, e.g., of the compact
    branches, which have no delay slots, and whose FPU is 64-bit, also on
    MIPS32. *)

val mips32r6eb : Theory.Target.t
val mips32r6le : Theory.Target.t
val mips64r6eb : Theory.Target.t
val mips64r6le : Theory.Target.t

val is_r6 : Theory.Target.t -> bool
(** [is_r6 t] if [t] is of the release 6. *)

(** {2 MIPS encodings} *)

val llvm_mips32 : Theory.language
val llvm_mips64 : Theory.language

val load : ?backend:string -> unit -> unit
(** [load ()] loads the knowledge base rules for the MIPS targets.

    This includes parsing the loader output and enabling backward compatibility
    with the old [Arch.t] representation. *)
