(** The JIT of LLVM.

    Compiles the modules of LLVM IR, in their text, to the native code of the
    host, e.g., of the blocks of the instructions, that the lifted engine of
    the Primus Unicorn runs. The code stays, until it is released.

    @since 2.6.0 *)

type t

val create : unit -> t
(** [create ()] the JIT of the host. Raises [Failure], if LLVM doesn't have the
    target of the host. *)

val define : t -> string -> nativeint -> unit
(** [define jit name addr] the symbol [name], that the modules declare, e.g.,
    of a function of C, is at [addr]. *)

type code
(** the code of a module, which stays, until it is released *)

val compile : t -> string -> string -> code
(** [compile jit ir name] optimizes the module, whose text is [ir], compiles
    it, and returns its code, whose function [name] is called. Raises
    [Failure], if the module is invalid. *)

val address : code -> nativeint
(** [address code] the address of the function of the code. Raises
    [Invalid_argument], if the code is released. *)

val release : code -> unit
(** [release code] removes the code, which must not run anymore, e.g., as the
    code, that it was compiled from, changed. Releasing it again does nothing.
    The code, that is collected, but not released, stays. *)
