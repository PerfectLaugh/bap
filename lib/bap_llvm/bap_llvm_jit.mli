(** The JIT of LLVM.

    Compiles the modules of LLVM IR, in their text, to the native code of the
    host, e.g., of the blocks of the instructions, that the lifted engine of
    the Primus Unicorn runs. The code lives as long as the program.

    @since 2.6.0 *)

type t

val create : unit -> t
(** [create ()] the JIT of the host. Raises [Failure], if LLVM doesn't have the
    target of the host. *)

val define : t -> string -> nativeint -> unit
(** [define jit name addr] the symbol [name], that the modules declare, e.g.,
    of a function of C, is at [addr]. *)

val compile : t -> string -> string -> nativeint
(** [compile jit ir name] optimizes the module, whose text is [ir], compiles
    it, and returns the address of its function [name]. Raises [Failure], if
    the module is invalid. *)
