open Core

(** Initialize LLVM backend.

    So far we keep the interface very tight, though later we may extend it by
    publishing more functions. *)
module Std : sig
  type x86_syntax = [ `att | `intel ] [@@deriving sexp]

  val llvm_version : string
  (** [llvm_version] the version of LLVM that BAP is built with *)

  val init_disassembler : ?x86_syntax:x86_syntax -> unit -> unit Or_error.t
  (** [init_disassembler ()] initializes and registers the LLVM based
      disassembler. *)

  val demangle : string -> string
  (** [demangle name] demangles the [name] with the demangler of LLVM, which
      knows the manglings of Itanium, e.g., of GCC and Clang, of MSVC, of Rust,
      and of D, or is the [name], if it is not mangled.

      @since 2.6.0 *)

  val init_loader : ?base:int64 -> ?pdb_path:string -> unit -> unit
  (** [init_loader ()] initializes and registers the LLVM based loader.

      @param base
        a base address to use. If not specified, then a base address specified
        by the binary is used. If there is no such address, then some arbitrary
        constant will be used.

      @param pdb_path
        is either a path to the pdb file or a path to a folder where it resides
        (by default, the current working directory). In the latter case, the pdb
        file name will be infered from the executable name. *)
end
