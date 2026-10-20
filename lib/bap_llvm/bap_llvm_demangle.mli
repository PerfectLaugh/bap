(** The demangler of LLVM. *)

val demangle : string -> string
(** [demangle name] the demangled [name], e.g., of C++, Rust, or D, or the
    [name] itself, if it is not mangled. *)
