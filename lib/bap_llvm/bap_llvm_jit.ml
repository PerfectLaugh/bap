type t

external create : unit -> t = "bap_llvm_jit_create"
external define : t -> string -> nativeint -> unit = "bap_llvm_jit_define"
external compile : t -> string -> string -> nativeint = "bap_llvm_jit_compile"
