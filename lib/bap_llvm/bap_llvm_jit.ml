type t
type code

external create : unit -> t = "bap_llvm_jit_create"
external define : t -> string -> nativeint -> unit = "bap_llvm_jit_define"

external compile_stub : t -> string -> string -> string -> code
  = "bap_llvm_jit_compile"

let compile ?(cache = "") t ir name = compile_stub t ir name cache

external address : code -> nativeint = "bap_llvm_jit_address"
external release : code -> unit = "bap_llvm_jit_release"
external symbol : t -> string -> nativeint = "bap_llvm_jit_symbol"
