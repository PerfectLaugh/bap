type t
type pcs = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
type sizes = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

type modes =
  (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

type accesses = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array2.t

external create : int -> int -> bool -> int -> t = "bap_native_trace_create"
external count : t -> int64 = "bap_native_trace_count"
external retained : t -> int = "bap_native_trace_retained"
external accesses_count : t -> int64 = "bap_native_trace_accesses_count"
external clear : t -> unit = "bap_native_trace_clear"

module Record = struct
  external prepare : t -> bool -> unit = "bap_native_trace_prepare"

  external record : t -> int64 -> int -> bool -> unit
    = "bap_native_trace_record"

  external extend : t -> int -> unit = "bap_native_trace_extend"

  external access : t -> bool -> int64 -> int -> int64 -> int64 -> int64 -> unit
    = "bap_native_trace_access_bytecode" "bap_native_trace_access"

  external unrun : t -> int64 -> unit = "bap_native_trace_unrun"

  external bound :
    t -> bool -> bool -> bool -> int64 -> int64 array -> bool -> unit
    = "bap_native_trace_bound_bytecode" "bap_native_trace_bound"
end

external blocks : t -> bool = "bap_native_trace_blocks"
external pcs : t -> int -> pcs = "bap_native_trace_pcs"
external sizes : t -> int -> sizes = "bap_native_trace_sizes"
external modes : t -> int -> modes = "bap_native_trace_modes"
external accesses : t -> int -> accesses = "bap_native_trace_mem"
external save : t -> int -> string -> int64 = "bap_native_trace_save"
external bounds : t -> pcs = "bap_native_trace_bounds"
external ranges : t -> pcs = "bap_native_trace_ranges"

let create ?(every = 1) ?(blocks = false) ?(accesses = 0) size =
  create size every blocks accesses

let pcs ?(last = -1) t = pcs t last
let sizes ?(last = -1) t = sizes t last
let modes ?(last = -1) t = modes t last
let accesses ?(last = -1) t = accesses t last
let save ?(last = -1) t file = save t last file
