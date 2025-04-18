module Std_bytes = Bytes

open Core

module Binable = Bin_prot.Utils.Make_binable_with_uuid(struct
    module Binable = String
    type t = Std_bytes.t
    let to_binable = Std_bytes.unsafe_to_string
    let of_binable = Std_bytes.of_string
    let caller_identity = Bin_shape.Uuid.of_string "19071993-d15a-49be-b3a2-4ef4bacd3c0a"
  end)


module Stringable = struct
  type t = Std_bytes.t
  let of_string = Std_bytes.of_string
  let to_string = Std_bytes.unsafe_to_string
end

module Sexpable = Sexpable.Of_stringable(Stringable)

module type Seq = sig
  type t [@@deriving sexp_of]
  type elt
  val create: int -> t
  val length: t -> int
  val get: t -> int -> elt
  val set: t -> int -> elt -> unit
  val unsafe_blit: src:t -> src_pos:int -> dst:t -> dst_pos:int -> len:int -> unit
end

module Make(S : Seq) = struct
  type t = S.t [@@deriving sexp_of]
  type elt = S.elt
  let create ~len = S.create len
  let length = S.length
  let get = S.get
  let set = S.set
  let unsafe_blit = S.unsafe_blit
end

module Elt = struct
  type t = char
  let equal t t' = Char.compare t t' = 0
  let of_bool b = if b then 'a' else 'b'
end

module T = struct
  include Std_bytes
  include Binable
  include Sexpable
  type elt = Elt.t
  let hash = Hashtbl.hash
  let unsafe_blit ~src ~src_pos ~dst ~dst_pos ~len =
    unsafe_blit src src_pos dst dst_pos len

  let init len ~f = init len f
  let map t ~f = map f t
  let mapi t ~f = mapi f t
  let iteri t ~f = iteri f t
end

module B = Make(T)
module Blit_bytes = Blit.Make(B)

include T
include Blit_bytes

module To_string = struct
  let blit = Blit_bytes.blit
  let blito = Blit_bytes.blito
  let unsafe_blit = Blit_bytes.unsafe_blit
  let sub t ~pos ~len = sub_string t pos len

  let subo ?(pos=0) ?len src =
    let len = match len with
      | None -> Bytes.length src - pos
      | Some len -> len in
    sub src ~pos ~len
end

module From_string =
  Blit.Make_distinct
    (struct
      type t = string
      let length = String.length
    end) (struct
    type nonrec t = t
    let create ~len = create len
    let length = length
    let unsafe_blit ~src ~src_pos ~dst ~dst_pos ~len =
      Std_bytes.blit_string src src_pos dst dst_pos len
  end)

let create = Std_bytes.create
let length = Std_bytes.length
let get = Std_bytes.get
let set = Std_bytes.set
let convert     = T.unsafe_to_string
let apply t f   = f (convert t)
let fold_until t = apply t String.fold_until
let fold_result t = apply t String.fold_result
let fold t      = apply t String.fold
let find t      = apply t String.find
let iter t      = apply t String.iter
let count t     = apply t String.count
let min_elt t   = apply t String.min_elt
let max_elt t   = apply t String.max_elt
let exists t    = apply t String.exists
let for_all t   = apply t String.for_all
let to_array t  = apply t String.to_array
let to_list t   = apply t String.to_list
let find_map t  = apply t String.find_map
let sum m t ~f  = apply t (fun s -> String.sum m s ~f)
let is_empty t  = apply t String.is_empty
let mem t elt = String.mem (convert t) elt
let lowercase = lowercase_ascii
let uppercase = uppercase_ascii
let capitalize = capitalize_ascii
let uncapitalize = uncapitalize_ascii

include Identifiable.Make_and_derive_hash_fold_t(struct
    type t = T.t [@@deriving bin_io, compare, sexp]
    include Hashable.Make_and_derive_hash_fold_t(T)
    let of_string = Stringable.of_string
    let to_string = Stringable.to_string
    let module_name = "Regular.Std.Bytes"
  end)

module Unsafe = struct
  [@@@ocaml.warning "-3"]

  let of_string = T.unsafe_of_string
  let to_string = T.unsafe_to_string

  (** The following is for system use only. Do not call directly. *)
  external get  : T.t -> int -> char = "%string_unsafe_get"
  external set  : T.t -> int -> char -> unit = "%string_unsafe_set"
  external blit : T.t -> int -> T.t -> int -> int -> unit = "caml_blit_string" "noalloc"
  external fill : T.t -> int -> int -> char -> unit = "caml_fill_string" "noalloc"
end
