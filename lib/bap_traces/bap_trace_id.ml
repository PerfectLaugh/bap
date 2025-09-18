open Core
open Regular.Std
open Bap.Std

module Bin = Bin_prot.Utils.Make_binable_with_uuid (struct
  module Binable = String

  type t = Uuidm.t

  let to_binable = Uuidm.to_binary_string

  let of_binable s =
    match Uuidm.of_binary_string s with
    | None -> invalid_arg "Bad UUID format"
    | Some uuid -> uuid

  let caller_identity =
    Bin_shape.Uuid.of_string "82c292b4-04e0-4f92-957b-3755d74d5794"
end)

module Stringable = struct
  type t = Uuidm.t

  let of_string s =
    match Uuidm.of_string s with
    | None -> invalid_arg "Bad UUID format"
    | Some uuid -> uuid

  let to_string s = Uuidm.to_string s
end

module Sexp = Sexpable.Of_stringable (Stringable)
include Uuidm

include Regular.Make (struct
  let compare = Uuidm.compare

  include Bin
  include Sexp
  include Stringable

  let hash = Hashtbl.hash
  let module_name = None
  let version = "1.0.0"
  let pp ppf t = Uuidm.pp ppf t
end)

let of_string = Stringable.of_string
