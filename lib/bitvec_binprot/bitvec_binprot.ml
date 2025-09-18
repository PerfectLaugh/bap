open Bin_prot.Std

type t = Bitvec.t

module Functions = Bin_prot.Utils.Make_binable_with_uuid (struct
  module Binable = struct
    type t = string [@@deriving bin_io]
  end

  type t = Bitvec.t

  let to_binable = Bitvec.to_binary
  let of_binable = Bitvec.of_binary

  let caller_identity =
    Bin_shape.Uuid.of_string "ae1bec04-6b5f-45b0-b4d6-412204cdc45b"
end)

include Functions
