open Core
open Bap.Std

module Parse : sig
  type value = E of exp | Global of string

  type item =
    | Assign of var * exp
    | Store of exp * exp * size
    | Leave of int * exp option

  type terminator =
    | Br of string
    | Cbr of exp * string * string
    | Switch of exp * int * (word * string) list * string
    | Unreachable
    | Return

  type block = {
    label : string;
    phis : (var * (exp * string) list) list;
    items : item list;
    terminator : terminator;
  }

  exception Error of string

  val error : ('a, unit, string, string, string, 'b) format6 -> 'a
  val tokenize : string -> string list
  val skip_flags : string list -> string list
  val width_of_type : string -> int
end

type thread_witness = {
  blocks : Parse.block list;
  header : Parse.block;
  predecessor : string;
  edge_predecessor : string;
  state : var;
  value : word;
  edge : Parse.block;
  leaf : Parse.block;
  env : word Var.Map.t;
}

type split_witness = {
  left : thread_witness;
  right : thread_witness;
  condition : exp;
  split : Parse.block;
}
