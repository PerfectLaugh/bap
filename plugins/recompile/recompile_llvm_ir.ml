open Core
open Bap.Std

module Parse = struct
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

  let error fmt = Printf.ksprintf (fun s -> raise (Error s)) fmt

  let tokenize line =
    let line =
      match String.index line ';' with
      | Some i -> String.prefix line i
      | None -> line
    in
    let tokens = ref [] and buf = Buffer.create 16 in
    let flush () =
      if Buffer.length buf > 0 then (
        tokens := Buffer.contents buf :: !tokens;
        Buffer.clear buf)
    in
    String.iter line ~f:(fun c ->
        match c with
        | ' ' | '\t' -> flush ()
        | ',' | '(' | ')' | '[' | ']' | '{' | '}' | '=' | '<' | '>' ->
            flush ();
            tokens := String.of_char c :: !tokens
        | c -> Buffer.add_char buf c);
    flush ();
    List.rev !tokens

  let flags =
    [
      "nuw";
      "nsw";
      "exact";
      "disjoint";
      "nneg";
      "samesign";
      "inbounds";
      "nusw";
      "tail";
      "musttail";
      "notail";
      "noundef";
      "signext";
      "zeroext";
      "volatile";
    ]

  let rec skip_flags = function
    | t :: rest when List.mem flags t ~equal:String.equal -> skip_flags rest
    | ts -> ts

  let width_of_type = function
    | "ptr" -> 64
    | t when String.is_prefix t ~prefix:"i" -> (
        match Int.of_string_opt (String.drop_prefix t 1) with
        | Some n -> n
        | None -> error "the type %s" t)
    | t -> error "the type %s" t
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
