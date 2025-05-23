open Core

open Stdlib.Format
open Bap_knowledge
open Bap_core_theory_value
open Knowledge.Syntax
open Knowledge.Let

module Value = Knowledge.Value

let package = "core"



let pure = KB.Context.declare ~package "let-variables" !!Int63.zero
let temp = KB.Context.declare ~package "tmp-variables" !!Int63.zero

type id = Int63.t [@@deriving bin_io, compare, hash, sexp]

type ident =
  | Var of {num : id; ver : int}
  | Let of {num : id}
  | Reg of {name : String.Caseless.t; ver : int}
[@@deriving bin_io, compare, hash, sexp]

type 'a var = 'a sort * ident
type 'a t = 'a var

let valid_first_char = function
  | '0'..'9' | '#' | '$' -> false
  | _ -> true

let escapeworthy = Char.all |> List.filter ~f:(function
    | '.' -> true
    | c -> Char.is_whitespace c || not (Char.is_print c))

let escape_char = '\\'

let escape =
  Staged.unstage @@
  String.Escaping.escape ~escapeworthy ~escape_char

let mangle_if_necessary name =
  let name = escape name in
  if String.is_empty name then "_"
  else if not (valid_first_char name.[0])
  then "_" ^ name
  else name

let define sort name : 'a var =
  sort, Reg {name=mangle_if_necessary name; ver=0}

let create sort ident = sort,ident

let forget (s,v) = Sort.forget s,v
let resort (_,v) s = s,v

let pp_ver ppf = function
  | 0 -> ()
  | n -> fprintf ppf ".%d" n

let pp_ident ppf ident = match ident with
  | Reg {name; ver} -> Format.fprintf ppf "%s%a" name pp_ver ver
  | Let {num} ->
    Format.fprintf ppf "$%a" Int63.pp num
  | Var {num; ver} ->
    Format.fprintf ppf "#%a%a" Int63.pp num pp_ver ver

let pp ppf (_,v) = Format.fprintf ppf "%a" pp_ident v
let name (_,v) = Format.asprintf "%a" pp_ident v
let ident (_,v) = v
let sort (s,_) = s
let is_virtual v = match ident v with
  | Let _ | Var _ -> true
  | Reg _ -> false
let is_mutable v = match ident v with
  | Let _ -> false
  | Reg _ | Var _ -> true

let nat1 = Knowledge.Domain.total "nat1"
    ~empty:0
    ~inspect:sexp_of_int
    ~order:Int.compare

let versioned (s,v) ver = match v with
  | Let _ -> (s,v)
  | Reg {name} -> s,Reg {name; ver}
  | Var {num} -> s,Var {num; ver}

let version v = match ident v with
  | Let _ -> 0
  | Reg {ver} | Var {ver} -> ver

let incr var =
  let* v = Knowledge.Context.get var in
  let+ () = Knowledge.Context.set var (Int63.succ v) in
  v

let fresh s =
  let+ num = incr pure in
  create s (Var {num; ver=0})

let reset_temporary_counter = KB.Context.set temp Int63.zero

type 'a pure = 'a Bap_core_theory_value.t knowledge

(* we're ensuring that a variable is immutable by constraining
   the scope computation to be pure. *)
let scoped : 'a sort -> ('a t -> 'b pure) -> 'b pure = fun s f ->
  let* num = Knowledge.Context.get pure in
  Knowledge.Context.with_var pure (Int63.succ num) @@ fun () ->
  f @@ create s (Let {num})

module Ident = struct
  type t = ident [@@deriving bin_io, compare, hash, sexp]

  let num s = try Int63.of_string s with _ ->
    failwithf "`%s' is not a valid temporary value" s ()

  let split_version s =
    match String.Escaping.rindex s ~escape_char '.' with
    | None -> s,0
    | Some n ->
      String.subo ~len:n s,
      Int.of_string (String.subo ~pos:(n+1) s)

  let sub1 = String.subo ~pos:1

  let of_string x =
    let n = String.length x in
    if n = 0
    then invalid_arg "a variable identifier can't be empty";
    match x.[0] with
    | '$' -> Let {num = num (sub1 x)}
    | '#' ->
      let s,ver = split_version (sub1 x) in
      Var {num = num s; ver}
    | _ ->
      let name,ver = split_version x in
      Reg {name; ver}

  let to_string x = Format.asprintf "%a" pp_ident x
  include Base.Comparable.Make(struct
      type t = ident [@@deriving bin_io, compare, sexp]
    end)

end
type ord = Ident.comparator_witness

module Top : sig
  type t = unit var [@@deriving bin_io, compare, sexp]
  include Base.Comparable.S with type t := t
end = struct
  type t = Sort.Top.t * ident [@@deriving bin_io, sexp]

  include Base.Comparable.Inherit(Ident)(struct
      type t = Sort.Top.t * ident
      let sexp_of_t = sexp_of_t
      let component = snd
    end)
end
