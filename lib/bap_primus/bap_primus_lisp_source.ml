open Core
open Format
module Cst = Parsexp.Cst
module Loc = Bap_primus_lisp_loc
module Index = Bap_primus_lisp_index
module Id = Index.Make ()
module Eq = Index.Make ()

type error = Bad_sexp of (string * Parsexp.Parse_error.t)

type ('a, 'i, 'e) interned = ('a, 'i, 'e) Index.interned = {
  data : 'a;
  id : 'i;
  eq : 'e;
}

type 'a indexed = ('a, Id.t, Eq.t) interned

type tree = token indexed
and token = Atom of string | List of tree list

type t = {
  lastid : Id.t;
  lasteq : Eq.t;
  hashed : Eq.t Sexp.Map.t;
  equivs : Eq.t Id.Map.t;
  origin : string Id.Map.t;
  ranges : Loc.range Id.Map.t;
  source : tree list String.Map.t;
  inputs : string String.Map.t;
  rclass : Id.t Id.Map.t;
}

let empty =
  {
    lastid = Id.null;
    lasteq = Eq.null;
    hashed = Sexp.Map.empty;
    equivs = Id.Map.empty;
    origin = Id.Map.empty;
    ranges = Id.Map.empty;
    source = String.Map.empty;
    inputs = String.Map.empty;
    rclass = Id.Map.empty;
  }

let is_empty { lastid } = Id.equal Id.null lastid
let equal_inputs = String.Map.equal String.equal
let equal x y = phys_equal x y || equal_inputs x.inputs y.inputs
let nextid p = { p with lastid = Id.next p.lastid }
let nexteq p = { p with lasteq = Eq.next p.lasteq }

let rec repr s id =
  match Map.find s.rclass id with
  | None -> id
  | Some id' -> if Id.(id = id') then id else repr s id'

let hashcons p sexp =
  match Map.find p.hashed sexp with
  | Some eq -> (p, eq)
  | None ->
      let p = nexteq p in
      ({ p with hashed = Map.set p.hashed ~key:sexp ~data:p.lasteq }, p.lasteq)

let unify p eq = { p with equivs = Map.set p.equivs ~key:p.lastid ~data:eq }
let nopos = Parsexp.Positions.beginning_of_file
let norange = Parsexp.Positions.make_range_incl ~start_pos:nopos ~last_pos:nopos

let getrange pos parents child =
  match pos with
  | None -> norange
  | Some pos -> (
      Parsexp.Positions.find_sub_sexp_in_list_phys pos parents ~sub:child
      |> function
      | None -> norange
      | Some range -> range)

let add_range p data = { p with ranges = Map.set p.ranges ~key:p.lastid ~data }

let of_cst p sexps =
  let newterm p r s =
    let p = nextid p in
    let p = add_range p r in
    hashcons p (Cst.Forget.t s)
  in
  let rec of_sexp p s =
    match s with
    | Cst.Comment _ -> (p, None)
    | Cst.Sexp (Atom { atom; loc; unescaped } as s) ->
        let p, eq = newterm p loc s in
        let x = Option.value unescaped ~default:atom in
        (unify p eq, Some { data = Atom x; id = p.lastid; eq })
    | Cst.Sexp (List { elements = xs; loc } as s) ->
        let p, data =
          List.fold ~init:(p, [])
            ~f:(fun (p, xs) sexp ->
              match of_sexp p sexp with
              | p, None -> (p, xs)
              | p, Some x -> (p, x :: xs))
            xs
        in
        let p, eq = newterm p loc s in
        (unify p eq, Some { data = List (List.rev data); id = p.lastid; eq })
  in
  let p, trees =
    List.fold sexps ~init:(p, []) ~f:(fun (p, xs) x ->
        match of_sexp p x with p, None -> (p, xs) | p, Some x -> (p, x :: xs))
  in
  (p, List.rev trees)

let of_sexps ?pos p sexps =
  let getrange = getrange pos sexps in
  let newterm p s =
    let p = nextid p in
    let p = add_range p (getrange s) in
    hashcons p s
  in
  let rec of_sexp p s =
    match s with
    | Sexp.Atom x ->
        let p, eq = newterm p s in
        (unify p eq, { data = Atom x; id = p.lastid; eq })
    | Sexp.List xs ->
        let p, data =
          List.fold ~init:(p, [])
            ~f:(fun (p, xs) sexp ->
              let p, x = of_sexp p sexp in
              (p, x :: xs))
            xs
        in
        let p, eq = newterm p s in
        (unify p eq, { data = List (List.rev data); id = p.lastid; eq })
  in
  let p, trees =
    List.fold sexps ~init:(p, []) ~f:(fun (p, xs) x ->
        let p, x = of_sexp p x in
        (p, x :: xs))
  in
  (p, List.rev trees)

let add_origin origins origin trees =
  let rec add origins token =
    let origins = Map.set origins ~key:token.id ~data:origin in
    match token.data with
    | Atom _ -> origins
    | List tokens -> List.fold tokens ~init:origins ~f:add
  in
  List.fold ~init:origins ~f:add trees

let load p filename =
  let source = In_channel.read_all filename in
  match Parsexp.Many_cst.parse_string source with
  | Error err -> Error (Bad_sexp (filename, err))
  | Ok cst ->
      let p, tree = of_cst p cst in
      let origin = add_origin p.origin filename tree in
      Ok
        {
          p with
          origin;
          source = Map.set p.source ~key:filename ~data:tree;
          inputs = Map.set p.inputs ~key:filename ~data:source;
        }

let find p filename = Map.find p.source filename
let inputs p = Map.to_alist p.inputs

let range p id =
  match Map.find p.ranges (repr p id) with None -> norange | Some rng -> rng

let filename p id =
  match Map.find p.origin (repr p id) with
  | None -> "/unknown/"
  | Some file -> file

let loc p tree = Loc.{ file = filename p tree; range = range p tree }
let has_loc p id = Map.mem p.origin (repr p id)
let lastid s = s.lastid
let lasteq s = s.lasteq

let fold p ~init ~f =
  Map.fold ~init p.source ~f:(fun ~key ~data user -> f key data user)

let derived p ~from id =
  if Id.(Id.null = from) then { p with lastid = Id.max id p.lastid }
  else
    {
      p with
      lastid = Id.max id p.lastid;
      rclass = Map.set p.rclass ~key:id ~data:from;
    }

(* the derived identifiers are above the identifiers of the source, so
   their map is built in a linear time and appended *)
let derived_all p ids =
  match List.last ids with
  | None -> p
  | Some (last, _) ->
      let upper_part =
        List.filter ids ~f:(fun (_, from) -> not Id.(Id.null = from))
        |> Array.of_list |> Id.Map.of_sorted_array_unchecked
      in
      let rclass =
        match Map.append ~lower_part:p.rclass ~upper_part with
        | `Ok rclass -> rclass
        | `Overlapping_key_ranges ->
            Map.merge_skewed p.rclass upper_part ~combine:(fun ~key:_ _ x -> x)
      in
      { p with lastid = Id.max last p.lastid; rclass }

(* The source, as it is stored in the cache, see [Bap_primus_lisp_cache],
   whose maps are arrays, in their orders, so that they are built in a
   linear time. The terms of [hashed], whose sexps contain the sexps of
   their subterms, are stored by the classes of their subterms, which are
   hashed before them, so that the sexps share their subterms again. *)
module Repr = struct
  type tree = { data : token; id : int; eq : int }
  and token = Atom of string | List of tree list [@@deriving bin_io]

  type term = Term_atom of string | Term_list of int list [@@deriving bin_io]
  type pos = { line : int; col : int; offset : int } [@@deriving bin_io]

  type t = {
    lastid : int;
    lasteq : int;
    hashed : (term * int) array;
    equivs : (int * int) array;
    files : string array;
    origin : (int * int) array;
    ranges : (int * pos * pos) array;
    source : (string * tree list) array;
    inputs : (string * string) array;
    rclass : (int * int) array;
  }
  [@@deriving bin_io]
end

let to_repr (p : t) : Repr.t =
  let id = Id.to_int and eq = Eq.to_int in
  let rec tree ({ data; id = i; eq = e } : tree) : Repr.tree =
    let data : Repr.token =
      match data with Atom x -> Atom x | List xs -> List (List.map xs ~f:tree)
    in
    { data; id = id i; eq = eq e }
  in
  let pos ({ line; col; offset } : Parsexp.Positions.pos) : Repr.pos =
    { line; col; offset }
  in
  let files =
    Map.data p.origin |> List.dedup_and_sort ~compare:String.compare
  in
  let file = String.Map.of_alist_exn (List.mapi files ~f:(fun i f -> (f, i))) in
  {
    lastid = id p.lastid;
    lasteq = eq p.lasteq;
    hashed =
      Map.to_alist p.hashed
      |> List.map ~f:(fun (sexp, e) ->
          let term : Repr.term =
            match sexp with
            | Sexp.Atom x -> Term_atom x
            | Sexp.List xs ->
                Term_list
                  (List.map xs ~f:(fun x -> eq (Map.find_exn p.hashed x)))
          in
          (term, eq e))
      |> Array.of_list;
    equivs =
      Map.to_alist p.equivs
      |> List.map ~f:(fun (i, e) -> (id i, eq e))
      |> Array.of_list;
    files = Array.of_list files;
    origin =
      Map.to_alist p.origin
      |> List.map ~f:(fun (i, f) -> (id i, Map.find_exn file f))
      |> Array.of_list;
    ranges =
      Map.to_alist p.ranges
      |> List.map ~f:(fun (i, { Parsexp.Positions.start_pos; end_pos }) ->
          (id i, pos start_pos, pos end_pos))
      |> Array.of_list;
    source =
      Map.to_alist p.source
      |> List.map ~f:(fun (f, trees) -> (f, List.map trees ~f:tree))
      |> Array.of_list;
    inputs = Map.to_alist p.inputs |> Array.of_list;
    rclass =
      Map.to_alist p.rclass
      |> List.map ~f:(fun (i, j) -> (id i, id j))
      |> Array.of_list;
  }

let of_repr (r : Repr.t) : t =
  let id = Id.of_int and eq = Eq.of_int in
  let rec tree ({ data; id = i; eq = e } : Repr.tree) : tree =
    let data =
      match data with Atom x -> Atom x | List xs -> List (List.map xs ~f:tree)
    in
    { data; id = id i; eq = eq e }
  in
  let pos ({ line; col; offset } : Repr.pos) : Parsexp.Positions.pos =
    { line; col; offset }
  in
  (* the sexps of the classes, the subterms first *)
  let sexps = Hashtbl.create (module Int) in
  Array.sorted_copy r.hashed ~compare:(fun (_, x) (_, y) -> Int.compare x y)
  |> Array.iter ~f:(fun (term, e) ->
      let sexp =
        match (term : Repr.term) with
        | Term_atom x -> Sexp.Atom x
        | Term_list xs -> Sexp.List (List.map xs ~f:(Hashtbl.find_exn sexps))
      in
      Hashtbl.set sexps ~key:e ~data:sexp);
  {
    lastid = id r.lastid;
    lasteq = eq r.lasteq;
    hashed =
      Array.map r.hashed ~f:(fun (_, e) -> (Hashtbl.find_exn sexps e, eq e))
      |> Sexp.Map.of_sorted_array_unchecked;
    equivs =
      Array.map r.equivs ~f:(fun (i, e) -> (id i, eq e))
      |> Id.Map.of_sorted_array_unchecked;
    origin =
      Array.map r.origin ~f:(fun (i, f) -> (id i, r.files.(f)))
      |> Id.Map.of_sorted_array_unchecked;
    ranges =
      Array.map r.ranges ~f:(fun (i, start_pos, end_pos) ->
          ( id i,
            {
              Parsexp.Positions.start_pos = pos start_pos;
              end_pos = pos end_pos;
            } ))
      |> Id.Map.of_sorted_array_unchecked;
    source =
      Array.map r.source ~f:(fun (f, trees) -> (f, List.map trees ~f:tree))
      |> String.Map.of_sorted_array_unchecked;
    inputs = String.Map.of_sorted_array_unchecked r.inputs;
    rclass =
      Array.map r.rclass ~f:(fun (i, j) -> (id i, id j))
      |> Id.Map.of_sorted_array_unchecked;
  }

let pp_error ppf (Bad_sexp (filename, err)) =
  Parsexp.Parse_error.report ppf ~filename err

let rec sexp_of_tree = function
  | { data = List xs } -> Sexp.List (List.map xs ~f:sexp_of_tree)
  | { data = Atom x } -> Sexp.Atom x

let pp_tree ppf t = Sexp.pp_hum ppf (sexp_of_tree t)

let pp_print_underline ppf (off, len) =
  let line = String.init len ~f:(fun i -> if i < off then ' ' else '^') in
  fprintf ppf "> %s@\n" line

let pp_underline ?(context = 4) { inputs } ppf
    { Loc.file; range = { start_pos; end_pos } } =
  match Map.find inputs file with
  | None -> ()
  | Some source ->
      let current = ref 0 in
      String.split_lines source
      |> List.iter ~f:(fun line ->
          incr current;
          if current.contents = end_pos.line + 1 then
            pp_print_underline ppf (start_pos.col, end_pos.col);
          let distance =
            min
              (abs (!current - start_pos.line))
              (abs (!current - end_pos.line))
          in
          let bad = !current >= start_pos.line && !current <= end_pos.line in
          if distance < context then
            fprintf ppf "%c %s@\n" (if bad then '>' else '|') line);
      (* in case if the error was on the last line in a file *)
      if current.contents = end_pos.line then
        pp_print_underline ppf (start_pos.col, end_pos.col)

let pp { inputs } ppf { Loc.file; range = { start_pos; end_pos } } =
  match Map.find inputs file with
  | None -> ()
  | Some source ->
      let pos = start_pos.offset in
      let len = end_pos.offset - start_pos.offset + 1 in
      let exp = String.sub source ~pos ~len in
      fprintf ppf "%s" exp
