open Core
open Bap.Std

type interval = { first : int; last : int }
type cover = interval Tid.Map.t
type t = { mutable parents : var Var.Map.t; mutable covers : cover Var.Map.t }

let rec representative t var =
  match Map.find t.parents var with
  | None -> var
  | Some parent ->
      if Var.equal parent var then var
      else
        let root = representative t parent in
        t.parents <- Map.set t.parents ~key:var ~data:root;
        root

let intervals_overlap x y =
  Map.to_alist x
  |> List.exists ~f:(fun (tid, x) ->
      match Map.find y tid with
      | Some y -> x.first < y.last && y.first < x.last
      | None -> false)

let bits var = match Var.typ var with Type.Imm bits -> Some bits | _ -> None

let merge t left right =
  let left = representative t left and right = representative t right in
  if Var.equal left right then ()
  else
    let compatible =
      Option.equal Int.equal (bits left) (bits right)
      &&
      match (Map.find t.covers left, Map.find t.covers right) with
      | Some x, Some y -> not (intervals_overlap x y)
      | _ -> false
    in
    if compatible then (
      let left_cover = Map.find_exn t.covers left in
      let right_cover = Map.find_exn t.covers right in
      let cover =
        Map.fold right_cover ~init:left_cover ~f:(fun ~key:tid ~data:y cover ->
            Map.update cover tid ~f:(function
              | None -> y
              | Some x ->
                  {
                    first = Int.min x.first y.first;
                    last = Int.max x.last y.last;
                  }))
      in
      t.parents <- Map.set t.parents ~key:right ~data:left;
      t.covers <- Map.remove t.covers right;
      t.covers <- Map.set t.covers ~key:left ~data:cover)

let add_point covers var tid point =
  let cover =
    match Map.find covers var with Some cover -> cover | None -> Tid.Map.empty
  in
  let cover =
    Map.update cover tid ~f:(function
      | None -> { first = point; last = point }
      | Some interval ->
          {
            first = Int.min interval.first point;
            last = Int.max interval.last point;
          })
  in
  Map.set covers ~key:var ~data:cover

let add_vars covers vars tid point =
  Set.fold vars ~init:covers ~f:(fun covers var ->
      add_point covers var tid point)

let jmp_vars jmp =
  let labels =
    match Jmp.kind jmp with
    | Goto label | Ret label -> [ label ]
    | Call call -> Call.target call :: Option.to_list (Call.return call)
    | Int _ -> []
  in
  List.fold labels ~init:(Jmp.free_vars jmp) ~f:(fun vars -> function
    | Direct _ -> vars
    | Indirect exp -> Set.union vars (Exp.free_vars exp))

let covers sub =
  let covers = ref Var.Map.empty in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      let tid = Term.tid blk in
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          covers := add_point !covers (Phi.lhs phi) tid 0;
          Phi.values phi
          |> Seq.iter ~f:(fun (_, exp) ->
              covers := add_vars !covers (Exp.free_vars exp) tid 0));
      let count = ref 1 in
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def ->
          covers := add_point !covers (Def.lhs def) tid !count;
          covers := add_vars !covers (Def.free_vars def) tid !count;
          incr count);
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp ->
          covers := add_vars !covers (jmp_vars jmp) tid !count;
          incr count));
  !covers

let create sub =
  let t = { parents = Var.Map.empty; covers = covers sub } in
  Term.enum blk_t sub
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def ->
          match Def.rhs def with
          | Bil.Var right -> merge t (Def.lhs def) right
          | _ -> ());
      Term.enum phi_t blk
      |> Seq.iter ~f:(fun phi ->
          Phi.values phi
          |> Seq.iter ~f:(fun (_, exp) ->
              match exp with
              | Bil.Var right -> merge t (Phi.lhs phi) right
              | _ -> ())));
  let vars =
    Map.keys t.covers
    |> List.sort ~compare:(fun x y -> Int.compare (Var.index x) (Var.index y))
  in
  List.iter vars ~f:(fun left ->
      List.iter vars ~f:(fun right ->
          if Var.same (Var.base left) (Var.base right) then merge t left right));
  t

let representative t var = representative t var
