open Core
open Bap.Std

type t = { blks : blk term list; replaces : Tid.Set.t }

let blks t = t.blks
let with_blks t blks = { t with blks }
let entry t = List.hd_exn t.blks

let ends blk =
  match Term.last jmp_t blk with
  | Some jmp -> ( match Jmp.cond jmp with Int w -> Word.is_one w | _ -> false)
  | None -> false

let close ~last blks =
  let continue blk dst =
    if ends blk then Ok blk
    else
      match dst with
      | Some dst -> Ok (Term.append jmp_t blk (Jmp.create_goto dst))
      | None ->
          Or_error.errorf "the block %s falls through, without the next"
            (Tid.to_string (Term.tid blk))
  in
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | [ blk ] ->
        Result.map (continue blk last) ~f:(fun b -> List.rev (b :: acc))
    | blk :: (next :: _ as rest) ->
        Result.bind
          (continue blk (Some (Direct (Term.tid next))))
          ~f:(fun b -> loop (b :: acc) rest)
  in
  loop [] blks

let create ~last blks =
  match blks with
  | [] -> Or_error.error_string "the region has no blocks"
  | _ ->
      Result.map (close ~last blks) ~f:(fun blks ->
          { blks; replaces = Tid.Set.of_list (List.map blks ~f:Term.tid) })

let of_blks ?next blks =
  create ~last:(Option.map next ~f:(fun a -> Indirect (Bil.int a))) blks

let of_sub sub = create ~last:None (Term.enum blk_t sub |> Seq.to_list)

let targets blk =
  Term.enum jmp_t blk |> Seq.to_list
  |> List.concat_map ~f:(fun jmp ->
      let direct = function Some (Direct tid) -> [ tid ] | _ -> [] in
      match Jmp.kind jmp with
      | Goto l | Ret l -> direct (Some l)
      | Call c -> direct (Call.return c)
      | Int (_, tid) -> [ tid ])

let of_range sub ~lo ~hi =
  let blks = Term.enum blk_t sub |> Seq.to_list in
  let _, marked =
    List.fold_map blks ~init:None ~f:(fun addr blk ->
        let addr =
          match Term.get_attr blk address with Some a -> Some a | None -> addr
        in
        let inside =
          match addr with
          | Some a -> Addr.(a >= lo) && Addr.(a < hi)
          | None -> false
        in
        (addr, (blk, inside)))
  in
  let inside = List.filter_map marked ~f:(fun (b, i) -> Option.some_if i b) in
  match inside with
  | [] -> Or_error.error_string "no blocks of the sub are in the range"
  | entry :: _ ->
      let tids = Tid.Set.of_list (List.map inside ~f:Term.tid) in
      let entered =
        List.filter_map marked ~f:(fun (b, i) -> Option.some_if (not i) b)
        |> List.concat_map ~f:targets
        |> List.filter ~f:(fun tid ->
            Set.mem tids tid && not (Tid.equal tid (Term.tid entry)))
      in
      if not (List.is_empty entered) then
        Or_error.errorf "the code outside of the range jumps to %s inside"
          (Tid.to_string (List.hd_exn entered))
      else
        let after =
          List.drop_while blks ~f:(fun b ->
              not (Tid.equal (Term.tid b) (Term.tid (List.last_exn inside))))
          |> List.tl |> Option.bind ~f:List.hd
        in
        create ~last:(Option.map after ~f:(fun b -> Direct (Term.tid b))) inside

let update sub t =
  let placed = ref false in
  let blks =
    Term.enum blk_t sub |> Seq.to_list
    |> List.concat_map ~f:(fun b ->
        if not (Set.mem t.replaces (Term.tid b)) then [ b ]
        else if !placed then []
        else (
          placed := true;
          t.blks))
  in
  let updated =
    Sub.create ~tid:(Term.tid sub) ~name:(Sub.name sub)
      ~args:(Term.enum arg_t sub |> Seq.to_list)
      ~blks ()
  in
  Term.with_attrs updated (Term.attrs sub)
