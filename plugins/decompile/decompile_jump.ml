open Core
open Bap.Std

let rec strip = function Bil.Cast (_, _, exp) -> strip exp | exp -> exp

let int_value exp =
  match strip exp with
  | Bil.Int value ->
      Some (Word.to_int64_exn (Word.signed value) |> Int64.to_int_exn)
  | _ -> None

let rec address exp =
  match strip exp with
  | Bil.Int value -> Some (value, 0L)
  | Bil.BinOp (PLUS, left, right) -> (
      match (address left, address right) with
      | Some (base, left_offset), Some (_, right_offset) ->
          Some (base, Int64.(left_offset + right_offset))
      | _ -> None)
  | Bil.BinOp (MINUS, left, right) -> (
      match (address left, address right) with
      | Some (base, left_offset), Some (_, right_offset) ->
          Some (base, Int64.(left_offset - right_offset))
      | _ -> None)
  | _ -> None

let scale_of exp =
  match strip exp with
  | Bil.BinOp (TIMES, left, right) -> (
      match int_value left with
      | Some _ as value -> value
      | None -> int_value right)
  | Bil.BinOp (LSHIFT, _, value) ->
      Option.map (int_value value) ~f:(fun bits -> 1 lsl bits)
  | _ -> Some 1

let unscale exp =
  match strip exp with
  | Bil.BinOp (TIMES, left, right) -> (
      match int_value left with Some _ -> right | None -> left)
  | Bil.BinOp (LSHIFT, value, _) -> value
  | exp -> exp

let indexed exp =
  let rec split exp =
    match strip exp with
    | Bil.BinOp (PLUS, left, right) -> (
        match (address left, scale_of right, address right, scale_of left) with
        | Some base, Some scale, _, _ -> Some (base, unscale right, scale)
        | _, _, Some base, Some scale -> Some (base, unscale left, scale)
        | _ -> None)
    | exp -> (
        match address exp with Some base -> Some (base, exp, 1) | None -> None)
  in
  split exp

let bound sub index =
  Term.enum blk_t sub
  |> Seq.fold ~init:None ~f:(fun best blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:best ~f:(fun best jmp ->
          match Jmp.cond jmp with
          | Bil.BinOp (((LT | LE) as op), left, right) -> (
              let variable = strip left in
              if not (Exp.equal variable (strip index)) then best
              else
                match int_value right with
                | Some value ->
                    let count =
                      match op with LT -> value | LE -> value + 1 | _ -> value
                    in
                    if count > 0 then
                      match best with
                      | Some old when old <= count -> best
                      | _ -> Some count
                    else best
                | None -> best)
          | _ -> best))

let find_memory memory addr =
  Memmap.to_sequence memory
  |> Seq.find_map ~f:(fun (mem, _) ->
      if Memory.contains mem addr then Some mem else None)

let target_of sub table_base relative value =
  let candidates =
    if relative then [ Word.( + ) table_base value; value ] else [ value ]
  in
  List.find_map candidates ~f:(fun addr ->
      Term.enum sub_t sub
      |> Seq.find ~f:(fun candidate ->
          match Term.get_attr candidate Bap.Std.address with
          | Some entry -> Word.equal entry addr
          | None -> false)
      |> Option.map ~f:Term.tid)

let entries memory prog table_base index index_bits stride size count relative =
  let rec loop acc i =
    if i >= count || List.length acc >= 256 then Some (List.rev acc)
    else
      let addr = Addr.nsucc table_base (i * stride) in
      match find_memory memory addr with
      | None -> None
      | Some mem -> (
          match Memory.get ~scale:size ~addr mem with
          | Error _ -> None
          | Ok value -> (
              match target_of prog table_base relative value with
              | Some target ->
                  let condition =
                    Bil.BinOp
                      (EQ, index, Bil.Int (Word.of_int ~width:index_bits i))
                  in
                  loop ((condition, target) :: acc) (i + 1)
              | None -> None))
  in
  loop [] 0

let recover_jump memory prog sub jmp =
  match Jmp.kind jmp with
  | Goto (Indirect (Bil.Load (_, address_expr, _, size))) -> (
      match indexed address_expr with
      | None -> None
      | Some ((table_base, offset), index, stride) ->
          let table_base =
            Word.( + ) table_base
              (Word.of_int64 ~width:(Word.bitwidth table_base) offset)
          in
          let index_bits =
            match Type.infer index with
            | Ok (Type.Imm bits) -> bits
            | _ -> Size.in_bits size
          in
          let count =
            match bound sub index with
            | Some count -> Some count
            | None ->
                Option.map (find_memory memory table_base) ~f:(fun mem ->
                    Int.min 256 (Memory.length mem / stride))
          in
          Option.bind count ~f:(fun count ->
              if count < 2 then None
              else
                match
                  entries memory prog table_base index index_bits stride size
                    count false
                with
                | Some _ as entries -> entries
                | None ->
                    entries memory prog table_base index index_bits stride size
                      count true))
  | _ -> None

let recover_sub memory prog sub =
  Term.map blk_t sub ~f:(fun blk ->
      let jmps =
        Term.enum jmp_t blk |> Seq.to_list
        |> List.concat_map ~f:(fun jmp ->
            match recover_jump memory prog sub jmp with
            | None -> [ jmp ]
            | Some entries ->
                List.map entries ~f:(fun (condition, target) ->
                    Jmp.create_goto ~cond:condition (Direct target)))
      in
      let blk = Term.filter jmp_t blk ~f:(fun _ -> false) in
      List.fold jmps ~init:blk ~f:(Term.append jmp_t))

let recover ~memory prog = Term.map sub_t prog ~f:(recover_sub memory prog)
