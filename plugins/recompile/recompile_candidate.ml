open Core
open Bap.Std

let direct_destinations jmp =
  let direct = function Some (Direct tid) -> [ tid ] | _ -> [] in
  match Jmp.kind jmp with
  | Goto label | Ret label -> direct (Some label)
  | Call call -> direct (Call.return call)
  | Int (_, tid) -> [ tid ]

let external_boundary sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun boundary blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:boundary ~f:(fun boundary jmp ->
          List.fold (direct_destinations jmp) ~init:boundary
            ~f:(fun boundary tid ->
              if Set.mem blocks tid then boundary else Set.add boundary tid)))

let validate_destinations ~boundary sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Ok ()) ~f:(fun result blk ->
      Result.bind result ~f:(fun () ->
          Term.enum jmp_t blk
          |> Seq.fold ~init:(Ok ()) ~f:(fun result jmp ->
              Result.bind result ~f:(fun () ->
                  List.fold (direct_destinations jmp) ~init:(Ok ())
                    ~f:(fun result tid ->
                      Result.bind result ~f:(fun () ->
                          if Set.mem blocks tid || Set.mem boundary tid then
                            Ok ()
                          else
                            Or_error.errorf
                              "the sub %s has the jump %s in the block %s to \
                               the missing destination %s"
                              (Sub.name sub)
                              (Tid.to_string (Term.tid jmp))
                              (Tid.to_string (Term.tid blk))
                              (Tid.to_string tid)))))))

let opaque_exits sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  let internal tid = Set.mem blocks tid in
  let continuation = function
    | None -> "none"
    | Some (Direct tid) when internal tid -> "internal"
    | Some (Direct tid) -> "external:" ^ Tid.to_string tid
    | Some (Indirect _) -> "indirect"
  in
  let signature jmp =
    let kind =
      match Jmp.kind jmp with
      | Goto (Direct tid) when internal tid -> None
      | Goto (Direct tid) -> Some ("goto:" ^ Tid.to_string tid)
      | Goto (Indirect _) -> Some "goto:indirect"
      | Ret (Direct tid) when internal tid -> None
      | Ret (Direct tid) -> Some ("return:" ^ Tid.to_string tid)
      | Ret (Indirect _) -> Some "return:indirect"
      | Call call ->
          let target =
            match Call.target call with
            | Direct tid -> Tid.to_string tid
            | Indirect _ -> "indirect"
          in
          Some ("call:" ^ target ^ ":" ^ continuation (Call.return call))
      | Int (number, _) -> Some ("interrupt:" ^ Int.to_string number)
    in
    Option.map kind ~f:(fun kind ->
        kind ^ ":" ^ Sexp.to_string_mach (Dict.sexp_of_t (Term.attrs jmp)))
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:String.Map.empty ~f:(fun exits blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:exits ~f:(fun exits jmp ->
          match signature jmp with
          | None -> exits
          | Some signature ->
              Map.update exits signature ~f:(function
                | None -> 1
                | Some count -> count + 1)))

let validate_opaque_exits original optimized =
  let before = opaque_exits original and after = opaque_exits optimized in
  if Map.equal Int.equal before after then Ok ()
  else
    let total =
      Map.fold ~init:0 ~f:(fun ~key:_ ~data:count sum -> sum + count)
    in
    Or_error.errorf "the sub %s changed opaque exits (%d before, %d after)"
      (Sub.name original) (total before) (total after)

let validate_candidate original optimized =
  Result.bind
    (validate_destinations ~boundary:(external_boundary original) optimized)
    ~f:(fun () -> validate_opaque_exits original optimized)
