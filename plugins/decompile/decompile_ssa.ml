open Core
open Bap.Std
open Bap_core_theory

type t = {
  sub : sub term;
  frame : Bap_recompile.Frame.t option;
  frame_error : string option;
}

let is_block sub tid = Option.is_some (Term.find blk_t sub tid)

let successors sub blk =
  Term.enum jmp_t blk |> Seq.to_list
  |> List.concat_map ~f:(fun jmp ->
      let local = function
        | Direct tid when is_block sub tid -> [ tid ]
        | _ -> []
      in
      match Jmp.kind jmp with
      | Goto label | Ret label -> local label
      | Call call -> (
          match Call.return call with Some label -> local label | None -> [])
      | Int (_, tid) when is_block sub tid -> [ tid ]
      | Int _ -> [])
  |> List.dedup_and_sort ~compare:Tid.compare

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

let live_out sub live blk =
  successors sub blk
  |> List.fold ~init:Var.Set.empty ~f:(fun out succ ->
      let incoming =
        Map.find live succ |> Option.value ~default:Var.Set.empty
      in
      match Term.find blk_t sub succ with
      | None -> Set.union out incoming
      | Some succ_blk ->
          let phis = Term.enum phi_t succ_blk |> Seq.to_list in
          let without_lhs =
            List.fold phis ~init:incoming ~f:(fun vars phi ->
                Set.remove vars (Phi.lhs phi))
          in
          List.fold phis ~init:(Set.union out without_lhs) ~f:(fun vars phi ->
              match Phi.select phi (Term.tid blk) with
              | None -> vars
              | Some exp -> Set.union vars (Exp.free_vars exp)))

let uses_of_block blk =
  Term.enum jmp_t blk
  |> Seq.fold ~init:Var.Set.empty ~f:(fun vars jmp ->
      Set.union vars (jmp_vars jmp))

let transfer sub live blk =
  let out = Set.union (live_out sub live blk) (uses_of_block blk) in
  Term.enum def_t ~rev:true blk
  |> Seq.fold ~init:out ~f:(fun live def ->
      Set.union (Set.remove live (Def.lhs def)) (Def.free_vars def))

let liveness sub =
  let blocks = Term.enum blk_t sub |> Seq.to_list in
  let rec iterate live =
    let live' =
      List.fold blocks ~init:live ~f:(fun state blk ->
          Map.set state ~key:(Term.tid blk) ~data:(transfer sub live blk))
    in
    if Map.equal Var.Set.equal live live' then live else iterate live'
  in
  iterate Tid.Map.empty

let live_in sub blk = transfer sub (liveness sub) blk

let flag_names target =
  let roles =
    Theory.Role.Register.
      [ status; zero_flag; carry_flag; sign_flag; overflow_flag; parity_flag ]
  in
  List.fold roles ~init:String.Set.empty ~f:(fun names role ->
      Theory.Target.regs target ~roles:[ role ]
      |> Set.fold ~init:names ~f:(fun names register ->
          Set.add names (Theory.Var.name register)))
  |> fun names ->
  List.fold
    [ "CF"; "PF"; "AF"; "ZF"; "SF"; "OF"; "NF"; "VF" ]
    ~init:names ~f:Set.add

let is_flag ~target var = Set.mem (flag_names target) (Var.name var)
let removable ~target var = Var.is_virtual var || is_flag ~target var

let remove_dead ~target sub live =
  Term.map blk_t sub ~f:(fun blk ->
      let out = Set.union (live_out sub live blk) (uses_of_block blk) in
      let defs = Term.enum def_t ~rev:true blk |> Seq.to_list in
      let keep, _ =
        List.fold defs ~init:([], out) ~f:(fun (keep, needed) def ->
            let lhs = Def.lhs def in
            if Set.mem needed lhs || not (removable ~target lhs) then
              ( def :: keep,
                Set.union (Set.remove needed lhs) (Def.free_vars def) )
            else (keep, needed))
      in
      let blk = Term.filter def_t blk ~f:(fun _ -> false) in
      List.fold keep ~init:blk ~f:(Term.append def_t))

let rec pure = function
  | Bil.Var _ | Bil.Int _ -> true
  | Bil.BinOp (_, x, y) | Bil.Concat (x, y) -> pure x && pure y
  | Bil.UnOp (_, x) | Bil.Cast (_, _, x) | Bil.Extract (_, _, x) -> pure x
  | Bil.Ite (c, x, y) -> pure c && pure x && pure y
  | Bil.Let (_, value, body) -> pure value && pure body
  | Bil.Load (mem, addr, _, _) -> pure mem && pure addr
  | Bil.Store _ | Bil.Unknown _ -> false

let rec substitute exp var value =
  match exp with
  | Bil.Var v when Var.equal v var -> value
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> exp
  | Bil.Load (mem, addr, endian, size) ->
      Bil.Load
        (substitute mem var value, substitute addr var value, endian, size)
  | Bil.Store (mem, addr, value', endian, size) ->
      Bil.Store
        ( substitute mem var value,
          substitute addr var value,
          substitute value' var value,
          endian,
          size )
  | Bil.BinOp (op, x, y) ->
      Bil.BinOp (op, substitute x var value, substitute y var value)
  | Bil.UnOp (op, x) -> Bil.UnOp (op, substitute x var value)
  | Bil.Cast (cast, bits, x) -> Bil.Cast (cast, bits, substitute x var value)
  | Bil.Let (v, x, body) when Var.equal v var ->
      Bil.Let (v, substitute x var value, body)
  | Bil.Let (v, x, body) ->
      Bil.Let (v, substitute x var value, substitute body var value)
  | Bil.Ite (c, x, y) ->
      Bil.Ite
        (substitute c var value, substitute x var value, substitute y var value)
  | Bil.Extract (hi, lo, x) -> Bil.Extract (hi, lo, substitute x var value)
  | Bil.Concat (x, y) ->
      Bil.Concat (substitute x var value, substitute y var value)

let rec expression_size = function
  | Bil.Var _ | Bil.Int _ | Bil.Unknown _ -> 1
  | Bil.UnOp (_, x) | Bil.Cast (_, _, x) | Bil.Extract (_, _, x) ->
      1 + expression_size x
  | Bil.BinOp (_, x, y) | Bil.Concat (x, y) ->
      1 + expression_size x + expression_size y
  | Bil.Load (mem, addr, _, _) -> 1 + expression_size mem + expression_size addr
  | Bil.Store (mem, addr, value, _, _) ->
      1 + expression_size mem + expression_size addr + expression_size value
  | Bil.Let (_, value, body) -> 1 + expression_size value + expression_size body
  | Bil.Ite (c, x, y) ->
      1 + expression_size c + expression_size x + expression_size y

let propagate_block ~target ?(physical = false) ?(multi = false) blk =
  let rec loop blk =
    let defs = Term.enum def_t blk |> Seq.to_list in
    let jmps = Term.enum jmp_t blk |> Seq.to_list in
    let rec find index =
      match List.nth defs index with
      | None -> None
      | Some def ->
          let lhs = Def.lhs def in
          let rhs = Def.rhs def in
          if (not (physical || removable ~target lhs)) || not (pure rhs) then
            find (index + 1)
          else
            let later = List.drop defs (index + 1) in
            let before_redefinition, redefinitions =
              List.split_while later ~f:(fun d ->
                  not (Var.equal (Var.base (Def.lhs d)) (Var.base lhs)))
            in
            let redefined = not (List.is_empty redefinitions) in
            let later = before_redefinition @ List.take redefinitions 1 in
            let users =
              List.filter_map later ~f:(fun d ->
                  if Set.mem (Def.free_vars d) lhs then Some (`Def d) else None)
              @
              if redefined then []
              else
                List.filter_map jmps ~f:(fun j ->
                    if Set.mem (jmp_vars j) lhs then Some (`Jmp j) else None)
            in
            let dependencies = Exp.free_vars rhs in
            let clobbered =
              List.fold_until later ~init:false
                ~f:(fun clobbered d ->
                  if Term.same d (List.hd_exn defs) then Continue clobbered
                  else if
                    (not multi)
                    && List.exists users ~f:(function
                      | `Def user -> Term.same d user
                      | `Jmp _ -> false)
                  then Stop clobbered
                  else Continue (clobbered || Set.mem dependencies (Def.lhs d)))
                ~finish:Fn.id
            in
            if
              clobbered || List.is_empty users
              || ((not multi) && List.length users <> 1)
              || multi
                 && (List.length users > 4
                    || expression_size rhs > 8
                       &&
                       match rhs with
                       | Bil.UnOp (NOT, _) | Bil.BinOp ((PLUS | MINUS), _, _) ->
                           false
                       | _ -> true)
            then find (index + 1)
            else Some (def, users)
    in
    match find 0 with
    | None -> blk
    | Some (def, users) ->
        let lhs = Def.lhs def and rhs = Def.rhs def in
        let blk = Term.remove def_t blk (Term.tid def) in
        let blk =
          List.fold users ~init:blk ~f:(fun blk -> function
            | `Def user ->
                Term.update def_t blk (Def.substitute user (Bil.var lhs) rhs)
            | `Jmp user ->
                Term.update jmp_t blk (Jmp.substitute user (Bil.var lhs) rhs))
        in
        loop blk
  in
  loop blk

let copies sub src dst =
  match Term.find blk_t sub dst with
  | None -> []
  | Some blk ->
      Term.enum phi_t blk |> Seq.to_list
      |> List.filter_map ~f:(fun phi ->
          Option.map (Phi.select phi src) ~f:(fun exp -> (Phi.lhs phi, exp)))

let normalize ~target sub =
  let sub = Decompile_simplify.sub sub |> Decompile_range.simplify_sub in
  let live = liveness sub in
  let sub = remove_dead ~target sub live in
  let sub = Term.map blk_t sub ~f:(propagate_block ~target) in
  let live = liveness sub in
  let sub = remove_dead ~target sub live in
  let frame, frame_error =
    match Bap_recompile.Frame.analyze ~target sub with
    | Ok frame -> (Some frame, None)
    | Error error -> (None, Some error)
  in
  let sub =
    Term.map blk_t sub ~f:(propagate_block ~target ~physical:true ~multi:true)
  in
  let sub = Decompile_simplify.sub sub in
  let live = liveness sub in
  let sub = remove_dead ~target sub live in
  let sub =
    Term.map blk_t sub ~f:(propagate_block ~target ~physical:true ~multi:true)
  in
  let sub = Decompile_simplify.sub sub in
  let sub = Term.map blk_t sub ~f:(propagate_block ~target) in
  let sub = Decompile_simplify.sub sub in
  let live = liveness sub in
  let sub = remove_dead ~target sub live in
  { sub; frame; frame_error }
