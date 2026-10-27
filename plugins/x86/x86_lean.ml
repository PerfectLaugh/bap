open Core
open Bap.Std
open Result.Monad_infix
module Bil_lean = Bap_bil_plugin.Bil_lean

type state = {
  env : Bil.exp Var.Map.t;
  vars : Bil.var String.Map.t;
  writes : String.Set.t;
}

let flags = [ "CF"; "OF"; "AF"; "SF"; "ZF"; "PF" ]
let architectural_writes = "RAX" :: flags

let initial =
  { env = Var.Map.empty; vars = String.Map.empty; writes = String.Set.empty }

let register_var vars var = Map.set vars ~key:(Var.name var) ~data:var

let register_exp vars exp =
  Set.fold (Exp.free_vars exp) ~init:vars ~f:register_var

let substitute env exp =
  Map.fold env ~init:exp ~f:(fun ~key ~data exp ->
      Exp.substitute (Bil.Var key) data exp)

let rec execute state = function
  | [] -> Ok state
  | Bil.Move (var, exp) :: rest ->
      let evaluated = substitute state.env exp in
      let state =
        {
          env = Map.set state.env ~key:var ~data:evaluated;
          vars = register_exp (register_var state.vars var) exp;
          writes =
            (if Var.is_physical var then Set.add state.writes (Var.name var)
             else state.writes);
        }
      in
      execute state rest
  | _ -> Error "only straight-line BIL Move statements can be validated"

let output state name =
  match Map.find state.vars name with
  | None -> Error (sprintf "the BIL does not define %s" name)
  | Some var -> (
      match Map.find state.env var with
      | None -> Error (sprintf "the BIL does not define %s" name)
      | Some exp ->
          let free = Exp.free_vars exp in
          if Set.exists free ~f:Var.is_virtual then
            Error (sprintf "%s depends on an uninitialized temporary" name)
          else Ok exp)

let input state name =
  match Map.find state.vars name with
  | None -> Error (sprintf "the BIL does not contain input %s" name)
  | Some var -> Ok (Bil.Var var)

let check_writes state =
  let expected = String.Set.of_list architectural_writes in
  if Set.equal expected state.writes then Ok ()
  else
    Error
      (sprintf "unexpected architectural writes: expected %s, got %s"
         (String.concat ~sep:", " (Set.to_list expected))
         (String.concat ~sep:", " (Set.to_list state.writes)))

let check_application ~checker ~function_name ~projection ~unfold actual
    arguments =
  Bil_lean.validate_application_with ~checker ~imports:[ "Lean"; "X86Proofs" ]
    ~function_name ~projection ~unfold actual arguments

let validate_add_with ~checker ~width bil =
  if not (List.mem [ 8; 16; 32; 64 ] width ~equal:Int.equal) then
    Error (sprintf "unsupported ADD width %d" width)
  else
    execute initial bil >>= fun state ->
    check_writes state >>= fun () ->
    input state "RAX" >>= fun rax ->
    input state "RBX" >>= fun rbx ->
    let low value = Bil.Extract (width - 1, 0, value) in
    let arguments = if width = 64 then [ rax; rbx ] else [ low rax; low rbx ] in
    let unfold = [ "X86.add"; "X86.msb"; "X86.parity" ] in
    let result_function, result_projection, result_arguments, result_unfold =
      match width with
      | 8 -> ("X86.add8Result", None, [ rax; rbx ], "X86.add8Result")
      | 16 -> ("X86.add16Result", None, [ rax; rbx ], "X86.add16Result")
      | 32 -> ("X86.add32Result", None, [ rax; rbx ], "X86.add32Result")
      | 64 -> ("X86.add", Some "result", arguments, "X86.add")
      | _ -> assert false
    in
    output state "RAX" >>= fun actual ->
    check_application ~checker ~function_name:result_function
      ~projection:result_projection ~unfold:(result_unfold :: unfold) actual
      result_arguments
    >>= fun () ->
    List.fold flags ~init:(Ok ()) ~f:(fun result flag ->
        result >>= fun () ->
        output state flag >>= fun actual ->
        check_application ~checker ~function_name:"X86.add"
          ~projection:(Some (String.lowercase flag))
          ~unfold actual arguments
        |> Result.map_error ~f:(fun message -> sprintf "%s: %s" flag message))

let validate_add = validate_add_with ~checker:Bil_lean.check
