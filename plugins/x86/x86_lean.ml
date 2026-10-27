open Core
open Bap.Std
open Result.Monad_infix
module Bil_lean = Bap_bil_plugin.Bil_lean
module Lifter = Bap_bil_plugin.Bil_lifter_proof

type operation = Add | Sub | And | Or | Xor

let arithmetic_flags = [ "CF"; "OF"; "AF"; "SF"; "ZF"; "PF" ]
let logic_flags = [ "CF"; "OF"; "SF"; "ZF"; "PF" ]

let operation_model = function
  | Add -> "X86.add"
  | Sub -> "X86.sub"
  | And -> "X86.logicalAnd"
  | Or -> "X86.logicalOr"
  | Xor -> "X86.logicalXor"

let operation_name = function
  | Add -> "ADD"
  | Sub -> "SUB"
  | And -> "AND"
  | Or -> "OR"
  | Xor -> "XOR"

let operation_flags = function
  | Add | Sub -> arithmetic_flags
  | And | Or | Xor -> logic_flags

let execute = Lifter.execute
let output = Lifter.output
let input = Lifter.input

let check_writes ~operation ~destination state =
  Lifter.check_writes ~expected:(destination :: operation_flags operation) state

let check_application ~checker ~function_name ~projection ~unfold actual
    arguments =
  Bil_lean.validate_application_with ~checker ~imports:[ "Lean"; "X86Proofs" ]
    ~function_name ~projection ~unfold actual arguments

let validate_reg_reg_with ~checker ~operation ~width ~destination ~left ~right
    bil =
  if not (List.mem [ 8; 16; 32; 64 ] width ~equal:Int.equal) then
    Error (sprintf "unsupported %s width %d" (operation_name operation) width)
  else
    execute bil >>= fun state ->
    check_writes ~operation ~destination state >>= fun () ->
    input state left >>= fun left ->
    input state right >>= fun right ->
    let low value = Bil.Extract (width - 1, 0, value) in
    let arguments =
      if width = 64 then [ left; right ] else [ low left; low right ]
    in
    let model = operation_model operation in
    let unfold =
      (match operation with
        | Add | Sub -> []
        | And | Or | Xor -> [ "X86.logic" ])
      @ [ model; "X86.msb"; "X86.parity" ]
    in
    let result_function, result_projection, result_arguments, result_unfold =
      if width = 64 then (model, Some "result", arguments, unfold)
      else
        let wrapper = sprintf "X86.result%d" width in
        ( sprintf "%s (fun x y => (%s x y).result)" wrapper model,
          None,
          [ left; right ],
          wrapper :: unfold )
    in
    output state destination >>= fun actual ->
    check_application ~checker ~function_name:result_function
      ~projection:result_projection ~unfold:result_unfold actual
      result_arguments
    >>= fun () ->
    List.fold (operation_flags operation) ~init:(Ok ()) ~f:(fun result flag ->
        result >>= fun () ->
        output state flag >>= fun actual ->
        check_application ~checker ~function_name:model
          ~projection:(Some (String.lowercase flag))
          ~unfold actual arguments
        |> Result.map_error ~f:(fun message -> sprintf "%s: %s" flag message))

let validate_reg_reg = validate_reg_reg_with ~checker:Bil_lean.check

let validate_add_with ~checker ~width bil =
  validate_reg_reg_with ~checker ~operation:Add ~width ~destination:"RAX"
    ~left:"RAX" ~right:"RBX" bil

let validate_add = validate_add_with ~checker:Bil_lean.check
