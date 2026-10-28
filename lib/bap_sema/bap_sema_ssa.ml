open Core
open Regular.Std
open Bap_types.Std
open Bap_ir
open Bap_core_theory
open KB.Syntax

let ssa_form =
  Value.Tag.register ~uuid:"9abecd51-c6c3-4363-b9c6-51f923d965fe"
    ~name:"ssa_form"
    (module Unit)

let is_transformed sub = Term.has_attr sub ssa_form
let unwrap = function Ok value -> value | Error message -> failwith message

external ssa_native :
  Bap_ir_wire.wire_sub -> (Bap_ir_wire.wire_sub, string) result = "bap_cfg_rs_ssa"

let transform sub =
  let env, input = Bap_ir_wire.encode_sub sub in
  let transformed =
    ssa_native input |> unwrap
    |> Bap_ir_wire.decode_ssa env ~start:Bap_tid_graph.start ~exit:Bap_tid_graph.exit sub in
  Term.set_attr transformed ssa_form ()

module KB = struct
  let sub sub = if is_transformed sub then !!sub else !!(transform sub)
end

let ssa_result = Toplevel.var "ssa"

let sub sub =
  Toplevel.put ssa_result @@ KB.sub sub;
  Toplevel.get ssa_result
