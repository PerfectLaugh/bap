open Core
open Regular.Std
open Graphlib.Std
open Bap_ir
module G = Graphlib.Make (Tid) (Tid)

let start = Tid.for_name ~package:"bap" "start-pseudo-node"
let exit = Tid.for_name ~package:"bap" "exit-pseudo-node"
let unwrap = function Ok value -> value | Error message -> failwith message

external edges_native :
  Bap_ir_wire.wire_sub -> bool -> (Bap_ir_wire.wire_edge list, string) result =
  "bap_cfg_rs_edges"

let build connected sub =
  let env, input = Bap_ir_wire.encode_sub sub in
  let edges =
    edges_native input connected |> unwrap
    |> Bap_ir_wire.decode_edges env ~start ~exit
  in
  let nodes =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Seq.to_list
    |> fun nodes -> if connected then start :: exit :: nodes else nodes
  in
  List.fold nodes ~init:G.empty ~f:(fun graph node -> G.Node.insert node graph)
  |> fun graph ->
  List.fold edges ~init:graph ~f:(fun graph (source, target, label) ->
      G.Edge.insert (G.Edge.create source target label) graph)

let of_sub = build false
let create = build true

include G
