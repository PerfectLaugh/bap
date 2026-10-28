external fold_consts_native :
  Bap_bil_wire.wire_stmt list -> (Bap_bil_wire.wire_stmt list, string) result =
  "bap_bir_rs_fold_consts"

external propagate_consts_native :
  Bap_bil_wire.wire_stmt list -> (Bap_bil_wire.wire_stmt list, string) result =
  "bap_bir_rs_propagate_consts"

external prune_dead_virtuals_native :
  Bap_bil_wire.wire_stmt list -> (Bap_bil_wire.wire_stmt list, string) result =
  "bap_bir_rs_prune_dead_virtuals"

let unwrap = function Ok value -> value | Error message -> failwith message

let apply operation bil =
  let env, input = Bap_bil_wire.encode bil in
  operation input |> unwrap |> Bap_bil_wire.decode env

let fold_consts = apply fold_consts_native
let propagate_consts = apply propagate_consts_native
let prune_dead_virtuals = apply prune_dead_virtuals_native
