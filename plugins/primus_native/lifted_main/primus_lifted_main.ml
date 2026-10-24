(* the executors of the lifted engine, see Primus_native_options *)

let () =
  Bap_primus_native_plugin.Primus_native_options.declare ~engine:`Lifted
    ~name:"lifted" ~runs_in:"the lifted engine"
    ~doc:
      "runs the binary programs in Primus with the lifted engine, which runs \
       the semantics of the instructions, that BAP lifts, see Bap_lifted"
