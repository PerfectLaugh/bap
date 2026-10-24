(* the executors of Unicorn, see Primus_native_options *)

let () =
  Bap_primus_native_plugin.Primus_native_options.declare ~engine:`Unicorn
    ~name:"unicorn" ~runs_in:"Unicorn"
    ~doc:"runs the binary programs in Primus with Unicorn"
