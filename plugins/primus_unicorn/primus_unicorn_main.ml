(* the executors of Unicorn, see Primus_unicorn_options *)

let () =
  Bap_primus_unicorn_plugin.Primus_unicorn_options.declare ~engine:`Unicorn
    ~name:"unicorn" ~runs_in:"Unicorn"
    ~doc:"runs the binary programs in Primus with Unicorn"
