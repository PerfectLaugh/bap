#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  List.iter
    [ (`Unicorn, "unicorn"); (`Lifted, "lifted") ]
    ~f:(fun (engine, name) ->
      let emu = Emu.create ~engine (Bap_script.project file) in
      let first = ref 0 and second = ref 0 and disjoint = ref 0 in
      let subscription callback : Emu.write_subscription =
        {
          first = Some 0x40200bL;
          last = Some 0x40200bL;
          primus = true;
          callback;
        }
      in
      Emu.on_writes emu
        [
          subscription (fun _ _ _ _ -> incr first);
          subscription (fun _ _ _ _ -> incr second);
          {
            first = Some 0x1L;
            last = Some 0x1L;
            primus = false;
            callback = (fun _ _ _ _ -> incr disjoint);
          };
        ];
      ignore (Emu.run emu : Emu.status);
      let profile = Emu.write_profile emu in
      printf
        "%s: first=%d second=%d disjoint=%d dispatch=%d callbacks=%d time=%b\n"
        name !first !second !disjoint profile.dispatches profile.callbacks
        Float.(profile.seconds >= 0.);
      let emu = Emu.create ~engine (Bap_script.project file) in
      Emu.scoped emu (fun () ->
          Emu.on_writes emu
            [
              {
                first = None;
                last = None;
                primus = false;
                callback = (fun _ _ _ _ -> incr first);
              };
            ]);
      ignore (Emu.run emu : Emu.status);
      let profile = Emu.write_profile emu in
      printf "%s: after scope callbacks=%d\n" name profile.callbacks)
