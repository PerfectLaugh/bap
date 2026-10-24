#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

(* The observer of the stores, that needs the stores to the code only,
   see Primus.Track.cover_code, e.g., the dynamic code of Primus, sees
   them in both engines, which hook the writes to the code only, and
   keep them, until they stop, see smc-text.c, whose f and g patch their
   instructions in loops: the bytes of the code, that the program
   wrote, with their values, as they are at the end, in both engines. *)
let stores = Hashtbl.create (module Int64)

(* the stores to the page of f and g, as the interpreter posts its own
   stores, e.g., of the stubs to the stack, to the observer too *)
let code a = Int64.(a >= 0x402000L && a < 0x403000L)

module Counter (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Track = Primus.Track.Make (Machine)

  let init () =
    Track.cover_code Primus.Interpreter.stored >>= fun () ->
    Machine.Observation.observe Primus.Interpreter.stored (fun (a, v) ->
        let int64 x =
          Bitvec.to_int64 (Word.to_bitvec (Primus.Value.to_word x))
        in
        if code (int64 a) then Hashtbl.set stores ~key:(int64 a) ~data:(int64 v);
        Machine.return ())
end

let () =
  Primus.Components.register_generic ~package:"test" "code-stores"
    (module Counter)
    ~desc:"counts the stores to the code"

let () =
  match Bap_script.args () with
  | [ smc ] ->
      List.iter
        [ (`Unicorn, "unicorn"); (`Lifted, "lifted") ]
        ~f:(fun (engine, name) ->
          Hashtbl.clear stores;
          let emu =
            Emu.create ~engine ~components:[ "test:code-stores" ]
              (Bap_script.project smc)
          in
          ignore (Emu.run emu);
          printf "%s: code stores:%s\n" name
            (Hashtbl.to_alist stores
            |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
            |> List.map ~f:(fun (a, v) -> sprintf " %Lx=%02Lx" a v)
            |> String.concat))
  | _ -> failwith "expected SMC-TEXT"
