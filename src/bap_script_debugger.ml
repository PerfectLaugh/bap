open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
module Stops = Primus.Interpreter.Stops

module type Handler = functor (Machine : Primus.Machine.S) -> sig
  val stopped : addr -> unit Machine.t
end

let handlers : (module Handler) list ref = ref []
let points : string list ref = ref []
let resolved = ref false
let break point = points := !points @ [ point ]
let step on = Stops.set_stepping on
let on_stop handler = handlers := !handlers @ [ handler ]

module Debugger (Machine : Primus.Machine.S) = struct
  open Machine.Syntax

  (* the address, or the address of the subroutine with the name *)
  let resolve point =
    Machine.gets Project.target >>| Theory.Target.bits >>= fun width ->
    match Int64.of_string point with
    | x -> Machine.return (Some (Addr.of_int64 ~width x))
    | exception _ ->
        Machine.gets Project.program >>| fun prog ->
        Term.enum sub_t prog
        |> Seq.find ~f:(fun sub -> String.equal (Sub.name sub) point)
        |> Option.bind ~f:(fun sub -> Term.get_attr sub address)

  (* the breakpoints are of the program, so the first machine resolves
     them *)
  let add_breakpoints () =
    if !resolved then Machine.return ()
    else begin
      resolved := true;
      Machine.List.iter !points ~f:(fun point ->
          resolve point >>| function
          | Some addr -> Stops.add addr
          | None ->
              eprintf "bap script: the breakpoint %s is not found\n%!" point)
    end

  (* the handlers are applied once, as the functors make their modules *)
  let stops =
    List.map !handlers ~f:(fun handler ->
        let module Handler = (val handler : Handler) in
        let module Handler = Handler (Machine) in
        Handler.stopped)

  let stopped addr =
    if Stops.stepping () || Stops.mem addr then
      Machine.List.iter stops ~f:(fun stopped -> stopped addr)
    else Machine.return ()

  let init () =
    Machine.sequence
      [ add_breakpoints (); Primus.Interpreter.pc_change >>> stopped ]
end

let () =
  Primus.Components.register_generic ~package:"script" "debugger"
    (module Debugger)
    ~desc:"Calls the handlers of the script at the stops.";
  Bap_script.require_options [ "--run-components=script:debugger" ]
