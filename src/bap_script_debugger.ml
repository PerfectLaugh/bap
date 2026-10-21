open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std

module type Handler = functor (Machine : Primus.Machine.S) -> sig
  val stopped : addr -> unit Machine.t
end

let handlers : (module Handler) list ref = ref []
let points : string list ref = ref []
let break point = points := !points @ [ point ]
let on_stop handler = handlers := !handlers @ [ handler ]

(* the breakpoints are of the program, so the first machine of a system
   resolves them *)
let resolved =
  Primus.Machine.State.declare ~uuid:"3f9b6d24-71c8-4e05-b2a7-d84e1c6f5a93"
    ~name:"script-debugger-resolved" (fun _ -> false)

module Debugger (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Stops = Primus.Interpreter.Stops.Make (Machine)

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

  let add_breakpoints () =
    Machine.Global.get resolved >>= fun done_ ->
    if done_ then Machine.return ()
    else
      Machine.Global.put resolved true >>= fun () ->
      Machine.List.iter !points ~f:(fun point ->
          resolve point >>= function
          | Some addr -> Stops.add addr
          | None ->
              eprintf "bap script: the breakpoint %s is not found\n%!" point;
              Machine.return ())

  (* the handlers are applied once, as the functors make their modules *)
  let stops =
    List.map !handlers ~f:(fun handler ->
        let module Handler = (val handler : Handler) in
        let module Handler = Handler (Machine) in
        Handler.stopped)

  let stopped addr = Machine.List.iter stops ~f:(fun stopped -> stopped addr)

  (* the stops, but not every address, which the executors, e.g.,
     Unicorn, observe only for the observers of [pc_change] *)
  let init () =
    Machine.sequence
      [ add_breakpoints (); Primus.Interpreter.stop_reached >>> stopped ]
end

let () =
  Primus.Components.register_generic ~package:"script" "debugger"
    (module Debugger)
    ~desc:"Calls the handlers of the script at the stops."

let component : Primus.Machine.component = (module Debugger)
