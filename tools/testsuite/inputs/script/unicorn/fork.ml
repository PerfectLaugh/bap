#require "bap-primus, monads"

open Core
open Bap.Std
open Bap_primus.Std

(* forks the machine at the third putchar, and then switches between
   the parent and the child at each putchar, so that they take Unicorn
   from each other in the middle of their runs, and the parent, which
   doesn't run in Unicorn, capitalizes its argument world *)
module Fork (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Env = Primus.Env.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)

  let calls = ref 0
  let machines = ref []
  let patched = ref false

  (* the string, to which a word of the stack points, e.g., the copy of
     the argument in the heap, which echo prints *)
  let find_string sp text =
    Memory.load_bytes sp 0x1000 >>= fun bytes ->
    let word i =
      List.init 8 ~f:(fun k ->
          match bytes.(i + k) with Some (c, _) -> Char.to_int c | None -> 0)
      |> List.foldi ~init:0L ~f:(fun k acc b ->
          Int64.(acc lor shift_left (of_int b) Int.(8 * k)))
    in
    let pointers =
      List.init (0x1000 / 8) ~f:(fun i ->
          Addr.of_int64 ~width:64 (word (i * 8)))
    in
    Machine.List.find pointers ~f:(fun p ->
        Memory.load_bytes p (String.length text) >>| fun bytes ->
        String.equal text
          (String.of_array
             (Array.map bytes ~f:(function Some (c, _) -> c | None -> '?'))))

  let capitalize () =
    Machine.current () >>= fun self ->
    match !machines with
    | parent :: _
      when Monads.Std.Monad.State.Multi.Id.equal parent self && not !patched
      -> (
        patched := true;
        Env.get (Var.create "RSP" (Type.imm 64)) >>= fun sp ->
        find_string (Primus.Value.to_word sp) "world\000" >>= function
        | Some p -> Memory.store p (Word.of_int ~width:8 (Char.to_int 'W'))
        | None -> Machine.return ())
    | _ -> Machine.return ()

  let switch () =
    Machine.forks () >>= fun alive ->
    Machine.current () >>= fun self ->
    let others =
      List.filter !machines ~f:(fun id ->
          (not (Monads.Std.Monad.State.Multi.Id.equal id self))
          && Seq.exists alive ~f:(Monads.Std.Monad.State.Multi.Id.equal id))
    in
    match others with
    | other :: _ -> Machine.switch other
    | [] -> Machine.return ()

  (* the calls are counted after the name of the program, argv[0] *)
  let started = ref false

  let call (name, args) =
    if String.equal name "putchar" && not !started then begin
      (match args with
      | [ c ] when Word.to_int_exn (Primus.Value.to_word c) = 10 ->
          started := true
      | _ -> ());
      Machine.return ()
    end
    else if String.equal name "putchar" then begin
      incr calls;
      if !calls = 3 then
        Machine.current () >>= fun parent ->
        Machine.fork () >>= fun () ->
        Machine.current () >>= fun self ->
        if Monads.Std.Monad.State.Multi.Id.equal self parent then
          Machine.return ()
        else begin
          machines := [ parent; self ];
          Machine.return ()
        end
      else if !calls > 3 then switch () >>= capitalize
      else Machine.return ()
    end
    else Machine.return ()

  let init () = Primus.Linker.Trace.call >>> call
end

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor"
       ~init:[ (module Fork) ]
       ~args:[ "hello"; "cruel"; "world" ]
       (Bap_script.project file))
