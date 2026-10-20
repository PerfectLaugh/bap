(* The debugger of the Primus machines.

   The machine stops at the breakpoints, or at every instruction, while
   stepping, see [Primus.Interpreter.Stops], where the debugger reads
   the commands from the terminal or a file, which show and change the
   registers and the memory of the machine, call the Lisp functions, and
   set the breakpoints, until a command continues the machine.

   The interpreter posts [pc_change] at every instruction, and Unicorn
   at the stops, so the debugger is the same for both. *)

open Core
open Bap_main
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
include Loggers ()

let package = "bap"

let breakpoints =
  Extension.Configuration.parameter
    Extension.Type.(list string)
    "break"
    ~doc:
      "Stops the machines at the given addresses or the names of the \
       subroutines. Without them, the machines stop at their first \
       instruction."

let commands =
  Extension.Configuration.parameter
    Extension.Type.(some string)
    "commands"
    ~doc:
      "Reads the commands of the debugger from the given file, instead of the \
       terminal, and continues the machines without stopping, after the last \
       one."

let help =
  {|commands:
  c, continue           continue to the next breakpoint
  s, step               stop at the next instruction
  b, break ADDR|NAME    stop at the address or the subroutine
  d, delete ADDR|NAME   remove the breakpoint
  breaks                list the breakpoints
  pc                    show the program counter
  regs                  show the registers, without the aliases
  reg NAME              show the register
  set NAME VALUE        set the register
  x ADDR [LEN]          dump LEN (64) bytes of the memory
  write ADDR BYTE...    store the bytes to the memory
  call NAME ARG...      call the Lisp function and show its result
  quit [CODE]           exit bap with CODE (0)
  help                  show this help|}

(* the commands, from the file or the terminal, which is prompted *)
type input = { channel : In_channel.t; prompt : bool }

let input : input option ref = ref None
let detached = ref false

(* the breakpoints of the options, which the first machine of a system
   resolves, as they are of its program *)
let points : string list ref = ref []

let resolved =
  Primus.Machine.State.declare ~uuid:"0a7e3c19-5d82-4b6f-a1e4-93c2d8f05b7a"
    ~name:"debugger-resolved" (fun _ -> false)

let read_command () =
  match !input with
  | None -> None
  | Some { channel; prompt } -> (
      if prompt then (
        Out_channel.output_string stdout "(bap) ";
        Out_channel.flush stdout);
      match In_channel.input_line channel with
      | None ->
          (* the commands are over, the machines run to the end, see
             [Debugger.repl] *)
          detached := true;
          None
      | Some line ->
          if not prompt then printf "(bap) %s\n" line;
          Some line)

let hex addr = "0x" ^ Addr.string_of_value addr

let say fmt =
  ksprintf
    (fun s ->
      Out_channel.output_string stdout s;
      Out_channel.newline stdout;
      Out_channel.flush stdout)
    fmt

module Debugger (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  open Machine.Let
  module Eval = Primus.Interpreter.Make (Machine)
  module Env = Primus.Env.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)
  module Value = Primus.Value.Make (Machine)
  module Lisp = Primus.Lisp.Make (Machine)
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let width = Machine.gets Project.target >>| Theory.Target.bits

  let number s =
    match Int64.of_string s with x -> Some x | exception _ -> None

  (* the address, or the address of the subroutine with the name *)
  let resolve point =
    let* width = width in
    match number point with
    | Some x -> Machine.return (Some (Addr.of_int64 ~width x))
    | None ->
        let+ prog = Machine.gets Project.program in
        Term.enum sub_t prog
        |> Seq.find ~f:(fun sub -> String.equal (Sub.name sub) point)
        |> Option.bind ~f:(fun sub -> Term.get_attr sub address)

  let with_point point f =
    resolve point >>= function
    | Some addr -> f addr
    | None -> Machine.return (say "%s is not found" point)

  let pp_value ppf x = Format.fprintf ppf "%a" Word.pp_hex (Value.to_word x)

  (* the registers of the target, which the machine has, without the
     aliases, e.g., EAX of RAX, which Primus doesn't keep in sync *)
  let registers ?(aliases = false) () =
    let* target = Machine.gets Project.target in
    let exclude = if aliases then [] else [ Theory.Role.Register.alias ] in
    let names =
      Theory.Target.regs ~exclude target
      |> Set.to_list
      |> List.map ~f:Theory.Var.name
      |> String.Set.of_list
    in
    let* vars = Env.all in
    Seq.to_list vars
    |> List.filter ~f:(fun v -> Set.mem names (Var.name v))
    |> List.dedup_and_sort ~compare:(fun x y ->
        String.compare (Var.name x) (Var.name y))
    |> Machine.List.filter ~f:Env.is_set

  let find_register name =
    let+ regs = registers ~aliases:true () in
    List.find regs ~f:(fun v -> String.Caseless.equal (Var.name v) name)

  let show_register v =
    let+ x = Env.get v in
    say "%s = %s" (Var.name v) (Format.asprintf "%a" pp_value x)

  let set_register name value =
    find_register name >>= function
    | None -> Machine.return (say "no register %s" name)
    | Some v -> (
        match (number value, Var.typ v) with
        | Some x, Imm width ->
            let* x = Value.of_word (Word.of_int64 ~width x) in
            Eval.set v x
        | _ -> Machine.return (say "can't set %s to %s" name value))

  (* the line of 16 bytes, as dump-memory-region shows *)
  let dump addr len =
    let byte a =
      Memory.protection a >>= function
      | None -> Machine.return ("??", '.')
      | Some { readable = false; _ } -> Machine.return ("--", '.')
      | Some _ ->
          let+ x = Memory.load a in
          let c = Char.of_int_exn (Word.to_int_exn x) in
          (sprintf "%02x" (Char.to_int c), if Char.is_print c then c else '.')
    in
    let rec lines off =
      if off >= len then Machine.return ()
      else
        let base = Addr.(addr ++ off) in
        let* bytes =
          Machine.List.map
            (List.init (Int.min 16 (len - off)) ~f:Fn.id)
            ~f:(fun i -> byte Addr.(base ++ i))
        in
        say "%s: %-47s |%s|" (hex base)
          (List.map bytes ~f:fst |> String.concat ~sep:" ")
          (List.map bytes ~f:snd |> String.of_char_list);
        lines (off + 16)
    in
    lines 0

  (* the stores go through the interpreter, so that the copies of the
     memory, e.g., in Unicorn, see them *)
  let write addr bytes =
    Machine.List.iter
      (List.mapi bytes ~f:(fun i b -> (i, b)))
      ~f:(fun (i, b) ->
        match number b with
        | None -> Machine.return (say "%s is not a byte" b)
        | Some b ->
            let* width = width in
            let* a = Value.of_word Addr.(addr ++ i) in
            let* x = Value.of_word (Word.of_int64 ~width:8 b) in
            Eval.store a x LittleEndian `r8)

  let call name args =
    let* width = width in
    let* args =
      Machine.List.filter_map args ~f:(fun a ->
          match number a with
          | Some x -> Value.of_word (Word.of_int64 ~width x) >>| Option.some
          | None -> Value.Symbol.to_value a >>| Option.some)
    in
    let+ r = Lisp.eval_fun name args in
    say "%s" (Format.asprintf "%a" pp_value r)

  (* runs the command, and tells whether the machine continues *)
  let execute words =
    let stay = Machine.return false and go = Machine.return true in
    match words with
    | [] -> stay
    | ("c" | "continue") :: _ -> Stops.set_stepping false >>= fun () -> go
    | ("s" | "step") :: _ -> Stops.set_stepping true >>= fun () -> go
    | ("b" | "break") :: [ point ] ->
        with_point point (fun addr ->
            let+ () = Stops.add addr in
            say "breakpoint at %s" (hex addr))
        >>= fun () -> stay
    | ("d" | "delete") :: [ point ] ->
        with_point point Stops.remove >>= fun () -> stay
    | [ "breaks" ] ->
        let* stops = Stops.to_list in
        List.iter stops ~f:(fun addr -> say "%s" (hex addr));
        stay
    | [ "pc" ] ->
        let* pc = Eval.pc in
        say "%s" (hex pc);
        stay
    | [ "regs" ] ->
        let* regs = registers () in
        Machine.List.iter regs ~f:show_register >>= fun () -> stay
    | [ "reg"; name ] -> (
        find_register name >>= function
        | None ->
            say "no register %s" name;
            stay
        | Some v -> show_register v >>= fun () -> stay)
    | [ "set"; name; value ] -> set_register name value >>= fun () -> stay
    | "x" :: addr :: rest -> (
        let len = match rest with [ n ] -> number n | _ -> Some 64L in
        match (number addr, len) with
        | Some a, Some n ->
            let* width = width in
            dump (Addr.of_int64 ~width a) (Int64.to_int_exn n) >>= fun () ->
            stay
        | _ ->
            say "x ADDR [LEN]";
            stay)
    | "write" :: addr :: (_ :: _ as bytes) -> (
        match number addr with
        | Some a ->
            let* width = width in
            write (Addr.of_int64 ~width a) bytes >>= fun () -> stay
        | None ->
            say "write ADDR BYTE...";
            stay)
    | "call" :: name :: args -> call name args >>= fun () -> stay
    | "quit" :: rest ->
        let code =
          match rest with
          | [ n ] -> Option.value_map (number n) ~default:0 ~f:Int64.to_int_exn
          | _ -> 0
        in
        Stdlib.exit code
    | _ ->
        say "%s" help;
        stay

  (* a failed command, e.g., a store to the memory that is not
     writable, doesn't stop the machine *)
  let execute words =
    Machine.catch (execute words) (fun exn ->
        say "error: %s" (Primus.Exn.to_string exn);
        Machine.return false)

  let rec repl () =
    match read_command () with
    | None when !detached ->
        (* the machines of the system run to the end *)
        let* () = Stops.set_stepping false in
        Stops.to_list >>= Machine.List.iter ~f:Stops.remove
    | None -> Machine.return ()
    | Some line ->
        let words =
          String.split_on_chars line ~on:[ ' '; '\t' ]
          |> List.filter ~f:(Fn.non String.is_empty)
        in
        execute words >>= fun continues ->
        if continues then Machine.return () else repl ()

  (* the commands, which run the code, e.g., call, don't stop it *)
  let busy = ref false

  let stopped addr =
    if !busy || !detached then Machine.return ()
    else
      let* stepping = Stops.stepping in
      let* stopped = Stops.mem addr in
      if not (stepping || stopped) then Machine.return ()
      else
        let* id = Machine.current () in
        say "stopped at %s in machine %s" (hex addr)
          (Format.asprintf "%a" Monads.Std.Monad.State.Multi.Id.pp id);
        busy := true;
        let+ () = repl () in
        busy := false

  let add_breakpoints () =
    let* done_ = Machine.Global.get resolved in
    if done_ then Machine.return ()
    else
      let* () = Machine.Global.put resolved true in
      if List.is_empty !points then Stops.set_stepping true
      else
        Machine.List.iter !points ~f:(fun point -> with_point point Stops.add)

  let init () =
    Machine.sequence
      [ add_breakpoints (); Primus.Interpreter.pc_change >>> stopped ]
end

let () =
  Extension.declare ~doc:"debugs the Primus machines" ~provides:[ "primus" ]
  @@ fun ctxt ->
  points := Extension.Configuration.get ctxt breakpoints;
  (input :=
     match Extension.Configuration.get ctxt commands with
     | None -> Some { channel = In_channel.stdin; prompt = true }
     | Some file -> Some { channel = In_channel.create file; prompt = false });
  Primus.Components.register_generic ~package "debugger"
    (module Debugger)
    ~desc:
      "Stops the machines at the breakpoints, given with \
       --primus-debugger-break, or at their first instruction, and reads the \
       commands of the debugger, which show and change the machine. Add it to \
       a system with --run-components=bap:debugger.";
  Ok ()
