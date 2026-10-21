open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
include Self ()

(* the origin of a channel, from which a checkpoint opens it anew, see
   [Persistent] *)
type source = Std of int | File of string [@@deriving bin_io]

type channel = {
  input : In_channel.t option;
  output : Out_channel.t option;
  source : source;
}

type state = {
  redirections : string String.Map.t;
  channels : channel Int.Map.t;
}

let default_channels =
  Int.Map.of_alist_exn
    [
      ( 0,
        {
          input = Some In_channel.stdin;
          output = Some Out_channel.stdout;
          source = Std 0;
        } );
      (1, { input = None; output = Some Out_channel.stdout; source = Std 1 });
      (2, { input = None; output = Some Out_channel.stderr; source = Std 2 });
    ]

let standard_channels = [ "<stdin>"; "<stdout>"; "<stderr>" ]

let fd_of_name name =
  List.find_mapi standard_channels ~f:(fun i chan ->
      if String.equal name chan then Some i else None)

let init_channels =
  List.fold ~init:default_channels ~f:(fun chans (chan, name) ->
      match fd_of_name chan with
      | None -> chans
      | Some fd ->
          info "redirecting fd %d to %s" fd name;
          let chan =
            if fd > 0 then
              {
                input = None;
                output = Some (Out_channel.create name);
                source = File name;
              }
            else
              {
                output = None;
                input = Some (In_channel.create name);
                source = File name;
              }
          in
          Map.set chans ~key:fd ~data:chan)

let init_redirections =
  List.fold ~init:String.Map.empty ~f:(fun redirs (oldname, newname) ->
      match fd_of_name oldname with
      | Some _ -> redirs
      | None -> Map.set redirs ~key:oldname ~data:newname)

let init redirs =
  { redirections = init_redirections redirs; channels = init_channels redirs }

let try_open path =
  Or_error.try_with (fun () ->
      {
        input = Some (In_channel.create path);
        output = Some (Out_channel.create ~append:true path);
        source = File path;
      })

let try_flush { output } =
  Or_error.try_with @@ fun () -> Option.iter ~f:Out_channel.flush output

let input_byte chan = Or_error.try_with @@ fun () -> In_channel.input_byte chan

let next_fd channels =
  match Map.max_elt channels with None -> 0 | Some (fd, _) -> fd + 1

let state =
  Primus.Machine.State.declare ~name:"io-channels"
    ~uuid:"f326a07d-16ed-42ec-958d-76ef584cb341" (fun _ ->
      { redirections = String.Map.empty; channels = Int.Map.empty })

(* The channels of the machine, which the checkpoints keep, e.g., of the
   Unicorn executor, as their origins and the positions of their inputs,
   from which they are opened anew. The outputs are flushed, and the files
   are appended to. A channel, that can't be opened anew, is closed. *)
module Persistent = struct
  type saved = {
    fd : int;
    source : source;
    input : int64 option;  (** the position of the input, if it has one *)
    output : bool;
  }
  [@@deriving bin_io]

  type t = { redirections : (string * string) list; channels : saved list }
  [@@deriving bin_io]

  let save_channel fd ({ input; output; source } : channel) : saved =
    Option.iter output ~f:Out_channel.flush;
    {
      fd;
      source;
      input =
        Option.bind input ~f:(fun ch ->
            Option.try_with (fun () -> In_channel.pos ch));
      output = Option.is_some output;
    }

  let open_channel ({ source; input; output; _ } : saved) : channel option =
    Option.try_with @@ fun () : channel ->
    match source with
    | Std n ->
        {
          source;
          input = Option.map input ~f:(fun _ -> In_channel.stdin);
          output =
            Option.some_if output
              (if n = 2 then Out_channel.stderr else Out_channel.stdout);
        }
    | File path ->
        {
          source;
          input =
            Option.map input ~f:(fun pos ->
                let ch = In_channel.create path in
                In_channel.seek ch pos;
                ch);
          output = Option.some_if output (Out_channel.create ~append:true path);
        }

  module Extension (Machine : Primus.Machine.S) = struct
    open Machine.Syntax

    let save =
      Machine.Local.get state >>| fun { redirections; channels } ->
      Some
        (Binable.to_string
           (module struct
             type nonrec t = t [@@deriving bin_io]
           end)
           {
             redirections = Map.to_alist redirections;
             channels =
               Map.to_alist channels
               |> List.map ~f:(fun (fd, ch) -> save_channel fd ch);
           })

    let restore data =
      let saved =
        Binable.of_string
          (module struct
            type nonrec t = t [@@deriving bin_io]
          end)
          data
      in
      let channels =
        List.filter_map saved.channels ~f:(fun ch ->
            match open_channel ch with
            | Some chan -> Some (ch.fd, chan)
            | None ->
                warning "can't open the channel %d anew, it is closed" ch.fd;
                None)
      in
      Machine.Local.put state
        {
          redirections =
            String.Map.of_alist_reduce saved.redirections ~f:(fun _ x -> x);
          channels = Int.Map.of_alist_reduce channels ~f:(fun _ x -> x);
        }
  end

  let () =
    Primus.Checkpoint.register ~package:"bap" "lisp-channels" (module Extension)
end

let init redirections =
  let module Lib (Machine : Primus.Machine.S) = struct
    include Machine.Syntax
    module Eval = Primus.Interpreter.Make (Machine)
    module Value = Primus.Value.Make (Machine)

    let addr_width = Machine.gets Project.target >>| Theory.Target.bits
    let nil = Value.b0
    let error = addr_width >>= fun w -> Value.of_word (Word.ones w)
    let ok = addr_width >>= Value.zero
    let int x = addr_width >>= fun width -> Value.of_int ~width x

    let value_to_fd fd =
      Value.to_word fd |> Word.to_int |> function
      | Error _ -> None
      | Ok n -> Some n

    let string_of_charp ptr =
      let rec loop chars ptr =
        Eval.load ptr LittleEndian `r8 >>= fun c ->
        let c =
          (* [load p e `r8] must return a byte *)
          Char.of_int_exn @@ Word.to_int_exn @@ Value.to_word c
        in
        if Char.(c = '\000') then
          Machine.return (String.of_char_list (List.rev chars))
        else Value.succ ptr >>= loop (c :: chars)
      in
      loop [] ptr

    module Closure = Primus.Lisp.Closure.Make (Machine)

    (* a closure is applied to as many arguments as its type declares,
       unless the program is ill-typed (the type errors don't stop it) *)
    let wrong_arity () =
      Closure.name >>= fun name ->
      Machine.raise
        (Primus.Lisp.Runtime_error
           (sprintf "%s: wrong number of arguments" name))
  end in
  let module Open (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | [ path ] -> (
          string_of_charp path >>= fun path ->
          Machine.Local.get state >>= fun { redirections } ->
          match Map.find redirections path with
          | None -> error
          | Some path -> (
              match try_open path with
              | Error _ -> error
              | Ok channel ->
                  Machine.Local.get state >>= fun s ->
                  let fd = next_fd s.channels in
                  Machine.Local.put state
                    {
                      s with
                      channels =
                        Map.set s.channels ~key:(next_fd s.channels)
                          ~data:channel;
                    }
                  >>= fun () ->
                  addr_width >>= fun width -> Value.of_int ~width fd))
      | _ -> wrong_arity ()
  end in
  let module Close (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | [ fd ] -> (
          value_to_fd fd |> function
          | None -> error
          | Some fd ->
              Machine.Local.get state >>= fun s ->
              if Map.mem s.channels fd then
                Machine.Local.put state
                  { s with channels = Map.remove s.channels fd }
                >>= fun () -> ok
              else error)
      | _ -> wrong_arity ()
  end in
  let module Output (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | fd :: xs -> (
          value_to_fd fd |> function
          | None -> error
          | Some fd -> (
              Machine.Local.get state >>= fun { channels } ->
              match Map.find channels fd with
              | Some { output = Some ch } ->
                  List.iter xs ~f:(fun w ->
                      Word.enum_chars (Value.to_word w) LittleEndian
                      |> Seq.hd
                      |> Option.iter ~f:(Out_channel.output_char ch));
                  ok
              | _ -> error))
      | _ -> wrong_arity ()
  end in
  let module Flush (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | [ fd ] -> (
          value_to_fd fd |> function
          | None -> error
          | Some fd -> (
              Machine.Local.get state >>= fun s ->
              match Map.find s.channels fd with
              | None -> error
              | Some chan -> (
                  match try_flush chan with Error _ -> error | Ok () -> ok)))
      | _ -> wrong_arity ()
  end in
  let module Input (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | [ fd ] -> (
          value_to_fd fd |> function
          | None -> error
          | Some fd -> (
              Machine.Local.get state >>= fun s ->
              match Map.find s.channels fd with
              | None -> error
              | Some { input = None } -> error
              | Some { input = Some ch } -> (
                  match input_byte ch with
                  | Error _ -> error
                  | Ok None -> error
                  | Ok (Some ch) -> int ch)))
      | _ -> wrong_arity ()
  end in
  let module Seek (Machine : Primus.Machine.S) = struct
    include Lib (Machine)

    let run = function
      | [ fd; offset; whence ] -> (
          match
            ( value_to_fd fd,
              Word.to_int64 (Value.to_word offset),
              Word.to_int (Value.to_word whence) )
          with
          | Some fd, Ok offset, Ok whence -> (
              Machine.Local.get state >>= fun s ->
              match Map.find s.channels fd with
              | Some { input = Some ch; _ } -> (
                  let origin =
                    match whence with
                    | 0 -> Some 0L
                    | 1 -> Some (In_channel.pos ch)
                    | 2 -> Some (In_channel.length ch)
                    | _ -> None
                  in
                  match origin with
                  | None -> error
                  | Some origin -> (
                      match
                        Or_error.try_with (fun () ->
                            In_channel.seek ch Int64.(origin + offset))
                      with
                      | Error _ -> error
                      | Ok () -> ok))
              | _ -> error)
          | _ -> error)
      | _ -> wrong_arity ()
  end in
  let module Primitives (Machine : Primus.Machine.S) = struct
    open Machine.Syntax
    module Lisp = Primus.Lisp.Make (Machine)
    module Env = Primus.Env.Make (Machine)
    module Value = Primus.Value.Make (Machine)
    module Lib = Lib (Machine)

    let setup_standard_channels =
      let set name descr =
        Lib.addr_width >>= fun width ->
        let v = Var.create name (Type.imm width) in
        Value.of_int ~width descr >>= Env.set v
      in
      Machine.sequence
        [
          set "posix:*standard-input*" 0;
          set "posix:*standard-output*" 1;
          (* the name of Common Lisp and the conventional one *)
          set "posix:*error-output*" 2;
          set "posix:*standard-error*" 2;
        ]

    let setup_redirections = Machine.Local.put state (init redirections)

    let init () =
      let open Primus.Lisp.Type.Spec in
      let def name types closure docs = Lisp.define ~docs ~types name closure in
      Machine.sequence
        [
          setup_standard_channels;
          setup_redirections;
          def "channel-open"
            ((one int // all int) @-> int)
            (module Open)
            {|(channel-open PTR) creates a new channel that is
            associated with a null-terminated path pointed by PTR.
            Returns a non-negative channel descriptor, if the channel
            subsystem have a mapping from the obtained path to a
            physical file and this file is accessible. Otherwise returns
            a negative value.
          |};
          def "channel-close"
            (one int @-> int)
            (module Close)
            {|(channel-close DESCR) closes a channel that has the
            specified descriptor DESCR. If no such channel exists,
            then returns -1. Otherwise returns 0. The descriptor of the
            closed channel will be reused by the consequent calls
            to `channel-open'. If the channel had any data associated
            with it and not yet flushed, then the data is discarded. |};
          def "channel-flush"
            (one int @-> int)
            (module Flush)
            {|(channel-flush DESCR) forces data that were written to a
            channel that has the descriptor DESCR to be outputted to the
            associated destination. Returns -1 if no such channel exists or
            if in case of an IO error.|};
          def "channel-input"
            (one int @-> int)
            (module Input)
            {|(channel-input DESC) reads one byte from a channel that
            has the descriptor DESC. Returns -1 if no such channel
            exists, or if any IO error occurs, if the channel is not
            readable, or if the channel is in the end-of-file condition.|};
          def "channel-seek"
            (tuple [ int; int; int ] @-> int)
            (module Seek)
            {|(channel-seek DESC OFFSET WHENCE) changes the current position
            of a readable channel. WHENCE is interpreted as in fseek: zero
            seeks from the beginning, one from the current position, and two
            from the end. Returns zero on success and -1 on failure.|};
          def "channel-output"
            ((one int // all byte) @-> int)
            (module Output)
            {|(channel-output DESCR CHAR ...) outputs one or more
            characters to a channel that has the descriptor
            DESCR. Returns -1 if no such channel exits, if a channel
            is not writable, or if any IO error occurs in an
            associated physical file. Otherwise, returns 0.
            Note: the channel system is buffered, and the actual IO
            operation (as well as errors) could be delayed until
            (channel-flush DESCR) is called. |};
        ]
  end in
  Primus.System.Repository.update ~package:"bap" "legacy-main" ~f:(fun s ->
      Primus.System.add_component s ~package:"bap" "lisp-basic-io");
  Primus.Components.register_generic "lisp-basic-io"
    (module Primitives)
    ~package:"bap" ~desc:"Provides basic IO primitives to Primus Lisp."

(* the redirections of the machine, instead of those of the options *)
let redirect redirections =
  let module Redirect (Machine : Primus.Machine.S) = struct
    let init () =
      Machine.Local.put state
        {
          redirections = init_redirections redirections;
          channels = init_channels redirections;
        }
  end in
  (module Redirect : Primus.Machine.Component)
