(* The checkpoint of a machine that runs in Unicorn.

   The state of the machine is in Primus, see [Primus_native_executor],
   so the checkpoint has the values of the variables and the memory of
   the machine, the states of the components, that extend the
   checkpoints, see [Primus.Checkpoint], e.g., the channels of Lisp, and
   the point, from which Unicorn continues, in the run that it was taken.
   The other runs of the machine, which wait for the code that Primus
   runs, e.g., for a Lisp stub, are not kept, as their code is not data,
   but their frames are, with the stubs, that called them, so that the
   known stubs are completed, when the run returns, see
   [Primus_native_executor.complete]. *)

open Core
open Bap.Std
open Bap_primus.Std

(* a run of the machine in Unicorn, that Primus called *)
type frame = {
  ret : int64;  (** the return address of the run *)
  sp : int64;  (** the stack pointer after the return *)
  callee : string option;  (** the function of the program, that runs *)
  caller : string option;  (** the stub, that called it, e.g., in Lisp *)
}
[@@deriving bin_io]

(* a thread, that doesn't run, whose registers are the variables, see
   [Primus_native_executor.thread_var] *)
type thread = {
  tid : int;
  extra : (int * string) list;
      (** the registers of Unicorn, that Primus doesn't have, by their ids *)
  next : int64;  (** the address, from which it continues *)
  waiting : int64 list option;
      (** the addresses, e.g., of the futexes, or of the objects of Windows, on
          which it waits *)
  clear : int64 option;  (** the address of its TID, cleared at its exit *)
  woken : bool;  (** if it was woken, from its wait *)
}
[@@deriving bin_io]

(* the threads of the machine, see [Primus_native_executor.threads] *)
type threads = {
  current : int;  (** the TID of the thread, that runs *)
  cleared : int64 option;  (** its [clear] *)
  others : thread list;
  last : int;  (** the last TID *)
  woken : bool;  (** if the thread, that runs, was woken *)
}
[@@deriving bin_io]

type model_state = { name : string; version : int; required : bool }
[@@deriving bin_io]

type journal_event = { kind : string; detail : string } [@@deriving bin_io]

module V5 = struct
  type t = {
    target : string;
    digest : string;
    pc : int64;
    frames : frame list;
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.t;
    symbols : (string * int64) list;
    unstubbed : int64 list;
    extensions : (string * string) list;
    extra : (int * string) list;
    threads : threads option;
  }
  [@@deriving bin_io]
end

module V6 = struct
  type t = {
    target : string;
    digest : string;
    pc : int64;
    frames : frame list;
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.t;
    symbols : (string * int64) list;
    unstubbed : int64 list;
    extensions : (string * string) list;
    extra : (int * string) list;
    threads : threads option;
    model_states : model_state list option;
  }
  [@@deriving bin_io]
end

module T = struct
  type t = {
    target : string;
    digest : string;
    pc : int64;
    frames : frame list;
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.t;
    symbols : (string * int64) list;
    unstubbed : int64 list;
    extensions : (string * string) list;
    extra : (int * string) list;
    threads : threads option;
    model_states : model_state list option;
    thread_journal : journal_event list;
    quantum_remaining : float;
  }
  [@@deriving bin_io]
end

include T

module Delta = struct
  type t = {
    parent : string;
    parent_digest : string;
    target : string;
    digest : string;
    pc : int64;
    frames : frame list;
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.delta;
    symbols : (string * int64) list;
    unstubbed : int64 list;
    extensions : (string * string) list;
    extra : (int * string) list;
    threads : threads option;
    model_states : model_state list option;
    thread_journal : journal_event list;
    quantum_remaining : float;
  }
  [@@deriving bin_io]
end

type link = {
  file : string;
  version : int;
  digest : string;
  parent : (string * string) option;
  models : model_state list option;
}

type resolution = { checkpoint : t; chain : link list; states : t list }

let magic5 = "bap-primus-unicorn-checkpoint 5\n"
let magic6 = "bap-primus-unicorn-checkpoint 6\n"
let magic = "bap-primus-unicorn-checkpoint 7\n"
let delta_magic = "bap-primus-unicorn-checkpoint-delta 1\n"
let delta_version = 1
let version = 7

let validate_parts quantum_remaining model_states extensions =
  if
    (not (Float.is_finite quantum_remaining))
    || Float.(quantum_remaining < 0. || quantum_remaining > 0.005)
  then failwith "the checkpoint has an invalid scheduler quantum";
  match model_states with
  | None -> ()
  | Some models ->
      let names = List.map models ~f:(fun m -> m.name) in
      let payloads = List.map extensions ~f:fst in
      let check_duplicates kind values =
        List.sort values ~compare:String.compare
        |> List.iter ~f:(fun name ->
            if List.count values ~f:(String.equal name) > 1 then
              failwithf "the checkpoint has duplicate %s %s" kind name ())
      in
      check_duplicates "model" names;
      check_duplicates "extension" payloads;
      if
        not
          (List.for_all payloads ~f:(fun payload ->
               List.exists names ~f:(String.equal payload)))
      then failwith "an extension state has no model manifest entry"

let validate (t : t) =
  validate_parts t.quantum_remaining t.model_states t.extensions

let validate_delta (d : Delta.t) =
  validate_parts d.quantum_remaining d.model_states d.extensions

let of_v6 (v : V6.t) : t =
  {
    target = v.target;
    digest = v.digest;
    pc = v.pc;
    frames = v.frames;
    vars = v.vars;
    memory = v.memory;
    symbols = v.symbols;
    unstubbed = v.unstubbed;
    extensions = v.extensions;
    extra = v.extra;
    threads = v.threads;
    model_states = v.model_states;
    thread_journal = [];
    quantum_remaining = 0.005;
  }

let of_v5 (v : V5.t) : t =
  of_v6
    {
      target = v.target;
      digest = v.digest;
      pc = v.pc;
      frames = v.frames;
      vars = v.vars;
      memory = v.memory;
      symbols = v.symbols;
      unstubbed = v.unstubbed;
      extensions = v.extensions;
      extra = v.extra;
      threads = v.threads;
      model_states = None;
    }

(* the digest of the file of the program, which the checkpoint is of *)
let digest path = Stdlib.Digest.(to_hex (file path))

let state (d : Delta.t) memory : t =
  {
    target = d.target;
    digest = d.digest;
    pc = d.pc;
    frames = d.frames;
    vars = d.vars;
    memory;
    symbols = d.symbols;
    unstubbed = d.unstubbed;
    extensions = d.extensions;
    extra = d.extra;
    threads = d.threads;
    model_states = d.model_states;
    thread_journal = d.thread_journal;
    quantum_remaining = d.quantum_remaining;
  }

let delta ~parent ~parent_digest base (t : t) : Delta.t =
  {
    parent;
    parent_digest;
    target = t.target;
    digest = t.digest;
    pc = t.pc;
    frames = t.frames;
    vars = t.vars;
    memory = Primus.Memory.Snapshot.diff base t.memory;
    symbols = t.symbols;
    unstubbed = t.unstubbed;
    extensions = t.extensions;
    extra = t.extra;
    threads = t.threads;
    model_states = t.model_states;
    thread_journal = t.thread_journal;
    quantum_remaining = t.quantum_remaining;
  }

let temporary path =
  Stdlib.Filename.temp_file
    ~temp_dir:(Stdlib.Filename.dirname path)
    (Stdlib.Filename.basename path)
    ".tmp"

let remove path = try Stdlib.Sys.remove path with Sys_error _ -> ()

(* Full checkpoints retain their replacement-on-publish behavior. *)
let save_full path t =
  match validate t with
  | exception exn -> Error (Exn.to_string exn)
  | () -> (
      match temporary path with
      | exception Sys_error msg -> Error msg
      | tmp -> (
          try
            Out_channel.with_file ~binary:true tmp ~f:(fun out ->
                Out_channel.output_string out magic;
                Out_channel.output_string out (Binable.to_string (module T) t));
            Stdlib.Sys.rename tmp path;
            Ok ()
          with Sys_error msg ->
            remove tmp;
            Error msg))

let save_delta path (d : Delta.t) =
  if Stdlib.Sys.file_exists path then
    Error (sprintf "the checkpoint %s already exists" path)
  else
    match temporary path with
    | exception Sys_error msg -> Error msg
    | tmp -> (
        try
          Out_channel.with_file ~binary:true tmp ~f:(fun out ->
              Out_channel.output_string out delta_magic;
              Out_channel.output_string out (Binable.to_string (module Delta) d));
          Caml_unix.link tmp path;
          remove tmp;
          Ok ()
        with
        | Sys_error msg ->
            remove tmp;
            Error msg
        | Caml_unix.Unix_error (error, _, _) ->
            remove tmp;
            Error
              (sprintf "can't publish the delta checkpoint %s: %s" path
                 (Caml_unix.error_message error)))

type encoded = Full of int * t | Delta of Delta.t

let broken path exn =
  Error (sprintf "the checkpoint %s is broken: %s" path (Exn.to_string exn))

let decode path data =
  let current = String.chop_prefix data ~prefix:magic in
  let v6 = String.chop_prefix data ~prefix:magic6 in
  let v5 = String.chop_prefix data ~prefix:magic5 in
  let delta = String.chop_prefix data ~prefix:delta_magic in
  match (current, v6, v5, delta) with
  | Some data, _, _, _ -> (
      try
        let (t : t) = Binable.of_string (module T) data in
        validate t;
        Ok (Full (version, t))
      with exn -> broken path exn)
  | _, Some data, _, _ -> (
      try Ok (Full (6, of_v6 (Binable.of_string (module V6) data)))
      with exn -> broken path exn)
  | _, _, Some data, _ -> (
      try Ok (Full (5, of_v5 (Binable.of_string (module V5) data)))
      with exn -> broken path exn)
  | _, _, _, Some data -> (
      try
        let (d : Delta.t) = Binable.of_string (module Delta) data in
        validate_delta d;
        Ok (Delta d)
      with exn -> broken path exn)
  | None, None, None, None
    when String.is_prefix data ~prefix:"bap-primus-unicorn-checkpoint "
         || String.is_prefix data ~prefix:"bap-primus-unicorn-checkpoint-delta "
    ->
      Error
        (sprintf "the checkpoint %s is of another version of primus-unicorn"
           path)
  | None, None, None, None ->
      Error (sprintf "%s is not a checkpoint of primus-unicorn" path)

let resolve path =
  let visiting = String.Hash_set.create () in
  let rec visit ?expected file =
    let canonical =
      try Ok (Caml_unix.realpath file)
      with Caml_unix.Unix_error (error, _, _) ->
        Error
          (sprintf "can't resolve the checkpoint %s: %s" file
             (Caml_unix.error_message error))
    in
    match canonical with
    | Error _ as error -> error
    | Ok canonical when Hash_set.mem visiting canonical ->
        Error (sprintf "the checkpoint chain has a cycle at %s" canonical)
    | Ok canonical ->
        Hash_set.add visiting canonical;
        let result =
          match In_channel.read_all file with
          | exception Sys_error msg -> Error msg
          | data -> (
              let file_digest = Stdlib.Digest.(to_hex (string data)) in
              match expected with
              | Some expected when not (String.equal expected file_digest) ->
                  Error
                    (sprintf
                       "the parent checkpoint %s has digest %s, expected %s"
                       file file_digest expected)
              | _ -> (
                  match decode file data with
                  | Error _ as error -> error
                  | Ok (Full (version, checkpoint)) ->
                      Ok
                        {
                          checkpoint;
                          states = [ checkpoint ];
                          chain =
                            [
                              {
                                file = canonical;
                                version;
                                digest = file_digest;
                                parent = None;
                                models = checkpoint.model_states;
                              };
                            ];
                        }
                  | Ok (Delta d) -> (
                      let parent =
                        if Stdlib.Filename.is_relative d.parent then
                          Stdlib.Filename.concat
                            (Stdlib.Filename.dirname file)
                            d.parent
                        else d.parent
                      in
                      match visit ~expected:d.parent_digest parent with
                      | Error _ as error -> error
                      | Ok base -> (
                          try
                            let memory =
                              Primus.Memory.Snapshot.apply
                                base.checkpoint.memory d.memory
                            in
                            let checkpoint = state d memory in
                            validate checkpoint;
                            Ok
                              {
                                checkpoint;
                                states = base.states @ [ checkpoint ];
                                chain =
                                  base.chain
                                  @ [
                                      {
                                        file = canonical;
                                        version = delta_version;
                                        digest = file_digest;
                                        parent = Some (d.parent, d.parent_digest);
                                        models = d.model_states;
                                      };
                                    ];
                              }
                          with exn -> broken file exn))))
        in
        Hash_set.remove visiting canonical;
        result
  in
  visit path

let load path =
  match resolve path with
  | Error _ as error -> error
  | Ok resolved -> Ok resolved.checkpoint

let chain path =
  match resolve path with
  | Error _ as error -> error
  | Ok resolved -> Ok resolved.chain

let save ?parent path t =
  match parent with
  | None -> save_full path t
  | Some parent -> (
      match validate t with
      | exception exn -> Error (Exn.to_string exn)
      | () -> (
          if Stdlib.Sys.file_exists path then
            Error (sprintf "the checkpoint %s already exists" path)
          else
            match resolve parent with
            | Error msg ->
                Error
                  (sprintf "can't use the parent checkpoint %s: %s" parent msg)
            | Ok base -> (
                match List.last base.chain with
                | None -> Error "the parent checkpoint chain is empty"
                | Some link ->
                    save_delta path
                      (delta ~parent:link.file ~parent_digest:link.digest
                         base.checkpoint.memory t))))
