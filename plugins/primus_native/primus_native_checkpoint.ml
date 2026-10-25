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
  }
  [@@deriving bin_io]
end

include T

let magic5 = "bap-primus-unicorn-checkpoint 5\n"
let magic = "bap-primus-unicorn-checkpoint 6\n"

let validate (t : t) =
  match t.model_states with
  | None -> ()
  | Some models ->
      let names = List.map models ~f:(fun m -> m.name) in
      let payloads = List.map t.extensions ~f:fst in
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

let of_v5 (v : V5.t) : t =
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

(* the checkpoint is written to a temporary file first, so that the file
   is never partly written, which is new, rather than a file of a known
   name, which another user may have made, e.g., a link, in a directory,
   that they can write *)
let save path t =
  match validate t with
  | exception exn -> Error (Exn.to_string exn)
  | () -> (
      match
        Stdlib.Filename.temp_file
          ~temp_dir:(Stdlib.Filename.dirname path)
          (Stdlib.Filename.basename path)
          ".tmp"
      with
      | exception Sys_error msg -> Error msg
      | tmp -> (
          try
            Out_channel.with_file ~binary:true tmp ~f:(fun out ->
                Out_channel.output_string out magic;
                Out_channel.output_string out (Binable.to_string (module T) t));
            Stdlib.Sys.rename tmp path;
            Ok ()
          with Sys_error msg ->
            (try Stdlib.Sys.remove tmp with Sys_error _ -> ());
            Error msg))

let load path =
  match In_channel.read_all path with
  | exception Sys_error msg -> Error msg
  | data -> (
      match
        ( String.chop_prefix data ~prefix:magic,
          String.chop_prefix data ~prefix:magic5 )
      with
      | None, None
        when String.is_prefix data ~prefix:"bap-primus-unicorn-checkpoint " ->
          Error
            (sprintf "the checkpoint %s is of another version of primus-unicorn"
               path)
      | None, None ->
          Error (sprintf "%s is not a checkpoint of primus-unicorn" path)
      | Some data, _ -> (
          try
            let (t : t) = Binable.of_string (module T) data in
            validate t;
            Ok t
          with exn ->
            Error
              (sprintf "the checkpoint %s is broken: %s" path
                 (Exn.to_string exn)))
      | _, Some data -> (
          try Ok (of_v5 (Binable.of_string (module V5) data))
          with exn ->
            Error
              (sprintf "the checkpoint %s is broken: %s" path
                 (Exn.to_string exn))))
