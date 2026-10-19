(* The checkpoint of a machine that runs in Unicorn.

   The state of the machine is in Primus, see [Primus_unicorn_executor],
   so the checkpoint has the values of the variables and the memory of
   the machine, and the point, from which Unicorn continues, in the run
   that it was taken. The other runs of the machine, which wait for the
   code that Primus runs, e.g., for a Lisp stub, are not kept, as their
   code is not data. *)

open Core
open Bap.Std
open Bap_primus.Std

module T = struct
  type t = {
    target : string;  (** the target of the program, see [Theory.Target] *)
    pc : int64;
        (** the address of the next instruction, with the lower bit set in the
            Thumb state of ARM *)
    ret : int64;  (** the return address of the run *)
    sp : int64;  (** the stack pointer after the return *)
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.t;
  }
  [@@deriving bin_io]
end

include T

let magic = "bap-primus-unicorn-checkpoint 1\n"

(* the checkpoint is written to a temporary file first, so that the file
   is never partly written *)
let save path t =
  let tmp = path ^ ".tmp" in
  try
    Out_channel.with_file ~binary:true tmp ~f:(fun out ->
        Out_channel.output_string out magic;
        Out_channel.output_string out (Binable.to_string (module T) t));
    Stdlib.Sys.rename tmp path;
    Ok ()
  with Sys_error msg -> Error msg

let load path =
  match In_channel.read_all path with
  | exception Sys_error msg -> Error msg
  | data -> (
      match String.chop_prefix data ~prefix:magic with
      | None -> Error (sprintf "%s is not a checkpoint of primus-unicorn" path)
      | Some data -> (
          try Ok (Binable.of_string (module T) data)
          with exn ->
            Error
              (sprintf "the checkpoint %s is broken: %s" path
                 (Exn.to_string exn))))
