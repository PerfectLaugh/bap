(* The checkpoint of a machine that runs in Unicorn.

   The state of the machine is in Primus, see [Primus_unicorn_executor],
   so the checkpoint has the values of the variables and the memory of
   the machine, the states of the components, that extend the
   checkpoints, see [Primus.Checkpoint], e.g., the channels of Lisp, and
   the point, from which Unicorn continues, in the run that it was taken.
   The other runs of the machine, which wait for the code that Primus
   runs, e.g., for a Lisp stub, are not kept, as their code is not data,
   but their frames are, with the stubs, that called them, so that the
   known stubs are completed, when the run returns, see
   [Primus_unicorn_executor.complete]. *)

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

module T = struct
  type t = {
    target : string;  (** the target of the program, see [Theory.Target] *)
    digest : string;  (** the digest of the file of the program *)
    pc : int64;
        (** the address of the next instruction, with the lower bit set in the
            Thumb state of ARM *)
    frames : frame list;
        (** the runs of the machine, the innermost first, from which Unicorn
            continues *)
    vars : (Var.t * Word.t) list;
    memory : Primus.Memory.Snapshot.t;
    symbols : (string * int64) list;
        (** the names of the code, that the script gave, e.g., of the code that
            the program unpacked, see [Bap_emu.add_symbol] *)
    unstubbed : int64 list;
        (** the functions of the program, whose code runs instead of their
            stubs, see [Bap_emu.unstub] *)
    extensions : (string * string) list;
        (** the states of the components, by the names of their extensions, see
            [Primus.Checkpoint] *)
  }
  [@@deriving bin_io]
end

include T

let magic = "bap-primus-unicorn-checkpoint 3\n"

(* the digest of the file of the program, which the checkpoint is of *)
let digest path = Stdlib.Digest.(to_hex (file path))

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
      | None when String.is_prefix data ~prefix:"bap-primus-unicorn-checkpoint "
        ->
          Error
            (sprintf "the checkpoint %s is of another version of primus-unicorn"
               path)
      | None -> Error (sprintf "%s is not a checkpoint of primus-unicorn" path)
      | Some data -> (
          try Ok (Binable.of_string (module T) data)
          with exn ->
            Error
              (sprintf "the checkpoint %s is broken: %s" path
                 (Exn.to_string exn))))
