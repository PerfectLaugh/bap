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
    extra : (int * string) list;
        (** the registers of Unicorn, that Primus doesn't have, e.g., of TLS, by
            their ids *)
    threads : threads option;
        (** the threads, if the program created them, which switch in the run,
            from which Unicorn continues *)
  }
  [@@deriving bin_io]
end

include T

let magic = "bap-primus-unicorn-checkpoint 5\n"

(* the digest of the file of the program, which the checkpoint is of *)
let digest path = Stdlib.Digest.(to_hex (file path))

(* the checkpoint is written to a temporary file first, so that the file
   is never partly written, which is new, rather than a file of a known
   name, which another user may have made, e.g., a link, in a directory,
   that they can write *)
let save path t =
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
        Error msg)

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
