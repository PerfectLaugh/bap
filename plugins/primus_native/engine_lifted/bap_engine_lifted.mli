(** The lifted backend of {!Bap_engine}. *)

exception Error of int * string

type t = Bap_engine.t
type engine = Bap_engine.engine
type hook = Bap_engine.hook
type context = Bap_engine.context
type arch = Bap_engine.arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

module Mode = Bap_engine.Mode
module Perm = Bap_engine.Perm
module Cpu = Bap_engine.Cpu
module Trace = Bap_engine.Trace

type taint = Bap_engine.taint

type access = Bap_engine.access =
  | Read
  | Write
  | Fetch
  | Read_unmapped
  | Write_unmapped
  | Fetch_unmapped
  | Write_prot
  | Read_prot
  | Fetch_prot
  | Read_after

include
  Bap_engine.S
    with type t := t
     and type hook := hook
     and type context := context

type config = Bap_lifted.config = {
  lift :
    thumb:bool ->
    int64 ->
    string ->
    (int * string * Bap.Std.blk Bap.Std.term list) option;
  name : Bap.Std.tid -> string option;
  policy : int;
  delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
  locate : string -> (int * int * int) option;
  owner : string -> string option;
  pc : int;
  big_endian : bool;
  bits : int;
  jit : bool;
  cache : string option;
}

module Direct : sig
  include Bap_engine.S

  val create : config -> arch -> Mode.t -> t
end

val create : config -> arch -> Mode.t -> t
(** [create config arch mode] opens the lifted engine and erases its backend
    once. *)
