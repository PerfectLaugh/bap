(** The Unicorn backend of {!Bap_engine}. *)

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

module Direct : sig
  include Bap_engine.S

  val create : arch -> Mode.t -> t
end

val create : arch -> Mode.t -> t
(** [create arch mode] opens Unicorn and erases its backend once. *)

val version : unit -> int * int
val supported : arch -> bool
val regs : arch -> (string * int) list
val reg : arch -> string -> int option
val interrupted : unit -> bool
val process_signals : unit -> unit
