open Core
open Bap.Std
open Bap_primus_types
module Generator = Bap_primus_generator

val generated : (addr * value) Bap_primus_observation.t

type protection = { readable : bool; writable : bool; executable : bool }
[@@deriving equal]

val protected : (addr * addr * protection) Bap_primus_observation.t
val allocated : (addr * addr) Bap_primus_observation.t

type exn += Pagefault of addr
type exn += Unknown_segment of addr * addr
type memory

module Descriptor : sig
  type t = memory [@@deriving compare, sexp_of]

  val create : addr_size:int -> data_size:int -> string -> memory
  val unknown : addr_size:int -> data_size:int -> memory
  val name : memory -> string
  val addr_size : memory -> int
  val data_size : memory -> int

  include Comparable.S with type t := memory
end

module Backing : sig
  type t = {
    memory : string;
    pending : id -> addr -> bool;
    fetch : id -> addr -> (addr * string) list;
    fetch_all : id -> (addr * string) list;
    peek_all : id -> (addr * string) list;
    stored : id -> addr -> string -> unit;
  }
end

module Snapshot : sig
  type t [@@deriving bin_io]

  val values : t -> (addr * word) list
end

type origin = Stored | Generated | Mapped | Unmapped
[@@deriving compare, equal, sexp]

module Make (Machine : Machine) : sig
  val set_backing : Backing.t option -> unit Machine.t
  val switch : memory -> unit Machine.t
  val memory : memory Machine.t
  val load : addr -> word Machine.t
  val store : addr -> word -> unit Machine.t
  val store_never_fail : addr -> word -> unit Machine.t
  val get : addr -> value Machine.t
  val set : addr -> value -> unit Machine.t
  val set_never_fail : addr -> value -> unit Machine.t
  val del : addr -> unit Machine.t
  val add_text : mem -> unit Machine.t
  val add_data : mem -> unit Machine.t

  val add_region :
    ?readonly:bool ->
    ?executable:bool ->
    ?init:(addr -> word Machine.t) ->
    ?generator:Generator.t ->
    lower:addr ->
    upper:addr ->
    unit ->
    unit Machine.t

  val allocate :
    ?readonly:bool ->
    ?executable:bool ->
    ?init:(addr -> word Machine.t) ->
    ?generator:Generator.t ->
    addr ->
    int ->
    unit Machine.t

  val map : ?readonly:bool -> ?executable:bool -> mem -> unit Machine.t
  val is_mapped : addr -> bool Machine.t
  val is_writable : addr -> bool Machine.t
  val is_executable : addr -> bool Machine.t
  val protection : addr -> protection option Machine.t
  val regions : (addr * addr * protection) list Machine.t
  val origin : addr -> origin Machine.t
  val values_of : ?generated:bool -> id -> (addr * word) list Machine.t
  val origins_of : id -> addr list -> origin list Machine.t
  val peek : addr -> int -> string Machine.t
  val load_bytes : addr -> int -> (char * protection) option array Machine.t
  val store_bytes : addr -> string -> unit Machine.t
  val protect : lower:addr -> upper:addr -> protection -> unit Machine.t
  val snapshot : Snapshot.t Machine.t
  val values : (memory * addr * value) list Machine.t
  val restore : Snapshot.t -> unit Machine.t
end
