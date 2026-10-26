(** Structured, opt-in comparison of execution events. *)

type criterion = Bap_emu_slice.location = Reg of string | Mem of int64 * int

type event =
  | Instruction of { pc : int64; thread : int }
  | Block of { pc : int64; size : int; thread : int }
  | Branch of { site : int64; target : int64; taken : bool; thread : int }
  | Call of { site : int64; targets : (int64 * int) list; thread : int }
  | Syscall of { number : int64; args : int64 list; thread : int }
  | Capture of { site : int64; values : int64 list; thread : int }
  | Write of {
      pc : int64;
      addr : int64;
      size : int;
      value : int64;
      thread : int;
    }
[@@deriving compare, equal, sexp]

type kind =
  | Instruction_kind
  | Block_kind
  | Branch_kind
  | Call_kind
  | Syscall_kind
  | Capture_kind
  | Write_kind
[@@deriving compare, equal, sexp]

type address_field = Pc | Site | Target [@@deriving compare, equal, sexp]

type values_field = Arguments | Registers | Targets
[@@deriving compare, equal, sexp]

type side = Left | Right [@@deriving compare, equal, sexp]

type reason =
  | Kind_mismatch of { left : kind; right : kind }
  | Thread_mismatch of { left : int; right : int }
  | Address_mismatch of { field : address_field; left : int64; right : int64 }
  | Size_mismatch of { left : int; right : int }
  | Taken_mismatch of { left : bool; right : bool }
  | Number_mismatch of { left : int64; right : int64 }
  | Values_mismatch of {
      field : values_field;
      position : int;
      left : int64;
      right : int64;
    }
  | Values_length_mismatch of { field : values_field; left : int; right : int }
  | Call_count_mismatch of { target : int64; left : int; right : int }
  | Memory_address_mismatch of {
      left : int64;
      right : int64;
      size : int;
      criterion : criterion;
    }
  | Memory_size_mismatch of {
      left : int;
      right : int;
      addr : int64;
      criterion : criterion;
    }
  | Memory_value_mismatch of {
      left : int64;
      right : int64;
      addr : int64;
      size : int;
      criterion : criterion;
    }
  | Missing of { side : side; expected : kind }
[@@deriving compare, equal, sexp]

type normalize = { address : int64 -> int64; value : int64 -> int64 }

val normalization :
  ?address:(int64 -> int64) -> ?value:(int64 -> int64) -> unit -> normalize
(** [normalization ()] is the identity normalization. [address] applies to every
    instruction, branch, call, capture, and memory address, and [value] to every
    syscall argument, captured register, and written value. *)

type difference = {
  index : int;
  reason : reason;
  before : event list;
  left : event list;
  right : event list;
}
[@@deriving compare, equal, sexp]

type result = Equal | Difference of difference
[@@deriving compare, equal, sexp]

val compare :
  ?context:int -> ?normalize:normalize -> event list -> event list -> result
(** [compare left right] compares corresponding events and stops at the first
    difference, or when only one sequence remains. With [context], by default 3,
    [before] contains at most that many original events immediately before the
    difference, and [left] and [right] contain at most that many original events
    starting at it. Normalization affects equality and the values in [reason],
    not the events retained in the neighborhood. A memory [criterion] uses the
    original address and size of the left write. Raises [Invalid_argument] if
    [context] is negative. *)

val syscall : thread:int -> int64 -> int64 list -> event
(** [syscall ~thread number args] constructs an event from the arguments of
    [Emu.on_syscall]. *)
