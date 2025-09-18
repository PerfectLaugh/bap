open Core
(** Common BIL type definitions.

    In this module basic types are defined, and it can be considered as an
    internal [Std] module, that should be included most modules, internal to the
    library. *)

open Regular.Std

module Bitvector = Bap_bitvector
(** {2 Basic modules}
    The following modules defines the most basic types, on which the `bap_core`
    library is built. *)

module Integer = Bap_integer
module Trie = Bap_trie

module type Integer = Integer.S
(** {2 Basic Interfaces} *)

module type Trie = Bap_trie_intf.S

type endian = Bitvector.endian = LittleEndian | BigEndian
[@@deriving sexp, bin_io, compare]

module Size = struct
  type all = [ `r8 | `r16 | `r32 | `r64 | `r128 | `r256 ]
  [@@deriving bin_io, compare, sexp, equal, variants]
  (** Defines possible sizes for operations operands *)

  type 'a p = 'a constraint 'a = [< all ]
  [@@deriving bin_io, compare, equal, sexp]

  type t = all p [@@deriving bin_io, compare, equal, sexp]
end

type size = Size.t [@@deriving bin_io, compare, equal, sexp]
(** size of operand *)

type addr_size = [ `r32 | `r64 ] Size.p
[@@deriving bin_io, compare, equal, sexp]
(** size of address *)

type nat1 = int [@@deriving bin_io, compare, equal, sexp]

(** The IR type of a BIL expression *)
module Type = struct
  type t =
    | Imm of nat1  (** [Imm n] - n-bit immediate *)
    | Mem of addr_size * size
        (** [Mem (a,t)]memory with a specified addr_size *)
    | Unk
  [@@deriving bin_io, compare, equal, sexp, variants]
end

type typ = Type.t [@@deriving bin_io, compare, equal, sexp]

(** Supported architectures *)
module Arch = struct
  type x86 = [ `x86 | `x86_64 ] [@@deriving bin_io, compare, enumerate, sexp]

  type arm = [ `armv4 | `armv5 | `armv6 | `armv7 ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type armeb = [ `armv4eb | `armv5eb | `armv6eb | `armv7eb ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type thumb = [ `thumbv4 | `thumbv5 | `thumbv6 | `thumbv7 ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type thumbeb = [ `thumbv4eb | `thumbv5eb | `thumbv6eb | `thumbv7eb ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type aarch64 = [ `aarch64 | `aarch64_be ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type ppc = [ `ppc | `ppc64 | `ppc64le ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type mips = [ `mips | `mipsel | `mips64 | `mips64el ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type sparc = [ `sparc | `sparcv9 ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type nvptx = [ `nvptx | `nvptx64 ]
  [@@deriving bin_io, compare, enumerate, sexp]

  type hexagon = [ `hexagon ] [@@deriving bin_io, compare, enumerate, sexp]
  type r600 = [ `r600 ] [@@deriving bin_io, compare, enumerate, sexp]
  type systemz = [ `systemz ] [@@deriving bin_io, compare, enumerate, sexp]
  type xcore = [ `xcore ] [@@deriving bin_io, compare, enumerate, sexp]
  type unknown = [ `unknown ] [@@deriving bin_io, compare, enumerate, sexp]

  type t =
    [ aarch64
    | arm
    | armeb
    | thumb
    | thumbeb
    | hexagon
    | mips
    | nvptx
    | ppc
    | r600
    | sparc
    | systemz
    | x86
    | xcore
    | unknown ]
  [@@deriving bin_io, compare, enumerate, sexp]
end

(** {2 Common type abbreviations}
    You will see them later. *)

type arch = Arch.t [@@deriving bin_io, compare, sexp]
type word = Bap_bitvector.t [@@deriving bin_io, compare, sexp]
type addr = Bap_bitvector.t [@@deriving bin_io, compare, sexp]
