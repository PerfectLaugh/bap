open Core
open Bap_core_theory
open Regular.Std
open Bap_common_types

val of_string : string -> arch option

val addr_size : arch -> addr_size

val endian : arch -> endian

val slot : (Theory.program, arch) KB.slot

val unit_slot : (Theory.Unit.cls, arch) KB.slot

include Regular.S with type t := arch
