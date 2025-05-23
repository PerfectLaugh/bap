open Core
open Bap_disasm_backend_types

type t = int

external create :
  backend:string ->
  triple:string ->
  cpu:string ->
  attrs:string ->
  debug_level:int -> t =
  "bap_disasm_create_with_attrs_stub" [@@noalloc]


external backends_size : unit -> int =
  "bap_disasm_backends_size_stub" [@@noalloc]

external backend_name : int -> string = "bap_disasm_backend_name_stub"

external delete : t -> unit = "bap_disasm_delete_stub"  [@@noalloc]
external set_memory : t -> int64 -> Bigstring.t -> off:int -> len:int -> unit
  = "bap_disasm_set_memory_stub" [@@noalloc]

external store_predicates : t -> bool -> unit =
  "bap_disasm_store_predicates_stub" [@@noalloc]

external store_asm_string : t -> bool -> unit =
  "bap_disasm_store_asm_strings_stub" [@@noalloc]

external insn_table : t -> Bigstring.t =
  "bap_disasm_insn_table_stub"

external reg_table : t -> Bigstring.t =
  "bap_disasm_reg_table_stub"

external predicates_clear : t -> unit =
  "bap_disasm_predicates_clear_stub" [@@noalloc]

external predicates_push : t -> predicate -> unit =
  "bap_disasm_predicates_push_stub" [@@noalloc]

external is_supported : t -> predicate -> bool =
  "bap_disasm_predicate_is_supported_stub" [@@noalloc]

external set_offset : t -> int -> unit =
  "bap_disasm_set_offset_stub" [@@noalloc]

external offset : t -> int =
  "bap_disasm_offset_stub" [@@noalloc]

external run : t -> unit =
  "bap_disasm_run_stub" [@@noalloc]

external insns_clear : t -> unit =
  "bap_disasm_insns_clear_stub" [@@noalloc]

external insns_size : t -> int =
  "bap_disasm_insns_size_stub" [@@noalloc]

external insn_size : t -> insn:int -> int =
  "bap_disasm_insn_size_stub" [@@noalloc]

external insn_name : t -> insn:int -> int =
  "bap_disasm_insn_name_stub" [@@noalloc]

external insn_code : t -> insn:int -> int =
  "bap_disasm_insn_code_stub" [@@noalloc]

external insn_offset : t -> insn:int -> int =
  "bap_disasm_insn_offset_stub" [@@noalloc]

external insn_asm_size : t -> insn:int -> int =
  "bap_disasm_insn_asm_size_stub" [@@noalloc]

external insn_asm_copy : t -> insn:int -> Bytes.t -> unit =
  "bap_disasm_insn_asm_copy_stub" [@@noalloc]

external insn_satisfies : t -> insn:int -> predicate -> bool =
  "bap_disasm_insn_satisfies_stub" [@@noalloc]

external insn_ops_size : t -> insn:int -> int =
  "bap_disasm_insn_ops_size_stub" [@@noalloc]

external insn_op_type : t -> insn:int -> oper:int -> op =
  "bap_disasm_insn_op_type_stub" [@@noalloc]

external insn_op_reg_name : t -> insn:int -> oper:int -> int =
  "bap_disasm_insn_op_reg_name_stub" [@@noalloc]

external insn_op_reg_code : t -> insn:int -> oper:int -> int =
  "bap_disasm_insn_op_reg_code_stub" [@@noalloc]

external insn_op_imm_value : t -> insn:int -> oper:int -> int64 =
  "bap_disasm_insn_op_imm_value_stub"

external insn_op_imm_small_value : t -> insn:int -> oper:int -> int =
  "bap_disasm_insn_op_imm_small_value_stub" [@@noalloc]


external insn_op_fmm_value : t -> insn:int -> oper:int -> float =
  "bap_disasm_insn_op_fmm_value_stub"
