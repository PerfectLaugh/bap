open Core
open Bap_bil
open Bap_common_types

module Var = Bap_var
module Word = Bap_bitvector

type bytes = (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

let bigarray_of_string input =
  let bytes = Bigarray.Array1.create Bigarray.int8_unsigned Bigarray.c_layout (String.length input) in
  String.iteri input ~f:(fun index value -> bytes.{index} <- Char.to_int value);
  bytes

let string_of_bigarray bytes =
  String.init (Bigarray.Array1.dim bytes) ~f:(fun index -> Char.of_int_exn bytes.{index})

type wire_type = Unknown | Unit | Mem of int * int | Imm of int
type wire_var = { id : int; index : int; typ : wire_type; is_virtual : bool }
type wire_endian = Little | Big
type wire_cast = Low | High | Signed | Unsigned
type wire_unop = Neg | Not
type wire_binop =
  | Add | Sub | Mul | Div | SDiv | Rem | SRem | Mod | LShift | RShift | AShift
  | And | Or | Xor | Eq | Neq | Lt | Le | Gt | Ge | SLt | SLe | SGt | SGe

type wire_exp =
  | Word of int * bytes
  | Var of wire_var
  | Load of wire_exp * wire_exp * wire_endian * int
  | Store of wire_exp * wire_exp * wire_exp * wire_endian * int
  | Bin of wire_binop * wire_exp * wire_exp
  | Un of wire_unop * wire_exp
  | Cast of wire_cast * int * wire_exp
  | Let of wire_var * wire_exp * wire_exp
  | Ite of wire_exp * wire_exp * wire_exp
  | Extract of int * int * wire_exp
  | Concat of wire_exp * wire_exp
  | Unknown of string * wire_type

type wire_stmt =
  | Move of wire_var * wire_exp
  | Jmp of wire_exp
  | Special of string
  | While of wire_exp * wire_stmt list
  | If of wire_exp * wire_stmt list * wire_stmt list
  | CpuExn of int

type env = { vars : Var.t array }
type encoder = { mutable vars_rev : Var.t list; ids : int Var.Table.t }

let create_encoder () = { vars_rev = []; ids = Var.Table.create () }

let intern encoder var =
  Hashtbl.find_or_add encoder.ids var ~default:(fun () ->
      let id = List.length encoder.vars_rev in
      encoder.vars_rev <- var :: encoder.vars_rev;
      id)

let finish_encoder encoder = { vars = Array.of_list_rev encoder.vars_rev }

let rec typ = function
  | Type.Imm width -> Imm width
  | Type.Mem (address, value) -> Mem (Bap_size.in_bits address, Bap_size.in_bits value)
  | Type.Unk -> Unknown

let typ_of_wire = function
  | Imm width -> Type.Imm width
  | Mem (address, value) -> Type.Mem (Bap_size.addr_of_int_exn address, Bap_size.of_int_exn value)
  | Unknown -> Type.Unk
  | Unit -> Type.Unk

let var encoder value =
  {
    id = intern encoder value;
    index = Var.index value;
    typ = typ (Var.typ value);
    is_virtual = Var.is_virtual value;
  }

let var_of_wire env value = Var.with_index env.vars.(value.id) value.index

let word value =
  Word (Word.bitwidth value, bigarray_of_string (Bitvec.to_binary (Word.to_bitvec value)))

let word_of_wire width value =
  Word.create (Bitvec.of_binary (string_of_bigarray value)) width

let endian = function LittleEndian -> Little | BigEndian -> Big
let endian_of_wire = function Little -> LittleEndian | Big -> BigEndian

let cast = function
  | Cast.LOW -> Low
  | Cast.HIGH -> High
  | Cast.SIGNED -> Signed
  | Cast.UNSIGNED -> Unsigned

let cast_of_wire = function
  | Low -> Cast.LOW
  | High -> Cast.HIGH
  | Signed -> Cast.SIGNED
  | Unsigned -> Cast.UNSIGNED

let binop = function
  | Binop.PLUS -> Add
  | Binop.MINUS -> Sub
  | Binop.TIMES -> Mul
  | Binop.DIVIDE -> Div
  | Binop.SDIVIDE -> SDiv
  | Binop.MOD -> Rem
  | Binop.SMOD -> Mod
  | Binop.LSHIFT -> LShift
  | Binop.RSHIFT -> RShift
  | Binop.ARSHIFT -> AShift
  | Binop.AND -> And
  | Binop.OR -> Or
  | Binop.XOR -> Xor
  | Binop.EQ -> Eq
  | Binop.NEQ -> Neq
  | Binop.LT -> Lt
  | Binop.LE -> Le
  | Binop.SLT -> SLt
  | Binop.SLE -> SLe

let binop_of_wire = function
  | Add -> Binop.PLUS
  | Sub -> Binop.MINUS
  | Mul -> Binop.TIMES
  | Div -> Binop.DIVIDE
  | SDiv -> Binop.SDIVIDE
  | Rem -> Binop.MOD
  | Mod -> Binop.SMOD
  | LShift -> Binop.LSHIFT
  | RShift -> Binop.RSHIFT
  | AShift -> Binop.ARSHIFT
  | And -> Binop.AND
  | Or -> Binop.OR
  | Xor -> Binop.XOR
  | Eq -> Binop.EQ
  | Neq -> Binop.NEQ
  | Lt -> Binop.LT
  | Le -> Binop.LE
  | SLt -> Binop.SLT
  | SLe -> Binop.SLE
  | Gt | Ge | SRem | SGt | SGe -> failwith "unsupported BAP binary operator"

let unop = function Unop.NEG -> Neg | Unop.NOT -> Not
let unop_of_wire = function Neg -> Unop.NEG | Not -> Unop.NOT

let rec exp encoder = function
  | Exp.Int value -> word value
  | Exp.Var value -> Var (var encoder value)
  | Exp.Load (memory, address, edn, size) ->
      Load (exp encoder memory, exp encoder address, endian edn, Bap_size.in_bits size / 8)
  | Exp.Store (memory, address, value, edn, size) ->
      Store (exp encoder memory, exp encoder address, exp encoder value, endian edn, Bap_size.in_bits size / 8)
  | Exp.BinOp (operation, left, right) -> Bin (binop operation, exp encoder left, exp encoder right)
  | Exp.UnOp (operation, value) -> Un (unop operation, exp encoder value)
  | Exp.Cast (operation, size, value) -> Cast (cast operation, size, exp encoder value)
  | Exp.Let (variable, value, body) -> Let (var encoder variable, exp encoder value, exp encoder body)
  | Exp.Ite (condition, yes, no) -> Ite (exp encoder condition, exp encoder yes, exp encoder no)
  | Exp.Extract (high, low, value) -> Extract (high, low, exp encoder value)
  | Exp.Concat (left, right) -> Concat (exp encoder left, exp encoder right)
  | Exp.Unknown (message, typ') -> Unknown (message, typ typ')

let rec exp_of_wire env = function
  | Word (width, value) -> Exp.Int (word_of_wire width value)
  | Var value -> Exp.Var (var_of_wire env value)
  | Load (memory, address, edn, size) ->
      Exp.Load (exp_of_wire env memory, exp_of_wire env address, endian_of_wire edn, Bap_size.of_int_exn (size * 8))
  | Store (memory, address, value, edn, size) ->
      Exp.Store
        ( exp_of_wire env memory,
          exp_of_wire env address,
          exp_of_wire env value,
          endian_of_wire edn,
          Bap_size.of_int_exn (size * 8) )
  | Bin (operation, left, right) ->
      Exp.BinOp (binop_of_wire operation, exp_of_wire env left, exp_of_wire env right)
  | Un (operation, value) -> Exp.UnOp (unop_of_wire operation, exp_of_wire env value)
  | Cast (operation, size, value) -> Exp.Cast (cast_of_wire operation, size, exp_of_wire env value)
  | Let (variable, value, body) ->
      Exp.Let (var_of_wire env variable, exp_of_wire env value, exp_of_wire env body)
  | Ite (condition, yes, no) ->
      Exp.Ite (exp_of_wire env condition, exp_of_wire env yes, exp_of_wire env no)
  | Extract (high, low, value) -> Exp.Extract (high, low, exp_of_wire env value)
  | Concat (left, right) -> Exp.Concat (exp_of_wire env left, exp_of_wire env right)
  | Unknown (message, typ) -> Exp.Unknown (message, typ_of_wire typ)

let rec stmt encoder = function
  | Stmt.Move (variable, value) -> Move (var encoder variable, exp encoder value)
  | Stmt.Jmp target -> Jmp (exp encoder target)
  | Stmt.Special message -> Special message
  | Stmt.While (condition, body) -> While (exp encoder condition, List.map body ~f:(stmt encoder))
  | Stmt.If (condition, yes, no) ->
      If (exp encoder condition, List.map yes ~f:(stmt encoder), List.map no ~f:(stmt encoder))
  | Stmt.CpuExn number -> CpuExn number

let rec stmt_of_wire env = function
  | Move (variable, value) -> Stmt.Move (var_of_wire env variable, exp_of_wire env value)
  | Jmp target -> Stmt.Jmp (exp_of_wire env target)
  | Special message -> Stmt.Special message
  | While (condition, body) -> Stmt.While (exp_of_wire env condition, List.map body ~f:(stmt_of_wire env))
  | If (condition, yes, no) ->
      Stmt.If (exp_of_wire env condition, List.map yes ~f:(stmt_of_wire env), List.map no ~f:(stmt_of_wire env))
  | CpuExn number -> Stmt.CpuExn number

let encode bil =
  let encoder = create_encoder () in
  let wire = List.map bil ~f:(stmt encoder) in
  (finish_encoder encoder, wire)

let decode env = List.map ~f:(stmt_of_wire env)
