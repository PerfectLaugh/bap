open Core
open Bap_core_theory
open Bap.Std
open Bil.Types
module P = Bap_protobuf_ir

type fmt = [ `pb | `json ] [@@deriving sexp, enumerate]

let malformed what = invalid_argf "Bil_proto: no %s in the message" what ()
let required what = function Some x -> x | None -> malformed what
let int32 = Int32.of_int_exn
let int = Int32.to_int_exn

let encode fmt encode_pb encode_json x =
  match fmt with
  | `pb ->
      let encoder = Pbrt.Encoder.create () in
      encode_pb x encoder;
      Pbrt.Encoder.to_string encoder
  | `json -> Yojson.Basic.to_string (encode_json x)

let decode fmt decode_pb decode_json s =
  match fmt with
  | `pb -> decode_pb (Pbrt.Decoder.of_string s)
  | `json -> decode_json (Yojson.Basic.from_string s)

let cast_to_proto : cast -> P.cast_type = function
  | UNSIGNED -> Unsigned
  | SIGNED -> Signed
  | HIGH -> High
  | LOW -> Low

let cast_of_proto : P.cast_type -> cast = function
  | Unsigned -> UNSIGNED
  | Signed -> SIGNED
  | High -> HIGH
  | Low -> LOW

let unop_to_proto : unop -> P.unop_type = function NEG -> Neg | NOT -> Not
let unop_of_proto : P.unop_type -> unop = function Neg -> NEG | Not -> NOT

let binop_to_proto : binop -> P.binop_type = function
  | PLUS -> Plus
  | MINUS -> Minus
  | TIMES -> Times
  | DIVIDE -> Divide
  | SDIVIDE -> Sdivide
  | MOD -> Mod
  | SMOD -> Smod
  | LSHIFT -> Lshift
  | RSHIFT -> Rshift
  | ARSHIFT -> Arshift
  | AND -> And
  | OR -> Or
  | XOR -> Xor
  | EQ -> Eq
  | NEQ -> Neq
  | LT -> Lt
  | LE -> Le
  | SLT -> Slt
  | SLE -> Sle

let binop_of_proto : P.binop_type -> binop = function
  | Plus -> PLUS
  | Minus -> MINUS
  | Times -> TIMES
  | Divide -> DIVIDE
  | Sdivide -> SDIVIDE
  | Mod -> MOD
  | Smod -> SMOD
  | Lshift -> LSHIFT
  | Rshift -> RSHIFT
  | Arshift -> ARSHIFT
  | And -> AND
  | Or -> OR
  | Xor -> XOR
  | Eq -> EQ
  | Neq -> NEQ
  | Lt -> LT
  | Le -> LE
  | Slt -> SLT
  | Sle -> SLE

let endian_to_proto : endian -> P.endian = function
  | LittleEndian -> Little_endian
  | BigEndian -> Big_endian

let endian_of_proto : P.endian -> endian = function
  | Little_endian -> LittleEndian
  | Big_endian -> BigEndian

let size_to_proto s = int32 (Size.in_bits s)
let size_of_proto s = Size.of_int_exn (int s)

let typ_to_proto : typ -> P.typ = function
  | Imm n -> Imm (int32 n)
  | Mem (addr, elt) ->
      Mem
        (P.make_mem_type ~addr_size:(size_to_proto addr)
           ~elt_size:(size_to_proto elt) ())
  | Unk -> Unk

let typ_of_proto : P.typ -> typ = function
  | Imm n -> Imm (int n)
  | Mem { addr_size; elt_size; _ } ->
      Mem (Size.addr_of_int_exn (int addr_size), size_of_proto elt_size)
  | Unk -> Unk

(* the name is the identity of the variable, which, unlike its name,
   tells its index and the virtual variable, e.g., #42 *)
let var_to_proto v =
  P.make_var
    ~name:(Theory.Var.Ident.to_string (Var.ident v))
    ~index:(int32 (Var.index v))
    ~typ:(typ_to_proto (Var.typ v))
    ~is_virtual:(Var.is_virtual v) ()

(* the sort of the variables of the type [typ] *)
let sort_of_typ typ = Var.sort (Var.create "sort" typ)

let var_of_proto ({ name; typ; _ } : P.var) =
  let typ = typ_of_proto (required "type of the variable" typ) in
  Var.reify
    (Theory.Var.create (sort_of_typ typ) (Theory.Var.Ident.of_string name))

let rec exp_to_proto : exp -> P.expr = function
  | Load (mem, addr, endian, size) ->
      Load
        (P.make_load ~memory:(exp_to_proto mem) ~address:(exp_to_proto addr)
           ~endian:(endian_to_proto endian) ~size:(size_to_proto size) ())
  | Store (mem, addr, value, endian, size) ->
      Store
        (P.make_store ~memory:(exp_to_proto mem) ~address:(exp_to_proto addr)
           ~value:(exp_to_proto value) ~endian:(endian_to_proto endian)
           ~size:(size_to_proto size) ())
  | BinOp (op, lhs, rhs) ->
      Binop
        (P.make_binop ~op:(binop_to_proto op) ~lhs:(exp_to_proto lhs)
           ~rhs:(exp_to_proto rhs) ())
  | UnOp (op, arg) ->
      Unop (P.make_unop ~op:(unop_to_proto op) ~arg:(exp_to_proto arg) ())
  | Var v -> Var (var_to_proto v)
  | Int w -> Word (Word.to_string w)
  | Cast (kind, size, arg) ->
      Cast
        (P.make_cast ~kind:(cast_to_proto kind) ~size:(int32 size)
           ~arg:(exp_to_proto arg) ())
  | Let (v, def, body) ->
      Let_exp
        (P.make_let_exp ~bound:(var_to_proto v) ~definition:(exp_to_proto def)
           ~body:(exp_to_proto body) ())
  | Unknown (descr, typ) ->
      Unknown (P.make_unknown ~descr ~typ:(typ_to_proto typ) ())
  | Ite (cond, yes, no) ->
      Ite
        (P.make_ite ~cond:(exp_to_proto cond) ~if_true:(exp_to_proto yes)
           ~if_false:(exp_to_proto no) ())
  | Extract (hi, lo, arg) ->
      Extract
        (P.make_extract ~hi:(int32 hi) ~lo:(int32 lo) ~arg:(exp_to_proto arg) ())
  | Concat (lhs, rhs) ->
      Concat (P.make_concat ~lhs:(exp_to_proto lhs) ~rhs:(exp_to_proto rhs) ())

let rec exp_of_proto : P.expr -> exp = function
  | Load { memory; address; endian; size; _ } ->
      Load
        ( sub "memory" memory,
          sub "address" address,
          endian_of_proto endian,
          size_of_proto size )
  | Store { memory; address; value; endian; size; _ } ->
      Store
        ( sub "memory" memory,
          sub "address" address,
          sub "value" value,
          endian_of_proto endian,
          size_of_proto size )
  | Binop { op; lhs; rhs; _ } ->
      BinOp (binop_of_proto op, sub "operand" lhs, sub "operand" rhs)
  | Unop { op; arg; _ } -> UnOp (unop_of_proto op, sub "operand" arg)
  | Var v -> Var (var_of_proto v)
  | Word w -> Int (Word.of_string w)
  | Cast { kind; size; arg; _ } ->
      Cast (cast_of_proto kind, int size, sub "operand" arg)
  | Let_exp { bound; definition; body; _ } ->
      Let
        ( var_of_proto (required "bound variable" bound),
          sub "definition" definition,
          sub "body" body )
  | Unknown { descr; typ; _ } ->
      Unknown (descr, typ_of_proto (required "type" typ))
  | Ite { cond; if_true; if_false; _ } ->
      Ite (sub "condition" cond, sub "branch" if_true, sub "branch" if_false)
  | Extract { hi; lo; arg; _ } -> Extract (int hi, int lo, sub "operand" arg)
  | Concat { lhs; rhs; _ } -> Concat (sub "operand" lhs, sub "operand" rhs)

and sub what exp = exp_of_proto (required what exp)

let rec stmt_to_proto : stmt -> P.stmt = function
  | Move (v, exp) ->
      Move (P.make_move ~lhs:(var_to_proto v) ~rhs:(exp_to_proto exp) ())
  | Jmp dst -> Jmp (exp_to_proto dst)
  | Special s -> Special s
  | While (cond, body) ->
      While_stmt
        (P.make_while_stmt ~cond:(exp_to_proto cond)
           ~body:(bil_to_proto body) ())
  | If (cond, yes, no) ->
      If_stmt
        (P.make_if_stmt ~cond:(exp_to_proto cond) ~yes:(bil_to_proto yes)
           ~no:(bil_to_proto no) ())
  | CpuExn n -> Cpuexn (int32 n)

and bil_to_proto bil = List.map ~f:stmt_to_proto bil

let rec stmt_of_proto : P.stmt -> stmt = function
  | Move { lhs; rhs; _ } ->
      Move (var_of_proto (required "variable" lhs), sub "expression" rhs)
  | Jmp dst -> Jmp (exp_of_proto dst)
  | Special s -> Special s
  | While_stmt { cond; body; _ } ->
      While (sub "condition" cond, bil_of_proto body)
  | If_stmt { cond; yes; no; _ } ->
      If (sub "condition" cond, bil_of_proto yes, bil_of_proto no)
  | Cpuexn n -> CpuExn (int n)

and bil_of_proto stmts = List.map ~f:stmt_of_proto stmts

let exp_to_string fmt exp =
  encode fmt P.encode_pb_expr P.encode_json_expr (exp_to_proto exp)

let exp_of_string fmt s =
  decode fmt P.decode_pb_expr P.decode_json_expr s |> exp_of_proto

let stmt_to_string fmt stmt =
  encode fmt P.encode_pb_stmt P.encode_json_stmt (stmt_to_proto stmt)

let stmt_of_string fmt s =
  decode fmt P.decode_pb_stmt P.decode_json_stmt s |> stmt_of_proto

let bil_to_string fmt bil =
  encode fmt P.encode_pb_bil P.encode_json_bil
    (P.make_bil ~stmts:(bil_to_proto bil) ())

let bil_of_string fmt s =
  let ({ stmts; _ } : P.bil) = decode fmt P.decode_pb_bil P.decode_json_bil s in
  bil_of_proto stmts
