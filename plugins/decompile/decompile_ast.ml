open Bap.Std

type sign = Signed | Unsigned | Unknown_sign

type typ =
  | Unknown of int
  | Memory
  | Int of int * sign
  | Bool
  | Float of int
  | Pointer of typ
  | Array of typ * int option
  | Structure of string
  | Function of signature

and signature = { return : typ; params : (string * typ) list; variadic : bool }

type variable = { id : int; name : string; typ : typ }

type expression = { node : expr; typ : typ }

and expr =
  | Var of variable
  | Const of word
  | Unary of string * expression
  | Binary of string * expression * expression
  | Cast of typ * expression
  | Deref of expression
  | Address of expression
  | Field of expression * string * int
  | Index of expression * expression
  | Call of call
  | Conditional of expression * expression * expression
  | Machine of string * expression list
  | Raw_exp of exp

and call = { target : expression; arguments : expression list; result : typ }

type stmt =
  | Decl of variable
  | Assign of expression * expression
  | Expr of expression
  | Return of expression option
  | If of expression * stmt list * stmt list
  | While of expression * stmt list
  | Do_while of stmt list * expression
  | Switch of expression * (word * stmt list) list * stmt list option
  | Break
  | Continue
  | Label of string
  | Goto of string
  | Raw_jump of jmp term
  | Comment of string

type func = {
  id : int;
  name : string;
  signature : signature;
  locals : variable list;
  body : stmt list;
  external_ : bool;
}

type structure = { name : string; fields : (string * int * typ) list }
type program = { structures : structure list; functions : func list }

let unknown bits = Unknown bits
let int ?(sign = Unknown_sign) bits = Int (bits, sign)
let pointer typ = Pointer typ
let expr ?(typ = Unknown 0) node = { node; typ }
let var v = { node = Var v; typ = v.typ }

let signature ?(return = Unknown 0) ?(variadic = false) params =
  { return; params; variadic }
