(* The symbolic execution of the programs in Primus: the inputs, the
   formulas of the values, that the program computes from them, which
   the Executor component tracks, the constraints of the paths, which the
   Paths component collects, and the SMT solver, that finds the models of
   the constraints, which the symbolic executor, see
   primus_symbolic_executor_main.ml, and the scripts, see Bap_emu.Symbolic,
   use. *)

open Core
open Bap_core_theory
open Bap.Std
open Bap_primus.Std
open Monads.Std

type memory = {
  bank : Primus.Memory.Descriptor.t;
  lower : Addr.t;
  upper : Addr.t;
}
[@@deriving compare, equal]

let memories =
  Primus.Machine.State.declare ~uuid:"15dbb89a-3bfb-421c-8b19-16605425c3f5"
    ~name:"symbolic-memories"
  @@ fun _ -> String.Map.empty

module Bank = Primus.Memory.Descriptor
module Id = Monad.State.Multi.Id

let debug_msg, post_msg =
  Primus.Observation.provide "executor-debug" ~inspect:sexp_of_string

module Debug (Machine : Primus.Machine.S) = struct
  open Machine.Syntax

  let msg fmt =
    Format.kasprintf
      (fun msg ->
        Machine.current () >>= fun id ->
        let msg = Format.asprintf "%a: %s" Id.pp id msg in
        Machine.Observation.make post_msg msg)
      fmt
end

module Input : sig
  type t

  val ptr : Primus.Memory.Descriptor.t -> addr -> t
  val var : var -> t
  val to_symbol : t -> string
  val size : t -> int

  module Make (Machine : Primus.Machine.S) : sig
    val set : t -> Primus.Value.t -> unit Machine.t
  end

  include Base.Comparable.S with type t := t
end = struct
  type t =
    | Var of var
    | Ptr of { bank : Primus.Memory.Descriptor.t; addr : addr }
  [@@deriving compare, sexp_of]

  let ptr bank addr = Ptr { bank; addr }
  let var p = Var p

  let to_symbol = function
    | Var v -> Format.asprintf "%a" Var.pp v
    | Ptr { bank; addr } ->
        Format.asprintf "%s[%a]"
          (Primus.Memory.Descriptor.name bank)
          Addr.pp_hex addr

  let size = function
    | Ptr { bank } -> Primus.Memory.Descriptor.data_size bank
    | Var v -> ( match Var.typ v with Imm m -> m | _ -> 1)

  module Make (Machine : Primus.Machine.S) = struct
    open Machine.Syntax
    module Mems = Primus.Memory.Make (Machine)
    module Env = Primus.Env.Make (Machine)
    module Lisp = Primus.Lisp.Make (Machine)

    let allocate bank lower upper =
      let width = Bank.data_size bank in
      let seed = Hashtbl.hash (Bank.name bank) in
      let generator = Primus.Generator.Random.lcg ~width seed in
      Mems.add_region ~generator ~lower ~upper ()

    let allocate_if_not bank addr =
      Mems.is_writable addr >>= function
      | true -> Machine.return ()
      | false -> (
          let name = Primus.Memory.Descriptor.name bank in
          Machine.Global.get memories >>= fun memories ->
          match Map.find memories name with
          | None -> allocate bank addr addr
          | Some { lower; upper } -> allocate bank lower upper)

    let set input value =
      match input with
      | Ptr { bank; addr } ->
          Mems.memory >>= fun current ->
          Mems.switch bank >>= fun () ->
          allocate_if_not bank addr >>= fun () ->
          Mems.set addr value >>= fun () -> Mems.switch current
      | Var v -> Env.set v value
  end

  include Base.Comparable.Make (struct
    type nonrec t = t [@@deriving compare, sexp_of]
  end)
end

module SMT : sig
  type formula
  type expr
  type value
  type model

  val formula : ?refute:bool -> expr -> formula
  val inverse : formula -> formula
  val word : Word.t -> expr
  val var : string -> int -> expr
  val binop : binop -> expr -> expr -> expr
  val unop : unop -> expr -> expr
  val extract : int -> int -> expr -> expr
  val concat : expr -> expr -> expr
  val ite : expr -> expr -> expr -> expr
  val cast : cast -> int -> expr -> expr
  val check : ?timeout:int -> formula list -> model option

  module Model : sig
    type t = model

    val get : model -> Input.t -> value option
  end

  module Value : sig
    type t = value

    val to_word : value -> word
    val to_formula : value -> formula
    val to_string : value -> string

    include Base.Comparable.S with type t := value
  end

  module Formula : Base.Comparable.S with type t = formula

  val pp_expr : Format.formatter -> expr -> unit
  val pp_formula : Format.formatter -> formula -> unit
  val pp_value : Format.formatter -> value -> unit
  val set_timeout : int -> unit
end = struct
  module Bitv = Z3.BitVector
  module Bool = Z3.Boolean
  module Expr = Z3.Expr
  module Sort = Z3.Sort

  type expr = Expr.expr
  type formula = expr
  type value = expr

  let () = Z3.set_global_param "parallel.enable" "true"
  let ctxt = Z3.mk_context [ ("model", "true"); ("timeout", "16") ]
  let timeout = ref 16

  let set_timeout ms =
    timeout := ms;
    Z3.Params.update_param_value ctxt "timeout" (string_of_int ms)

  let to_string = Expr.to_string
  let pp_expr ppf expr = Format.fprintf ppf "%s" (to_string expr)
  let pp_formula = pp_expr
  let pp_value = pp_expr

  let coerce_shift op ctxt x y =
    let sx = Bitv.get_size (Expr.get_sort x)
    and sy = Bitv.get_size (Expr.get_sort y) in
    if sx = sy then op ctxt x y
    else
      let y = Bitv.mk_zero_ext ctxt (sx - sy) y in
      op ctxt x y

  let z3_of_binop : binop -> _ = function
    | PLUS -> Bitv.mk_add
    | MINUS -> Bitv.mk_sub
    | TIMES -> Bitv.mk_mul
    | DIVIDE -> Bitv.mk_udiv
    | SDIVIDE -> Bitv.mk_sdiv
    | MOD -> Bitv.mk_srem
    | SMOD -> Bitv.mk_urem
    | LSHIFT -> coerce_shift Bitv.mk_shl
    | RSHIFT -> coerce_shift Bitv.mk_lshr
    | ARSHIFT -> coerce_shift Bitv.mk_ashr
    | AND -> Bitv.mk_and
    | OR -> Bitv.mk_or
    | XOR -> Bitv.mk_xor
    | LT -> Bitv.mk_ult
    | LE -> Bitv.mk_ule
    | SLT -> Bitv.mk_slt
    | SLE -> Bitv.mk_sle
    | EQ ->
        fun ctxt x y ->
          Bitv.mk_not ctxt @@ Bitv.mk_redor ctxt @@ Bitv.mk_xor ctxt x y
    | NEQ -> fun ctxt x y -> Bitv.mk_redor ctxt @@ Bitv.mk_xor ctxt x y

  let do_simpl x = try Expr.simplify x None with Z3.Error "canceled" -> x
  let is_literal x = Expr.is_numeral x || Bool.is_true x || Bool.is_false x

  (* simplifies [x] only when all its operands are literals, i.e., folds
     constants. Simplifying a term with symbolic operands rewrites the
     whole term anew on each operation, so they are simplified only
     when they become formulae. *)
  let fold x =
    if List.for_all (Expr.get_args x) ~f:is_literal then do_simpl x else x

  let bit0 = Expr.mk_numeral_int ctxt 0 (Bitv.mk_sort ctxt 1)
  let bit1 = Expr.mk_numeral_int ctxt 1 (Bitv.mk_sort ctxt 1)
  let is_bool = Bool.is_bool

  let bit_of_bool x =
    if Bool.is_bool x then fold @@ Bool.mk_ite ctxt x bit1 bit0 else x

  let bool_of_bit x = fold @@ Bool.mk_eq ctxt x bit1

  let z3_of_unop : unop -> _ = function
    | NEG -> Bitv.mk_neg
    | NOT -> Bitv.mk_not

  let coerce_to_bit x = if is_bool x then bit_of_bool x else x
  let coerce_to_bool x = if is_bool x then x else bool_of_bit x
  let simpl x = fold x |> coerce_to_bit
  let binop op x y = simpl (z3_of_binop op ctxt x y)
  let unop op x = simpl (z3_of_unop op ctxt x)

  let word x =
    let s = Bitv.mk_sort ctxt (Word.bitwidth x) in
    let x = Word.to_bitvec x in
    if Bitvec.fits_int x then Expr.mk_numeral_int ctxt (Bitvec.to_int x) s
    else
      let x = Bitvec.to_bigint x in
      Expr.mk_numeral_string ctxt (Z.to_string x) s

  let extract hi lo x =
    let xs = Bitv.get_size (Expr.get_sort x) and ns = hi - lo + 1 in
    simpl
    @@
    if ns > xs then
      if lo = 0 then Bitv.mk_zero_ext ctxt (ns - xs) x
      else Bitv.mk_extract ctxt hi lo @@ Bitv.mk_zero_ext ctxt (ns - xs) x
    else Bitv.mk_extract ctxt hi lo x

  let concat x y = simpl @@ Bitv.mk_concat ctxt x y
  let ite c x y = simpl @@ Bool.mk_ite ctxt (coerce_to_bool c) x y

  let cast (c : cast) s x =
    let old = Bitv.get_size (Expr.get_sort x) in
    simpl
    @@
    match c with
    | SIGNED ->
        if old < s then Bitv.mk_sign_ext ctxt (s - old) x
        else extract (s - 1) 0 x
    | UNSIGNED ->
        if old < s then Bitv.mk_zero_ext ctxt (s - old) x
        else extract (s - 1) 0 x
    | HIGH -> extract (old - 1) (old - s) x
    | LOW -> extract (s - 1) 0 x

  let var name size = Expr.mk_const_s ctxt name (Bitv.mk_sort ctxt size)

  type model = { model : Z3.Model.model }

  let inverse x = do_simpl @@ Bool.mk_not ctxt x

  let formula ?(refute = false) expr =
    let lhs = Expr.mk_numeral_int ctxt 0 (Expr.get_sort expr) in
    let formula = Bool.mk_eq ctxt lhs expr in
    if refute then do_simpl @@ formula else inverse formula

  module Model = struct
    type t = model

    let get { model } input =
      let var = var (Input.to_symbol input) (Input.size input) in
      match Z3.Model.eval model var false with
      | Some x when Expr.is_numeral x -> Some x
      | _ -> None
  end

  let solver = Z3.Solver.mk_simple_solver ctxt

  (* the [timeout] is of this check, after which the timeout of the
     options is restored *)
  let check ?timeout:ms assertions =
    let default = !timeout in
    Option.iter ms ~f:set_timeout;
    Z3.Solver.push solver;
    Z3.Solver.add solver assertions;
    let result =
      match Z3.Solver.check solver [] with
      | exception Z3.Error "canceled" -> None
      | UNSATISFIABLE | UNKNOWN -> None
      | SATISFIABLE -> (
          match Z3.Solver.get_model solver with
          | None -> None
          | Some model -> Some { model })
    in
    Z3.Solver.pop solver 1;
    if Option.is_some ms then set_timeout default;
    result

  module Formula = struct
    type t = formula

    include Base.Comparable.Make (struct
      type t = formula

      let compare = Expr.compare
      let sexp_of_t x = Sexp.Atom (to_string x)
    end)
  end

  module Value = struct
    type t = value

    let to_formula = Fn.id

    let to_bigint x =
      let s = Expr.to_string x in
      let len = String.length s in
      if String.length s > 2 && Char.(s.[0] = '#') then
        let base =
          match s.[1] with
          | 'b' -> 2
          | 'x' -> 16
          | _ -> failwithf "Not a literal value %s" s ()
        in
        Z.of_substring_base base s ~pos:2 ~len:(len - 2)
      else Z.of_string s

    let to_word x =
      let s = Bitv.get_size (Expr.get_sort x) and z = to_bigint x in
      Word.create Bitvec.(bigint z mod modulus s) s

    let to_string x = Expr.to_string x

    include (Formula : Base.Comparable.S with type t := value)
  end
end

type executor = {
  inputs : Set.M(Input).t;
  values : SMT.expr Primus.Value.Id.Map.t;
}

let executor =
  Primus.Machine.State.declare ~uuid:"e21aa0fe-bc37-48e3-b398-ce7e764843c8"
    ~name:"symbolic-executor-formulae"
  @@ fun _ ->
  { values = Primus.Value.Id.Map.empty; inputs = Set.empty (module Input) }

module Context : sig
  type scope

  module Scope : sig
    type t = scope

    val declare : string -> scope
    val user : scope
    val path : scope

    include Base.Comparable.S with type t := t
  end

  module Make (Machine : Primus.Machine.S) : sig
    val add : scope -> SMT.formula -> unit Machine.t
    val get : scope -> Set.M(SMT.Formula).t Machine.t
  end
end = struct
  type scope = string
  type context = { assertions : Set.M(SMT.Formula).t Map.M(String).t }

  let context =
    Primus.Machine.State.declare ~uuid:"9538b1fa-b6c0-464a-b11e-22377a10b0b6"
      ~name:"symbolic-context"
    @@ fun _ -> { assertions = Map.empty (module String) }

  module Scope = struct
    let scopes = String.Hash_set.create ()

    let declare scope =
      if Hash_set.mem scopes scope then
        invalid_argf "the scope named %s is already declared" scope ();
      scope

    let user = declare "user"
    let path = declare "path"

    include (String : Base.Comparable.S with type t = scope)
  end

  module Make (Machine : Primus.Machine.S) = struct
    open Machine.Syntax

    let add scope x =
      Machine.Local.update context ~f:(fun s ->
          {
            assertions =
              Map.update s.assertions scope ~f:(function
                | None -> Set.singleton (module SMT.Formula) x
                | Some xs -> Set.add xs x);
          })

    let get scope =
      Machine.Local.get context >>| fun s ->
      match Map.find s.assertions scope with
      | None -> Set.empty (module SMT.Formula)
      | Some xs -> xs
  end
end

module Executor (Machine : Primus.Machine.S) : sig
  val value : Primus.Value.t -> SMT.expr option Machine.t
  val inputs : Input.t seq Machine.t
  val init : unit -> unit Machine.t
  val set_input : Input.t -> Primus.Value.t -> unit Machine.t
end = struct
  open Machine.Syntax
  module Value = Primus.Value.Make (Machine)
  module Mems = Primus.Memory.Make (Machine)
  module Debug = Debug (Machine)
  module Ctxt = Context.Make (Machine)
  module Track = Primus.Track.Make (Machine)

  let id = Primus.Value.id
  let value s x = Map.find s.values (id x)
  let word x = SMT.word @@ Primus.Value.to_word x
  let to_formula x = function None -> word x | Some x -> x

  let lift1 x r f =
    Machine.Local.get executor >>= fun s ->
    match value s x with
    | None -> Machine.return ()
    | Some x ->
        Machine.Local.put executor
          { s with values = Map.add_exn s.values ~key:(id r) ~data:(f x) }
        >>= fun () -> Track.track r

  let lift2 x y r f =
    Machine.Local.get executor >>= fun s ->
    match (value s x, value s y) with
    | None, None -> Machine.return ()
    | fx, fy ->
        let x = to_formula x fx and y = to_formula y fy in
        Machine.Local.put executor
          { s with values = Map.add_exn s.values ~key:(id r) ~data:(f x y) }
        >>= fun () -> Track.track r

  let lift3 x y z r f =
    Machine.Local.get executor >>= fun s ->
    match (value s x, value s y, value s z) with
    | None, None, None -> Machine.return ()
    | fx, fy, fz ->
        let x = to_formula x fx
        and y = to_formula y fy
        and z = to_formula z fz in
        Machine.Local.put executor
          { s with values = Map.add_exn s.values ~key:(id r) ~data:(f x y z) }
        >>= fun () -> Track.track r

  let on_binop ((op, x, y), z) = lift2 x y z @@ SMT.binop op
  let on_unop ((op, x), z) = lift1 x z @@ SMT.unop op
  let on_extract ((hi, lo, x), z) = lift1 x z @@ SMT.extract hi lo
  let on_concat ((x, y), z) = lift2 x y z @@ SMT.concat
  let on_ite ((c, x, y), z) = lift3 c x y z @@ SMT.ite
  let on_cast ((c, w, x), z) = lift1 x z @@ SMT.cast c w

  let set_input origin v =
    let id = Primus.Value.id v in
    let size = Input.size origin in
    let x = SMT.var (Input.to_symbol origin) size in
    Machine.Local.update executor ~f:(fun s ->
        {
          inputs = Set.add s.inputs origin;
          values = Map.set s.values ~key:id ~data:x;
        })
    >>= fun () -> Track.track v

  let on_memory_input (p, x) =
    Mems.memory >>= fun desc -> set_input (Input.ptr desc p) x

  let on_env_input (v, x) = set_input (Input.var v) x
  let inputs = Machine.Local.get executor >>| fun s -> Set.to_sequence s.inputs
  let value v = Machine.Local.get executor >>| fun s -> value s v

  let init () =
    Machine.sequence
      Primus.Interpreter.
        [
          binop >>> on_binop;
          unop >>> on_unop;
          extract >>> on_extract;
          concat >>> on_concat;
          ite >>> on_ite;
          cast >>> on_cast;
          Primus.Memory.generated >>> on_memory_input;
          Primus.Env.generated >>> on_env_input;
        ]
end

module Paths (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Constraints = Context.Make (Machine)
  module Executor = Executor (Machine)
  module Value = Primus.Value.Make (Machine)

  let add_constraint x =
    Executor.value x >>= function
    | None -> Machine.return ()
    | Some v ->
        Constraints.add Context.Scope.path
        @@ SMT.formula ~refute:(Value.is_zero x) v

  let init () = Primus.Interpreter.eval_cond >>> add_constraint
end
