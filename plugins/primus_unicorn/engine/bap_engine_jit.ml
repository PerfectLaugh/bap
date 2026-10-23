(* The blocks of the lifted engine, that the JIT of LLVM compiles, see
   bap_engine_lifted.ml, which runs them.

   A block is the instructions, that run one after another, the IR of
   whose semantics are the functions of LLVM IR

     i32 @block(ptr %frame, ptr %regs)

   whose registers are the slots of [%regs], the pointers to the bytes of
   the registers of the engine, which are read at the start of the block,
   and written at the end of each instruction, which writes them, so that
   the instruction, whose access faults, writes none. The frame is the
   one of bap_engine_jit_stubs.c, and the accesses to the memory are the
   calls of its functions, which return zero, if they fault.

   The block returns 4k, if its instruction k stopped, before it ran,
   e.g., as its access faulted, or it divided by zero, so that the engine
   runs it, 4k + 1, if the instruction k jumped to the target, which is
   in the frame, and 4k + 2, if it is the last instruction, which didn't
   jump. The instructions, that the block can't run, e.g., that call an
   intrinsic, or that have delay slots, are not in it. *)

open Core
open Bap.Std

type insn = {
  pc : int64;
  next : int64;  (** the address after the instruction *)
  blks : blk term list;
}

exception Unsupported of string

let unsupported fmt = ksprintf (fun msg -> raise (Unsupported msg)) fmt

type value =
  | Val of string * int  (** the operand, and its width *)
  | Mem of (string * string * int * endian) list
      (** the stores, the latest first, their addresses, the values, of
          their widths, which are the sizes, in bits *)

type t = {
  locate : string -> (int * int * int) option;
  reg_size : int -> int;
  body : Buffer.t;
  slots : (int, int) Hashtbl.t;  (** the registers of the slots *)
  mutable temps : int;
  mutable vars : (string * int) list;  (** the allocas of the variables *)
  mutable decls : String.Set.t;  (** the intrinsics of LLVM *)
}

type insn_state = {
  k : int;
  ins : insn;
  index : tid -> int option;
  mutable written : Int.Set.t;  (** the slots, that the instruction writes *)
  mutable lets : (string * value) list;
  mutable virtuals : (string * (string * int)) list;
}

let emit t fmt = ksprintf (fun s -> Buffer.add_string t.body s) fmt

let fresh t =
  t.temps <- t.temps + 1;
  sprintf "%%t%d" t.temps

let label t =
  t.temps <- t.temps + 1;
  sprintf "l%d" t.temps

let start t l = emit t "%s:\n" l

(* the constant of the bits of [x], of the width [w], which LLVM reads
   signed *)
let const w (z : Z.t) =
  let z = Z.extract z 0 w in
  let z = if Z.testbit z (w - 1) then Z.sub z (Z.shift_left Z.one w) else z in
  Z.to_string z

let of_word x =
  let w = Word.bitwidth x in
  Val (const w (Bitvec.to_bigint (Word.to_bitvec x)), w)

let ty w = sprintf "i%d" w

let assign t fmt =
  ksprintf
    (fun rhs ->
      let r = fresh t in
      emit t "  %s = %s\n" r rhs;
      r)
    fmt

(* [resize t x w w'] the bits of [x], of the width [w], zero extended or
   truncated to [w'] *)
let resize t x w w' =
  if w = w' then x
  else if w < w' then assign t "zext %s %s to %s" (ty w) x (ty w')
  else assign t "trunc %s %s to %s" (ty w) x (ty w')

let sresize t x w w' =
  if w = w' then x
  else if w < w' then assign t "sext %s %s to %s" (ty w) x (ty w')
  else assign t "trunc %s %s to %s" (ty w) x (ty w')

let value = function
  | Val (x, w) -> (x, w)
  | Mem _ -> unsupported "a memory as a value"

let slot t id =
  match Hashtbl.find t.slots id with
  | Some i -> i
  | None ->
      let i = Hashtbl.length t.slots in
      Hashtbl.set t.slots ~key:id ~data:i;
      i

let reg_width t id = t.reg_size id * 8

let declare t decl = t.decls <- Set.add t.decls decl

let bswap t x w =
  if w = 8 then x
  else begin
    declare t (sprintf "declare %s @llvm.bswap.%s(%s)" (ty w) (ty w) (ty w));
    assign t "call %s @llvm.bswap.%s(%s %s)" (ty w) (ty w) (ty w) x
  end

(* the virtual variable of the instruction, an alloca of the block *)
let virtual_var t s name w =
  match List.Assoc.find s.virtuals name ~equal:String.equal with
  | Some (p, w') when w = w' -> p
  | Some _ -> unsupported "the variable %s of two widths" name
  | None ->
      let p = sprintf "%%v%d" (List.length t.vars) in
      t.vars <- (p, w) :: t.vars;
      s.virtuals <- (name, (p, w)) :: s.virtuals;
      p

let width_of_var v =
  match Var.typ v with
  | Imm n -> n
  | Mem _ -> unsupported "a memory variable %s" (Var.name v)
  | Unk -> unsupported "an untyped %s" (Var.name v)

let read_var t s v =
  let name = Var.name v in
  match List.Assoc.find s.lets name ~equal:String.equal with
  | Some x -> x
  | None when Var.is_virtual v ->
      let w = width_of_var v in
      let p = virtual_var t s name w in
      Val (assign t "load %s, ptr %s" (ty w) p, w)
  | None -> (
      match t.locate name with
      | Some (id, lo, width) ->
          let i = slot t id and size = reg_width t id in
          let x = assign t "load %s, ptr %%sh%d" (ty size) i in
          let x =
            if lo = 0 then x else assign t "lshr %s %s, %d" (ty size) x lo
          in
          Val (resize t x size width, width)
      | None -> (
          match Var.typ v with
          | Mem _ -> Mem []
          | _ -> unsupported "the register %s, that is not mapped" name))

(* the access to the memory, which stops the instruction, if it faults *)
let access t s ~load addr bytes =
  if bytes > 64 then unsupported "an access of %d bytes" bytes;
  let ok =
    assign t "call i32 @bap_jit_%s(ptr %%f, i64 %s, i32 %d, ptr %%buf)"
      (if load then "load" else "store")
      addr bytes
  in
  let failed = assign t "icmp eq i32 %s, 0" ok in
  let l = label t in
  emit t "  br i1 %s, label %%i%d.stop, label %%%s\n" failed s.k l;
  start t l

let load t s addr endian bits =
  let bytes = bits / 8 in
  access t s ~load:true addr bytes;
  let x = assign t "load %s, ptr %%buf, align 1" (ty bits) in
  match endian with
  | LittleEndian -> x
  | BigEndian -> bswap t x bits

let store t s (addr, x, bits, endian) =
  let x = match endian with LittleEndian -> x | BigEndian -> bswap t x bits in
  emit t "  store %s %s, ptr %%buf, align 1\n" (ty bits) x;
  access t s ~load:false addr (bits / 8)

let write_var t s v x =
  let name = Var.name v in
  match x with
  | Mem stores -> (
      match (Var.typ v, t.locate name) with
      | Mem _, None -> List.iter (List.rev stores) ~f:(store t s)
      | _ -> unsupported "the stores to %s" name)
  | Val (x, w) when Var.is_virtual v ->
      let w' = width_of_var v in
      if w <> w' then unsupported "a value of %d bits to %s" w name;
      emit t "  store %s %s, ptr %s\n" (ty w) x (virtual_var t s name w)
  | Val (x, w) -> (
      match t.locate name with
      | None -> unsupported "the register %s, that is not mapped" name
      | Some (id, lo, width) ->
          let i = slot t id and size = reg_width t id in
          s.written <- Set.add s.written i;
          let x = resize t (resize t x w width) width size in
          let x =
            if lo = 0 && width = size then x
            else
              let ones = Z.(shift_left one width - one) in
              let m = Z.shift_left ones lo in
              let prev = assign t "load %s, ptr %%sh%d" (ty size) i in
              let kept =
                assign t "and %s %s, %s" (ty size) prev
                  (const size (Z.lognot m))
              in
              let x =
                if lo = 0 then x else assign t "shl %s %s, %d" (ty size) x lo
              in
              assign t "or %s %s, %s" (ty size) kept x
          in
          emit t "  store %s %s, ptr %%sh%d\n" (ty size) x i)

let addr64 t x w = resize t x w 64

(* the division, which stops the instruction, if it divides by zero,
   which is the exception of the target, that Primus raises *)
let nonzero t s y w =
  let zero = assign t "icmp eq %s %s, 0" (ty w) y in
  let l = label t in
  emit t "  br i1 %s, label %%i%d.stop, label %%%s\n" zero s.k l;
  start t l

let shift t op x w a wa =
  let wide = Int.max w wa in
  let a = resize t a wa wide in
  let over = assign t "icmp uge %s %s, %d" (ty wide) a w in
  let a = resize t a wide w in
  let shifted =
    assign t "%s %s %s, %s"
      (match op with `shl -> "shl" | `lshr -> "lshr" | `ashr -> "ashr")
      (ty w) x a
  in
  let saturated =
    match op with
    | `ashr -> assign t "ashr %s %s, %d" (ty w) x (w - 1)
    | `shl | `lshr -> "0"
  in
  assign t "select i1 %s, %s %s, %s %s" over (ty w) saturated (ty w) shifted

let binop t s (op : binop) (x, w) (y, w') =
  let same () = if w <> w' then unsupported "the operands of %d and %d bits" w w' in
  let arith name =
    same ();
    Val (assign t "%s %s %s, %s" name (ty w) x y, w)
  and cmp pred =
    same ();
    Val (assign t "icmp %s %s %s, %s" pred (ty w) x y, 1)
  in
  match op with
  | PLUS -> arith "add"
  | MINUS -> arith "sub"
  | TIMES -> arith "mul"
  | DIVIDE ->
      same ();
      nonzero t s y w;
      arith "udiv"
  | MOD ->
      same ();
      nonzero t s y w;
      arith "urem"
  | SDIVIDE | SMOD ->
      same ();
      nonzero t s y w;
      (* the overflow, of the minimum by -1, wraps, as in the closures,
         where LLVM is undefined *)
      let minus1 = assign t "icmp eq %s %s, -1" (ty w) y in
      let y' = assign t "select i1 %s, %s 1, %s %s" minus1 (ty w) (ty w) y in
      let r =
        assign t "%s %s %s, %s"
          (if Poly.equal op SDIVIDE then "sdiv" else "srem")
          (ty w) x y'
      in
      let special =
        if Poly.equal op SDIVIDE then assign t "sub %s 0, %s" (ty w) x else "0"
      in
      Val (assign t "select i1 %s, %s %s, %s %s" minus1 (ty w) special (ty w) r, w)
  | LSHIFT -> Val (shift t `shl x w y w', w)
  | RSHIFT -> Val (shift t `lshr x w y w', w)
  | ARSHIFT -> Val (shift t `ashr x w y w', w)
  | AND -> arith "and"
  | OR -> arith "or"
  | XOR -> arith "xor"
  | EQ -> cmp "eq"
  | NEQ -> cmp "ne"
  | LT -> cmp "ult"
  | LE -> cmp "ule"
  | SLT -> cmp "slt"
  | SLE -> cmp "sle"

let rec exp t s : exp -> value = function
  | Var v -> read_var t s v
  | Int x -> of_word x
  | Load (mem, addr, endian, size) -> (
      let a, aw = value (exp t s addr) in
      let a = addr64 t a aw in
      match exp t s mem with
      | Mem [] -> Val (load t s a endian (Size.in_bits size), Size.in_bits size)
      | Mem _ -> unsupported "a load from the pending stores"
      | Val _ -> unsupported "a load from a value")
  | Store (mem, addr, x, endian, size) -> (
      let a, aw = value (exp t s addr) in
      let a = addr64 t a aw in
      let x, w = value (exp t s x) in
      if w <> Size.in_bits size then unsupported "a store of %d bits" w;
      match exp t s mem with
      | Mem stores -> Mem ((a, x, w, endian) :: stores)
      | Val _ -> unsupported "a store to a value")
  | BinOp (op, x, y) ->
      let x = value (exp t s x) in
      let y = value (exp t s y) in
      binop t s op x y
  | UnOp (op, x) -> (
      let x, w = value (exp t s x) in
      match op with
      | NEG -> Val (assign t "sub %s 0, %s" (ty w) x, w)
      | NOT -> Val (assign t "xor %s %s, -1" (ty w) x, w))
  | Cast (kind, n, x) -> (
      let x, w = value (exp t s x) in
      match kind with
      | UNSIGNED | LOW -> Val (resize t x w n, n)
      | SIGNED -> Val (sresize t x w n, n)
      | HIGH ->
          let x = if w > n then assign t "lshr %s %s, %d" (ty w) x (w - n) else x in
          Val (resize t x w n, n))
  | Let (v, x, body) ->
      let x = exp t s x in
      s.lets <- (Var.name v, x) :: s.lets;
      let r = exp t s body in
      s.lets <- List.tl_exn s.lets;
      r
  | Unknown (_, Imm n) -> Val ("0", n)
  | Unknown _ -> unsupported "an unknown value"
  | Ite (c, x, y) ->
      let c, cw = value (exp t s c) in
      let c = assign t "icmp ne %s %s, 0" (ty cw) c in
      let lx = label t and ly = label t and lj = label t in
      emit t "  br i1 %s, label %%%s, label %%%s\n" c lx ly;
      start t lx;
      let x, w = value (exp t s x) in
      let ex = label t in
      emit t "  br label %%%s\n" ex;
      start t ex;
      emit t "  br label %%%s\n" lj;
      start t ly;
      let y, w' = value (exp t s y) in
      let ey = label t in
      emit t "  br label %%%s\n" ey;
      start t ey;
      emit t "  br label %%%s\n" lj;
      if w <> w' then unsupported "the branches of %d and %d bits" w w';
      start t lj;
      Val (assign t "phi %s [%s, %%%s], [%s, %%%s]" (ty w) x ex y ey, w)
  | Extract (hi, lo, x) ->
      let x, w = value (exp t s x) in
      let wide = Int.max w (hi + 1) in
      let x = resize t x w wide in
      let x = if lo = 0 then x else assign t "lshr %s %s, %d" (ty wide) x lo in
      Val (resize t x wide (hi - lo + 1), hi - lo + 1)
  | Concat (x, y) ->
      let x, a = value (exp t s x) in
      let y, b = value (exp t s y) in
      let w = a + b in
      let x = resize t x a w and y = resize t y b w in
      let x = assign t "shl %s %s, %d" (ty w) x b in
      Val (assign t "or %s %s, %s" (ty w) x y, w)

(* the instruction [k], whose blocks are the labels i<k>b<j>, and which
   ends at i<k>.done, if it doesn't jump, at i<k>.jump, with the target in
   %tgt, if it jumps, and at i<k>.stop, if it stops *)
let insn t k (ins : insn) =
  let blks = Array.of_list ins.blks in
  let index tid =
    Array.findi blks ~f:(fun _ b -> Tid.equal (Term.tid b) tid)
    |> Option.map ~f:fst
  in
  let s = { k; ins; index; written = Int.Set.empty; lets = []; virtuals = [] } in
  emit t "i%d:\n  store i32 0, ptr %%undo\n  br label %%i%db0\n" k k;
  let jump_to a =
    emit t "  store i64 %s, ptr %%tgt\n  br label %%i%d.jump\n" a k
  in
  let goto = function
    | Direct tid -> (
        match index tid with
        (* the jump to the instruction itself, e.g., b . of ARM *)
        | Some 0 -> jump_to (Int64.to_string ins.pc)
        | Some i -> emit t "  br label %%i%db%d\n" k i
        | None -> unsupported "a call of %s" (Tid.name tid))
    | Indirect e ->
        let a, w = value (exp t s e) in
        let a = addr64 t a w in
        let next = assign t "icmp eq i64 %s, %Ld" a ins.next in
        let l = label t in
        emit t "  br i1 %s, label %%i%d.done, label %%%s\n" next k l;
        start t l;
        jump_to a
  in
  Array.iteri blks ~f:(fun j blk ->
      emit t "i%db%d:\n" k j;
      Term.enum def_t blk
      |> Seq.iter ~f:(fun def -> write_var t s (Def.lhs def) (exp t s (Def.rhs def)));
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp ->
          let c, w = value (exp t s (Jmp.cond jmp)) in
          let c = assign t "icmp ne %s %s, 0" (ty w) c in
          let taken = label t and rest = label t in
          emit t "  br i1 %s, label %%%s, label %%%s\n" c taken rest;
          start t taken;
          (match Jmp.kind jmp with
          | Goto label | Ret label -> goto label
          | Call c -> (
              match Call.target c with
              | Indirect e ->
                  let a, w = value (exp t s e) in
                  jump_to (addr64 t a w)
              | label -> goto label)
          | Int _ -> unsupported "an interrupt");
          start t rest);
      if j + 1 < Array.length blks then emit t "  br label %%i%db%d\n" k (j + 1)
      else emit t "  br label %%i%d.done\n" k);
  if Array.is_empty blks then emit t "i%db0:\n  br label %%i%d.done\n" k k;
  let commit () =
    Set.iter s.written ~f:(fun i ->
        let id =
          Hashtbl.to_alist t.slots
          |> List.find_map_exn ~f:(fun (id, i') -> Option.some_if (i = i') id)
        in
        let size = reg_width t id in
        let x = assign t "load %s, ptr %%sh%d" (ty size) i in
        emit t "  store %s %s, ptr %%rp%d, align 1\n" (ty size) x i)
  in
  emit t "i%d.done:\n" k;
  commit ();
  emit t "  br label %%i%d\n" (k + 1);
  emit t "i%d.jump:\n" k;
  commit ();
  let a = assign t "load i64, ptr %%tgt" in
  emit t "  store i64 %s, ptr %%next\n  ret i32 %d\n" a ((4 * k) + 1);
  emit t "i%d.stop:\n  ret i32 %d\n" k (4 * k)

let header t name =
  let b = Buffer.create 4096 in
  let add fmt = ksprintf (Buffer.add_string b) fmt in
  add "declare i32 @bap_jit_load(ptr, i64, i32, ptr)\n";
  add "declare i32 @bap_jit_store(ptr, i64, i32, ptr)\n";
  Set.iter t.decls ~f:(fun d -> add "%s\n" d);
  add "define i32 @%s(ptr noalias %%f, ptr noalias %%regs) {\nentry:\n" name;
  add "  %%next = getelementptr inbounds i8, ptr %%f, i64 8\n";
  add "  %%undo = getelementptr inbounds i8, ptr %%f, i64 16\n";
  add "  %%buf = alloca [64 x i8], align 16\n";
  add "  %%tgt = alloca i64\n";
  List.iter (List.rev t.vars) ~f:(fun (p, w) ->
      add "  %s = alloca %s\n  store %s 0, ptr %s\n" p (ty w) (ty w) p);
  Hashtbl.to_alist t.slots
  |> List.sort ~compare:(fun (_, i) (_, j) -> Int.compare i j)
  |> List.iter ~f:(fun (id, i) ->
      let w = reg_width t id in
      add "  %%rpp%d = getelementptr inbounds ptr, ptr %%regs, i64 %d\n" i i;
      add "  %%rp%d = load ptr, ptr %%rpp%d\n" i i;
      add "  %%sh%d = alloca %s\n" i (ty w);
      add "  %%ld%d = load %s, ptr %%rp%d, align 1\n" i (ty w) i;
      add "  store %s %%ld%d, ptr %%sh%d\n" (ty w) i i);
  add "  br label %%i0\n";
  b

type block = {
  ir : string;
  regs : int array;  (** the registers of the slots *)
  length : int;  (** the instructions of the block *)
}

(* [compile ~locate ~reg_size insns] the block of the longest prefix
   of [insns], that it can run, with the reasons, why the next
   instruction is not in it, or [None], if it can't run the first one *)
let compile ~locate ~reg_size insns =
  let t =
    {
      locate;
      reg_size;
      body = Buffer.create 4096;
      slots = Hashtbl.create (module Int);
      temps = 0;
      vars = [];
      decls = String.Set.empty;
    }
  in
  let rec loop k = function
    | [] -> (k, None)
    | ins :: rest -> (
        let saved =
          (Buffer.contents t.body, Hashtbl.copy t.slots, t.vars, t.decls, t.temps)
        in
        match insn t k ins with
        | () -> loop (k + 1) rest
        | exception Unsupported reason ->
            let body, slots, vars, decls, temps = saved in
            Buffer.clear t.body;
            Buffer.add_string t.body body;
            Hashtbl.clear t.slots;
            Hashtbl.iteri slots ~f:(fun ~key ~data -> Hashtbl.set t.slots ~key ~data);
            t.vars <- vars;
            t.decls <- decls;
            t.temps <- temps;
            (k, Some reason))
  in
  let length, reason = loop 0 insns in
  if length = 0 then Error (Option.value reason ~default:"no instructions")
  else begin
    emit t "i%d:\n  ret i32 %d\n}\n" length ((4 * (length - 1)) + 2);
    let b = header t "block" in
    Buffer.add_buffer b t.body;
    let regs = Array.create ~len:(Hashtbl.length t.slots) 0 in
    Hashtbl.iteri t.slots ~f:(fun ~key ~data -> regs.(data) <- key);
    Ok { ir = Buffer.contents b; regs; length }
  end

(* the runtime of the blocks, see bap_engine_jit_stubs.c *)
module Runtime = struct
  type mem

  external create : unit -> mem = "bap_jit_mem_create"

  external map : mem -> int64 -> Core.Bigstring.t -> int -> unit
    = "bap_jit_mem_map"

  external unmap : mem -> int64 -> unit = "bap_jit_mem_unmap"
  external protect : mem -> int64 -> int -> unit = "bap_jit_mem_protect"
  external helpers : unit -> nativeint * nativeint = "bap_jit_helpers"

  external run :
    (nativeint[@unboxed]) ->
    mem ->
    Bytes.t array ->
    string ->
    (int64[@unboxed]) ->
    (int[@untagged]) = "bap_jit_run_byte" "bap_jit_run"
  [@@noalloc]

  external next : mem -> (int64[@unboxed]) = "bap_jit_next_byte" "bap_jit_next"
  [@@noalloc]
end

(* the JIT of the program, whose blocks call the runtime *)
let llvm =
  lazy
    (let jit = Bap_llvm_jit.create () in
     let load, store = Runtime.helpers () in
     Bap_llvm_jit.define jit "bap_jit_load" load;
     Bap_llvm_jit.define jit "bap_jit_store" store;
     jit)

let blocks = ref 0

(* the address of the function of the block *)
let native block =
  incr blocks;
  let name = sprintf "bap_block_%d" !blocks in
  let ir =
    String.substr_replace_first block.ir ~pattern:"@block(" ~with_:("@" ^ name ^ "(")
  in
  Bap_llvm_jit.compile (Lazy.force llvm) ir name
