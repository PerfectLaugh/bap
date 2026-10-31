(* The blocks of the lifted engine, that the JIT of LLVM compiles, see
   bap_lifted.ml, which runs them.

   A block is the instructions, that run one after another, the IR of
   whose semantics are the functions of LLVM IR

     i32 @block(ptr %frame, ptr %regs)

   whose registers are the slots of [%regs], the pointers to the bytes of
   the registers of the engine, which are read at the start of the block,
   and written, when it ends, so that LLVM removes the values, that the
   block doesn't keep, e.g., the flags, that the next instruction sets
   again. The instruction, whose access faults, writes none: the block,
   that it stops, writes the registers, as the previous instructions
   left them, which each instruction copies, before it changes them. The frame is the
   one of bap_lifted_jit_stubs.c, and the accesses to the memory are the
   calls of its functions, which return zero, if they fault.

   The block returns 4k, if its instruction k stopped, before it ran,
   e.g., as its access faulted, or it divided by zero, so that the engine
   runs it, 4k + 1, if the instruction k jumped to the target, which is
   in the frame, 4k + 2, if it is the last instruction, which didn't
   jump, and 4k + 3, if the instruction k, the delay slot of the branch
   before it, that jumps to the target, which is in the frame, stopped,
   so that the engine runs it, and then jumps. The instructions, that the block can't run, e.g., that call an
   intrinsic, or that have delay slots, are not in it.

   The code and the data of the program are untrusted, so the blocks run
   only what the closures run the same, and nothing, that may abort
   LLVM, or run long without returning to OCaml: the instructions, whose
   blocks loop, e.g., the string instructions of x86, which repeat, the
   integers of more than [max_width] bits, the divisions of more than 128
   bits, and the blocks of more than [max_slots] registers aren't in
   them, and the accesses of the memory check the pages. *)

open Core
open Bap.Std

type insn = {
  pc : int64;
  next : int64;  (** the address after the instruction *)
  blks : blk term list;
  delay : [ `None | `Delayed | `Likely ];
      (** if the branch has a delay slot, e.g., of MIPS, which runs after it,
          always, or, if it is likely, only if it is taken, and is the next
          instruction of the block *)
}

exception Unsupported of string

let unsupported fmt = ksprintf (fun msg -> raise (Unsupported msg)) fmt
let max_width = 1024

(* the slots, that the runtime passes, see MAX_REGS of the stubs, and
   their bytes, whose copies are on the stack of the block, whose frame
   is less than a page, so that the code needs no probes of the stack,
   e.g., __chkstk of Windows, that the JIT doesn't link *)
let max_slots = 256
let max_slot_bytes = 1024

type value =
  | Val of string * int  (** the operand, and its width *)
  | Mem of (string * string * int * endian) list
      (** the stores, the latest first, their addresses, the values, of their
          widths, which are the sizes, in bits *)

type t = {
  locate : string -> (int * int * int) option;
  reg_size : int -> int;
  global : int -> int;
      (** the index of the register in the pointers, that the blocks of the
          engine share *)
  body : Buffer.t;
  slots : (int, int) Hashtbl.t;  (** the registers of the slots *)
  mutable temps : int;
  mutable vars : (string * int) list;  (** the allocas of the variables *)
  mutable decls : String.Set.t;  (** the intrinsics of LLVM *)
  mutable written_before : Int.Set.t;
      (** the slots, that the instructions, that are compiled, write *)
  mutable outs : (string * string * int * int) list;
      (** the incomings of the exit, that the jumps, and the end of the block,
          share, their labels, targets, numbers of instructions, and results, so
          that the values, that only it uses, e.g., the flags, sink into it, see
          [compile] *)
  mutable exits : (Int.Set.t -> unit) list;
      (** the exits of the instructions, which write all slots, that the block
          writes, see [insn], as the block may loop *)
  loop : int64 option;
      (** the address of the block, whose jump to it loops in it *)
  fields : (int, (int * int) list) Hashtbl.t;
      (** the registers, that the block reads and writes only by their fields,
          which are disjoint, by their first bits and widths, e.g., the flags of
          EFLAGS of x86, whose fields are its variables, that the register gets,
          when it is written, see [split] *)
}

type insn_state = {
  k : int;
  ins : insn;
  index : tid -> int option;
  mutable written : Int.Set.t;  (** the slots, that the instruction writes *)
  mutable lets : (string * value) list;
  mutable virtuals : (string * (string * int)) list;
  undo : bool;
      (** if the stores log the bytes, that they overwrite, as an access or a
          division may stop the instruction after them, see [undoable] *)
}

let emit t fmt = ksprintf (fun s -> Buffer.add_string t.body s) fmt

let fresh t =
  t.temps <- t.temps + 1;
  sprintf "%%t%d" t.temps

let label t =
  t.temps <- t.temps + 1;
  sprintf "l%d" t.temps

let start t l = emit t "%s:\n" l
let start_label = start
let fst4 (x, _, _, _) = x

(* the constant of the bits of [x], of the width [w], which LLVM reads
   signed *)
let const w (z : Z.t) =
  let z = Z.extract z 0 w in
  let z = if Z.testbit z (w - 1) then Z.sub z (Z.shift_left Z.one w) else z in
  Z.to_string z

let of_word x =
  let w = Word.bitwidth x in
  Val (const w (Bitvec.to_bigint (Word.to_bitvec x)), w)

let ty w =
  if w < 1 || w > max_width then unsupported "an integer of %d bits" w;
  sprintf "i%d" w

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
      if i = max_slots then unsupported "more than %d registers" max_slots;
      if t.global id >= max_slots then
        unsupported "more than %d registers of the engine" max_slots;
      let bytes =
        Hashtbl.fold t.slots ~init:(t.reg_size id) ~f:(fun ~key ~data:_ n ->
            n + t.reg_size key)
      in
      if bytes > max_slot_bytes then
        unsupported "the registers of more than %d bytes" max_slot_bytes;
      Hashtbl.set t.slots ~key:id ~data:i;
      i

let reg_width t id = t.reg_size id * 8
let declare t decl = t.decls <- Set.add t.decls decl

let bswap t x w =
  if w mod 16 <> 0 && w <> 8 then unsupported "a swap of %d bits" w;
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
      | Some (id, lo, width) when Hashtbl.mem t.fields id ->
          let i = slot t id in
          Val (assign t "load %s, ptr %%sf%d_%d" (ty width) i lo, width)
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
  if bytes < 1 then unsupported "an access of no bytes";
  let ok =
    assign t "call i32 @bap_jit_%s(ptr %%f, i64 %s, i32 %d, ptr %%buf)"
      (if load then "load" else "store")
      addr bytes
  in
  let failed = assign t "icmp eq i32 %s, 0" ok in
  let l = label t in
  emit t "  br i1 %s, label %%i%d.stop, label %%%s\n" failed s.k l;
  start t l

(* the types of the accesses for the alias analysis of LLVM, so that the
   loads of the cache of the pages, and the stores of the undo log, which
   are of the host, are not reloaded after the stores of the program, to
   its memory, which are of the guest, e.g., the cache entry of the same
   page, which is loaded once, for the accesses of a block *)
let tbaa =
  "!0 = !{!\"bap-jit\"}\n\
   !1 = !{!\"guest\", !0, i64 0}\n\
   !2 = !{!\"host\", !0, i64 0}\n\
   !3 = !{!1, !1, i64 0}\n\
   !4 = !{!2, !2, i64 0}\n"

let guest = ", !tbaa !3"
let host = ", !tbaa !4"

(* The accesses of 1, 2, 4, or 8 bytes in a page, that the cache of the
   runtime has, whose permissions allow them, are made by the code, and
   the others by the runtime, see [access]: the entries of the cache, of
   the type {i64, ptr, i32}, are the address of the page, its bytes, and
   its permissions, see [entry] of bap_lifted_jit_stubs.c, and the store
   writes the bytes, that it overwrites, to the undo log, whose entries,
   of the type {ptr, i64, i32}, are their address, the bytes, and their
   number, see [undo_entry], of at most [undo_size] entries. *)

let undo_size = 4096

let fast_access ?(undo = true) t ~load addr bytes =
  let page = assign t "and i64 %s, -4096" addr in
  let index = assign t "lshr i64 %s, 12" addr in
  let index = assign t "and i64 %s, 255" index in
  let entry =
    assign t "getelementptr {i64, ptr, i32}, ptr %%tlb, i64 %s" index
  in
  let base = assign t "load i64, ptr %s%s" entry host in
  let hit = assign t "icmp eq i64 %s, %s" base page in
  let permp =
    assign t "getelementptr {i64, ptr, i32}, ptr %s, i64 0, i32 2" entry
  in
  let perm = assign t "load i32, ptr %s%s" permp host in
  let off = assign t "and i64 %s, 4095" addr in
  let fits = assign t "icmp ule i64 %s, %d" off (4096 - bytes) in
  let allowed =
    if load then
      let r = assign t "and i32 %s, 1" perm in
      assign t "icmp ne i32 %s, 0" r
    else
      (* writable, and not executable, as the code doesn't write the code *)
      let r = assign t "and i32 %s, 6" perm in
      let w = assign t "icmp eq i32 %s, 2" r in
      if not undo then w
      else
        let u = assign t "load i32, ptr %%undo%s" host in
        let room = assign t "icmp ult i32 %s, %d" u undo_size in
        assign t "and i1 %s, %s" w room
  in
  let ok = assign t "and i1 %s, %s" hit fits in
  let ok = assign t "and i1 %s, %s" ok allowed in
  let datap =
    assign t "getelementptr {i64, ptr, i32}, ptr %s, i64 0, i32 1" entry
  in
  (ok, datap, off)

let load t s addr endian bits =
  if bits mod 8 <> 0 then unsupported "a load of %d bits" bits;
  let bytes = bits / 8 in
  let x =
    if List.mem [ 1; 2; 4; 8 ] bytes ~equal:Int.equal then begin
      let ok, datap, off = fast_access t ~load:true addr bytes in
      let fast = label t and slow = label t and join = label t in
      emit t "  br i1 %s, label %%%s, label %%%s\n" ok fast slow;
      start t fast;
      let data = assign t "load ptr, ptr %s%s" datap host in
      let p = assign t "getelementptr i8, ptr %s, i64 %s" data off in
      let x = assign t "load %s, ptr %s, align 1%s" (ty bits) p guest in
      let fast_end = label t in
      emit t "  br label %%%s\n%s:\n  br label %%%s\n" fast_end fast_end join;
      start t slow;
      access t s ~load:true addr bytes;
      let y = assign t "load %s, ptr %%buf, align 1" (ty bits) in
      let slow_end = label t in
      emit t "  br label %%%s\n%s:\n  br label %%%s\n" slow_end slow_end join;
      start t join;
      assign t "phi %s [%s, %%%s], [%s, %%%s]" (ty bits) x fast_end y slow_end
    end
    else begin
      access t s ~load:true addr bytes;
      assign t "load %s, ptr %%buf, align 1" (ty bits)
    end
  in
  match endian with LittleEndian -> x | BigEndian -> bswap t x bits

let store t s (addr, x, bits, endian) =
  if bits mod 8 <> 0 then unsupported "a store of %d bits" bits;
  let bytes = bits / 8 in
  let x = match endian with LittleEndian -> x | BigEndian -> bswap t x bits in
  if List.mem [ 1; 2; 4; 8 ] bytes ~equal:Int.equal then begin
    let ok, datap, off = fast_access ~undo:s.undo t ~load:false addr bytes in
    let fast = label t and slow = label t and join = label t in
    emit t "  br i1 %s, label %%%s, label %%%s\n" ok fast slow;
    start t fast;
    let data = assign t "load ptr, ptr %s%s" datap host in
    let p = assign t "getelementptr i8, ptr %s, i64 %s" data off in
    if s.undo then begin
      let u = assign t "load i32, ptr %%undo%s" host in
      let e = assign t "getelementptr {ptr, i64, i32}, ptr %%log, i32 %s" u in
      emit t "  store ptr %s, ptr %s%s\n" p e host;
      let old = assign t "load %s, ptr %s, align 1%s" (ty bits) p guest in
      let old = resize t old bits 64 in
      let oldp =
        assign t "getelementptr {ptr, i64, i32}, ptr %s, i64 0, i32 1" e
      in
      emit t "  store i64 %s, ptr %s%s\n" old oldp host;
      let sizep =
        assign t "getelementptr {ptr, i64, i32}, ptr %s, i64 0, i32 2" e
      in
      emit t "  store i32 %d, ptr %s%s\n" bytes sizep host;
      let u' = assign t "add i32 %s, 1" u in
      emit t "  store i32 %s, ptr %%undo%s\n" u' host
    end;
    emit t "  store %s %s, ptr %s, align 1%s\n  br label %%%s\n" (ty bits) x p
      guest join;
    start t slow;
    emit t "  store %s %s, ptr %%buf, align 1\n" (ty bits) x;
    access t s ~load:false addr bytes;
    emit t "  br label %%%s\n" join;
    start t join
  end
  else begin
    emit t "  store %s %s, ptr %%buf, align 1\n" (ty bits) x;
    access t s ~load:false addr bytes
  end

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
      | Some (id, lo, width) when Hashtbl.mem t.fields id ->
          let i = slot t id in
          s.written <- Set.add s.written i;
          emit t "  store %s %s, ptr %%sf%d_%d\n" (ty width)
            (resize t x w width) i lo
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
let nonzero t k y w =
  if w > 128 then unsupported "a division of %d bits" w;
  let zero = assign t "icmp eq %s %s, 0" (ty w) y in
  let l = label t in
  emit t "  br i1 %s, label %%i%d.stop, label %%%s\n" zero k l;
  start t l

(* the signed modulus, which the division, that truncates, gives: its remainder
   has the sign of the dividend, so it takes the divisor, if the signs differ.
   The operation is total, while [srem] is undefined on a zero divisor, and on
   the overflow of the minimum by -1, so it divides by 1 in them, whose
   remainder is the result of -1, and [smod x 0 = x]. In one bit, 1 is -1, so
   there is no safe divisor, and the result is [x] by 0 and 0 by -1. *)
let smod t x y w =
  if w > 128 then unsupported "a division of %d bits" w;
  if w = 1 then assign t "and i1 %s, %s" x (assign t "xor i1 %s, true" y)
  else
    let i = ty w in
    let zero = assign t "icmp eq %s %s, 0" i y in
    let minus1 = assign t "icmp eq %s %s, -1" i y in
    let unsafe = assign t "or i1 %s, %s" zero minus1 in
    let d = assign t "select i1 %s, %s 1, %s %s" unsafe i i y in
    let r = assign t "srem %s %s, %s" i x d in
    let differs = assign t "xor %s %s, %s" i r y in
    let differs = assign t "icmp slt %s %s, 0" i differs in
    let inexact = assign t "icmp ne %s %s, 0" i r in
    let adjust = assign t "and i1 %s, %s" differs inexact in
    let sum = assign t "add %s %s, %s" i r y in
    let m = assign t "select i1 %s, %s %s, %s %s" adjust i sum i r in
    assign t "select i1 %s, %s %s, %s %s" zero i x i m

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

let binop t k (op : binop) (x, w) (y, w') =
  let same () =
    if w <> w' then unsupported "the operands of %d and %d bits" w w'
  in
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
      nonzero t k y w;
      arith "udiv"
  | MOD ->
      same ();
      nonzero t k y w;
      arith "urem"
  | SDIVIDE when w = 1 ->
      same ();
      nonzero t k y w;
      (* the divisor is -1, whose quotient is -x = x, where the 1 below is -1 *)
      Val (x, w)
  | SDIVIDE ->
      same ();
      nonzero t k y w;
      (* the overflow, of the minimum by -1, wraps, as in the closures,
         where LLVM is undefined *)
      let minus1 = assign t "icmp eq %s %s, -1" (ty w) y in
      let y' = assign t "select i1 %s, %s 1, %s %s" minus1 (ty w) (ty w) y in
      let r = assign t "sdiv %s %s, %s" (ty w) x y' in
      let special = assign t "sub %s 0, %s" (ty w) x in
      Val
        (assign t "select i1 %s, %s %s, %s %s" minus1 (ty w) special (ty w) r, w)
  | SMOD ->
      same ();
      Val (smod t x y w, w)
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

(* the operation alone, in the function, that the tests run *)
let binop_module op w =
  let t =
    {
      locate = (fun _ -> None);
      reg_size = (fun _ -> 0);
      global = (fun i -> i);
      body = Buffer.create 256;
      slots = Hashtbl.create (module Int);
      temps = 0;
      vars = [];
      decls = String.Set.empty;
      written_before = Int.Set.empty;
      exits = [];
      outs = [];
      loop = None;
      fields = Hashtbl.create (module Int);
    }
  in
  let r, width = value (binop t 0 op ("%x", w) ("%y", w)) in
  sprintf
    "define i1 @binop(%s %%x, %s %%y, ptr %%out) {\n\
     entry:\n\
     %s  store %s %s, ptr %%out\n\
    \  ret i1 true\n\
     i0.stop:\n\
    \  ret i1 false\n\
     }\n"
    (ty w) (ty w) (Buffer.contents t.body) (ty width) r

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
      binop t s.k op x y
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
          let x =
            if w > n then assign t "lshr %s %s, %d" (ty w) x (w - n) else x
          in
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

let slot_id t i =
  Hashtbl.to_alist t.slots
  |> List.find_map_exn ~f:(fun (id, i') -> Option.some_if (i = i') id)

let slot_width t i = reg_width t (slot_id t i)

(* the value of the register of the slot [i], whose fields are split, from
   its value, when the block started, and its fields, by [field] *)
let compose t i fields ~field =
  let size = slot_width t i in
  let mask =
    List.fold fields ~init:Z.zero ~f:(fun m (lo, w) ->
        Z.(m lor shift_left (shift_left one w - one) lo))
  in
  List.fold fields
    ~init:
      (assign t "and %s %%ld%d, %s" (ty size) i (const size (Z.lognot mask)))
    ~f:(fun acc (lo, w) ->
      let x = resize t (field lo w) w size in
      let x = if lo = 0 then x else assign t "shl %s %s, %d" (ty size) x lo in
      assign t "or %s %s, %s" (ty size) acc x)

(* the slots are written to the registers, from their copies of the
   start of the instruction [k], if they are [copy] *)
let commit ?copy t slots =
  Set.iter slots ~f:(fun i ->
      let ty' = ty (slot_width t i) in
      let copied =
        match copy with
        | Some (k, copied) when Set.mem copied i -> Some k
        | _ -> None
      in
      let x =
        match (Hashtbl.find t.fields (slot_id t i), copied) with
        | Some fields, Some k ->
            compose t i fields ~field:(fun lo _ ->
                sprintf "%%copy%d_%d_%d" k i lo)
        | Some fields, None ->
            compose t i fields ~field:(fun lo w ->
                assign t "load %s, ptr %%sf%d_%d" (ty w) i lo)
        | None, Some k -> sprintf "%%copy%d_%d" k i
        | None, None -> assign t "load %s, ptr %%sh%d" ty' i
      in
      emit t "  store %s %s, ptr %%rp%d, align 1\n" ty' x i)

(* The exit of the block to [target], after [ran] instructions, continues
   with the next block, that the runtime linked, whose function, address,
   end, and length are in one of the two entries of @block_slots, keyed
   by the target, see bap_lifted_jit_stubs.c, if the frame allows it: the
   chain is on, the instructions are within the budget, and the next
   block doesn't reach the address, at which the run stops. The call is
   the tail call, so that the stack doesn't grow, and else the block
   returns [result]. The offsets of the frame are the ones of [frame]. *)
(* the instructions of the blocks, that ran before this one, and of the
   iterations of its loop, are written to the frame, before it returns *)
let write_chained t =
  let c = assign t "load i64, ptr %%chained" in
  emit t "  store i64 %s, ptr %%chainedp\n" c

let exit_to t ~target ~ran ~result =
  let l = label t in
  let ret = label t and try_ = label t in
  emit t "  br i1 %%on, label %%%s, label %%%s\n" try_ ret;
  start t try_;
  let field i f =
    assign t
      "getelementptr inbounds [2 x {i64, ptr, i64, i64, i64}], ptr \
       @block_slots, i64 0, i64 %d, i32 %d"
      i f
  in
  let k0 = assign t "load i64, ptr %s" (field 0 0) in
  let first = assign t "icmp eq i64 %s, %s" k0 target in
  let i = assign t "zext i1 %s to i64" first in
  let i = assign t "sub i64 1, %s" i in
  let entry f =
    assign t
      "getelementptr inbounds [2 x {i64, ptr, i64, i64, i64}], ptr \
       @block_slots, i64 0, i64 %s, i32 %d"
      i f
  in
  let key = assign t "load i64, ptr %s" (entry 0) in
  let fn = assign t "load ptr, ptr %s" (entry 1) in
  let pc = assign t "load i64, ptr %s" (entry 2) in
  let end_ = assign t "load i64, ptr %s" (entry 3) in
  let len = assign t "load i64, ptr %s" (entry 4) in
  let hit = assign t "icmp eq i64 %s, %s" key target in
  let some = assign t "icmp ne ptr %s, null" fn in
  let field_ off = assign t "getelementptr inbounds i8, ptr %%f, i64 %d" off in
  let chainedp = field_ 24 and lastp = field_ 32 in
  let chained = assign t "load i64, ptr %%chained" in
  let until = "%until" in
  let total = assign t "add i64 %s, %s" chained ran in
  let need = assign t "add i64 %s, %s" total len in
  let within = assign t "icmp ule i64 %s, %%budget" need in
  let at = assign t "icmp eq i64 %s, %s" until pc in
  let after = assign t "icmp ugt i64 %s, %s" until pc in
  let before = assign t "icmp ult i64 %s, %s" until end_ in
  let inside = assign t "and i1 %s, %s" after before in
  let stops = assign t "or i1 %s, %s" at inside in
  let go = assign t "and i1 %s, %s" hit some in
  let go = assign t "and i1 %s, %s" go within in
  let runs = assign t "xor i1 %s, true" stops in
  let go = assign t "and i1 %s, %s" go runs in
  emit t "  br i1 %s, label %%%s, label %%%s\n" go l ret;
  start t l;
  emit t "  store i64 %s, ptr %s\n  store i64 %s, ptr %s\n" total chainedp pc
    lastp;
  let r = assign t "musttail call i32 %s(ptr %%f, ptr %%regs)" fn in
  emit t "  ret i32 %s\n" r;
  start t ret;
  write_chained t;
  emit t "  ret i32 %s\n" result

(* The jump of the block to its start runs it again, as the loop of the
   function, whose registers stay, rather than they are written, and the
   next block is called, so that LLVM removes the values, that the next
   iteration sets again, e.g., the flags, while the frame allows it, as
   for the next block, see [exit_to], and the run doesn't stop at its
   start. The instructions of the iteration are in the chained ones. *)
let loop_back t ~start ~target ~ran =
  let self = assign t "icmp eq i64 %s, %Ld" target start in
  let on = "%on" in
  let chained = assign t "load i64, ptr %%chained" in
  let total = assign t "add i64 %s, %d" chained ran in
  let need = assign t "add i64 %s, %d" total ran in
  let within = assign t "icmp ule i64 %s, %%budget" need in
  let stops = assign t "icmp eq i64 %%until, %Ld" start in
  let runs = assign t "xor i1 %s, true" stops in
  let go = assign t "and i1 %s, %s" self on in
  let go = assign t "and i1 %s, %s" go within in
  let go = assign t "and i1 %s, %s" go runs in
  let back = label t and out = label t in
  emit t "  br i1 %s, label %%%s, label %%%s\n" go back out;
  start_label t back;
  emit t "  store i64 %s, ptr %%chained\n  br label %%i0\n" total;
  start_label t out

(* if a store of the instruction may be followed by an access or a
   division, which may stop it, so that the store is undone, i.e., if it
   has more than one access, or a division, as most instructions access
   the memory at most once, whose stores don't log their bytes *)
let undoable blks =
  let fallible =
    object
      inherit [int] Exp.visitor
      method! enter_load ~mem:_ ~addr:_ _ _ n = n + 1
      method! enter_store ~mem:_ ~addr:_ ~exp:_ _ _ n = n + 1

      method! enter_binop op _ _ n =
        match op with Bil.DIVIDE | SDIVIDE | MOD -> n + 2 | _ -> n
    end
  in
  let count e n = fallible#visit_exp e n in
  List.fold blks ~init:0 ~f:(fun n blk ->
      let n =
        Term.enum def_t blk
        |> Seq.fold ~init:n ~f:(fun n def -> count (Def.rhs def) n)
      in
      Term.enum jmp_t blk
      |> Seq.fold ~init:n ~f:(fun n jmp ->
          let n = count (Jmp.cond jmp) n in
          match Jmp.kind jmp with
          | Call c -> (
              match Call.target c with Indirect e -> count e n | _ -> n)
          | Goto (Indirect e) | Ret (Indirect e) -> count e n
          | _ -> n))
  > 1

(* the instruction [k], whose blocks are the labels i<k>b<j>, and which
   ends at i<k>.done, if it doesn't jump, at i<k>.jump, with the target in
   %tgt, if it jumps, and at i<k>.stop, if it stops *)
let insn ?(role = `Plain) t k (ins : insn) =
  let blks = Array.of_list ins.blks in
  let index tid =
    Array.findi blks ~f:(fun _ b -> Tid.equal (Term.tid b) tid)
    |> Option.map ~f:fst
  in
  let s =
    {
      k;
      ins;
      index;
      written = Int.Set.empty;
      lets = [];
      virtuals = [];
      undo = undoable ins.blks;
    }
  in
  (* the body of the instruction is compiled first, so that its start
     copies the slots, that it writes, see [stop] *)
  let before = Buffer.contents t.body in
  Buffer.clear t.body;
  let jump_to a =
    (match role with
    | `Slot -> unsupported "a jump in a delay slot"
    | `Plain | `Branch _ -> ());
    emit t "  store i64 %s, ptr %%tgt\n  br label %%i%d.jump\n" a k
  in
  let goto j = function
    | Direct tid -> (
        match index tid with
        (* the jump to the instruction itself, e.g., b . of ARM *)
        | Some 0 -> jump_to (Int64.to_string ins.pc)
        (* the loop, e.g., of rep movs of x86, may run for long *)
        | Some i when i <= j -> unsupported "a loop in the instruction"
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
      |> Seq.iter ~f:(fun def ->
          write_var t s (Def.lhs def) (exp t s (Def.rhs def)));
      Term.enum jmp_t blk
      |> Seq.iter ~f:(fun jmp ->
          let c, w = value (exp t s (Jmp.cond jmp)) in
          let c = assign t "icmp ne %s %s, 0" (ty w) c in
          let taken = label t and rest = label t in
          emit t "  br i1 %s, label %%%s, label %%%s\n" c taken rest;
          start t taken;
          (match Jmp.kind jmp with
          | Goto label | Ret label -> goto j label
          | Call c -> (
              match Call.target c with
              | Indirect e ->
                  let a, w = value (exp t s e) in
                  jump_to (addr64 t a w)
              | label -> goto j label)
          | Int _ -> unsupported "an interrupt");
          start t rest);
      if j + 1 < Array.length blks then emit t "  br label %%i%db%d\n" k (j + 1)
      else emit t "  br label %%i%d.done\n" k);
  if Array.is_empty blks then emit t "i%db0:\n  br label %%i%d.done\n" k k;
  let copied = s.written in
  (* the exit of the block to [a], after the instruction *)
  let out a =
    (match t.loop with
    | Some start -> loop_back t ~start ~target:a ~ran:(k + 1)
    | None -> ());
    let l = label t in
    emit t "  br label %%%s\n%s:\n  br label %%exit\n" l l;
    t.outs <- (l, a, k + 1, (4 * k) + 1) :: t.outs
  in
  (match role with
  | `Plain -> emit t "i%d.done:\n  br label %%i%d\n" k (k + 1)
  (* the branch, that isn't taken, runs its delay slot, or skips it, if
     it is likely *)
  | `Branch (`Delayed, _) ->
      emit t "i%d.done:\n  store i1 0, ptr %%pend\n  br label %%i%d\n" k (k + 1)
  | `Branch (`Likely, after) ->
      emit t "i%d.done:\n" k;
      out (Int64.to_string after)
  (* the slot jumps to the target of the branch, that is taken *)
  | `Slot ->
      emit t "i%d.done:\n" k;
      let taken = assign t "load i1, ptr %%pend" in
      let l = label t in
      emit t "  br i1 %s, label %%%s, label %%i%d\n" taken l (k + 1);
      start t l;
      out (assign t "load i64, ptr %%pendt"));
  t.exits <-
    (fun _ ->
      emit t "i%d.jump:\n" k;
      let a = assign t "load i64, ptr %%tgt" in
      match role with
      (* the branch, that is taken, runs its delay slot first *)
      | `Branch _ ->
          emit t "  store i1 1, ptr %%pend\n  store i64 %s, ptr %%pendt\n" a;
          emit t "  br label %%i%d\n" (k + 1)
      | `Plain | `Slot -> out a)
    :: (fun all ->
      (* the registers, as the previous instructions left them, as the
       instruction copied them, and the ones, that it doesn't write, as
       they are, which may be of the previous iteration of a loop *)
      emit t "i%d.stop:\n" k;
      commit t ~copy:(k, copied) all;
      write_chained t;
      match role with
      | `Plain | `Branch _ -> emit t "  ret i32 %d\n" (4 * k)
      (* the slot of the branch, that is taken, stops with its target *)
      | `Slot ->
          let taken = assign t "load i1, ptr %%pend" in
          let a = assign t "load i64, ptr %%pendt" in
          emit t "  store i64 %s, ptr %%next\n" a;
          let r =
            assign t "select i1 %s, i32 %d, i32 %d" taken ((4 * k) + 3) (4 * k)
          in
          emit t "  ret i32 %s\n" r)
    :: t.exits;
  let body = Buffer.contents t.body in
  Buffer.clear t.body;
  Buffer.add_string t.body before;
  emit t "i%d:\n  store i32 0, ptr %%undo%s\n" k host;
  Set.iter copied ~f:(fun i ->
      match Hashtbl.find t.fields (slot_id t i) with
      | Some fields ->
          List.iter fields ~f:(fun (lo, w) ->
              emit t "  %%copy%d_%d_%d = load %s, ptr %%sf%d_%d\n" k i lo (ty w)
                i lo)
      | None ->
          emit t "  %%copy%d_%d = load %s, ptr %%sh%d\n" k i
            (ty (slot_width t i))
            i);
  emit t "  br label %%i%db0\n" k;
  Buffer.add_string t.body body;
  t.written_before <- Set.union t.written_before s.written

let header t name =
  let b = Buffer.create 4096 in
  let add fmt = ksprintf (Buffer.add_string b) fmt in
  add "declare i32 @bap_jit_load(ptr, i64, i32, ptr)\n";
  add "declare i32 @bap_jit_store(ptr, i64, i32, ptr)\n";
  Set.iter t.decls ~f:(fun d -> add "%s\n" d);
  add
    "@block_slots = global [2 x {i64, ptr, i64, i64, i64}] [{i64, ptr, i64, \
     i64, i64} {i64 -1, ptr null, i64 0, i64 0, i64 0}, {i64, ptr, i64, i64, \
     i64} {i64 -1, ptr null, i64 0, i64 0, i64 0}]\n";
  add "define i32 @%s(ptr noalias %%f, ptr noalias %%regs) {\nentry:\n" name;
  add "  %%next = getelementptr inbounds i8, ptr %%f, i64 8\n";
  add "  %%undo = getelementptr inbounds i8, ptr %%f, i64 16\n";
  add "  %%buf = alloca [64 x i8], align 16\n";
  (* the values of the frame, that the run doesn't change, and the
     instructions of the chained blocks, see [exit_to] *)
  add "  %%chainedp = getelementptr inbounds i8, ptr %%f, i64 24\n";
  add "  %%chained = alloca i64\n";
  add "  %%chained0 = load i64, ptr %%chainedp\n";
  add "  store i64 %%chained0, ptr %%chained\n";
  add "  %%budgetp = getelementptr inbounds i8, ptr %%f, i64 40\n";
  add "  %%budget = load i64, ptr %%budgetp\n";
  add "  %%untilp = getelementptr inbounds i8, ptr %%f, i64 48\n";
  add "  %%until = load i64, ptr %%untilp\n";
  add "  %%tlbp = getelementptr inbounds i8, ptr %%f, i64 64\n";
  add "  %%tlb = load ptr, ptr %%tlbp\n";
  add "  %%logp = getelementptr inbounds i8, ptr %%f, i64 72\n";
  add "  %%log = load ptr, ptr %%logp\n";
  add "  %%onp = getelementptr inbounds i8, ptr %%f, i64 56\n";
  add "  %%on0 = load i32, ptr %%onp\n";
  add "  %%on = icmp ne i32 %%on0, 0\n";
  add "  %%tgt = alloca i64\n";
  add "  %%pend = alloca i1\n  store i1 0, ptr %%pend\n";
  add "  %%pendt = alloca i64\n  store i64 0, ptr %%pendt\n";
  List.iter (List.rev t.vars) ~f:(fun (p, w) ->
      add "  %s = alloca %s\n  store %s 0, ptr %s\n" p (ty w) (ty w) p);
  Hashtbl.to_alist t.slots
  |> List.sort ~compare:(fun (_, i) (_, j) -> Int.compare i j)
  |> List.iter ~f:(fun (id, i) ->
      let w = reg_width t id in
      add "  %%rpp%d = getelementptr inbounds ptr, ptr %%regs, i64 %d\n" i
        (t.global id);
      add "  %%rp%d = load ptr, ptr %%rpp%d\n" i i;
      add "  %%sh%d = alloca %s\n" i (ty w);
      add "  %%ld%d = load %s, ptr %%rp%d, align 1\n" i (ty w) i;
      add "  store %s %%ld%d, ptr %%sh%d\n" (ty w) i i;
      Option.iter (Hashtbl.find t.fields id) ~f:(fun fields ->
          List.iter fields ~f:(fun (lo, fw) ->
              add "  %%sf%d_%d = alloca %s\n" i lo (ty fw);
              add "  %%sfv%d_%d = lshr %s %%ld%d, %d\n" i lo (ty w) i lo;
              add "  %%sft%d_%d = trunc %s %%sfv%d_%d to %s\n" i lo (ty w) i lo
                (ty fw);
              add "  store %s %%sft%d_%d, ptr %%sf%d_%d\n" (ty fw) i lo i lo)));
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
(* the registers of the instructions, that are read and written only by
   their disjoint fields, see [fields] *)
let split ~locate ~reg_size insns =
  let accesses = Hashtbl.create (module Int) in
  let var v =
    if not (Var.is_virtual v) then
      Option.iter
        (locate (Var.name v))
        ~f:(fun (id, lo, w) -> Hashtbl.add_multi accesses ~key:id ~data:(lo, w))
  in
  let exp e = Set.iter (Exp.free_vars e) ~f:var in
  List.iter insns ~f:(fun ins ->
      List.iter ins.blks ~f:(fun blk ->
          Term.enum def_t blk
          |> Seq.iter ~f:(fun def ->
              var (Def.lhs def);
              exp (Def.rhs def));
          Term.enum jmp_t blk
          |> Seq.iter ~f:(fun jmp ->
              exp (Jmp.cond jmp);
              match Jmp.kind jmp with
              | Goto (Indirect e) | Ret (Indirect e) -> exp e
              | Call c -> (
                  match Call.target c with Indirect e -> exp e | _ -> ())
              | _ -> ())));
  let fields = Hashtbl.create (module Int) in
  Hashtbl.iteri accesses ~f:(fun ~key:id ~data ->
      let size = reg_size id * 8 in
      let data = List.dedup_and_sort data ~compare:Poly.compare in
      let disjoint =
        List.for_all data ~f:(fun (lo, w) ->
            (lo <> 0 || w <> size)
            && List.for_all data ~f:(fun (lo', w') ->
                (lo = lo' && w = w') || lo + w <= lo' || lo' + w' <= lo))
      in
      if disjoint && List.length data > 1 then Hashtbl.set fields ~key:id ~data);
  fields

let compile ?loop ~locate ~reg_size ~global insns =
  let t =
    {
      locate;
      reg_size;
      global;
      body = Buffer.create 4096;
      slots = Hashtbl.create (module Int);
      temps = 0;
      vars = [];
      decls = String.Set.empty;
      written_before = Int.Set.empty;
      exits = [];
      outs = [];
      loop;
      fields = split ~locate ~reg_size insns;
    }
  in
  let rec loop k = function
    | [] -> (k, None)
    | ins :: rest -> (
        let saved =
          ( Buffer.contents t.body,
            Hashtbl.copy t.slots,
            t.vars,
            t.decls,
            t.temps,
            t.written_before,
            t.exits,
            t.outs )
        in
        (* the branch, that has a delay slot, and its slot, are in the
           block together, or not at all *)
        let compiled () =
          match (ins.delay, rest) with
          | `None, _ ->
              insn t k ins;
              (1, rest)
          | ((`Delayed | `Likely) as kind), slot :: rest ->
              insn ~role:(`Branch (kind, slot.next)) t k ins;
              insn ~role:`Slot t (k + 1) slot;
              (2, rest)
          | _, [] -> unsupported "a branch without its delay slot"
        in
        match compiled () with
        | n, rest -> loop (k + n) rest
        | exception Unsupported reason ->
            let body, slots, vars, decls, temps, written_before, exits, outs =
              saved
            in
            t.written_before <- written_before;
            t.exits <- exits;
            t.outs <- outs;
            Buffer.clear t.body;
            Buffer.add_string t.body body;
            Hashtbl.clear t.slots;
            Hashtbl.iteri slots ~f:(fun ~key ~data ->
                Hashtbl.set t.slots ~key ~data);
            t.vars <- vars;
            t.decls <- decls;
            t.temps <- temps;
            (k, Some reason))
  in
  let length, reason = loop 0 insns in
  if length = 0 then Error (Option.value reason ~default:"no instructions")
  else begin
    emit t "i%d:\n  br label %%exit\n" length;
    let last = List.nth_exn insns (length - 1) in
    t.outs <-
      ( sprintf "i%d" length,
        Int64.to_string last.next,
        length,
        (4 * (length - 1)) + 2 )
      :: t.outs;
    List.iter (List.rev t.exits) ~f:(fun exit -> exit t.written_before);
    (* the exit, that the jumps, and the end, share *)
    let phi ty f =
      assign t "phi %s %s" ty
        (String.concat ~sep:", "
           (List.map t.outs ~f:(fun out ->
                sprintf "[%s, %%%s]" (f out) (fst4 out))))
    in
    emit t "exit:\n";
    let target = phi "i64" (fun (_, a, _, _) -> a) in
    let ran = phi "i64" (fun (_, _, n, _) -> Int.to_string n) in
    let result = phi "i32" (fun (_, _, _, r) -> Int.to_string r) in
    commit t t.written_before;
    emit t "  store i64 %s, ptr %%next\n" target;
    exit_to t ~target ~ran ~result;
    emit t "}\n";
    let b = header t "block" in
    Buffer.add_buffer b t.body;
    Buffer.add_string b tbaa;
    let regs = Array.create ~len:(Hashtbl.length t.slots) 0 in
    Hashtbl.iteri t.slots ~f:(fun ~key ~data -> regs.(data) <- key);
    Ok { ir = Buffer.contents b; regs; length }
  end

(* the runtime of the blocks, see bap_lifted_jit_stubs.c *)
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

  external link :
    mem ->
    int64 ->
    nativeint ->
    string ->
    int ->
    int64 ->
    int ->
    nativeint ->
    unit = "bap_jit_link_byte" "bap_jit_link"

  external traces : mem -> Bap_native_trace.t array -> unit = "bap_jit_traces"
  external starts : mem -> bool = "bap_jit_starts"
  external unlink : mem -> int64 -> unit = "bap_jit_unlink"
  external unlink_all : mem -> unit = "bap_jit_unlink_all"
  external limits : mem -> bool -> int -> int64 -> unit = "bap_jit_limits"

  external last : mem -> (int64[@unboxed]) = "bap_jit_last_byte" "bap_jit_last"
  [@@noalloc]

  external chained : mem -> (int[@untagged])
    = "bap_jit_chained_byte" "bap_jit_chained"
  [@@noalloc]
end

(* the JIT of an engine, whose blocks call the runtime, which has its
   own, as the blocks of the same code, e.g., of two emulators of the
   same program, have the same names *)
let create () =
  let jit = Bap_llvm_jit.create () in
  let load, store = Runtime.helpers () in
  Bap_llvm_jit.define jit "bap_jit_load" load;
  Bap_llvm_jit.define jit "bap_jit_store" store;
  jit

(* the code of the block, whose name is the digest of its IR, so that its
   object is the same, in the other runs of the program, which is in the
   [cache], if any, and the IR of which BAP_LIFTED_IR=DIR writes *)
let native ?cache llvm block =
  let name = "bap_block_" ^ Stdlib.Digest.(to_hex (string block.ir)) in
  let ir =
    String.substr_replace_first block.ir ~pattern:"@block("
      ~with_:("@" ^ name ^ "(")
    |> String.substr_replace_all ~pattern:"@block_slots"
         ~with_:("@" ^ name ^ "_slots")
  in
  (match Sys.getenv "BAP_LIFTED_IR" with
  | Some dir ->
      Out_channel.write_all (Filename.concat dir (name ^ ".ll")) ~data:ir
  | None -> ());
  let cache =
    Option.map cache ~f:(fun dir -> Filename.concat dir (name ^ ".o"))
  in
  let code = Bap_llvm_jit.compile ?cache llvm ir name in
  (code, Bap_llvm_jit.symbol llvm (name ^ "_slots"))
