(* The lifted engine, which runs the IR of the instructions, that BAP
   lifts, with the interface of Unicorn, see bap_lifted.mli.

   The registers are the registers of Unicorn, their bytes in the order
   of the host, by their identifiers, so that the registers of BAP are
   the bits of them, as Primus_native_target.Regs maps them, and the
   registers, that the semantics read, which are not mapped, e.g., the
   temporaries, are the values of a table. The memory is the pages of
   4 KB, with their permissions.

   An instruction runs as a transaction: its writes to the registers and
   the memory are undone, if it faults, so that it runs again, after the
   hook of the invalid access, e.g., which mapped the page, as Unicorn
   runs it. The instruction, whose semantics the engine can't run, e.g.,
   which calls an intrinsic, isn't run, and the hooks of [unsupported]
   are called, which stop the emulation, so that it is interpreted. *)

open Core
open Bap.Std
module Engine = Bap_engine
module Trace = Bap_native_trace

type config = {
  lift : thumb:bool -> int64 -> string -> (int * string * blk term list) option;
  name : tid -> string option;
  policy : int;
  delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
  locate : string -> (int * int * int) option;
  owner : string -> string option;
  pc : int;
  big_endian : bool;
  bits : int;
  jit : bool;
  cache : string option;
}

type kind =
  | Code of (int64 -> int -> unit)
  | Sites of Int64.Hash_set.t * (int64 -> int -> unit)
      (** the instructions at the addresses of the set *)
  | Block of (int64 -> int -> unit)
  | Interrupt of (int -> unit)
  | Invalid_insn of (unit -> bool)
  | Unsupported of (int64 -> unit)
  | Mem of Engine.access list * (Engine.access -> int64 -> int -> int64 -> unit)
  | Mem_invalid of
      Engine.access list * (Engine.access -> int64 -> int -> int64 -> bool)
  | Trace_code of Trace.t  (** records the instructions, or the blocks *)
  | Trace_mem of Trace.t  (** records the accesses *)

type hook = {
  first : int64 option;
  last : int64 option;
  kind : kind;
  mutable deleted : bool;
}

(* the hooks by their kinds, and the pages of the hooks of the code and
   of the blocks, if they are all ranged, which [hooks_changed] makes *)
type by_kind = {
  code : hook array;
  blocks : hook array;
  code_pages : Int64.Hash_set.t option;
      (** the pages, that the hooks of the code, and of the blocks, cover, or
          [None], if one of them covers too many *)
  reads : hook array;  (** the hooks of the memory, that see the reads *)
  writes : hook array;  (** the hooks of the memory, that see the writes *)
  invalid_mem : hook array;
  trace_code : hook array;
  trace_mem : hook array;
  interrupts : hook array;
  invalid_insns : hook array;
  unsupported_insns : hook array;
}

let no_hooks =
  {
    code = [||];
    blocks = [||];
    code_pages = Some (Int64.Hash_set.create ());
    reads = [||];
    writes = [||];
    invalid_mem = [||];
    trace_code = [||];
    trace_mem = [||];
    interrupts = [||];
    invalid_insns = [||];
    unsupported_insns = [||];
  }

(* the bytes of the pages are outside of the heap, as the blocks, that
   the JIT compiled, access them, see Bap_lifted_jit *)
type page = {
  data : Bigstring.t;
  mutable perm : Engine.Perm.t;
  mutable code : (int64 * int64 * int64) list;
      (** the blocks, that the JIT compiled, whose bytes are on the page, their
          addresses, and the first and the last address of their bytes, which
          are dropped, when they are written, see [code_written] *)
}

(* the outcome of an instruction *)
type next = Next | Jump of int64 | Interrupt_at of int * int64

(* the registers, that the instruction reads, and writes, as the
   registers, whose taints they have, see [owner], with the writes of the
   whole registers, if it accesses the memory, and the instruction, that
   propagates the taint, see [shadow] *)
type taint_info = {
  reads : string array;
  writes : (string * bool) array;
  memory : bool;
  shadowed : unit -> next;
}

(* the instruction, that is lifted, and its bytes, in the mode, e.g.,
   Thumb of ARM *)
type insn = {
  code : string;
  size : int;
  name : string;
  thumb : bool;
  blks : blk term list;
  jumps : bool;
      (** if it may jump, so that it ends the block, even if it doesn't jump, as
          in Unicorn *)
  atomic : [ `None | `Load | `Store ];
      (** if it is a load linked, or a store conditional, see [link] *)
  it : int option;  (** the firstcond and the mask of IT of Thumb *)
  modes : (bool * bool) option;
      (** the modes of ARM, Thumb or not, after the jumps of the instruction to
          the even and to the odd addresses, see [jump] *)
  run : unit -> next;  (** the compiled instruction *)
  taint : taint_info Lazy.t;  (** see [shadow] *)
}

(* the block, that the JIT compiled, of the instructions, that start at
   the addresses, see Bap_lifted_jit *)
type block = {
  native : Bap_llvm_jit.code;
  fn : nativeint;
  slots : nativeint;
      (** the entries of the next blocks, that its code calls, see
          [Bap_lifted_jit.exit_to] *)
  mutable chained : bool;
      (** if the runs of the other blocks continue with it, see [chainable] *)
  code : string;  (** the bytes of its instructions *)
  pcs : int64 array;
  insns : insn array;
  mutable gen : int;  (** the hooks, that it was checked against *)
  atomic : bool;  (** if an instruction is atomic, see [link] *)
  has_it : bool;  (** if an instruction is IT of Thumb *)
  it_closed : bool;
      (** if its IT blocks end in it, so that the IT state is zero, when it
          ends, as when it starts *)
  super : bool;
      (** if it runs on after the branches, that aren't taken, see [jit.whole]
      *)
  mutable entry_hooked : bool;
      (** if the hooks of the code or of the blocks hook its first instruction,
          which are called before it runs *)
}

(* the blocks are compiled, after they run [hot] times *)
type compiled = Counting of int | Compiled of block | Failed

type jit = {
  mem : Bap_lifted_jit.Runtime.mem;
  blocks : compiled Int64.Table.t;
  mutable gen : int;  (** the version of the hooks *)
  mutable traced : bool;
      (** if the traces of the code record the instructions of the blocks *)
  mutable native : bool;
      (** if the traces are of the blocks only, whose blocks, that the runs
          chain, the runtime records, see [Bap_lifted_jit.Runtime.traces] *)
  mutable whole : bool;
      (** if the blocks may run on after the branches, that aren't taken, as no
          hook or trace needs the blocks of Unicorn, see [falls] *)
  mutable jitted : int;  (** the instructions, that the blocks ran *)
  compiles : int Int64.Table.t;  (** the blocks compiled at the addresses *)
  mutable live : int;  (** the blocks, that are not released *)
  llvm : Bap_llvm_jit.t Lazy.t;  (** the JIT of the engine *)
  globals : int Int.Table.t;
      (** the indices of the registers in [registers], see [global] *)
  mutable registers : Bytes.t array;
      (** the bytes of the registers, that the blocks share, so that the run of
          a block continues with the next one, see [chainable] *)
}

(* The taint, that the engine propagates itself, rather than the
   interpreter, see [taint_start]: the sets of the labels, e.g., of the
   tainted objects, by their numbers, the sets of the registers, by the
   names of their bases, see [config.owner], and of the bytes of the
   memory, and the classes of the labels, which tell, if the labels
   propagate through the computations, e.g., the arithmetic, or only
   through the moves, e.g., the loads and the stores, or not at all. *)
type label_class = [ `All | `Moves | `None ]

type shadow = {
  mutable on : bool;
  mutable jumps : bool;
      (** if a jump, whose condition is tainted, is unsupported, e.g., as its
          observers see it *)
  mutable sets : Int.Set.t array;  (** the sets by their numbers, 0 is empty *)
  mutable count : int;
  ids : (int list, int) Hashtbl.t;
  unions : (int * int, int) Hashtbl.t;
  moves : int Int.Table.t;  (** the labels of a set, that the moves keep *)
  comps : int Int.Table.t;  (** and that the computations keep *)
  classes : label_class Int.Table.t;
  sregs : int String.Table.t;  (** the tainted registers *)
  smem : int Int64.Table.t;  (** the tainted bytes *)
  spages : int Int64.Table.t;  (** the numbers of the tainted bytes of pages *)
  dirty_regs : String.Hash_set.t;  (** the changes since [taint_changes] *)
  dirty_mem : Int64.Hash_set.t;
  mutable cur : int;  (** the taint of the value, that was computed last *)
}

type t = {
  config : config;
  arch : Engine.arch;
  cpsr : int option;  (** CPSR of ARM, whose bit T is the Thumb state *)
  regs : Bytes.t Int.Table.t;
  sizes : int Int.Table.t;
  others : word String.Table.t;  (** the registers, that are not mapped *)
  pages : page Int64.Table.t;
  insns : insn Int64.Table.t;
  mutable hooks : hook list;
  mutable by_kind : by_kind;
      (** the hooks, that aren't deleted, by their kinds, in their order, see
          [hooks_changed], so that each event walks only its own hooks *)
  mutable stopped : bool;
  mutable closed : bool;
  mutable undo : (unit -> unit) list;
  mutable last_block : int64 option;
  mutable block : bool;  (** the next instruction starts a block *)
  mutable running : bool;
  mutable current : int64;  (** the instruction, that runs *)
  mutable current_size : int;
  mutable recorded : bool;
      (** if the traces recorded the instruction, that runs, which they do after
          its hooks *)
  (* the writes of the registers and the memory, while the emulation is
     stopped, which make a boundary of the traces, when it starts, see
     [Trace.bounds], but the fills of the pages, that are mapped *)
  mutable wrote_regs : bool;
  mutable wrote : (int64 * int64) list;
  mutable wrote_all : bool;
  fresh : unit Int64.Table.t;
  mutable reads : (int64 * int) list;
      (** the reads of the instruction, that runs, which the semantics may
          repeat, e.g., of an operand, that the flags use too, but the traces
          record once, as Unicorn reads it once *)
  mutable ran : int;  (** the instructions, that the engine ran *)
  mutable linked : int option;
      (** the instruction, that loaded linked last, e.g., ll of MIPS, by [ran],
          until a store conditional, see [expired] *)
  mutable unsupported : int;  (** the instructions, that it couldn't run *)
  jit : jit option;  (** if [config.jit], on a little-endian host *)
  mutable stale : int64 list;
      (** the blocks, whose code was written, which are dropped, before the next
          block runs, see [drop_stale] *)
  shadow : shadow;
}

exception Fault of Engine.access * int64

(* the instruction, that the engine can't run *)
exception Unsupported_insn of string

(* the system call of the instruction, which interrupts the engine, as it
   interrupts Unicorn, with the number of its interrupt *)
exception Trap of int

(* the loads and the stores of the atomic sequences, e.g., ll and sc of
   MIPS, by the names of their instructions, as the executor knows them,
   whose semantics have no reservation, so that the store succeeds, if
   another thread wrote, while the engine stopped between them *)
let load_linked name =
  List.exists
    [
      "LDREX";
      "LDAEX";
      "LDXR";
      "LDAXR";
      "LDXP";
      "LDAXP";
      "LBARX";
      "LHARX";
      "LWARX";
      "LDARX";
      "LR_";
      "LL_";
      "LLD_";
    ] ~f:(fun prefix -> String.is_prefix name ~prefix)
  || List.mem [ "LL"; "LLD"; "LL64"; "LLD64" ] name ~equal:String.equal

let store_conditional name =
  List.exists
    [
      "STREX";
      "STLEX";
      "STXR";
      "STLXR";
      "STXP";
      "STLXP";
      "STBCX";
      "STHCX";
      "STWCX";
      "STDCX";
      "SC_";
      "SCD_";
    ] ~f:(fun prefix -> String.is_prefix name ~prefix)
  || List.mem [ "SC"; "SCD"; "SC64"; "SCD64" ] name ~equal:String.equal

(* the instruction, that ran, starts or ends an atomic sequence *)
let link t (insn : insn) =
  match insn.atomic with
  | `Load -> t.linked <- Some t.ran
  | `Store -> t.linked <- None
  | `None -> ()

(* the time doesn't stop the engine in an atomic sequence, of at most so
   many instructions, as the threads switch, when it stops *)
let max_linked = 32

(* if the engine stopped in an atomic sequence, whose store would succeed,
   if another thread wrote in between, so that the threads don't switch *)
let in_atomic t = Option.exists t.linked ~f:(fun at -> t.ran - at < max_linked)

(* the times of the lifts, the compiles of the JIT, and the runs of the
   blocks, with BAP_LIFTED_STATS, which are not measured else, as the
   time is not free to get *)
let stats = Option.is_some (Sys.getenv "BAP_LIFTED_STATS")
let lift_time = ref 0.
let compile_time = ref 0.
let run_time = ref 0.
let lifted_count = ref 0
let compiled_count = ref 0

let timed time f =
  if not stats then f ()
  else
    let start = Time_float.now () in
    Exn.protect ~f ~finally:(fun () ->
        time :=
          !time
          +. Time_float.Span.to_sec (Time_float.diff (Time_float.now ()) start))

let page_size = 0x1000L
let page_of addr = Int64.(addr land lnot (page_size - 1L))

let error code fmt =
  Printf.ksprintf (fun msg -> raise (Engine.Error (code, msg))) fmt

(* the codes of the errors of Unicorn *)
let uc_err_read_unmapped = 6
let uc_err_write_unmapped = 7
let uc_err_fetch_unmapped = 8
let uc_err_insn_invalid = 10
let uc_err_write_prot = 12
let uc_err_read_prot = 13
let uc_err_fetch_prot = 14

let create config arch _mode =
  let t =
    {
      config;
      arch;
      cpsr =
        (match arch with
        | Arm ->
            Option.map (Engine.Register.by_name arch ~bits:config.bits "CPSR")
              ~f:(fun r -> r.id)
        | _ -> None);
      regs = Int.Table.create ();
      sizes = Int.Table.create ();
      others = String.Table.create ();
      pages = Int64.Table.create ();
      insns = Int64.Table.create ();
      hooks = [];
      stopped = false;
      closed = false;
      undo = [];
      last_block = None;
      block = true;
      running = false;
      current = 0L;
      current_size = 0;
      recorded = false;
      wrote_regs = false;
      wrote = [];
      wrote_all = false;
      fresh = Int64.Table.create ();
      reads = [];
      by_kind = no_hooks;
      ran = 0;
      linked = None;
      stale = [];
      unsupported = 0;
      shadow =
        {
          on = false;
          jumps = false;
          sets = Array.create ~len:16 Int.Set.empty;
          count = 1;
          ids = Hashtbl.Poly.create ();
          unions = Hashtbl.Poly.create ();
          moves = Int.Table.create ();
          comps = Int.Table.create ();
          classes = Int.Table.create ();
          sregs = String.Table.create ();
          smem = Int64.Table.create ();
          spages = Int64.Table.create ();
          dirty_regs = String.Hash_set.create ();
          dirty_mem = Int64.Hash_set.create ();
          cur = 0;
        };
      jit =
        (if Sys.big_endian || not config.jit then None
         else
           Some
             {
               mem = Bap_lifted_jit.Runtime.create ();
               blocks = Int64.Table.create ();
               gen = 0;
               traced = false;
               native = false;
               whole = not (Poly.equal arch Engine.Arm);
               jitted = 0;
               compiles = Int64.Table.create ();
               live = 0;
               llvm = lazy (Bap_lifted_jit.create ());
               globals = Int.Table.create ();
               registers = [||];
             });
    }
  in
  (* the numbers of the instructions, with BAP_LIFTED_STATS *)
  if Option.is_some (Sys.getenv "BAP_LIFTED_STATS") then
    at_exit (fun () ->
        Printf.eprintf
          "lifted engine: %d instructions run, %d unsupported, %d jitted, %d \
           lifts in %.3f s, %d compiles in %.3f s, the blocks ran %.3f s\n\
           %!"
          t.ran t.unsupported
          (Option.value_map t.jit ~default:0 ~f:(fun j -> j.jitted))
          !lifted_count !lift_time !compiled_count !compile_time !run_time);
  t

let check t = if t.closed then invalid_arg "the engine is closed"

let close t =
  Option.iter t.jit ~f:(fun j ->
      Hashtbl.iter j.blocks ~f:(function
        | Compiled b -> Bap_llvm_jit.release b.native
        | Counting _ | Failed -> ());
      Hashtbl.clear j.blocks;
      j.live <- 0);
  t.closed <- true

(* the registers *)

let register t id =
  match Engine.Register.by_id t.arch ~bits:t.config.bits id with
  | Some r -> r
  | None -> error 15 "Invalid argument (UC_ERR_ARG)"

let reg_size t id =
  check t;
  match Hashtbl.find t.sizes id with
  | Some size -> size
  | None ->
      let r = register t id in
      Hashtbl.set t.sizes ~key:id ~data:r.size;
      r.size

let reg_bytes t id =
  match Hashtbl.find t.regs id with
  | Some b -> b
  | None ->
      let r = register t id in
      let b = Bytes.make r.size '\000' in
      Option.iter r.reset ~f:(fun x ->
          let n = Int.min r.size 8 in
          for i = 0 to n - 1 do
            let shift = if Sys.big_endian then 8 * (n - 1 - i) else 8 * i in
            Bytes.set b i
              (Char.of_int_exn
                 Int64.(to_int_exn (shift_right_logical x shift land 0xFFL)))
          done);
      Hashtbl.set t.regs ~key:id ~data:b;
      b

let reg_read_bytes t id = Bytes.to_string (reg_bytes t id)

let write_reg_bytes t id data =
  let b = reg_bytes t id in
  if String.length data <> Bytes.length b then
    invalid_arg "Unicorn.reg_write_bytes: a wrong size";
  Bytes.From_string.blit ~src:data ~src_pos:0 ~dst:b ~dst_pos:0
    ~len:(String.length data)

(* the bytes of the host, which is little endian, see [Engine.reg_read] *)
let int64_of_bytes b n =
  let x = ref 0L in
  for i = Int.min n 8 - 1 downto 0 do
    x := Int64.((!x lsl 8) lor of_int (Char.to_int (Bytes.get b i)))
  done;
  !x

let reg_read t id =
  let b = reg_bytes t id in
  if Bytes.length b > 8 then invalid_arg "Unicorn.reg_read: a wide register";
  int64_of_bytes b (Bytes.length b)

let write_reg t id x =
  let b = reg_bytes t id in
  if Bytes.length b > 8 then invalid_arg "Unicorn.reg_write: a wide register";
  for i = 0 to Bytes.length b - 1 do
    Bytes.set b i
      (Char.of_int_exn Int64.(to_int_exn ((x lsr Int.(i * 8)) land 0xFFL)))
  done

let pc t = reg_read t t.config.pc

(* the instruction, that runs, e.g., in a hook, or the next one, when the
   engine is stopped *)
let current t = if t.running then t.current else pc t

let set_pc t pc =
  if reg_size t t.config.pc > 8 then invalid_arg "the program counter is wide"
  else write_reg t t.config.pc pc

(* the memory *)

let pages_of addr size f =
  let rec loop page =
    if Int64.(page < addr + size) then begin
      f page;
      loop Int64.(page + page_size)
    end
  in
  if Int64.(size > 0L) then loop (page_of addr)

let aligned addr size =
  Int64.(addr land (page_size - 1L) = 0L && size land (page_size - 1L) = 0L)

(* the blocks of the code of the page, whose bytes from [addr] are
   written, or which is unmapped, or not executable anymore, are stale, as
   the compiled blocks don't check their bytes, when they run, and the JIT
   never writes the pages, that are executable, see bap_lifted_jit_stubs.c *)
let code_written ?range t (p : page) =
  if not (List.is_empty p.code) then begin
    let ( <=: ) x y = Stdlib.Int64.unsigned_compare x y <= 0 in
    let written (_, lo, hi) =
      match range with
      | None -> true
      | Some (addr, size) -> (lo <=: Int64.(addr + size - 1L)) && addr <=: hi
    in
    let stale, rest = List.partition_tf p.code ~f:written in
    if not (List.is_empty stale) then begin
      t.stale <- List.map stale ~f:(fun (pc, _, _) -> pc) @ t.stale;
      p.code <- rest
    end
  end

(* the permissions of the page, that the compiled blocks see, without
   the reads or the writes, that the hooks of the memory, or the traces,
   of the page see, so that its accesses stop the block, as their faults
   do, and the closures run them, and call the hooks, while the rest of
   the code runs compiled *)
let effective t page (perm : Engine.Perm.t) =
  let last = Int64.(page + page_size - 1L) in
  let overlaps h =
    (not h.deleted)
    &&
    match (h.first, h.last) with
    | Some first, Some l when Int64.(first <= l) ->
        Int64.(first <= last && l >= page)
    | _ -> true
  in
  let hooked access =
    List.exists t.hooks ~f:(fun h ->
        overlaps h
        &&
        match h.kind with
        | Trace_mem _ -> true
        | Mem (accesses, _) ->
            List.exists accesses ~f:(fun a ->
                match (a, access) with
                | (Engine.Read | Read_after), `read | Write, `write -> true
                | _ -> false)
        | _ -> false)
  in
  let perm = (perm :> int) in
  (* the tainted bytes are accessed by the closures, see [shadow] *)
  let tainted = t.shadow.on && Hashtbl.mem t.shadow.spages page in
  let perm = if tainted || hooked `read then perm land lnot 1 else perm in
  if tainted || hooked `write then perm land lnot 2 else perm

let mem_map t addr size perm =
  check t;
  if not (aligned addr size) then error 15 "Invalid argument (UC_ERR_ARG)";
  pages_of addr size (fun page ->
      if Hashtbl.mem t.pages page then
        error 11 "Invalid memory mapping (UC_ERR_MAP)");
  pages_of addr size (fun page ->
      let data =
        Bigstring.init (Int64.to_int_exn page_size) ~f:(fun _ -> '\000')
      in
      Hashtbl.set t.fresh ~key:page ~data:();
      Hashtbl.set t.pages ~key:page ~data:{ data; perm; code = [] };
      Option.iter t.jit ~f:(fun j ->
          Bap_lifted_jit.Runtime.map j.mem page data (effective t page perm)))

let mem_unmap t addr size =
  check t;
  pages_of addr size (fun page ->
      if not (Hashtbl.mem t.pages page) then
        error 11 "Invalid memory mapping (UC_ERR_NOMEM)");
  pages_of addr size (fun page ->
      Option.iter (Hashtbl.find t.pages page) ~f:(code_written t);
      Option.iter t.jit ~f:(fun j -> Bap_lifted_jit.Runtime.unmap j.mem page);
      Hashtbl.remove t.pages page)

let mem_protect t addr size perm =
  check t;
  pages_of addr size (fun page ->
      match Hashtbl.find t.pages page with
      | Some p ->
          if not Engine.Perm.(mem perm exec) then code_written t p;
          p.perm <- perm;
          Option.iter t.jit ~f:(fun j ->
              Bap_lifted_jit.Runtime.protect j.mem page (effective t page perm))
      | None -> error 11 "Invalid memory mapping (UC_ERR_NOMEM)")

let offset addr = Int64.(to_int_exn (addr - page_of addr))

(* the sets of the labels of the taint, see [shadow] *)
let set_id s (labels : Int.Set.t) =
  if Set.is_empty labels then 0
  else
    let key = Set.to_list labels in
    match Hashtbl.find s.ids key with
    | Some i -> i
    | None ->
        let i = s.count in
        if i = Array.length s.sets then begin
          let sets = Array.create ~len:(2 * i) Int.Set.empty in
          Array.blit ~src:s.sets ~src_pos:0 ~dst:sets ~dst_pos:0 ~len:i;
          s.sets <- sets
        end;
        s.sets.(i) <- labels;
        s.count <- i + 1;
        Hashtbl.set s.ids ~key ~data:i;
        i

let union s a b =
  if a = 0 || a = b then b
  else if b = 0 then a
  else
    let key = if a < b then (a, b) else (b, a) in
    match Hashtbl.find s.unions key with
    | Some i -> i
    | None ->
        let i = set_id s (Set.union s.sets.(a) s.sets.(b)) in
        Hashtbl.set s.unions ~key ~data:i;
        i

let filter s memo keep a =
  if a = 0 then 0
  else
    match Hashtbl.find memo a with
    | Some i -> i
    | None ->
        let i =
          set_id s
            (Set.filter s.sets.(a) ~f:(fun l ->
                 keep (Option.value (Hashtbl.find s.classes l) ~default:`None)))
        in
        Hashtbl.set memo ~key:a ~data:i;
        i

(* the labels, that the moves, e.g., the loads, and the computations,
   e.g., the arithmetic, propagate *)
let moves s a =
  filter s s.moves (function `All | `Moves -> true | `None -> false) a

let comps s a = filter s s.comps (function `All -> true | _ -> false) a

(* the register, whose taint the register of BAP has *)
let owner t name = Option.value (t.config.owner name) ~default:name

let reg_taint t name =
  if Hashtbl.is_empty t.shadow.sregs then 0
  else Option.value (Hashtbl.find t.shadow.sregs name) ~default:0

let set_reg_taint_id ?(dirty = true) t name id =
  let s = t.shadow in
  if reg_taint t name <> id then begin
    if id = 0 then Hashtbl.remove s.sregs name
    else Hashtbl.set s.sregs ~key:name ~data:id;
    if dirty then Hash_set.add s.dirty_regs name
  end

let mem_taint t addr =
  if Hashtbl.is_empty t.shadow.smem then 0
  else Option.value (Hashtbl.find t.shadow.smem addr) ~default:0

let reprotect t page =
  Option.iter t.jit ~f:(fun j ->
      Option.iter (Hashtbl.find t.pages page) ~f:(fun p ->
          Bap_lifted_jit.Runtime.protect j.mem page (effective t page p.perm)))

(* the tainted pages are accessed by the closures, see [effective] *)
let set_mem_taint_id ?(dirty = true) t addr id =
  let s = t.shadow in
  let old = mem_taint t addr in
  if old <> id then begin
    if id = 0 then Hashtbl.remove s.smem addr
    else Hashtbl.set s.smem ~key:addr ~data:id;
    if dirty then Hash_set.add s.dirty_mem addr;
    let delta = (if id = 0 then 0 else 1) - if old = 0 then 0 else 1 in
    if delta <> 0 then begin
      let page = page_of addr in
      let n = Option.value (Hashtbl.find s.spages page) ~default:0 + delta in
      if n = 0 then Hashtbl.remove s.spages page
      else Hashtbl.set s.spages ~key:page ~data:n;
      if n = 0 || (n = 1 && delta > 0) then reprotect t page
    end
  end

(* the changes of the taint of an instruction, which are undone, if it
   faults *)
let write_reg_taint t name id =
  let old = reg_taint t name in
  if old <> id then begin
    t.undo <- (fun () -> set_reg_taint_id t name old) :: t.undo;
    set_reg_taint_id t name id
  end

let write_mem_taint t addr id =
  let old = mem_taint t addr in
  if old <> id then begin
    t.undo <- (fun () -> set_mem_taint_id t addr old) :: t.undo;
    set_mem_taint_id t addr id
  end

(* the bytes of the memory, regardless of the permissions *)
let mem_read t addr n =
  check t;
  String.init n ~f:(fun i ->
      let addr = Int64.(addr + of_int i) in
      match Hashtbl.find t.pages (page_of addr) with
      | Some p -> Bigstring.get p.data (offset addr)
      | None ->
          error uc_err_read_unmapped
            "Invalid memory read (UC_ERR_READ_UNMAPPED)")

let write_mem t addr data =
  check t;
  String.iteri data ~f:(fun i c ->
      let addr = Int64.(addr + of_int i) in
      match Hashtbl.find t.pages (page_of addr) with
      | Some p ->
          code_written t p ~range:(addr, 1L);
          Bigstring.set p.data (offset addr) c
      | None ->
          error uc_err_write_unmapped
            "Invalid memory write (UC_ERR_WRITE_UNMAPPED)")

let mem_regions t =
  Hashtbl.to_alist t.pages
  |> List.sort ~compare:(fun (x, _) (y, _) -> Int64.compare x y)
  |> List.fold ~init:[] ~f:(fun acc (page, p) ->
      let last = Int64.(page + page_size - 1L) in
      match acc with
      | (first, prev, perm) :: rest
        when Int64.(prev + 1L = page)
             && Engine.Perm.(mem perm p.perm && mem p.perm perm) ->
          (first, last, perm) :: rest
      | _ -> (page, last, p.perm) :: acc)
  |> List.rev

(* the hooks *)

(* the blocks of the JIT run, unless a hook needs the accesses, or the
   instructions, that the blocks run, and they are checked again against
   the hooks of the code *)
let unchain (j : jit) =
  Bap_lifted_jit.Runtime.unlink_all j.mem;
  Hashtbl.iter j.blocks ~f:(function
    | Compiled b -> b.chained <- false
    | Counting _ | Failed -> ())

(* the ranges of the hooks of the code, that span at most this number of
   pages, are indexed by their pages *)
let max_hooked_pages = 64L

let partition hooks =
  let live = List.filter hooks ~f:(fun h -> not h.deleted) in
  let only f = Array.of_list (List.filter live ~f:(fun h -> f h.kind)) in
  let mem access = function
    | Mem (accesses, _) ->
        List.exists accesses ~f:(List.mem access ~equal:Poly.equal)
    | _ -> false
  in
  let code = only (function Code _ | Sites _ -> true | _ -> false)
  and blocks = only (function Block _ -> true | _ -> false) in
  let code_pages =
    let pages = Int64.Hash_set.create () in
    Array.fold (Array.append code blocks) ~init:(Some pages) ~f:(fun acc h ->
        match (acc, h.first, h.last) with
        | Some pages, _, _ when match h.kind with Sites _ -> true | _ -> false
          -> (
            match h.kind with
            | Sites (sites, _) ->
                Hash_set.iter sites ~f:(fun a -> Hash_set.add pages (page_of a));
                Some pages
            | _ -> acc)
        | Some pages, Some first, Some last
          when Int64.(first <= last)
               && Int64.(
                    (page_of last - page_of first) / page_size
                    <= max_hooked_pages) ->
            let rec add page =
              Hash_set.add pages page;
              if Int64.(page < page_of last) then add Int64.(page + page_size)
            in
            add (page_of first);
            Some pages
        | _ -> None)
  in
  {
    code;
    blocks;
    code_pages;
    reads = only (mem [ Engine.Read; Read_after ]);
    writes = only (mem [ Engine.Write ]);
    invalid_mem = only (function Mem_invalid _ -> true | _ -> false);
    trace_code = only (function Trace_code _ -> true | _ -> false);
    trace_mem = only (function Trace_mem _ -> true | _ -> false);
    interrupts = only (function Interrupt _ -> true | _ -> false);
    invalid_insns = only (function Invalid_insn _ -> true | _ -> false);
    unsupported_insns = only (function Unsupported _ -> true | _ -> false);
  }

let hooks_changed t =
  t.by_kind <- partition t.hooks;
  Option.iter t.jit ~f:(fun j ->
      unchain j;
      j.gen <- j.gen + 1;
      Hashtbl.iteri t.pages ~f:(fun ~key:page ~data:p ->
          Bap_lifted_jit.Runtime.protect j.mem page (effective t page p.perm));
      j.traced <- not (Array.is_empty t.by_kind.trace_code);
      (* the traces of the whole blocks, without the accesses *)
      let native =
        Array.for_all t.by_kind.trace_code ~f:(fun h ->
            match h.kind with
            | Trace_code tr ->
                Trace.blocks tr && Option.is_none h.first
                && Option.is_none h.last
            | _ -> false)
        && Array.is_empty t.by_kind.trace_mem
        && Array.length t.by_kind.trace_code <= 4
      in
      j.native <- j.traced && native;
      Bap_lifted_jit.Runtime.traces j.mem
        (if j.native then
           Array.filter_map t.by_kind.trace_code ~f:(fun h ->
               match h.kind with Trace_code tr -> Some tr | _ -> None)
         else [||]);
      j.whole <-
        (not (Poly.equal t.arch Engine.Arm))
        && not
             (List.exists t.hooks ~f:(fun h ->
                  match h.kind with
                  | Trace_code _ | Block _ -> true
                  | _ -> false)))

let add t ?first ?last kind =
  check t;
  let h = { first; last; kind; deleted = false } in
  t.hooks <- t.hooks @ [ h ];
  hooks_changed t;
  h

let delete t h =
  h.deleted <- true;
  t.hooks <- List.filter t.hooks ~f:(fun h' -> not (phys_equal h h'));
  hooks_changed t

let covers h addr =
  match h.kind with
  | Sites (sites, _) -> Hash_set.mem sites addr
  | _ -> (
      match (h.first, h.last) with
      | Some first, Some last when Int64.(first <= last) ->
          Int64.(addr >= first && addr <= last)
      | _ -> true)

(* the hooks of a kind, but the ones, that the hooks before them deleted *)
let each hooks f = Array.iter hooks ~f:(fun h -> if not h.deleted then f h)

let mem_hooks t access addr size value =
  let hooks =
    match access with Engine.Write -> t.by_kind.writes | _ -> t.by_kind.reads
  in
  each hooks (fun h ->
      match h.kind with
      | Mem (accesses, f)
        when covers h addr && List.mem accesses access ~equal:Poly.equal ->
          f access addr size value
      | _ -> ())

(* if a hook of the reads sees the access, before which the read is
   checked, see [load_value], but not the writes, as Unicorn calls the
   hooks of the writes before it checks them *)
let reads_hooked t addr =
  Array.exists t.by_kind.reads ~f:(fun h -> (not h.deleted) && covers h addr)

(* The traces, that the engine records, as the native hooks of Unicorn
   record them, see [Trace]. *)

module Record = Trace.Record

let ranges_array ranges =
  List.concat_map ranges ~f:(fun (addr, size) -> [ addr; size ])
  |> Array.of_list

(* the boundary, before the instruction, that runs, of the writes of a
   hook *)
(* the boundary of the writes of a hook, before the instruction, that
   runs, which the trace of the blocks has, as Unicorn has the whole
   block, when its hooks run, though the engine extends the block with
   the instruction after them, so it is extended, and trimmed back *)
let bound_running t ~regs ~mem ranges =
  each t.by_kind.trace_code (fun h ->
      match h.kind with
      | Trace_code tr ->
          let early = Trace.blocks tr && (not t.block) && not t.recorded in
          if early then Record.extend tr t.current_size;
          Record.bound tr regs mem true t.current (ranges_array ranges) false;
          if early then Record.unrun tr t.current
      | _ -> ())

let wrote_regs t =
  if t.running then bound_running t ~regs:true ~mem:false []
  else t.wrote_regs <- true

let wrote_mem t addr size =
  let fresh = ref true in
  pages_of addr (Int64.of_int size) (fun page ->
      if not (Hashtbl.mem t.fresh page) then fresh := false);
  if size > 0 && not !fresh then
    if t.running then
      bound_running t ~regs:false ~mem:true [ (addr, Int64.of_int size) ]
    else if List.length t.wrote >= 4096 then t.wrote_all <- true
    else t.wrote <- (addr, Int64.of_int size) :: t.wrote

(* the writes, while the emulation was stopped, make a boundary, when it
   starts *)
let mark t =
  let mem = (not (List.is_empty t.wrote)) || t.wrote_all in
  if t.wrote_regs || mem then
    each t.by_kind.trace_code (fun h ->
        match h.kind with
        | Trace_code tr ->
            Record.bound tr t.wrote_regs mem false 0L
              (ranges_array (List.rev t.wrote))
              t.wrote_all
        | _ -> ());
  t.wrote_regs <- false;
  t.wrote <- [];
  t.wrote_all <- false;
  Hashtbl.clear t.fresh

let reg_write t id x =
  wrote_regs t;
  write_reg t id x

let reg_write_bytes t id data =
  wrote_regs t;
  write_reg_bytes t id data

let registers_restored t = t.wrote_regs <- false

let mem_write t addr data =
  wrote_mem t addr (String.length data);
  write_mem t addr data

(* if the instruction, that runs, read the bytes already, since it
   wrote them last, which the semantics may read again, e.g., an operand,
   that the flags use too, but Unicorn reads once *)
let read_again t addr size =
  List.mem t.reads (addr, size) ~equal:(fun (a, n) (b, m) ->
      Int64.equal a b && n = m)

let trace_access t ~write addr size value old =
  let read = (addr, size) in
  let again = (not write) && read_again t addr size in
  if write then
    t.reads <-
      List.filter t.reads ~f:(fun (a, n) ->
          Int64.(a + of_int n <= addr || addr + of_int size <= a))
  else if not again then t.reads <- read :: t.reads;
  if not again then
    each t.by_kind.trace_mem (fun h ->
        match h.kind with
        | Trace_mem tr when covers h addr ->
            Record.access tr write addr size value old t.current
        | _ -> ())

(* the instruction, that runs, in the traces of the code *)
let trace_insn t pc size thumb =
  t.reads <- [];
  each t.by_kind.trace_code (fun h ->
      match h.kind with
      | Trace_code tr when covers h pc ->
          if Trace.blocks tr && not t.block then Record.extend tr size
          else Record.record tr pc size thumb
      | _ -> ());
  t.recorded <- true;
  t.block <- false

(* the instruction, that didn't run, e.g., as it faulted *)
let unrun t pc =
  each t.by_kind.trace_code (fun h ->
      match h.kind with Trace_code tr -> Record.unrun tr pc | _ -> ())

(* the hooks of the invalid access, the access is retried, if one of them
   handled it, and else the instruction faults *)
let invalid t access addr size value =
  let handled = ref false in
  each t.by_kind.invalid_mem (fun h ->
      match h.kind with
      | Mem_invalid (accesses, f)
        when (not !handled) && covers h addr
             && List.mem accesses access ~equal:Poly.equal ->
          if f access addr size value then handled := true
      | _ -> ());
  if not !handled then raise (Fault (access, addr))

(* the accesses of the instructions, which check the permissions *)

let rec page_for t access addr size value =
  match Hashtbl.find t.pages (page_of addr) with
  | None ->
      let unmapped : Engine.access =
        match access with
        | `read -> Read_unmapped
        | `write -> Write_unmapped
        | `fetch -> Fetch_unmapped
      in
      invalid t unmapped addr size value;
      page_for t access addr size value
  | Some p ->
      let needed, prot =
        match access with
        | `read -> (Engine.Perm.read, Engine.Read_prot)
        | `write -> (Engine.Perm.write, Engine.Write_prot)
        | `fetch -> (Engine.Perm.exec, Engine.Fetch_prot)
      in
      if Engine.Perm.mem p.perm needed then p
      else begin
        invalid t prot addr size value;
        page_for t access addr size value
      end

let load t addr n =
  let bytes =
    String.init n ~f:(fun i ->
        let addr = Int64.(addr + of_int i) in
        let p = page_for t `read addr n 0L in
        Bigstring.get p.data (offset addr))
  in
  bytes

let store t addr data value =
  String.iteri data ~f:(fun i c ->
      let addr = Int64.(addr + of_int i) in
      let p = page_for t `write addr (String.length data) value in
      code_written t p ~range:(addr, 1L);
      let off = offset addr in
      let old = Bigstring.get p.data off in
      t.undo <- (fun () -> Bigstring.set p.data off old) :: t.undo;
      Bigstring.set p.data off c)

(* the values, of at most 64 bits, as the integers, whose bits above the
   width are zeros, and the wider ones, as the words *)

type value =
  | S of int * int64  (** the width and the bits *)
  | W of word
  | Memory of (int64 * value * endian * size * int) list
      (** the stores, with the taints of their values, see [shadow] *)

let mask w = if w >= 64 then -1L else Int64.((1L lsl w) - 1L)
let norm w x = Int64.(x land mask w)

let sext w x =
  if w >= 64 then x else Int64.((x lsl Int.(64 - w)) asr Int.(64 - w))

let small w x =
  if w <= 64 then S (w, norm w x) else W (Word.of_int64 ~width:w x)

let of_word x =
  let w = Word.bitwidth x in
  if w <= 64 then S (w, Word.to_int64_exn (Word.extract_exn ~hi:(w - 1) x))
  else W x

let word = function
  | S (w, x) -> Word.of_int64 ~width:w x
  | W x -> x
  | Memory _ -> raise (Unsupported_insn "a memory as a value")

let width = function
  | S (w, _) -> w
  | W x -> Word.bitwidth x
  | Memory _ -> raise (Unsupported_insn "a memory as a value")

(* the lower 64 bits *)
let bits = function
  | S (_, x) -> x
  | W x -> Word.to_int64_exn (Word.extract_exn ~hi:63 x)
  | Memory _ -> raise (Unsupported_insn "a memory as a value")

let is_zero = function
  | S (_, x) -> Int64.equal x 0L
  | v -> Word.is_zero (word v)

let bool b = S (1, if b then 1L else 0L)

(* the operations, whose operands the semantics may make wrong, e.g., of
   the widths, that don't match, which raise, make the instruction
   unsupported, rather than end the emulation, as the hooks aren't
   called in them *)
let semantic f =
  try f () with
  | Invalid_argument msg | Failure msg -> raise (Unsupported_insn msg)
  | Division_by_zero -> raise (Unsupported_insn "a division by zero")

(* the operations of BIL, see [Bil.Apply], on the small values *)
let binop (op : binop) x y =
  semantic @@ fun () ->
  match (x, y) with
  | S (w, a), S (w', b) -> (
      let same = Int.equal w w' in
      let open Int64 in
      let shift f =
        (* the shifts by the width, or more, saturate *)
        if b < 0L || b >= of_int w then f true 0 else f false (to_int_exn b)
      in
      match op with
      | PLUS when same -> S (w, norm w (a + b))
      | MINUS when same -> S (w, norm w (a - b))
      | TIMES when same -> S (w, norm w (a * b))
      | DIVIDE when same -> S (w, norm w (Stdlib.Int64.unsigned_div a b))
      | MOD when same -> S (w, norm w (Stdlib.Int64.unsigned_rem a b))
      | SDIVIDE when same ->
          S (w, norm w (Stdlib.Int64.div (sext w a) (sext w' b)))
      | SMOD when same -> S (w, norm w (Stdlib.Int64.rem (sext w a) (sext w' b)))
      | LSHIFT ->
          shift (fun over n -> S (w, if over then 0L else norm w (a lsl n)))
      | RSHIFT -> shift (fun over n -> S (w, if over then 0L else a lsr n))
      | ARSHIFT ->
          let s = sext w a in
          shift (fun over n ->
              S
                ( w,
                  norm w (if over then if s < 0L then -1L else 0L else s asr n)
                ))
      | AND when same -> S (w, a land b)
      | OR when same -> S (w, a lor b)
      | XOR when same -> S (w, a lxor b)
      | EQ when same -> bool (equal a b)
      | NEQ when same -> bool (not (equal a b))
      | LT when same -> bool Int.(Stdlib.Int64.unsigned_compare a b < 0)
      | LE when same -> bool Int.(Stdlib.Int64.unsigned_compare a b <= 0)
      | SLT when same -> bool (sext w a < sext w' b)
      | SLE when same -> bool (sext w a <= sext w' b)
      | _ -> of_word (Bil.Apply.binop op (word x) (word y)))
  | _ -> of_word (Bil.Apply.binop op (word x) (word y))

let unop (op : unop) x =
  semantic @@ fun () ->
  match x with
  | S (w, a) -> (
      match op with
      | NEG -> S (w, norm w (Int64.neg a))
      | NOT -> S (w, norm w (Int64.lnot a)))
  | x -> of_word (Bil.Apply.unop op (word x))

let cast (kind : cast) n x =
  semantic @@ fun () ->
  match x with
  | S (w, a) when n <= 64 -> (
      match kind with
      | UNSIGNED -> S (n, norm n a)
      | SIGNED -> S (n, norm n (sext w a))
      | LOW -> S (n, norm n a)
      | HIGH -> S (n, norm n (if w > n then Int64.(a lsr Int.(w - n)) else a)))
  | x -> of_word (Bil.Apply.cast kind n (word x))

let extract ~hi ~lo x =
  semantic @@ fun () ->
  match x with
  | S (_, a) when hi < 64 && lo <= hi ->
      let w = hi - lo + 1 in
      S (w, norm w Int64.(a lsr lo))
  | x -> of_word (Word.extract_exn ~hi ~lo (word x))

let concat x y =
  semantic @@ fun () ->
  match (x, y) with
  | S (a, x), S (b, y) when a + b <= 64 -> S (a + b, Int64.((x lsl b) lor y))
  | _ -> of_word (Word.concat (word x) (word y))

let bytes_of_word endian x =
  Word.enum_chars x endian |> Sequence.to_list |> String.of_char_list

(* the bytes of the value, in the order *)
let bytes_of_value endian = function
  | S (w, x) when w mod 8 = 0 ->
      let n = w / 8 in
      String.init n ~f:(fun i ->
          let k =
            match endian with LittleEndian -> i | BigEndian -> n - 1 - i
          in
          Char.of_int_exn Int64.(to_int_exn ((x lsr Int.(k * 8)) land 0xFFL)))
  | v -> bytes_of_word endian (word v)

let value_of_bytes endian data =
  let n = String.length data in
  if n <= 8 then (
    let x = ref 0L in
    for i = 0 to n - 1 do
      let k = match endian with LittleEndian -> n - 1 - i | BigEndian -> i in
      x := Int64.((!x lsl 8) lor of_int (Char.to_int data.[k]))
    done;
    S (n * 8, !x))
  else W (Word.of_binary ~width:(n * 8) endian data)

let load_value t stores addr endian size =
  let n = Size.in_bytes size in
  (* the stores of the expression, that aren't done yet, the latest first *)
  let pending =
    List.find stores ~f:(fun (a, _, _, s, _) ->
        Int64.equal a addr && Size.equal s size)
  in
  let sh = t.shadow in
  match pending with
  | Some (_, x, _, _, taint) ->
      if sh.on then sh.cur <- moves sh taint;
      x
  | None ->
      (* the hooks see a read once, as in Unicorn *)
      let again = read_again t addr n in
      (* the read faults before the hooks, as in Unicorn, so that they
         don't see it again, when the instruction runs again, though the
         write faults after them, see [write_stores] *)
      if (not again) && reads_hooked t addr then ignore (load t addr n : string);
      if not again then mem_hooks t Read addr n 0L;
      let x = value_of_bytes endian (load t addr n) in
      if not again then mem_hooks t Read_after addr n (bits x);
      trace_access t ~write:false addr n (bits x) 0L;
      if sh.on then begin
        let taint = ref 0 in
        if not (Hashtbl.is_empty sh.smem) then
          for i = 0 to n - 1 do
            taint := union sh !taint (mem_taint t Int64.(addr + of_int i))
          done;
        sh.cur <- moves sh !taint
      end;
      x

let addr_of v = bits v

(* the registers of BAP, whose bytes are in the order of the host *)

let host_word b =
  let s = Bytes.to_string b in
  let s = if Sys.big_endian then String.rev s else s in
  Word.of_binary ~width:(String.length s * 8) LittleEndian s

let host_bytes size x =
  let s =
    bytes_of_word LittleEndian (Word.extract_exn ~hi:((size * 8) - 1) x)
  in
  if Sys.big_endian then String.rev s else s

let read_host b =
  let n = Bytes.length b in
  let x = ref 0L in
  for i = 0 to n - 1 do
    let k = if Sys.big_endian then i else n - 1 - i in
    x := Int64.((!x lsl 8) lor of_int (Char.to_int (Bytes.get b k)))
  done;
  !x

let write_host b x =
  let n = Bytes.length b in
  for i = 0 to n - 1 do
    let k = if Sys.big_endian then n - 1 - i else i in
    Bytes.set b k
      (Char.of_int_exn Int64.(to_int_exn ((x lsr Int.(i * 8)) land 0xFFL)))
  done

(* The instructions are compiled to the closures, once, when they are
   lifted, whose registers are their bytes and bits, and whose
   temporaries, i.e., the virtual variables and the variables of the
   lets, are the slots of an array, so that an instruction, that runs
   again, doesn't look up the names of its variables. *)

module F = Primus_lisp_softfloat

type ctx = {
  t : t;
  slots : int String.Table.t;  (** the virtual variables *)
  mutable lets : (string * int) list;  (** the innermost first *)
  mutable size : int;
  env : value array ref;
  sh : shadow option;
      (** if the closures propagate the taint, see [shadow], whose taints of the
          virtual variables are in [senv] *)
  senv : int array ref;
}

let fresh ctx =
  let i = ctx.size in
  ctx.size <- i + 1;
  i

let slot ctx name =
  match List.Assoc.find ctx.lets name ~equal:String.equal with
  | Some i -> i
  | None -> Hashtbl.find_or_add ctx.slots name ~default:(fun () -> fresh ctx)

let unsupported_now reason () = raise (Unsupported_insn reason)

let rec read_var ctx v : unit -> value =
  match ctx.sh with
  | None -> read_value ctx v
  | Some s -> (
      let f = read_value ctx v in
      let name = Var.name v in
      if Var.is_virtual v || List.Assoc.mem ctx.lets name ~equal:String.equal
      then (
        let i = slot ctx name and senv = ctx.senv in
        fun () ->
          s.cur <- !senv.(i);
          f ())
      else
        match Var.typ v with
        | Mem _ ->
            fun () ->
              s.cur <- 0;
              f ()
        | _ ->
            let t = ctx.t and key = owner ctx.t name in
            fun () ->
              s.cur <- reg_taint t key;
              f ())

and read_value ctx v : unit -> value =
  let t = ctx.t and env = ctx.env in
  let name = Var.name v in
  if Var.is_virtual v || List.Assoc.mem ctx.lets name ~equal:String.equal then
    let i = slot ctx name in
    fun () -> !env.(i)
  else
    match t.config.locate name with
    | Some (id, lo, width) ->
        let b = reg_bytes t id and hi = lo + width - 1 in
        if Bytes.length b <= 8 then fun () ->
          S (width, norm width Int64.(read_host b lsr lo))
        else fun () -> of_word (Word.extract_exn ~hi ~lo (host_word b))
    | None -> (
        match Var.typ v with
        | Imm n -> (
            let zero = small n 0L in
            fun () ->
              match Hashtbl.find t.others name with
              | Some x -> of_word x
              | None -> zero)
        | Mem _ -> fun () -> Memory []
        | Unk -> unsupported_now ("an untyped " ^ name))

let write_stores t stores =
  (* the stores to the memory, in their order *)
  List.iter (List.rev stores) ~f:(fun (addr, x, endian, size, taint) ->
      let n = Size.in_bytes size in
      let data = bytes_of_value endian x in
      mem_hooks t Write addr n (bits x);
      (* the bytes, that the write overwrites, see [Trace.accesses] *)
      let old =
        if n > 8 then 0L
        else
          match mem_read t addr n with
          | old ->
              String.foldi old ~init:0L ~f:(fun i acc c ->
                  Int64.(acc lor (of_int (Char.to_int c) lsl Int.(8 * i))))
          | exception Engine.Error _ -> 0L
      in
      trace_access t ~write:true addr n (bits x) old;
      store t addr data 0L;
      let sh = t.shadow in
      if sh.on && (taint <> 0 || not (Hashtbl.is_empty sh.smem)) then begin
        let taint = moves sh taint in
        for i = 0 to n - 1 do
          write_mem_taint t Int64.(addr + of_int i) taint
        done
      end)

let rec write_var ctx v : value -> unit =
  match ctx.sh with
  | None -> write_value ctx v
  | Some s ->
      let f = write_value ctx v in
      let name = Var.name v in
      if Var.is_virtual v then (
        let i = slot ctx name and senv = ctx.senv in
        fun x ->
          (match x with Memory _ -> () | _ -> !senv.(i) <- s.cur);
          f x)
      else
        let t = ctx.t and key = owner ctx.t name in
        (* the write of a part of the register keeps the taint of the
           rest of it *)
        let full = String.equal key name in
        fun x ->
          (match x with
          | Memory _ -> ()
          | _ ->
              write_reg_taint t key
                (if full then s.cur else union s (reg_taint t key) s.cur));
          f x

and write_value ctx v : value -> unit =
  let t = ctx.t and env = ctx.env in
  let name = Var.name v in
  let other value =
    match value with
    | Memory stores -> write_stores t stores
    | x ->
        let x = word x in
        let prev = Hashtbl.find t.others name in
        t.undo <-
          (fun () ->
            match prev with
            | Some p -> Hashtbl.set t.others ~key:name ~data:p
            | None -> Hashtbl.remove t.others name)
          :: t.undo;
        Hashtbl.set t.others ~key:name ~data:x
  in
  if Var.is_virtual v then
    let i = slot ctx name in
    function
    | Memory stores -> write_stores t stores
    | value -> !env.(i) <- value
  else
    match t.config.locate name with
    | None -> other
    | Some (id, lo, width) -> (
        let b = reg_bytes t id in
        let size = Bytes.length b in
        let bits = size * 8 in
        let undo () =
          let old = Bytes.copy b in
          t.undo <-
            (fun () ->
              Bytes.blit ~src:old ~src_pos:0 ~dst:b ~dst_pos:0
                ~len:(Bytes.length b))
            :: t.undo
        in
        function
        | Memory stores -> write_stores t stores
        | S (_, x) when size <= 8 ->
            undo ();
            let m = Int64.(mask width lsl lo) in
            let prev = read_host b in
            write_host b
              Int64.(prev land lnot m lor ((norm width x lsl lo) land m))
        | x ->
            undo ();
            let x = Word.extract_exn ~hi:(width - 1) (word x) in
            let x =
              if lo = 0 && width = bits then x
              else
                let prev = host_word b in
                let x =
                  if lo = 0 then x
                  else Word.concat x (Word.extract_exn ~hi:(lo - 1) prev)
                in
                if lo + width = bits then x
                else
                  Word.concat
                    (Word.extract_exn ~hi:(bits - 1) ~lo:(lo + width) prev)
                    x
            in
            Bytes.From_string.blit ~src:(host_bytes size x) ~src_pos:0 ~dst:b
              ~dst_pos:0 ~len:size)

let rec compile_exp ctx : exp -> unit -> value =
 fun exp ->
  match ctx.sh with
  | None -> compile_plain ctx exp
  | Some s -> compile_tainted ctx s exp

and compile_plain ctx : exp -> unit -> value = function
  | Var v -> read_var ctx v
  | Int x ->
      let r = of_word x in
      fun () -> r
  | Load (mem, addr, endian, size) -> (
      let t = ctx.t in
      let mem = compile_exp ctx mem and addr = compile_exp ctx addr in
      fun () ->
        let a = addr_of (addr ()) in
        match mem () with
        | Memory stores -> load_value t stores a endian size
        | _ -> raise (Unsupported_insn "a load from a value"))
  | Store (mem, addr, x, endian, size) -> (
      let mem = compile_exp ctx mem
      and addr = compile_exp ctx addr
      and x = compile_exp ctx x in
      fun () ->
        let a = addr_of (addr ()) in
        let x = x () in
        match mem () with
        | Memory stores -> Memory ((a, x, endian, size, 0) :: stores)
        | _ -> raise (Unsupported_insn "a store to a value"))
  | BinOp (op, x, y) -> (
      let x = compile_exp ctx x and y = compile_exp ctx y in
      match op with
      | DIVIDE | SDIVIDE | MOD | SMOD ->
          fun () ->
            let x = x () and y = y () in
            (* the division by zero is the exception of the target, e.g.,
               of x86, which Primus raises *)
            if is_zero y then raise (Unsupported_insn "a division by zero")
            else binop op x y
      | _ -> fun () -> binop op (x ()) (y ()))
  | UnOp (op, x) ->
      let x = compile_exp ctx x in
      fun () -> unop op (x ())
  | Cast (kind, n, x) ->
      let x = compile_exp ctx x in
      fun () -> cast kind n (x ())
  | Let (v, x, body) ->
      let x = compile_exp ctx x in
      let i = fresh ctx in
      ctx.lets <- (Var.name v, i) :: ctx.lets;
      let body = compile_exp ctx body in
      ctx.lets <- List.tl_exn ctx.lets;
      let env = ctx.env in
      fun () ->
        !env.(i) <- x ();
        body ()
  | Unknown (_, typ) -> (
      (* the undefined values, e.g., of the flags, are zeros *)
      match typ with
      | Imm n ->
          let r = small n 0L in
          fun () -> r
      | _ -> unsupported_now "an unknown value")
  | Ite (c, x, y) ->
      let c = compile_exp ctx c
      and x = compile_exp ctx x
      and y = compile_exp ctx y in
      fun () -> if is_zero (c ()) then y () else x ()
  | Extract (hi, lo, x) ->
      let x = compile_exp ctx x in
      fun () -> extract ~hi ~lo (x ())
  | Concat (x, y) ->
      let x = compile_exp ctx x and y = compile_exp ctx y in
      fun () -> concat (x ()) (y ())

(* the expression, that computes its value, and its taint in [s.cur],
   as the policies of the taint propagate it, see [moves] and [comps]:
   the conditions of [Ite] don't taint its value, as in the interpreter,
   whose [ite] returns the value of a branch *)
and compile_tainted ctx s : exp -> unit -> value = function
  | Var v -> read_var ctx v
  | Int x ->
      let r = of_word x in
      fun () ->
        s.cur <- 0;
        r
  | Load (mem, addr, endian, size) -> (
      let t = ctx.t in
      let mem = compile_exp ctx mem and addr = compile_exp ctx addr in
      fun () ->
        let a = addr_of (addr ()) in
        match mem () with
        | Memory stores -> load_value t stores a endian size
        | _ -> raise (Unsupported_insn "a load from a value"))
  | Store (mem, addr, x, endian, size) -> (
      let mem = compile_exp ctx mem
      and addr = compile_exp ctx addr
      and x = compile_exp ctx x in
      fun () ->
        let a = addr_of (addr ()) in
        let x = x () in
        let taint = s.cur in
        match mem () with
        | Memory stores ->
            s.cur <- 0;
            Memory ((a, x, endian, size, taint) :: stores)
        | _ -> raise (Unsupported_insn "a store to a value"))
  | BinOp (op, x, y) ->
      let x = compile_exp ctx x and y = compile_exp ctx y in
      let apply =
        match op with
        | DIVIDE | SDIVIDE | MOD | SMOD ->
            fun a b ->
              if is_zero b then raise (Unsupported_insn "a division by zero")
              else binop op a b
        | _ -> binop op
      in
      fun () ->
        let a = x () in
        let ta = s.cur in
        let b = y () in
        let r = apply a b in
        s.cur <- comps s (union s ta s.cur);
        r
  | UnOp (op, x) ->
      let x = compile_exp ctx x in
      fun () ->
        let a = x () in
        s.cur <- comps s s.cur;
        unop op a
  | Cast (kind, n, x) ->
      let x = compile_exp ctx x in
      fun () ->
        let a = x () in
        s.cur <- moves s s.cur;
        cast kind n a
  | Let (v, x, body) ->
      let x = compile_exp ctx x in
      let i = fresh ctx in
      ctx.lets <- (Var.name v, i) :: ctx.lets;
      let body = compile_exp ctx body in
      ctx.lets <- List.tl_exn ctx.lets;
      let env = ctx.env and senv = ctx.senv in
      fun () ->
        !env.(i) <- x ();
        !senv.(i) <- s.cur;
        body ()
  | Unknown (_, typ) -> (
      match typ with
      | Imm n ->
          let r = small n 0L in
          fun () ->
            s.cur <- 0;
            r
      | _ -> unsupported_now "an unknown value")
  | Ite (c, x, y) ->
      let c = compile_exp ctx c
      and x = compile_exp ctx x
      and y = compile_exp ctx y in
      fun () -> if is_zero (c ()) then y () else x ()
  | Extract (hi, lo, x) ->
      let x = compile_exp ctx x in
      fun () ->
        let a = x () in
        s.cur <- moves s s.cur;
        extract ~hi ~lo a
  | Concat (x, y) ->
      let x = compile_exp ctx x and y = compile_exp ctx y in
      fun () ->
        let a = x () in
        let ta = s.cur in
        let b = y () in
        s.cur <- moves s (union s ta s.cur);
        concat a b

(* the intrinsics of IEEE 754, e.g., intrinsic:fadd_rne_ieee754_binary_64,
   whose operands are intrinsic:x0, ..., and whose result is intrinsic:y0,
   as the Primus Lisp program of ieee754-intrinsics.lisp runs them *)
let compile_intrinsic ctx tid : unit -> unit =
  let t = ctx.t in
  match t.config.name tid with
  | None -> unsupported_now ("a call of " ^ Tid.name tid)
  | Some "intrinsic:interrupt" ->
      (* int n of x86, whose interrupt is n *)
      let n = read_var ctx (Var.create "intrinsic:x0" (Type.imm 8)) in
      fun () -> raise (Trap (Int64.to_int_exn (bits (n ()))))
  | Some ("intrinsic:syscall" | "intrinsic:svc" | "intrinsic:sysenter") ->
      (* the interrupts of the system calls of Unicorn, after which its
         program counter is the next instruction *)
      let n =
        match t.arch with
        | Arm | Arm64 -> 2
        | Mips -> 17
        | Ppc | Riscv -> 8
        | X86 -> -1
      in
      fun () -> raise (Trap n)
  | Some name -> (
      let short = String.chop_prefix_if_exists name ~prefix:"intrinsic:" in
      match F.intrinsic short with
      | None -> unsupported_now ("the intrinsic " ^ name)
      | Some (op, rm, src, dst) -> (
          let nargs =
            match op with
            | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 13 | 14 -> 1
            | 15 -> 3
            | _ -> 2
          in
          let args =
            List.init nargs ~f:(fun i ->
                read_var ctx
                  (Var.create (sprintf "intrinsic:x%d" i) (Type.imm src)))
          in
          let result =
            write_var ctx (Var.create "intrinsic:y0" (Type.imm dst))
          in
          let rm = F.rmode_of_int rm
          and policy = F.policy_of_int t.config.policy in
          fun () ->
            let args =
              List.map args ~f:(fun arg ->
                  let x = arg () in
                  (* the interpreter propagates the taint of the
                     intrinsic, as it runs its program *)
                  (match ctx.sh with
                  | Some s when s.cur <> 0 ->
                      raise (Unsupported_insn ("the tainted " ^ name))
                  | _ -> ());
                  let x = Word.extract_exn ~hi:(src - 1) (word x) in
                  Bitvec.to_bigint (Word.to_bitvec x))
            in
            match F.apply ~op ~rm ~src ~dst policy args with
            | None -> raise (Unsupported_insn ("the intrinsic " ^ name))
            | Some x ->
                Option.iter ctx.sh ~f:(fun s -> s.cur <- 0);
                result (of_word (Word.create (Bitvec.bigint_unsafe x) dst))))

(* the block, that the first block only jumps to, and the others jump
   back to, e.g., the head of the loop of rep movs of x86, so that the
   jump back to it runs the instruction again, as Unicorn runs each
   iteration, with its hooks, and its records in the traces, and the
   instruction ends its block, as in Unicorn *)
let loop_head (blks : blk term list) =
  match blks with
  | [] -> None
  | first :: rest -> (
      let gotos blk =
        Term.enum jmp_t blk |> Seq.to_list
        |> List.filter_map ~f:(fun jmp ->
            match Jmp.kind jmp with Goto (Direct tid) -> Some tid | _ -> None)
      in
      match Term.enum jmp_t first |> Seq.to_list with
      | [ jmp ]
        when Seq.is_empty (Term.enum def_t first)
             &&
             match Jmp.cond jmp with
             | Int x -> not (Word.is_zero x)
             | _ -> false -> (
          match Jmp.kind jmp with
          | Goto (Direct tid)
            when List.exists rest ~f:(fun blk ->
                     List.mem (gotos blk) tid ~equal:Tid.equal) ->
              Some tid
          | _ -> None)
      | _ -> None)

(* the instruction, whose blocks run from the first one *)
let compile ?shadow t ~pc ~next (blks : blk term list) : unit -> next =
  let ctx =
    {
      t;
      slots = String.Table.create ();
      lets = [];
      size = 0;
      env = ref [||];
      sh = shadow;
      senv = ref [||];
    }
  in
  let blks = Array.of_list blks in
  let index tid = Array.findi blks ~f:(fun _ b -> Tid.equal (Term.tid b) tid) in
  let codes = Array.map blks ~f:(fun _ () -> Next) in
  let run i = if i < Array.length codes then codes.(i) () else Next in
  let addr exp =
    let exp = compile_exp ctx exp in
    fun () -> addr_of (exp ())
  in
  let head =
    Option.bind
      (loop_head (Array.to_list blks))
      ~f:(fun tid -> Option.map (index tid) ~f:fst)
  in
  let goto ?(from = 0) : label -> unit -> next = function
    | Indirect exp ->
        let a = addr exp in
        fun () ->
          let a = a () in
          if Int64.equal a next then Next else Jump a
    (* the jump to the instruction itself, e.g., b . of ARM, runs it
       again, after the hooks *)
    | Direct tid when Option.exists (index tid) ~f:(fun (i, _) -> i = 0) ->
        fun () -> Jump pc
    (* the loop back to the head, from any block, but the first one,
       which enters it *)
    | Direct tid
      when Option.exists (index tid) ~f:(fun (i, _) ->
               from > 0 && Option.equal Int.equal (Some i) head) ->
        fun () -> Jump pc
    | Direct tid -> (
        match index tid with
        | Some (i, _) -> fun () -> run i
        | None -> unsupported_now ("a call of " ^ Tid.name tid))
  in
  let call c : unit -> next =
    match Call.target c with
    | Direct tid when Option.is_none (index tid) -> (
        let intrinsic = compile_intrinsic ctx tid in
        let return =
          match Call.return c with
          | Some label -> goto label
          | None -> fun () -> Next
        in
        fun () ->
          match intrinsic () with
          | () -> return ()
          | exception Trap n -> Interrupt_at (n, next))
    | Indirect exp ->
        let a = addr exp in
        fun () -> Jump (a ())
    | label -> goto label
  in
  Array.iteri blks ~f:(fun i blk ->
      let defs =
        Term.enum def_t blk |> Seq.to_list
        |> List.map ~f:(fun def ->
            let lhs = write_var ctx (Def.lhs def)
            and rhs = compile_exp ctx (Def.rhs def) in
            fun () -> lhs (rhs ()))
        |> Array.of_list
      in
      let jumps =
        Term.enum jmp_t blk |> Seq.to_list
        |> List.map ~f:(fun jmp ->
            let cond = compile_exp ctx (Jmp.cond jmp) in
            let target =
              match Jmp.kind jmp with
              | Goto label | Ret label -> goto ~from:i label
              | Call c -> call c
              | Int (n, _) -> fun () -> Interrupt_at (n, next)
            in
            (cond, target))
      in
      let rec jump = function
        (* falls through to the next block of the instruction, if any *)
        | [] -> fun () -> run (i + 1)
        | (cond, target) :: rest -> (
            let rest = jump rest in
            match ctx.sh with
            | None -> fun () -> if is_zero (cond ()) then rest () else target ()
            | Some s ->
                (* the jump, whose condition is tainted, which its
                   observers see, is interpreted *)
                fun () ->
                  let c = cond () in
                  if s.jumps && s.cur <> 0 then
                    raise (Unsupported_insn "a jump on a tainted condition");
                  if is_zero c then rest () else target ())
      in
      let jumps = jump jumps in
      codes.(i) <-
        (fun () ->
          Array.iter defs ~f:(fun def -> def ());
          jumps ()));
  ctx.env := Array.create ~len:ctx.size (S (1, 0L));
  ctx.senv := Array.create ~len:ctx.size 0;
  fun () -> run 0

let taint_info t ~pc ~next blks =
  let defs = List.concat_map blks ~f:(fun b -> Term.enum def_t b |> Seq.to_list)
  and jmps =
    List.concat_map blks ~f:(fun b -> Term.enum jmp_t b |> Seq.to_list)
  in
  let exps =
    List.map defs ~f:Def.rhs
    @ List.concat_map jmps ~f:(fun jmp ->
        Jmp.cond jmp
        :: List.filter_map
             ( Jmp.kind jmp |> function
               | Goto l | Ret l -> [ Some l ]
               | Call c -> [ Some (Call.target c); Call.return c ]
               | Int _ -> [] )
             ~f:(function Some (Indirect e) -> Some e | _ -> None))
  in
  let registers vars =
    List.filter vars ~f:(fun v ->
        (not (Var.is_virtual v))
        && match Var.typ v with Imm _ -> true | _ -> false)
  in
  let free = List.concat_map exps ~f:(fun e -> Set.to_list (Exp.free_vars e)) in
  let reads =
    registers free
    |> List.map ~f:(fun v -> owner t (Var.name v))
    |> List.dedup_and_sort ~compare:String.compare
    |> Array.of_list
  and writes =
    registers (List.map defs ~f:Def.lhs)
    |> List.map ~f:(fun v ->
        let key = owner t (Var.name v) in
        (key, String.equal key (Var.name v)))
    |> List.dedup_and_sort ~compare:Poly.compare
    |> Array.of_list
  and memory =
    List.exists
      (free @ List.map defs ~f:Def.lhs)
      ~f:(fun v -> match Var.typ v with Mem _ -> true | _ -> false)
  in
  {
    reads;
    writes;
    memory;
    shadowed = compile ~shadow:t.shadow t ~pc ~next blks;
  }

(* the bytes of the instruction at [pc], at most [max] of them, which
   the instruction may fetch *)
let fetch t pc =
  let p = page_for t `fetch pc 1 0L in
  ignore p;
  let max = 16 in
  let rec bytes i acc =
    if i = max then acc
    else
      let addr = Int64.(pc + of_int i) in
      match Hashtbl.find t.pages (page_of addr) with
      | Some p when Engine.Perm.(mem p.perm exec) ->
          bytes (i + 1) (Bigstring.get p.data (offset addr) :: acc)
      | _ -> acc
  in
  String.of_char_list (List.rev (bytes 0 []))

(* the Thumb state of ARM, the bit T of CPSR *)
let thumb t =
  match t.cpsr with
  | Some cpsr -> Int64.(reg_read t cpsr land 0x20L <> 0L)
  | None -> false

let set_thumb t on =
  Option.iter t.cpsr ~f:(fun cpsr ->
      let x = reg_read t cpsr in
      write_reg t cpsr Int64.(if on then x lor 0x20L else x land lnot 0x20L))

(* if the blocks of the instruction may jump out of it *)
let may_jump blks =
  let internal tid =
    List.existsi blks ~f:(fun i b -> i > 0 && Tid.equal (Term.tid b) tid)
  in
  Option.is_some (loop_head blks)
  || List.exists blks ~f:(fun blk ->
      Term.enum jmp_t blk
      |> Seq.exists ~f:(fun jmp ->
          match Jmp.kind jmp with
          | Goto (Direct tid) | Ret (Direct tid) -> not (internal tid)
          | _ -> true))

(* if the bytes of the instruction, that are on the page of [pc], are
   its code, as [fetch] would read them *)
let same_code t pc (insn : insn) =
  let p = page_for t `fetch pc 1 0L in
  let off = offset pc and n = String.length insn.code in
  off + n <= Int64.to_int_exn page_size
  &&
  let rec same i =
    i = n
    || Char.equal (Bigstring.get p.data (off + i)) insn.code.[i]
       && same (i + 1)
  in
  same 0

let lifted t pc =
  let thumb = thumb t in
  match Hashtbl.find t.insns pc with
  | Some insn when Bool.equal insn.thumb thumb && same_code t pc insn ->
      Some insn
  | cached -> (
      let code = fetch t pc in
      match cached with
      | Some insn
        when Bool.equal insn.thumb thumb
             && String.is_prefix code ~prefix:insn.code ->
          Some insn
      | _ -> (
          incr lifted_count;
          match timed lift_time (fun () -> t.config.lift ~thumb pc code) with
          | None -> None
          | Some (size, name, blks) ->
              (* the jumps of ARM tell the mode, see [Primus.Interworking] *)
              let blks =
                match t.arch with
                | Arm -> Bap_primus.Std.Primus.Interworking.unmask blks
                | _ -> blks
              in
              let next = Int64.(pc + of_int size) in
              let insn =
                {
                  code = String.prefix code size;
                  size;
                  name;
                  thumb;
                  blks;
                  jumps = may_jump blks;
                  atomic =
                    (if load_linked name then `Load
                     else if store_conditional name then `Store
                     else `None);
                  (* IT, rather than a hint, whose mask is zero *)
                  it =
                    (if
                       thumb && size = 2
                       && Char.equal code.[1] '\xBF'
                       && Char.to_int code.[0] land 0xF <> 0
                     then Some (Char.to_int code.[0])
                     else None);
                  modes =
                    (match t.arch with
                    | Arm ->
                        let width = t.config.bits in
                        let mode dst =
                          snd
                            (Bap_primus.Std.Primus.Interworking.jump ~name
                               ~thumb
                               ~next:(Word.of_int64 ~width next)
                               blks (Word.of_int64 ~width dst))
                        in
                        Some (mode Int64.(next + 4L), mode Int64.(next + 5L))
                    | _ -> None);
                  run = compile t ~pc ~next blks;
                  taint = lazy (taint_info t ~pc ~next blks);
                }
              in
              Hashtbl.set t.insns ~key:pc ~data:insn;
              Some insn))

(* the target of the jump of the instruction, and its mode on ARM *)
(* the target of the jump, whose mode, after the jump, is the one, that
   [Primus.Interworking.jump] tells, which depends on the parity of the
   target, and on the instruction only, but for the next instruction *)
let jump t (insn : insn) ~next a =
  match insn.modes with
  | Some (even, odd) ->
      let dst = Int64.(a land lnot 1L) in
      set_thumb t
        (if Int64.equal dst next then insn.thumb
         else if Int64.(a land 1L = 1L) then odd
         else even);
      dst
  | None -> a

(* The IT blocks of Thumb, whose state is the IT bits of CPSR, as QEMU
   keeps it: IT[1:0] are the bits 26:25, and IT[7:2] are 15:10, and the
   condition of the instruction is IT[7:4], while IT[3:0] isn't zero. *)

let itstate t =
  match t.cpsr with
  | Some id when Poly.equal t.arch Engine.Arm ->
      let c = reg_read t id in
      Int64.(
        to_int_exn ((c lsr 25) land 3L lor (((c lsr 10) land 0x3FL) lsl 2)))
  | _ -> 0

let set_itstate t it =
  Option.iter t.cpsr ~f:(fun id ->
      let c = reg_read t id in
      let c = Int64.(c land lnot ((3L lsl 25) lor (0x3FL lsl 10))) in
      write_reg t id
        Int64.(
          c
          lor (of_int Int.(it land 3) lsl 25)
          lor (of_int Int.((it lsr 2) land 0x3F) lsl 10)))

let advance_it it =
  if it land 7 = 0 then 0 else it land 0xE0 lor ((it lsl 1) land 0x1F)

(* if the instruction is IT of Thumb, rather than a hint, whose mask is
   zero, then its firstcond and mask *)
let it_insn (insn : insn) = insn.it

let flag t name =
  match t.config.locate name with
  | Some (id, lo, _) -> Int64.((reg_read t id lsr lo) land 1L = 1L)
  | None -> false

let holds t cond =
  let n = flag t "NF"
  and z = flag t "ZF"
  and c = flag t "CF"
  and v = flag t "VF" in
  match cond with
  | 0 -> z
  | 1 -> not z
  | 2 -> c
  | 3 -> not c
  | 4 -> n
  | 5 -> not n
  | 6 -> v
  | 7 -> not v
  | 8 -> c && not z
  | 9 -> (not c) || z
  | 10 -> Bool.equal n v
  | 11 -> not (Bool.equal n v)
  | 12 -> (not z) && Bool.equal n v
  | 13 -> z || not (Bool.equal n v)
  | _ -> true

(* if the instruction is in an IT block, and its condition fails *)
let skipped t insn =
  insn.thumb
  &&
  let it = itstate t in
  it land 0xF <> 0 && not (holds t (it lsr 4))

(* the IT state after the instruction, that ran *)
let next_it t insn =
  if insn.thumb then
    match it_insn insn with
    | Some it -> set_itstate t it
    | None ->
        let it = itstate t in
        if it land 0xF <> 0 then set_itstate t (advance_it it)

(* the code of the block, that is dropped, is released, as the program
   may make the blocks anew, e.g., as it patches its code *)
let release (j : jit) = function
  | Compiled b ->
      Bap_lifted_jit.Runtime.unlink j.mem b.pcs.(0);
      Bap_llvm_jit.release b.native;
      j.live <- j.live - 1
  | Counting _ | Failed -> ()

(* the instruction, that the engine lifted at the address, to run it,
   with the bytes, that it was lifted from, which stay, when the memory
   changes, until it is lifted anew, see [lifted] *)
let insn_at t pc =
  Option.map (Hashtbl.find t.insns pc) ~f:(fun (i : insn) ->
      (i.code, i.name, i.thumb, i.blks))

(* the addresses of the instructions, that the engine lifted, see
   [insn_at] *)
let insn_addrs t = Hashtbl.keys t.insns

let inventory t =
  let blocks =
    Hashtbl.fold t.insns ~init:0 ~f:(fun ~key:_ ~data:(insn : insn) n ->
        n + List.length insn.blks)
  in
  let live = Option.value_map t.jit ~default:0 ~f:(fun j -> j.live) in
  (Hashtbl.length t.insns, blocks, live)

(* the instructions stay, as their bytes are checked, when they run, see
   [lifted], so that [insn_at] has them, when the code is written, and
   the blocks, that the JIT compiled, go *)
let flush_tb t =
  Option.iter t.jit ~f:(fun j ->
      (* the links go at once, rather than with each block *)
      unchain j;
      Hashtbl.iter j.blocks ~f:(release j);
      Hashtbl.clear j.blocks)

(* the hooks of the blocks, at the starts of the blocks, and then of the
   instruction, in their order, but the ones after the hook, that stops
   the emulation, as Unicorn calls them *)
let code_hooks t pc size =
  let k = t.by_kind in
  let unhooked =
    match k.code_pages with
    | Some pages -> not (Hash_set.mem pages (page_of pc))
    | None -> false
  in
  if not unhooked then begin
    let call f = if not t.stopped then f () in
    if t.block then
      each k.blocks (fun h ->
          match h.kind with
          | Block f when covers h pc -> call (fun () -> f pc size)
          | _ -> ());
    each k.code (fun h ->
        match h.kind with
        | (Code f | Sites (_, f)) when covers h pc -> call (fun () -> f pc size)
        | _ -> ())
  end

let stop t = t.stopped <- true

let unsupported t pc =
  t.unsupported <- t.unsupported + 1;
  each t.by_kind.unsupported_insns (fun h ->
      match h.kind with Unsupported f when covers h pc -> f pc | _ -> ());
  (* the instruction is never run here *)
  t.stopped <- true

let invalid_insn t =
  let handled = ref false in
  each t.by_kind.invalid_insns (fun h ->
      match h.kind with
      | Invalid_insn f when not !handled -> handled := f ()
      | _ -> ());
  !handled

let interrupt t n =
  each t.by_kind.interrupts (fun h ->
      match h.kind with Interrupt f -> f n | _ -> ())

let fault_error (access : Engine.access) =
  match access with
  | Read_unmapped ->
      (uc_err_read_unmapped, "Invalid memory read (UC_ERR_READ_UNMAPPED)")
  | Write_unmapped ->
      (uc_err_write_unmapped, "Invalid memory write (UC_ERR_WRITE_UNMAPPED)")
  | Fetch_unmapped ->
      (uc_err_fetch_unmapped, "Invalid memory fetch (UC_ERR_FETCH_UNMAPPED)")
  | Write_prot ->
      (uc_err_write_prot, "Write to write-protected memory (UC_ERR_WRITE_PROT)")
  | Read_prot ->
      (uc_err_read_prot, "Read from non-readable memory (UC_ERR_READ_PROT)")
  | Fetch_prot ->
      (uc_err_fetch_prot, "Fetch from non-executable memory (UC_ERR_FETCH_PROT)")
  | Read | Write | Fetch | Read_after -> (11, "Invalid memory access")

(* The blocks, that the JIT compiles, see Bap_lifted_jit, which start at
   the targets of the jumps, that run [hot] times, and run the
   instructions after them, until the one, that may jump, which ends the
   block, as in Unicorn, at most [max_block] of them, that don't have
   the delay slots, and whose code isn't hooked, but the first one's,
   whose hooks are called before the block runs. The block, whose
   instruction stops, e.g., as its access faults, returns to the
   closures, which run the instruction. The traces of the code record the
   instructions of the blocks, after they ran, while the hooks of the
   accesses, and the traces of them, need the closures. *)

let hot = 32
let max_block = 32

(* the blocks, that are compiled at an address, e.g., of the code, that
   the program patches, and of all addresses, at most, so that the code
   of the program doesn't use all memory, nor the time of the JIT *)
let max_compiles = 8
let max_live = 0x10000

let verbose () =
  Option.equal String.equal (Sys.getenv "BAP_LIFTED_STATS") (Some "verbose")

let hooked ?(blocks = false) t addr =
  let k = t.by_kind in
  let covering = Array.exists ~f:(fun h -> (not h.deleted) && covers h addr) in
  (match k.code_pages with
    | Some pages -> Hash_set.mem pages (page_of addr)
    | None -> true)
  && (covering k.code || (blocks && covering k.blocks))

(* the instructions, that may be in the block at [pc], whose bytes are
   fetched only from the executable pages, as the hooks of the invalid
   fetches are not called *)
(* if the instruction at [pc], that may jump, may run on, after its
   branch, that isn't taken, by its blocks, that reach its end, and its
   branch goes forward, rather than back, e.g., of a loop, which is taken
   rather, and whose target starts its own block *)
let falls pc (insn : insn) =
  let backward =
    List.exists insn.blks ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun jmp ->
            match Jmp.kind jmp with
            | Goto (Indirect (Int x)) ->
                Stdlib.Int64.unsigned_compare
                  (Word.to_int64_exn (Word.extract_exn ~hi:63 x))
                  pc
                <= 0
            | _ -> false))
  in
  (not backward)
  &&
  let blks = Array.of_list insn.blks in
  let index tid = Array.findi blks ~f:(fun _ b -> Tid.equal (Term.tid b) tid) in
  let seen = Array.create ~len:(Array.length blks) false in
  let rec visit i =
    i >= Array.length blks
    || (not seen.(i))
       && begin
         seen.(i) <- true;
         let jmps = Term.enum jmp_t blks.(i) |> Seq.to_list in
         let always jmp =
           match Jmp.cond jmp with Int x -> not (Word.is_zero x) | _ -> false
         in
         let target jmp =
           match Jmp.kind jmp with
           | Goto (Direct tid) | Ret (Direct tid) ->
               Option.map (index tid) ~f:fst
           | _ -> None
         in
         List.exists jmps ~f:(fun jmp ->
             match target jmp with Some j when j > 0 -> visit j | _ -> false)
         || ((not (List.exists jmps ~f:always)) && visit (i + 1))
       end
  in
  visit 0

let candidates t (j : jit) pc =
  let executable addr =
    match Hashtbl.find t.pages (page_of addr) with
    | Some p -> Engine.Perm.(mem p.perm exec)
    | None -> false
  in
  let rec loop i addr acc =
    if i = max_block || (i > 0 && (hooked t addr || not (executable addr))) then
      List.rev acc
    else
      match lifted t addr with
      | exception Fault _ -> List.rev acc
      | None -> List.rev acc
      | Some insn -> (
          match t.config.delay insn.code with
          | `None ->
              let acc = (addr, insn) :: acc in
              if insn.jumps && not (j.whole && falls addr insn) then
                List.rev acc
              else loop (i + 1) Int64.(addr + of_int insn.size) acc
          (* the branch, whose delay slot ends the block with it, see
             [Bap_lifted_jit.insn], if the slot doesn't jump *)
          | `Delayed | `Likely -> (
              let slot = Int64.(addr + of_int insn.size) in
              let ok (i : insn) =
                (not i.jumps) && Poly.equal (t.config.delay i.code) `None
              in
              match
                if hooked t slot || not (executable slot) then None
                else lifted t slot
              with
              | Some s when ok s -> List.rev ((slot, s) :: (addr, insn) :: acc)
              | _ | (exception Fault _) -> List.rev acc)
          | `Forbidden -> List.rev acc)
  in
  loop 0 pc []

(* the index of the register in the bytes, that the blocks share *)
let global t (j : jit) id =
  match Hashtbl.find j.globals id with
  | Some i -> i
  | None ->
      let i = Array.length j.registers in
      Hashtbl.set j.globals ~key:id ~data:i;
      j.registers <- Array.append j.registers [| reg_bytes t id |];
      i

let compile_block t j pc =
  let compiles = Option.value (Hashtbl.find j.compiles pc) ~default:0 in
  if compiles >= max_compiles || j.live >= max_live then Failed
  else begin
    Hashtbl.set j.compiles ~key:pc ~data:(compiles + 1);
    let candidates = candidates t j pc in
    let insns =
      List.map candidates ~f:(fun (pc, insn) ->
          {
            Bap_lifted_jit.pc;
            next = Int64.(pc + of_int insn.size);
            blks = insn.blks;
            delay =
              (match t.config.delay insn.code with
              | (`Delayed | `Likely) as d -> d
              | `None | `Forbidden -> `None);
          })
    in
    (* the jump of the block to its start loops in it, unless it changes
       the mode of ARM *)
    let loop =
      Option.some_if
        (List.for_all candidates ~f:(fun (_, (i : insn)) ->
             match i.modes with
             | Some (even, _) -> Bool.equal even i.thumb
             | None -> true))
        pc
    in
    match
      Bap_lifted_jit.compile ~locate:t.config.locate ~reg_size:(reg_size t)
        ~global:(global t j) ?loop insns
    with
    | Error reason ->
        if verbose () then
          Printf.eprintf "lifted engine: no block at %Lx: %s\n%!" pc reason;
        Failed
    | Ok b -> (
        if verbose () then
          Printf.eprintf "lifted engine: a block of %d at %Lx\n%!" b.length pc;
        incr compiled_count;
        match
          timed compile_time (fun () ->
              Bap_lifted_jit.native ?cache:t.config.cache (Lazy.force j.llvm) b)
        with
        | exception Failure msg ->
            if verbose () then
              Printf.eprintf "lifted engine: the block at %Lx failed: %s\n%!" pc
                msg;
            Failed
        | native, slots ->
            let candidates = List.take candidates b.length in
            j.live <- j.live + 1;
            (* the pages of its bytes, whose writes drop it, see [code_written] *)
            (let lo = pc
             and hi =
               Int64.(
                 List.fold candidates ~init:pc ~f:(fun _ (a, (i : insn)) ->
                     a + of_int i.size)
                 - 1L)
             in
             pages_of lo
               Int64.(hi - lo + 1L)
               (fun page ->
                 Option.iter (Hashtbl.find t.pages page) ~f:(fun (p : page) ->
                     p.code <- (pc, lo, hi) :: p.code)));
            Compiled
              {
                native;
                fn = Bap_llvm_jit.address native;
                slots;
                chained = false;
                code =
                  String.concat (List.map candidates ~f:(fun (_, i) -> i.code));
                pcs = Array.of_list_map candidates ~f:fst;
                insns = Array.of_list_map candidates ~f:snd;
                gen = j.gen;
                atomic =
                  List.exists candidates ~f:(fun (_, (i : insn)) ->
                      not (Poly.equal i.atomic `None));
                has_it =
                  List.exists candidates ~f:(fun (_, (i : insn)) ->
                      Option.is_some i.it);
                it_closed =
                  List.fold candidates ~init:0 ~f:(fun it (_, (i : insn)) ->
                      match i.it with
                      | Some it -> it
                      | None -> if it land 0xF <> 0 then advance_it it else it)
                  = 0;
                super =
                  List.exists (List.drop_last_exn candidates)
                    ~f:(fun (_, (i : insn)) -> i.jumps);
                entry_hooked = hooked ~blocks:true t pc;
              })
  end

(* the block, whose hooks of the code changed, is checked again *)
let unhooked t (j : jit) (b : block) =
  b.gen = j.gen
  || ((not b.super) || j.whole)
     &&
     let unhooked =
       Array.for_alli b.pcs ~f:(fun i pc -> i = 0 || not (hooked t pc))
     in
     if unhooked then begin
       b.gen <- j.gen;
       b.entry_hooked <- hooked ~blocks:true t b.pcs.(0)
     end;
     unhooked

(* runs the block at [pc], whose first instruction is [insn], whose hooks
   were called, if it is compiled, and returns the next instruction, the
   number of the instructions, that it ran, and if the next one starts a
   block *)
(* The run of a block continues with the next block, that the runtime
   links, in C, rather than in the loop of OCaml, if the next block runs,
   as if the loop entered it, see [fast_block]: its first instruction has
   no hooks, and it has no instructions, whose state the engine keeps,
   e.g., the atomics, see [link], and the IT blocks of Thumb, and the
   traces don't record its instructions, and its jump, if any, doesn't
   change the mode of ARM, while the run is limited, so that the loop checks the time,
   the stops, and the signals. *)

let max_chained = 0x10000

let chainable (j : jit) (b : block) =
  (not b.atomic)
  && ((not b.has_it) || b.it_closed)
  && (not b.entry_hooked) && b.gen = j.gen

(* the flags of the link of the block, see LINK_ARM of the stubs *)
let link_flags (b : block) =
  let last = b.insns.(Array.length b.insns - 1) in
  (* LINK_JUMPS, the next block starts a block of the traces *)
  (if last.jumps then 16 else 0)
  lor
  match last.modes with
  | None -> 0
  | Some (even, odd) ->
      8
      lor (if last.thumb then 1 else 0)
      lor (if even then 2 else 0)
      lor if odd then 4 else 0

(* the instruction, that reads a tainted register, or accesses the
   memory, while a byte is tainted, propagates the taint, and the others
   untaint the whole registers, that they write *)
let run_insn t (insn : insn) =
  let s = t.shadow in
  if not s.on then insn.run ()
  else
    let info = Lazy.force insn.taint in
    if
      Array.exists info.reads ~f:(fun r -> reg_taint t r <> 0)
      || (info.memory && not (Hashtbl.is_empty s.smem))
    then info.shadowed ()
    else
      let r = insn.run () in
      if not (Hashtbl.is_empty s.sregs) then
        Array.iter info.writes ~f:(fun (r, whole) ->
            if whole then set_reg_taint_id t r 0);
      r

(* the block, whose instructions read no tainted register, runs
   compiled, as its accesses of the tainted pages stop it, see
   [effective] *)
let untainted t (b : block) =
  let s = t.shadow in
  (not s.on) || Hashtbl.is_empty s.sregs
  || Array.for_all b.insns ~f:(fun insn ->
      Array.for_all (Lazy.force insn.taint).reads ~f:(fun r ->
          reg_taint t r = 0))

let untaint_writes t (b : block) k =
  if t.shadow.on && not (Hashtbl.is_empty t.shadow.sregs) then
    for i = 0 to k - 1 do
      Array.iter (Lazy.force b.insns.(i).taint).writes ~f:(fun (r, whole) ->
          if whole then set_reg_taint_id t r 0)
    done

let exec ?until ?count t j (b : block) pc n =
  (* the instructions, that ran, are recorded, after they ran, in their
     order, as the closures record them, of the block [b], that ran last,
     after the ones, that the runtime chained *)
  let ran (b : block) k =
    if b.atomic then
      for i = 0 to k - 1 do
        link t b.insns.(i);
        t.ran <- t.ran + 1
      done
    else t.ran <- t.ran + k;
    untaint_writes t b k;
    (* the IT state after the instructions, whose IT blocks the block
       ran, whose conditions are in their semantics *)
    if b.has_it then
      for i = 0 to k - 1 do
        next_it t b.insns.(i)
      done;
    j.jitted <- j.jitted + k;
    if j.traced then
      for i = 0 to k - 1 do
        let insn = b.insns.(i) in
        t.current <- b.pcs.(i);
        trace_insn t b.pcs.(i) insn.size insn.thumb
      done
  in
  if (not b.chained) && chainable j b then begin
    let last = Array.length b.pcs - 1 in
    Bap_lifted_jit.Runtime.link j.mem pc b.fn b.code (Array.length b.pcs)
      Int64.(b.pcs.(last) + of_int b.insns.(last).size)
      (link_flags b) b.slots;
    b.chained <- true
  end;
  Bap_lifted_jit.Runtime.limits j.mem
    (b.chained
    && ((not j.traced) || j.native)
    && Hashtbl.is_empty t.shadow.sregs)
    (match count with
    | Some c -> Int.min (c - n) max_chained
    | None -> max_chained)
    (Option.value until ~default:(-1L));
  let r =
    if stats then
      timed run_time (fun () ->
          Bap_lifted_jit.Runtime.run b.fn j.mem j.registers b.code pc)
    else Bap_lifted_jit.Runtime.run b.fn j.mem j.registers b.code pc
  in
  (* the instructions of the blocks, that ran before the last one *)
  let chained = Bap_lifted_jit.Runtime.chained j.mem in
  (* the runtime recorded the blocks before the last one, which starts a
     block of the traces, if the one before it jumped *)
  if chained > 0 && j.native then t.block <- Bap_lifted_jit.Runtime.starts j.mem;
  let pc, b =
    if chained = 0 then (pc, b)
    else begin
      t.ran <- t.ran + chained;
      j.jitted <- j.jitted + chained;
      let last = Bap_lifted_jit.Runtime.last j.mem in
      match Hashtbl.find j.blocks last with
      | Some (Compiled b) -> (last, b)
      | _ -> failwith "Bap_lifted: a linked block, that isn't compiled"
    end
  in
  let ran k =
    ran b k;
    k + chained
  in
  let k = r lsr 2 in
  let next k = Int64.(b.pcs.(k) + of_int b.insns.(k).size) in
  if r < 0 then (
    (* the code changed *)
    release j (Compiled b);
    Hashtbl.set j.blocks ~key:pc ~data:(Counting 0);
    if chained = 0 then None else Some (pc, chained, true, None))
  else
    match r land 3 with
    | 0 when k = 0 && chained = 0 -> None
    | 0 when k = 0 -> Some (pc, chained, true, None)
    | 0 ->
        let k' = ran k in
        Some (b.pcs.(k), k', false, None)
    | 1 ->
        let k' = ran (k + 1) in
        let target = Bap_lifted_jit.Runtime.next j.mem in
        Some (jump t b.insns.(k) ~next:(next k) target, k', true, None)
    (* the delay slot of the branch, that is taken, which the loop runs,
       and then jumps *)
    | 3 ->
        let k' = ran k in
        Some (b.pcs.(k), k', false, Some (Bap_lifted_jit.Runtime.next j.mem))
    | _ ->
        let k' = ran (k + 1) in
        Some (next k, k', b.insns.(k).jumps, None)

(* the block at [pc], that runs, before its first instruction is lifted
   again, and before the hooks, if its code isn't hooked, as the code of
   the block is checked, when it runs *)
(* the blocks, whose code was written, see [code_written] *)
let drop_stale t (j : jit) =
  if not (List.is_empty t.stale) then begin
    List.iter t.stale ~f:(fun pc ->
        match Hashtbl.find j.blocks pc with
        | Some (Compiled _ as b) ->
            release j b;
            Hashtbl.set j.blocks ~key:pc ~data:(Counting 0)
        | _ -> ());
    t.stale <- []
  end

let fast_block t j pc ~until ~count n =
  drop_stale t j;
  match Hashtbl.find j.blocks pc with
  | Some (Compiled b)
    when (not b.entry_hooked) && b.gen = j.gen
         && itstate t = 0
         && (not (j.traced && b.has_it))
         && Bool.equal b.insns.(0).thumb (thumb t)
         && (not (Option.exists count ~f:(fun c -> n + Array.length b.pcs > c)))
         && (not
               (Option.exists until ~f:(fun u ->
                    Array.existsi b.pcs ~f:(fun i a -> i > 0 && Int64.equal a u))))
         && untainted t b ->
      exec ?until ?count t j b pc n
  | _ -> None

let run_block t j insn pc ~until ~count n =
  drop_stale t j;
  let recount () =
    Option.iter (Hashtbl.find j.blocks pc) ~f:(release j);
    Hashtbl.set j.blocks ~key:pc ~data:(Counting 0)
  in
  match Hashtbl.find j.blocks pc with
  | None ->
      Hashtbl.set j.blocks ~key:pc ~data:(Counting 1);
      None
  | Some Failed -> None
  | Some (Counting c) ->
      Hashtbl.set j.blocks ~key:pc
        ~data:(if c + 1 < hot then Counting (c + 1) else compile_block t j pc);
      None
  (* the traces record the instructions of the IT blocks of Thumb, whose
     conditions fail, which the closures skip, see [skipped] *)
  | Some (Compiled b)
    when itstate t <> 0 || (j.traced && b.has_it) || not (untainted t b) ->
      None
  | Some (Compiled b) ->
      let length = Array.length b.pcs in
      if not (phys_equal b.insns.(0) insn) then (
        recount ();
        None)
      else if
        Option.exists count ~f:(fun c -> n + length > c)
        || Option.exists until ~f:(fun u ->
            Array.existsi b.pcs ~f:(fun i a -> i > 0 && Int64.equal a u))
      then None
      else if not (unhooked t j b) then (
        recount ();
        None)
      else exec ?until ?count t j b pc n

(* the seconds of the monotonic clock, as the executor measures the time
   slices of the threads, and the timeouts, see [Primus_native_executor] *)
let clock () = Mtime.Span.to_float_ns (Mtime_clock.elapsed ()) *. 1e-9

let start ?until ?timeout ?count ?(thread = 0) t pc =
  check t;
  each t.by_kind.trace_code (fun h ->
      match h.kind with Trace_code tr -> Trace.set_thread tr thread | _ -> ());
  each t.by_kind.trace_mem (fun h ->
      match h.kind with Trace_mem tr -> Trace.set_thread tr thread | _ -> ());
  t.stopped <- false;
  t.last_block <- None;
  let deadline =
    Option.map timeout ~f:(fun us -> clock () +. (Float.of_int us *. 1e-6))
  in
  (* [pending] is the target of the branch, whose delay slot is at [pc] *)
  let checked = ref 0 in
  (* the fault in the delay slot, e.g., of MIPS, is at its branch, as the
     processor has it, so that the branch runs again with its slot, when
     the engine continues, rather than the slot alone, which would fall
     through, as its branch isn't pending anymore, whose writes, e.g., of
     the return address, are the same again *)
  let faulted ?pending pc =
    match pending with Some _ -> Int64.(pc - 4L) | None -> pc
  in
  let rec loop ?pending ?(forbidden = false) pc n =
    set_pc t pc;
    let expired () =
      match deadline with
      | Some d ->
          (not (Option.exists t.linked ~f:(fun at -> t.ran - at < max_linked)))
          && n - !checked >= 0x100
          && begin
            checked := n;
            Float.(clock () >= d)
          end
      | None -> false
    in
    if
      t.stopped
      || Option.exists until ~f:(Int64.equal pc)
      || Option.exists count ~f:(fun c -> n >= c)
      || expired ()
    then ()
    else
      let fast =
        match t.jit with
        | Some j when t.block && Option.is_none pending && not forbidden ->
            fast_block t j pc ~until ~count n
        | _ -> None
      in
      match fast with
      | Some (next, k, starts, pending) ->
          t.block <- starts;
          loop ?pending next (n + k)
      | None -> (
          match lifted t pc with
          | exception Fault (access, addr) ->
              set_pc t (faulted ?pending pc);
              ignore addr;
              let code, msg = fault_error access in
              raise (Engine.Error (code, msg))
          | None ->
              if invalid_insn t then loop pc n
              else
                error uc_err_insn_invalid
                  "Invalid instruction (UC_ERR_INSN_INVALID)"
          | Some insn when skipped t insn ->
              (* the instruction of an IT block of Thumb, whose condition
                 fails, which Unicorn skips, without its hooks, and its
                 records, but in the size of the block *)
              set_itstate t (advance_it (itstate t));
              each t.by_kind.trace_code (fun h ->
                  match h.kind with
                  | Trace_code tr when Trace.blocks tr && not t.block ->
                      Record.extend tr insn.size
                  | _ -> ());
              t.ran <- t.ran + 1;
              loop Int64.(pc + of_int insn.size) (n + 1)
          | Some insn ->
              t.current <- pc;
              t.current_size <- insn.size;
              t.recorded <- false;
              code_hooks t pc insn.size;
              (* the stop in a delay slot stops at the target of its branch,
             after the slot, as Unicorn doesn't stop in a delay slot *)
              if t.stopped && Option.is_none pending && not forbidden then ()
              else begin
                let block =
                  match t.jit with
                  | Some j
                    when t.block && Option.is_none pending && not forbidden ->
                      run_block t j insn pc ~until ~count n
                  | _ -> None
                in
                match block with
                | Some (next, k, starts, pending) ->
                    t.block <- starts;
                    loop ?pending next (n + k)
                | None -> (
                    t.last_block <- Some pc;
                    let next = Int64.(pc + of_int insn.size) in
                    trace_insn t pc insn.size insn.thumb;
                    t.undo <- [];
                    match run_insn t insn with
                    | outcome -> (
                        t.undo <- [];
                        link t insn;
                        next_it t insn;
                        t.ran <- t.ran + 1;
                        if
                          t.ran land 0xFFFFF = 0
                          && Option.equal String.equal
                               (Sys.getenv "BAP_LIFTED_STATS")
                               (Some "verbose")
                        then
                          Printf.eprintf
                            "lifted engine: %d run in %.1f s at %Lx\n%!" t.ran
                            (Stdlib.Sys.time ()) pc;
                        (* the branch, that has a delay slot, e.g., of MIPS, runs
                   it before its target, and the likely one, that isn't
                   taken, skips it *)
                        let delay =
                          match pending with
                          | Some _ -> `None
                          | None -> t.config.delay insn.code
                        in
                        match (outcome, delay, pending) with
                        | Next, _, Some a ->
                            t.block <- true;
                            loop a (n + 1)
                        | Next, `Likely, None -> loop Int64.(next + 4L) (n + 1)
                        (* the forbidden slot of the compact branch of MIPS, that
                   isn't taken, runs with it, as in Unicorn *)
                        | Next, `Forbidden, None ->
                            loop ~forbidden:true next (n + 1)
                        | Next, _, None ->
                            if insn.jumps then t.block <- true;
                            loop next (n + 1)
                        | Jump a, (`Delayed | `Likely), _ ->
                            loop ~pending:a next (n + 1)
                        | Jump a, (`None | `Forbidden), _ ->
                            t.block <- true;
                            loop (jump t insn ~next a) (n + 1)
                        | Interrupt_at (no, next), _, _ ->
                            t.block <- true;
                            set_pc t next;
                            interrupt t no;
                            loop next (n + 1))
                    | exception Unsupported_insn reason ->
                        if
                          Option.equal String.equal
                            (Sys.getenv "BAP_LIFTED_STATS")
                            (Some "verbose")
                        then
                          Printf.eprintf
                            "lifted engine: unsupported %Lx (%s): %s\n%!" pc
                            (String.concat_map insn.code ~sep:" " ~f:(fun c ->
                                 sprintf "%02x" (Char.to_int c)))
                            reason;
                        List.iter t.undo ~f:(fun f -> f ());
                        t.undo <- [];
                        unrun t pc;
                        set_pc t pc;
                        unsupported t pc
                    | exception Fault (access, _) ->
                        List.iter t.undo ~f:(fun f -> f ());
                        t.undo <- [];
                        unrun t pc;
                        set_pc t (faulted ?pending pc);
                        let code, msg = fault_error access in
                        raise (Engine.Error (code, msg)))
              end)
  in
  (* the lower bit of the address of ARM is the Thumb state *)
  let pc =
    match t.arch with
    | Arm ->
        set_thumb t Int64.(pc land 1L = 1L);
        Int64.(pc land lnot 1L)
    | _ -> pc
  in
  mark t;
  t.block <- true;
  t.running <- true;
  Exn.protect
    ~f:(fun () -> loop pc 0)
    ~finally:(fun () ->
      t.running <- false;
      if Option.is_some (Sys.getenv "BAP_LIFTED_STATS") then
        Printf.eprintf "lifted engine: %d run, %d unsupported, at %Lx\n%!" t.ran
          t.unsupported (reg_read t t.config.pc))

let set_unmapped t name x = Hashtbl.set t.others ~key:name ~data:x

(* the hook constructors *)

let accesses_of kinds =
  List.map kinds ~f:(function
    | `read -> Engine.Read
    | `write -> Write
    | `fetch -> Fetch
    | `read_after -> Read_after)

let invalid_accesses accesses kinds =
  List.concat_map accesses ~f:(fun a ->
      List.filter_map kinds ~f:(fun k ->
          match (a, k) with
          | `read, `unmapped -> Some Engine.Read_unmapped
          | `write, `unmapped -> Some Write_unmapped
          | `fetch, `unmapped -> Some Fetch_unmapped
          | `read, `prot -> Some Read_prot
          | `write, `prot -> Some Write_prot
          | `fetch, `prot -> Some Fetch_prot))

let on_code ?first ?last t f = add t ?first ?last (Code f)
let on_sites t sites f = add t (Sites (Int64.Hash_set.of_list sites, f))
let on_block ?first ?last t f = add t ?first ?last (Block f)
let on_interrupt t f = add t (Interrupt f)
let on_invalid_insn t f = add t (Invalid_insn f)
let on_unsupported t f = add t (Unsupported f)

let on_mem ?first ?last t accesses f =
  add t ?first ?last (Mem (accesses_of accesses, f))

let trace ?first ?last ?watch ?(memory = false) t trace =
  Record.prepare trace (Poly.equal t.arch Engine.Arm);
  (* the range of the hook of the accesses is of their addresses *)
  let lower, upper =
    match watch with
    | Some (lower, upper) -> (Some lower, Some upper)
    | None -> (None, None)
  in
  add t ?first ?last (Trace_code trace)
  ::
  (if memory then [ add t ?first:lower ?last:upper (Trace_mem trace) ] else [])

let on_mem_invalid ?first ?last t accesses kinds f =
  add t ?first ?last (Mem_invalid (invalid_accesses accesses kinds, f))

(* the taint, see [shadow] *)

let reprotect_all t =
  Hashtbl.iter_keys t.pages ~f:(fun page -> reprotect t page)

let taint_clear ?(regs = true) ?(mem = true) t =
  let s = t.shadow in
  if regs then begin
    Hashtbl.clear s.sregs;
    Hash_set.clear s.dirty_regs
  end;
  if mem then begin
    let pages = Hashtbl.keys s.spages in
    Hashtbl.clear s.smem;
    Hashtbl.clear s.spages;
    Hash_set.clear s.dirty_mem;
    List.iter pages ~f:(reprotect t)
  end

let taint_start ?(jumps = false) t =
  let s = t.shadow in
  s.jumps <- jumps;
  if not s.on then begin
    s.on <- true;
    reprotect_all t
  end

let taint_stop t =
  taint_clear t;
  t.shadow.on <- false;
  reprotect_all t

let taint_active t = t.shadow.on

let taint_any t =
  not (Hashtbl.is_empty t.shadow.sregs && Hashtbl.is_empty t.shadow.smem)

let taint_labels t classes =
  let s = t.shadow in
  Hashtbl.clear s.classes;
  List.iter classes ~f:(fun (l, c) -> Hashtbl.set s.classes ~key:l ~data:c);
  Hashtbl.clear s.moves;
  Hashtbl.clear s.comps

let labels t id = Set.to_list t.shadow.sets.(id)
let reg_labels t name = labels t (reg_taint t name)

let set_reg_labels t name ls =
  set_reg_taint_id ~dirty:false t name (set_id t.shadow (Int.Set.of_list ls))

let mem_labels t addr = labels t (mem_taint t addr)

let set_mem_labels t addr ls =
  set_mem_taint_id ~dirty:false t addr (set_id t.shadow (Int.Set.of_list ls))

let tainted_regs t = Hashtbl.keys t.shadow.sregs
let tainted_mem t = Hashtbl.keys t.shadow.smem

(* the taint of the values, e.g., of the native functions of the executor,
   see [Primus_native_libc] *)
type taint = int

let no_taint = 0
let tainted x = x <> 0
let taint_jumps t = t.shadow.jumps
let union_taint t a b = union t.shadow a b
let moves_taint t a = moves t.shadow a

let mem_range_taint t addr n =
  let x = ref 0 in
  if not (Hashtbl.is_empty t.shadow.smem) then
    for i = 0 to n - 1 do
      x := union t.shadow !x (mem_taint t Int64.(addr + of_int i))
    done;
  !x

let set_reg_taint t name x = set_reg_taint_id t name x

let fill_mem_taint t addr n x =
  let x = moves t.shadow x in
  for i = 0 to n - 1 do
    set_mem_taint_id t Int64.(addr + of_int i) x
  done

(* byte by byte, from the first, so that the destination inside the
   source repeats the bytes before it *)
let copy_mem_taint t ~dst ~src n =
  for i = 0 to n - 1 do
    set_mem_taint_id t
      Int64.(dst + of_int i)
      (moves t.shadow (mem_taint t Int64.(src + of_int i)))
  done

let move_mem_taint t ~dst ~src n =
  let taints = Array.init n ~f:(fun i -> mem_taint t Int64.(src + of_int i)) in
  Array.iteri taints ~f:(fun i x ->
      set_mem_taint_id t Int64.(dst + of_int i) (moves t.shadow x))

let taint_changes t =
  let s = t.shadow in
  let regs = Hash_set.to_list s.dirty_regs
  and mem = Hash_set.to_list s.dirty_mem in
  Hash_set.clear s.dirty_regs;
  Hash_set.clear s.dirty_mem;
  (regs, mem)

type context = (int * string) list * (string * word) list

let save t : context =
  ( Hashtbl.to_alist t.regs
    |> List.map ~f:(fun (id, b) -> (id, Bytes.to_string b)),
    Hashtbl.to_alist t.others )

(* the bytes of the registers stay, as the compiled instructions read
   and write them *)
let restore t ((regs, others) : context) =
  Hashtbl.iter t.regs ~f:(fun b ->
      Bytes.fill b ~pos:0 ~len:(Bytes.length b) '\000');
  List.iter regs ~f:(fun (id, data) ->
      let b = reg_bytes t id in
      Bytes.From_string.blit ~src:data ~src_pos:0 ~dst:b ~dst_pos:0
        ~len:(Int.min (String.length data) (Bytes.length b)));
  Hashtbl.clear t.others;
  List.iter others ~f:(fun (name, x) -> Hashtbl.set t.others ~key:name ~data:x)
