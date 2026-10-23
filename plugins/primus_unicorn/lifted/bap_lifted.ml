(* The lifted engine, which runs the IR of the instructions, that BAP
   lifts, with the interface of Unicorn, see bap_lifted.mli.

   The registers are the registers of Unicorn, their bytes in the order
   of the host, by their identifiers, so that the registers of BAP are
   the bits of them, as Primus_unicorn_target.Regs maps them, and the
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
module Uc = Bap_unicorn

type config = {
  lift : thumb:bool -> int64 -> string -> (int * string * blk term list) option;
  name : tid -> string option;
  policy : int;
  delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
  locate : string -> (int * int * int) option;
  pc : int;
  big_endian : bool;
  bits : int;
  jit : bool;
}

type kind =
  | Code of (int64 -> int -> unit)
  | Block of (int64 -> int -> unit)
  | Interrupt of (int -> unit)
  | Invalid_insn of (unit -> bool)
  | Unsupported of (int64 -> unit)
  | Mem of Uc.access list * (Uc.access -> int64 -> int -> int64 -> unit)
  | Mem_invalid of Uc.access list * (Uc.access -> int64 -> int -> int64 -> bool)
  | Trace_code of Uc.Trace.t  (** records the instructions, or the blocks *)
  | Trace_mem of Uc.Trace.t  (** records the accesses *)

type hook = {
  first : int64 option;
  last : int64 option;
  kind : kind;
  mutable deleted : bool;
}

(* the bytes of the pages are outside of the heap, as the blocks, that
   the JIT compiled, access them, see Bap_lifted_jit *)
type page = {
  data : Bigstring.t;
  mutable perm : Uc.Perm.t;
  mutable code : (int64 * int64 * int64) list;
      (** the blocks, that the JIT compiled, whose bytes are on the page, their
          addresses, and the first and the last address of their bytes, which
          are dropped, when they are written, see [code_written] *)
}

(* the outcome of an instruction *)
type next = Next | Jump of int64 | Interrupt_at of int * int64

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
}

(* the block, that the JIT compiled, of the instructions, that start at
   the addresses, see Bap_lifted_jit *)
type block = {
  native : Bap_llvm_jit.code;
  fn : nativeint;
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
  mutable allowed : bool;
      (** if no hook, e.g., of the memory, needs the closures *)
  mutable traced : bool;
      (** if the traces of the code record the instructions of the blocks *)
  mutable jitted : int;  (** the instructions, that the blocks ran *)
  compiles : int Int64.Table.t;  (** the blocks compiled at the addresses *)
  mutable live : int;  (** the blocks, that are not released *)
  globals : int Int.Table.t;
      (** the indices of the registers in [registers], see [global] *)
  mutable registers : Bytes.t array;
      (** the bytes of the registers, that the blocks share, so that the run of
          a block continues with the next one, see [chainable] *)
}

type t = {
  config : config;
  arch : Uc.arch;
  cpsr : int option;  (** CPSR of ARM, whose bit T is the Thumb state *)
  regs : Bytes.t Int.Table.t;
  sizes : int Int.Table.t;
  probe : Uc.t Lazy.t;  (** the Unicorn, whose registers have the sizes *)
  others : word String.Table.t;  (** the registers, that are not mapped *)
  pages : page Int64.Table.t;
  insns : insn Int64.Table.t;
  mutable hooks : hook list;
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
     [Uc.Trace.bounds], but the fills of the pages, that are mapped *)
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
}

exception Fault of Uc.access * int64

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
let page_size = 0x1000L
let page_of addr = Int64.(addr land lnot (page_size - 1L))

let error code fmt =
  Printf.ksprintf (fun msg -> raise (Uc.Error (code, msg))) fmt

(* the codes of the errors of Unicorn *)
let uc_err_read_unmapped = 6
let uc_err_write_unmapped = 7
let uc_err_fetch_unmapped = 8
let uc_err_insn_invalid = 10
let uc_err_write_prot = 12
let uc_err_read_prot = 13
let uc_err_fetch_prot = 14

let create config arch mode =
  (* the sizes of the registers are the ones of Unicorn, which is asked
     about the registers, that are used *)
  let probe = lazy (Uc.create arch mode) in
  let t =
    {
      config;
      arch;
      cpsr = (match arch with Arm -> Uc.reg arch "CPSR" | _ -> None);
      regs = Int.Table.create ();
      sizes = Int.Table.create ();
      probe;
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
      ran = 0;
      linked = None;
      stale = [];
      unsupported = 0;
      jit =
        (if Sys.big_endian || not config.jit then None
         else
           Some
             {
               mem = Bap_lifted_jit.Runtime.create ();
               blocks = Int64.Table.create ();
               gen = 0;
               allowed = true;
               traced = false;
               jitted = 0;
               compiles = Int64.Table.create ();
               live = 0;
               globals = Int.Table.create ();
               registers = [||];
             });
    }
  in
  (* the numbers of the instructions, with BAP_LIFTED_STATS *)
  if Option.is_some (Sys.getenv "BAP_LIFTED_STATS") then
    at_exit (fun () ->
        Printf.eprintf
          "lifted engine: %d instructions run, %d unsupported, %d jitted\n%!"
          t.ran t.unsupported
          (Option.value_map t.jit ~default:0 ~f:(fun j -> j.jitted)));
  t

let check t = if t.closed then invalid_arg "the engine is closed"

let close t =
  if Lazy.is_val t.probe then Uc.close (Lazy.force t.probe);
  Option.iter t.jit ~f:(fun j ->
      Hashtbl.iter j.blocks ~f:(function
        | Compiled b -> Bap_llvm_jit.release b.native
        | Counting _ | Failed -> ());
      Hashtbl.clear j.blocks;
      j.live <- 0);
  t.closed <- true

(* the registers *)

let reg_size t id =
  check t;
  match Hashtbl.find t.sizes id with
  | Some size -> size
  | None ->
      let size = Uc.reg_size (Lazy.force t.probe) id in
      Hashtbl.set t.sizes ~key:id ~data:size;
      size

let reg_bytes t id =
  match Hashtbl.find t.regs id with
  | Some b -> b
  | None ->
      let b = Bytes.make (reg_size t id) '\000' in
      Hashtbl.set t.regs ~key:id ~data:b;
      b

let reg_read_bytes t id = Bytes.to_string (reg_bytes t id)

let write_reg_bytes t id data =
  let b = reg_bytes t id in
  if String.length data <> Bytes.length b then
    invalid_arg "Unicorn.reg_write_bytes: a wrong size";
  Bytes.From_string.blit ~src:data ~src_pos:0 ~dst:b ~dst_pos:0
    ~len:(String.length data)

(* the bytes of the host, which is little endian, see [Uc.reg_read] *)
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
          Bap_lifted_jit.Runtime.map j.mem page data (perm :> int)))

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
          if not Uc.Perm.(mem perm exec) then code_written t p;
          p.perm <- perm;
          Option.iter t.jit ~f:(fun j ->
              Bap_lifted_jit.Runtime.protect j.mem page (perm :> int))
      | None -> error 11 "Invalid memory mapping (UC_ERR_NOMEM)")

let offset addr = Int64.(to_int_exn (addr - page_of addr))

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
             && Uc.Perm.(mem perm p.perm && mem p.perm perm) ->
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

let hooks_changed t =
  Option.iter t.jit ~f:(fun j ->
      unchain j;
      j.gen <- j.gen + 1;
      j.allowed <-
        not
          (List.exists t.hooks ~f:(fun h ->
               match h.kind with Mem _ | Trace_mem _ -> true | _ -> false));
      j.traced <-
        List.exists t.hooks ~f:(fun h ->
            match h.kind with Trace_code _ -> true | _ -> false))

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
  match (h.first, h.last) with
  | Some first, Some last when Int64.(first <= last) ->
      Int64.(addr >= first && addr <= last)
  | _ -> true

let each t f = List.iter t.hooks ~f:(fun h -> if not h.deleted then f h)

let mem_hooks t access addr size value =
  each t (fun h ->
      match h.kind with
      | Mem (accesses, f)
        when covers h addr && List.mem accesses access ~equal:Poly.equal ->
          f access addr size value
      | _ -> ())

(* The traces, that the engine records, as the native hooks of Unicorn
   record them, see [Uc.Trace]. *)

module Record = Uc.Trace.Record

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
  each t (fun h ->
      match h.kind with
      | Trace_code tr ->
          let early = Uc.Trace.blocks tr && (not t.block) && not t.recorded in
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
    each t (fun h ->
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
    each t (fun h ->
        match h.kind with
        | Trace_mem tr when covers h addr ->
            Record.access tr write addr size value old t.current
        | _ -> ())

(* the instruction, that runs, in the traces of the code *)
let trace_insn t pc size thumb =
  t.reads <- [];
  each t (fun h ->
      match h.kind with
      | Trace_code tr when covers h pc ->
          if Uc.Trace.blocks tr && not t.block then Record.extend tr size
          else Record.record tr pc size thumb
      | _ -> ());
  t.recorded <- true;
  t.block <- false

(* the instruction, that didn't run, e.g., as it faulted *)
let unrun t pc =
  each t (fun h ->
      match h.kind with Trace_code tr -> Record.unrun tr pc | _ -> ())

(* the hooks of the invalid access, the access is retried, if one of them
   handled it, and else the instruction faults *)
let invalid t access addr size value =
  let handled = ref false in
  each t (fun h ->
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
      let unmapped : Uc.access =
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
        | `read -> (Uc.Perm.read, Uc.Read_prot)
        | `write -> (Uc.Perm.write, Uc.Write_prot)
        | `fetch -> (Uc.Perm.exec, Uc.Fetch_prot)
      in
      if Uc.Perm.mem p.perm needed then p
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
  | Memory of (int64 * value * endian * size) list

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
    List.find stores ~f:(fun (a, _, _, s) ->
        Int64.equal a addr && Size.equal s size)
  in
  match pending with
  | Some (_, x, _, _) -> x
  | None ->
      (* the hooks see a read once, as in Unicorn *)
      let again = read_again t addr n in
      if not again then mem_hooks t Read addr n 0L;
      let x = value_of_bytes endian (load t addr n) in
      if not again then mem_hooks t Read_after addr n (bits x);
      trace_access t ~write:false addr n (bits x) 0L;
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

let read_var ctx v : unit -> value =
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
  List.iter (List.rev stores) ~f:(fun (addr, x, endian, size) ->
      let n = Size.in_bytes size in
      let data = bytes_of_value endian x in
      mem_hooks t Write addr n (bits x);
      (* the bytes, that the write overwrites, see [Uc.Trace.accesses] *)
      let old =
        if n > 8 then 0L
        else
          match mem_read t addr n with
          | old ->
              String.foldi old ~init:0L ~f:(fun i acc c ->
                  Int64.(acc lor (of_int (Char.to_int c) lsl Int.(8 * i))))
          | exception Uc.Error _ -> 0L
      in
      trace_access t ~write:true addr n (bits x) old;
      store t addr data 0L)

let write_var ctx v : value -> unit =
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

let rec compile_exp ctx : exp -> unit -> value = function
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
        | Memory stores -> Memory ((a, x, endian, size) :: stores)
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
                  let x = Word.extract_exn ~hi:(src - 1) (word (arg ())) in
                  Bitvec.to_bigint (Word.to_bitvec x))
            in
            match F.apply ~op ~rm ~src ~dst policy args with
            | None -> raise (Unsupported_insn ("the intrinsic " ^ name))
            | Some x ->
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
let compile t ~pc ~next (blks : blk term list) : unit -> next =
  let ctx =
    { t; slots = String.Table.create (); lets = []; size = 0; env = ref [||] }
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
        | (cond, target) :: rest ->
            let rest = jump rest in
            fun () -> if is_zero (cond ()) then rest () else target ()
      in
      let jumps = jump jumps in
      codes.(i) <-
        (fun () ->
          Array.iter defs ~f:(fun def -> def ());
          jumps ()));
  ctx.env := Array.create ~len:ctx.size (S (1, 0L));
  fun () -> run 0

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
      | Some p when Uc.Perm.(mem p.perm exec) ->
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

let lifted t pc =
  let code = fetch t pc in
  let thumb = thumb t in
  match Hashtbl.find t.insns pc with
  | Some insn
    when Bool.equal insn.thumb thumb && String.is_prefix code ~prefix:insn.code
    ->
      Some insn
  | _ -> (
      match t.config.lift ~thumb pc code with
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
                        (Bap_primus.Std.Primus.Interworking.jump ~name ~thumb
                           ~next:(Word.of_int64 ~width next)
                           blks (Word.of_int64 ~width dst))
                    in
                    Some (mode Int64.(next + 4L), mode Int64.(next + 5L))
                | _ -> None);
              run = compile t ~pc ~next blks;
            }
          in
          Hashtbl.set t.insns ~key:pc ~data:insn;
          Some insn)

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
  | Some id when Poly.equal t.arch Uc.Arm ->
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

let flush_tb t =
  Hashtbl.clear t.insns;
  Option.iter t.jit ~f:(fun j ->
      (* the links go at once, rather than with each block *)
      unchain j;
      Hashtbl.iter j.blocks ~f:(release j);
      Hashtbl.clear j.blocks)

(* the hooks of the blocks, at the starts of the blocks, and then of the
   instruction, in their order, but the ones after the hook, that stops
   the emulation, as Unicorn calls them *)
let code_hooks t pc size =
  let call f = if not t.stopped then f () in
  if t.block then
    List.iter t.hooks ~f:(fun h ->
        match h.kind with
        | Block f when (not h.deleted) && covers h pc ->
            call (fun () -> f pc size)
        | _ -> ());
  List.iter t.hooks ~f:(fun h ->
      match h.kind with
      | Code f when (not h.deleted) && covers h pc -> call (fun () -> f pc size)
      | _ -> ())

let stop t = t.stopped <- true

let unsupported t pc =
  t.unsupported <- t.unsupported + 1;
  each t (fun h ->
      match h.kind with Unsupported f when covers h pc -> f pc | _ -> ());
  (* the instruction is never run here *)
  t.stopped <- true

let invalid_insn t =
  let handled = ref false in
  each t (fun h ->
      match h.kind with
      | Invalid_insn f when not !handled -> handled := f ()
      | _ -> ());
  !handled

let interrupt t n =
  each t (fun h -> match h.kind with Interrupt f -> f n | _ -> ())

let fault_error (access : Uc.access) =
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
  List.exists t.hooks ~f:(fun h ->
      match h.kind with
      | Code _ -> (not h.deleted) && covers h addr
      | Block _ when blocks -> (not h.deleted) && covers h addr
      | _ -> false)

(* the instructions, that may be in the block at [pc], whose bytes are
   fetched only from the executable pages, as the hooks of the invalid
   fetches are not called *)
let candidates t pc =
  let executable addr =
    match Hashtbl.find t.pages (page_of addr) with
    | Some p -> Uc.Perm.(mem p.perm exec)
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
              if insn.jumps then List.rev acc
              else loop (i + 1) Int64.(addr + of_int insn.size) acc
          | _ -> List.rev acc)
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
    let candidates = candidates t pc in
    let insns =
      List.map candidates ~f:(fun (pc, insn) ->
          {
            Bap_lifted_jit.pc;
            next = Int64.(pc + of_int insn.size);
            blks = insn.blks;
          })
    in
    match
      Bap_lifted_jit.compile ~locate:t.config.locate ~reg_size:(reg_size t)
        ~global:(global t j) insns
    with
    | Error reason ->
        if verbose () then
          Printf.eprintf "lifted engine: no block at %Lx: %s\n%!" pc reason;
        Failed
    | Ok b -> (
        if verbose () then
          Printf.eprintf "lifted engine: a block of %d at %Lx\n%!" b.length pc;
        match Bap_lifted_jit.native b with
        | exception Failure msg ->
            if verbose () then
              Printf.eprintf "lifted engine: the block at %Lx failed: %s\n%!" pc
                msg;
            Failed
        | native ->
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
                entry_hooked = hooked ~blocks:true t pc;
              })
  end

(* the block, whose hooks of the code changed, is checked again *)
let unhooked t (j : jit) (b : block) =
  b.gen = j.gen
  ||
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

let max_chained = 4096

let chainable (j : jit) (b : block) =
  (not b.atomic)
  && ((not b.has_it) || b.it_closed)
  && (not b.entry_hooked) && b.gen = j.gen

(* the flags of the link of the block, see LINK_ARM of the stubs *)
let link_flags (b : block) =
  let last = b.insns.(Array.length b.insns - 1) in
  match last.modes with
  | None -> 0
  | Some (even, odd) ->
      8
      lor (if last.thumb then 1 else 0)
      lor (if even then 2 else 0)
      lor if odd then 4 else 0

let exec ?until ?count t j (b : block) pc n =
  (* the instructions, that ran, are recorded, after they ran, in their
     order, as the closures record them *)
  let ran k =
    if b.atomic then
      for i = 0 to k - 1 do
        link t b.insns.(i);
        t.ran <- t.ran + 1
      done
    else t.ran <- t.ran + k;
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
      (link_flags b);
    b.chained <- true
  end;
  Bap_lifted_jit.Runtime.limits j.mem
    (b.chained && not j.traced)
    (match count with
    | Some c -> Int.min (c - n) max_chained
    | None -> max_chained)
    (Option.value until ~default:(-1L));
  let r = Bap_lifted_jit.Runtime.run b.fn j.mem j.registers b.code pc in
  (* the instructions of the blocks, that ran before the last one *)
  let chained = Bap_lifted_jit.Runtime.chained j.mem in
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
    ran k;
    k + chained
  in
  let k = r lsr 2 in
  let next k = Int64.(b.pcs.(k) + of_int b.insns.(k).size) in
  if r < 0 then (
    (* the code changed *)
    release j (Compiled b);
    Hashtbl.set j.blocks ~key:pc ~data:(Counting 0);
    if chained = 0 then None else Some (pc, chained, true))
  else
    match r land 3 with
    | 0 when k = 0 && chained = 0 -> None
    | 0 when k = 0 -> Some (pc, chained, true)
    | 0 ->
        let k' = ran k in
        Some (b.pcs.(k), k', false)
    | 1 ->
        let k' = ran (k + 1) in
        let target = Bap_lifted_jit.Runtime.next j.mem in
        Some (jump t b.insns.(k) ~next:(next k) target, k', true)
    | _ ->
        let k' = ran (k + 1) in
        Some (next k, k', b.insns.(k).jumps)

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
         && not
              (Option.exists until ~f:(fun u ->
                   Array.existsi b.pcs ~f:(fun i a -> i > 0 && Int64.equal a u)))
    ->
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
  | Some (Compiled b) when itstate t <> 0 || (j.traced && b.has_it) -> None
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

let start ?until ?timeout ?count t pc =
  check t;
  t.stopped <- false;
  t.last_block <- None;
  let deadline =
    Option.map timeout ~f:(fun us ->
        Time_float.(add (now ()) (Span.of_us (Float.of_int us))))
  in
  (* [pending] is the target of the branch, whose delay slot is at [pc] *)
  let checked = ref 0 in
  let rec loop ?pending ?(forbidden = false) pc n =
    set_pc t pc;
    let expired () =
      match deadline with
      | Some d ->
          (not (Option.exists t.linked ~f:(fun at -> t.ran - at < max_linked)))
          && n - !checked >= 0x100
          && begin
            checked := n;
            Time_float.(now () >= d)
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
        | Some j
          when j.allowed && t.block && Option.is_none pending && not forbidden
          ->
            fast_block t j pc ~until ~count n
        | _ -> None
      in
      match fast with
      | Some (next, k, starts) ->
          t.block <- starts;
          loop next (n + k)
      | None -> (
          match lifted t pc with
          | exception Fault (access, addr) ->
              set_pc t pc;
              ignore addr;
              let code, msg = fault_error access in
              raise (Uc.Error (code, msg))
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
              each t (fun h ->
                  match h.kind with
                  | Trace_code tr when Uc.Trace.blocks tr && not t.block ->
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
                    when j.allowed && t.block && Option.is_none pending
                         && not forbidden ->
                      run_block t j insn pc ~until ~count n
                  | _ -> None
                in
                match block with
                | Some (next, k, starts) ->
                    t.block <- starts;
                    loop next (n + k)
                | None -> (
                    t.last_block <- Some pc;
                    let next = Int64.(pc + of_int insn.size) in
                    trace_insn t pc insn.size insn.thumb;
                    t.undo <- [];
                    match insn.run () with
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
                        set_pc t pc;
                        let code, msg = fault_error access in
                        raise (Uc.Error (code, msg)))
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
    | `read -> Uc.Read
    | `write -> Write
    | `fetch -> Fetch
    | `read_after -> Read_after)

let invalid_accesses accesses kinds =
  List.concat_map accesses ~f:(fun a ->
      List.filter_map kinds ~f:(fun k ->
          match (a, k) with
          | `read, `unmapped -> Some Uc.Read_unmapped
          | `write, `unmapped -> Some Write_unmapped
          | `fetch, `unmapped -> Some Fetch_unmapped
          | `read, `prot -> Some Read_prot
          | `write, `prot -> Some Write_prot
          | `fetch, `prot -> Some Fetch_prot))

let on_code ?first ?last t f = add t ?first ?last (Code f)
let on_block ?first ?last t f = add t ?first ?last (Block f)
let on_interrupt t f = add t (Interrupt f)
let on_invalid_insn t f = add t (Invalid_insn f)
let on_unsupported t f = add t (Unsupported f)

let on_mem ?first ?last t accesses f =
  add t ?first ?last (Mem (accesses_of accesses, f))

let trace ?first ?last ?(memory = false) t trace =
  Record.prepare trace (Poly.equal t.arch Uc.Arm);
  add t ?first ?last (Trace_code trace)
  :: (if memory then [ add t ?first ?last (Trace_mem trace) ] else [])

let on_mem_invalid ?first ?last t accesses kinds f =
  add t ?first ?last (Mem_invalid (invalid_accesses accesses kinds, f))

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
