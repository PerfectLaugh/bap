open Core
open Bap_core_theory
open Bap.Std
open Format
open Bap_primus_types
module Generator = Bap_primus_generator
open Bap_primus_sexp

type exn += Pagefault of addr
type exn += Unknown_segment of addr * addr

let () =
  Exn.add_printer (function
    | Pagefault here -> Some (asprintf "Page fault at %a" Addr.pp_hex here)
    | Unknown_segment (lower, upper) ->
        Some
          (asprintf
             "The snapshot has the segment [%a,%a] of another program, which \
              is not mapped"
             Addr.pp_hex lower Addr.pp_hex upper)
    | _ -> None)

type dynamic = { lower : addr; upper : addr; value : Generator.t }
type region = Dynamic of dynamic | Static of mem
type perms = { readonly : bool; executable : bool }

type protection = { readable : bool; writable : bool; executable : bool }
[@@deriving bin_io, equal]

type layer = { mem : region; perms : perms }

(* a segment [lo,hi] of the address space, which starts at its key in
   the index, and the topmost layer that covers it, which is the
   [seq]th added layer *)
type segment = { hi : Bitvec.t; seq : int; layer : layer }

(* the index of layers: the layers whose bounds are unsigned words of
   the same width, with [lower <= upper], are split into disjoint
   segments, by the address width, so that the layer of an address is
   found by one lookup and without allocations. The [others] are
   searched linearly, newest first, using the generic comparison. *)
type index = {
  segments : segment Map.M(Bitvec_order).t Map.M(Int).t;
  others : (int * layer) list;
  count : int;
}

type memory = { name : string; addr : int; size : int }
[@@deriving bin_io, sexp]

let compare_memory { name = x } { name = y } = String.compare x y

module Descriptor = struct
  type t = memory [@@deriving bin_io, compare, sexp]

  let create ~addr_size ~data_size name =
    { addr = addr_size; size = data_size; name }

  let unknown ~addr_size ~data_size = create ~addr_size ~data_size "unknown"
  let name d = d.name
  let addr_size d = d.addr
  let data_size d = d.size

  include Comparable.Make (struct
    type t = memory [@@deriving bin_io, compare, sexp]
  end)
end

(* the protections of the ranges [lower,upper], that override the
   permissions of their layers, the newest first, they don't overlap *)
type state = {
  values : value Addr.Map.t;
  layers : layer list;
  index : index;
  protections : (addr * addr * protection) list;
}

type t = { curr : Descriptor.t; mems : state Descriptor.Map.t }

module Backing = struct
  type t = {
    memory : string;
    pending : id -> addr -> bool;
    fetch : id -> addr -> (addr * string) list;
    fetch_all : id -> (addr * string) list;
    stored : id -> addr -> string -> unit;
  }

  (* the backing is of the system, i.e., of all its machines *)
  let state : t option Bap_primus_machine.State.t =
    Bap_primus_machine.State.declare
      ~uuid:"c2b8e5f1-6a34-4d0b-9e72-1f8d3a6c5b49" ~name:"memory-backing"
      (fun _ -> None)
end

let sexp_of_word w = Sexp.Atom (asprintf "%a" Word.pp_hex w)

let sexp_of_dynamic { lower; upper; value } =
  Sexp.(
    List
      [
        Sexp.Atom "dynamic";
        sexp_of_word lower;
        sexp_of_word upper;
        Generator.sexp_of_t value;
      ])

let sexp_of_mem mem =
  Sexp.List
    [
      Sexp.Atom "static";
      sexp_of_word (Memory.min_addr mem);
      sexp_of_int (Memory.length mem);
    ]

let sexp_of_mem = function
  | Dynamic mem -> sexp_of_dynamic mem
  | Static mem -> sexp_of_mem mem

let sexp_of_layer { mem; perms = { readonly; executable } } =
  let flags =
    [ "R"; (if readonly then "" else "W"); (if executable then "X" else "") ]
    |> String.concat ~sep:""
  in
  Sexp.(List [ sexp_of_mem mem; Atom flags ])

let inspect_state { values; layers } =
  let values =
    Map.to_sequence values
    |> Seq.map ~f:(fun (key, value) ->
        Sexp.(List [ sexp_of_word key; sexp_of_value value ]))
    |> Seq.to_list_rev
  in
  let layers = List.map layers ~f:sexp_of_layer in
  Sexp.(
    List
      [
        List [ Atom "values"; List values ]; List [ Atom "layers"; List layers ];
      ])

let inspect_memory { curr; mems } =
  Sexp.List [ Sexp.Atom curr.name; Descriptor.Map.sexp_of_t inspect_state mems ]

let inspect_generated (ptr, x) = Sexp.List [ sexp_of_addr ptr; sexp_of_value x ]

let string_of_protection { readable; writable; executable } =
  String.concat
    [
      (if readable then "R" else "-");
      (if writable then "W" else "-");
      (if executable then "X" else "-");
    ]

let inspect_protected (lower, upper, protection) =
  Sexp.List
    [
      sexp_of_addr lower;
      sexp_of_addr upper;
      Sexp.Atom (string_of_protection protection);
    ]

let protected, on_protected =
  Bap_primus_observation.provide "memory-protected" ~inspect:inspect_protected
    ~package:"bap"
    ~desc:"Occurs when the protection of a range of the memory changes"

let generated, on_generated =
  Bap_primus_observation.provide "load-generated" ~inspect:inspect_generated
    ~package:"bap"
    ~desc:"Occurs when a new value is generated during the load operation"

let virtual_memory target =
  let mem = Theory.Target.data target in
  let s = Theory.Var.sort mem in
  let ks = Theory.Mem.keys s and vs = Theory.Mem.vals s in
  Descriptor.create ~addr_size:(Theory.Bitv.size ks)
    ~data_size:(Theory.Bitv.size vs) (Theory.Var.name mem)

let state =
  Bap_primus_machine.State.declare ~uuid:"4b94186d-3ae9-48e0-8a93-8c83c747bdbb"
    ~inspect:inspect_memory ~name:"memory"
  @@ fun p ->
  { mems = Descriptor.Map.empty; curr = virtual_memory (Project.target p) }

let inside { lower; upper } addr =
  if Addr.(lower <= upper) then Addr.(addr >= lower) && Addr.(addr <= upper)
  else Addr.(addr >= upper) || Addr.(addr <= lower)

let inside_region region addr =
  match region with
  | Dynamic mem -> inside mem addr
  | Static mem -> Memory.contains mem addr

let is_unsigned x = phys_equal (Word.unsigned x) x

(* for unsigned words of the same width the generic comparison is the
   comparison of their bitvectors, and a region with [lower <= upper]
   contains only the addresses of its width *)
let bounds_of_region region =
  let lower, upper =
    match region with
    | Dynamic { lower; upper } -> (lower, upper)
    | Static mem -> (Memory.min_addr mem, Memory.max_addr mem)
  in
  let width = Addr.bitwidth lower in
  let lo = Word.to_bitvec lower and hi = Word.to_bitvec upper in
  if
    width = Addr.bitwidth upper
    && is_unsigned lower && is_unsigned upper
    && Bitvec.compare lo hi <= 0
  then Some (width, lo, hi)
  else None

(* puts the [seq]th layer over the segments that [lo,hi] overlaps *)
let cover segments ~width ~lo ~hi seq layer =
  let m = Bitvec.modulus width in
  let below =
    match Map.closest_key segments `Less_than lo with
    | Some (key, seg) when Bitvec.compare seg.hi lo >= 0 -> [ (key, seg) ]
    | _ -> []
  in
  let overlapping =
    Map.fold_range_inclusive segments ~min:lo ~max:hi ~init:below
      ~f:(fun ~key ~data segs -> (key, data) :: segs)
  in
  List.fold overlapping ~init:segments ~f:(fun segments (key, seg) ->
      let segments = Map.remove segments key in
      let segments =
        if Bitvec.compare key lo < 0 then
          Map.set segments ~key ~data:{ seg with hi = Bitvec.(pred lo mod m) }
        else segments
      in
      if Bitvec.compare seg.hi hi > 0 then
        Map.set segments ~key:Bitvec.(succ hi mod m) ~data:seg
      else segments)
  |> Map.set ~key:lo ~data:{ hi; seq; layer }

let add_layer layer ({ layers; index } as s) =
  let seq = index.count in
  let index =
    match bounds_of_region layer.mem with
    | None -> { index with others = (seq, layer) :: index.others }
    | Some (width, lo, hi) ->
        let segments =
          Map.update index.segments width ~f:(fun segments ->
              let segments =
                Option.value segments ~default:(Map.empty (module Bitvec_order))
              in
              cover segments ~width ~lo ~hi seq layer)
        in
        { index with segments }
  in
  { s with layers = layer :: layers; index = { index with count = seq + 1 } }

(* the most recently added layer that contains [addr] *)
let find_layer addr { layers; index } =
  if not (is_unsigned addr) then
    List.find layers ~f:(fun { mem } -> inside_region mem addr)
  else
    let x = Word.to_bitvec addr in
    let segment =
      match Map.find index.segments (Addr.bitwidth addr) with
      | None -> None
      | Some segments -> (
          match Map.closest_key segments `Less_or_equal_to x with
          | Some (_, seg) when Bitvec.compare x seg.hi <= 0 -> Some seg
          | _ -> None)
    in
    let other =
      List.find index.others ~f:(fun (_, { mem }) -> inside_region mem addr)
    in
    match (segment, other) with
    | Some { seq; layer }, Some (seq', layer') ->
        Some (if seq > seq' then layer else layer')
    | Some { layer }, None | None, Some (_, layer) -> Some layer
    | None, None -> None

(* the layer of all bytes of [addr, last], if they are in one segment of
   the index, with no layer outside of it, see [find_layer], no value,
   and no protection, which the loads of the ranges read at once *)
let uniform_layer addr last s =
  if
    (not (is_unsigned addr))
    || (not (List.is_empty s.index.others))
    || List.exists s.protections ~f:(fun (lo, hi, _) ->
        Addr.(hi >= addr && lo <= last))
  then None
  else
    match Map.closest_key s.values `Greater_or_equal_to addr with
    | Some (k, _) when Addr.(k <= last) -> None
    | _ -> (
        match Map.find s.index.segments (Addr.bitwidth addr) with
        | None -> None
        | Some segments -> (
            let segment x =
              match Map.closest_key segments `Less_or_equal_to x with
              | Some (_, seg) when Bitvec.compare x seg.hi <= 0 -> Some seg
              | _ -> None
            in
            match
              (segment (Word.to_bitvec addr), segment (Word.to_bitvec last))
            with
            | Some a, Some b when phys_equal a b -> Some a.layer
            | _ -> None))

let is_mapped addr s =
  Map.mem s.values addr || Option.is_some (find_layer addr s)

let mapped = is_mapped

let empty_state =
  {
    values = Addr.Map.empty;
    layers = [];
    index = { segments = Map.empty (module Int); others = []; count = 0 };
    protections = [];
  }

(* the protected ranges of a machine, at most, see [protect] *)
let max_protections = 65530

type exn += Too_many_protections of addr * addr

let () =
  Exn.add_printer (function
    | Too_many_protections (lower, upper) ->
        Some
          (Format.asprintf
             "the protection of [%a,%a] makes more than %d protected ranges"
             Addr.pp lower Addr.pp upper max_protections)
    | _ -> None)

let find_protection addr { protections } =
  List.find_map protections ~f:(fun (lower, upper, protection) ->
      Option.some_if Addr.(addr >= lower && addr <= upper) protection)

(* removes the range [lower,upper] from the protected ranges, as a new
   protection or a new layer replaces their protections *)
let unprotect lower upper s =
  let protections =
    List.concat_map s.protections ~f:(fun ((lo, hi, p) as range) ->
        if Addr.(hi < lower || lo > upper) then [ range ]
        else
          (if Addr.(lo < lower) then [ (lo, Addr.pred lower, p) ] else [])
          @ if Addr.(hi > upper) then [ (Addr.succ upper, hi, p) ] else [])
  in
  { s with protections }

let bounds = function
  | Dynamic { lower; upper } -> (lower, upper)
  | Static mem -> (Memory.min_addr mem, Memory.max_addr mem)

(* a new layer replaces the protections of its addresses *)
let add_layer layer s =
  let lower, upper = bounds layer.mem in
  add_layer layer (unprotect lower upper s)

(* The state of the memory, in which the static layers, which are of
   the program, are kept by their bounds, the dynamic layers by their
   bounds and the value of their generator, if it is static, and the
   stored values by their words. *)
module Snapshot = struct
  (* the segments of the program and the allocated regions *)
  type kind = Program | Allocated of { width : int; fill : Word.t option }
  [@@deriving bin_io]

  type area = {
    lower : Addr.t;
    upper : Addr.t;
    readonly : bool;
    executable : bool;
    kind : kind;
  }
  [@@deriving bin_io]

  type mem = {
    layers : area list;  (** the oldest first *)
    values : (Addr.t * Word.t) list;
    protections : (Addr.t * Addr.t * protection) list;
  }
  [@@deriving bin_io]

  type t = { curr : Descriptor.t; mems : (Descriptor.t * mem) list }
  [@@deriving bin_io]

  let of_layer ({ mem; perms = { readonly; executable } } : layer) : area =
    let lower, upper = bounds mem in
    let kind =
      match mem with
      | Static _ -> Program
      | Dynamic { value } ->
          let width = Generator.width value in
          Allocated
            {
              width;
              fill =
                Option.map (Generator.fill value) ~f:(fun x ->
                    Word.create x width);
            }
    in
    { lower; upper; readonly; executable; kind }

  let of_state ({ values; layers; protections; _ } : state) : mem =
    {
      layers = List.rev_map layers ~f:of_layer;
      values =
        Map.to_alist values
        |> List.map ~f:(fun (addr, x) -> (addr, Bap_primus_value.to_word x));
      protections;
    }

  (* the layer, which [l] stands for, in the [layers] of the machine
     that restores the snapshot, which mapped the program, as the
     machine that made it *)
  let find_layer layers (l : area) =
    List.find layers ~f:(fun { mem; perms } ->
        let lower, upper = bounds mem in
        Addr.equal lower l.lower && Addr.equal upper l.upper
        && Bool.equal perms.readonly l.readonly
        && Bool.equal perms.executable l.executable
        &&
        match (mem, l.kind) with
        | Static _, Program -> true
        | Dynamic { value }, Allocated { width; fill } ->
            Generator.width value = width
            && Option.equal Word.equal fill
                 (Option.map (Generator.fill value) ~f:(fun x ->
                      Word.create x width))
        | _ -> false)

  (* the dynamic layer, which is not found, is mapped anew, with the
     default generator, unless its generator was static *)
  let to_layer layers (l : area) =
    match (find_layer layers l, l.kind) with
    | Some layer, _ -> Ok layer
    | None, Program -> Error (Unknown_segment (l.lower, l.upper))
    | None, Allocated { width; fill } ->
        let value =
          match fill with
          | Some x -> Generator.static ~width (Bitvec.to_int (Word.to_bitvec x))
          | None -> Generator.Random.Seeded.lcg ~width ()
        in
        Ok
          {
            mem = Dynamic { lower = l.lower; upper = l.upper; value };
            perms = { readonly = l.readonly; executable = l.executable };
          }
end

module Make (Machine : Machine) = struct
  open Machine.Syntax
  module Generate = Generator.Make (Machine)
  module Value = Bap_primus_value.Make (Machine)
  module Tracked = Bap_primus_track.Make (Machine)

  let memory = Machine.Local.get state >>| fun s -> s.curr

  (* the locations of the virtual memory, that hold the tracked values,
     are marked, see [Bap_primus_track] *)
  module Track = struct
    let stored addr value =
      Tracked.active >>= function
      | false -> Machine.return ()
      | true ->
          memory >>= fun curr ->
          Machine.gets Project.target >>= fun target ->
          if String.equal curr.name (virtual_memory target).name then
            Tracked.stored addr value
          else Machine.return ()

    (* the generated value isn't stored by the program, so it marks its
       location, if it is tracked, but doesn't unmark it, e.g., the
       location of the zeros of a page, that is marked, as tainted *)
    let generated addr value =
      Tracked.is_tracked value >>= function
      | false -> Machine.return ()
      | true ->
          memory >>= fun curr ->
          Machine.gets Project.target >>= fun target ->
          if String.equal curr.name (virtual_memory target).name then
            Tracked.mark addr
          else Machine.return ()
  end

  let switch curr = Machine.Local.update state ~f:(fun s -> { s with curr })

  let get_curr =
    Machine.Local.get state >>| fun { curr; mems } ->
    match Map.find mems curr with None -> empty_state | Some s -> s

  let put_curr mem =
    Machine.Local.get state >>= fun { curr; mems } ->
    Machine.Local.put state { curr; mems = Map.set mems ~key:curr ~data:mem }

  let update f = get_curr >>= fun s -> put_curr (f s)
  let pagefault addr = Machine.raise (Pagefault addr)

  let read_small mem addr size =
    assert (size < 8 && size > 0);
    let addr_size = Addr.bitwidth addr in
    (* to address {n 2^m} bits we need {m+log(m)} addr space,
       since {n < 8} (it is the word size in bits), we just add 3.*)
    let width = addr_size + 3 in
    let addr = Word.extract_exn ~hi:(width - 1) addr in
    let off = Addr.(addr - Memory.min_addr mem) in
    let off_in_bits = Word.(off * Word.of_int ~width size) in
    let full_bytes = Word.(off_in_bits / Word.of_int ~width 8) in
    let bit_off =
      Word.to_int_exn
      @@ Word.(off_in_bits - (full_bytes * Word.of_int ~width 8))
    in
    let leftover = Memory.length mem - Word.to_int_exn full_bytes in
    let len = min leftover 2 in
    let full_bytes = Word.extract_exn ~hi:(addr_size - 1) full_bytes in
    let from = Addr.(Memory.min_addr mem + full_bytes) in
    let mem = ok_exn @@ Memory.view mem ~from ~words:len in
    let data = Bigsubstring.to_string (Memory.to_buffer mem) in
    let vec = Word.of_binary ~width:(len * 8) BigEndian data in
    let hi = (len * 8) - bit_off - 1 in
    let lo = hi - size + 1 in
    Word.extract_exn ~hi ~lo vec

  (* we can't use Bap.Std.Memory here as we need arbitrary lengths *)
  let read_word mem base size =
    let start, next =
      match Memory.endian mem with
      | LittleEndian -> (Addr.nsucc base ((size / 8) - 1), Addr.pred)
      | BigEndian -> (base, Addr.succ)
    in
    let rec read addr left =
      let data = ok_exn @@ Memory.get ~addr mem in
      if left <= 8 then Word.extract_exn ~lo:(8 - left) data
      else Word.concat data @@ read (next addr) (left - 8)
    in
    if size >= 8 then read start size else read_small mem base size

  let store_word ?(notify = true) arch bytesize ~addr word values =
    let bytes = (Word.bitwidth word + bytesize - 1) / bytesize in
    let bite x = Word.extract_exn ~hi:(bytesize - 1) x in
    let shift =
      let bits = Word.of_int ~width:8 bytesize in
      fun x -> Word.lshift x bits
    in
    let addr, next =
      match Arch.endian arch with
      | LittleEndian -> (addr, Addr.succ)
      | BigEndian -> (Addr.nsucc addr (bytes - 1), Addr.pred)
    in
    let notify_if_generated key x values =
      if notify && not (Map.mem values key) then
        Machine.Observation.make on_generated (key, x)
      else Machine.return ()
    in
    let rec loop written ~key word values keys =
      if written < bytes then
        Value.of_word (bite word) >>= fun data ->
        notify_if_generated key data values >>= fun () ->
        loop (written + 1) ~key:(next key) (shift word)
          (Map.update values key ~f:(function
            | None -> data
            | Some data -> data))
          (key :: keys)
      else Machine.return (values, keys)
    in
    loop 0 ~key:addr word values []

  (* the generated values, which the analyses track, e.g., the symbolic
     ones, mark their locations *)
  let remembered ?notify s addr word =
    memory >>= fun { size } ->
    Machine.gets Project.arch >>= fun arch ->
    store_word ?notify arch size ~addr word s.values >>= fun (values, keys) ->
    put_curr { s with values } >>= fun () ->
    Machine.List.iter keys ~f:(fun key ->
        Track.generated key (Map.find_exn values key))
    >>| fun () -> Map.find_exn values addr

  let read addr ({ values } as s) =
    match find_protection addr s with
    | Some { readable = false } when is_mapped addr s -> pagefault addr
    | _ -> (
        match Map.find values addr with
        | Some v -> Machine.return v
        | None -> (
            match find_layer addr s with
            | None -> pagefault addr
            | Some layer -> (
                memory >>= fun { size } ->
                match layer.mem with
                | Static mem -> Value.of_word (read_word mem addr size)
                | Dynamic { value = g } ->
                    Generate.word g (Generator.width g) >>= remembered s addr)))

  let set_value addr value s =
    { s with values = Map.set s.values ~key:addr ~data:value }

  let write addr value s =
    match find_protection addr s with
    | Some { writable = false } when is_mapped addr s -> pagefault addr
    | Some { writable = true } when is_mapped addr s ->
        Machine.return @@ set_value addr value s
    | _ -> (
        if Map.mem s.values addr then Machine.return @@ set_value addr value s
        else
          match find_layer addr s with
          | None -> pagefault addr
          | Some { perms = { readonly = true } } -> pagefault addr
          | Some _ -> Machine.return @@ set_value addr value s)

  let ( ++ ) = add_layer

  let initialize values lower upper f =
    let rec loop values addr =
      if Addr.(addr < upper) then
        f addr >>= fun data ->
        Value.of_word data >>= fun data ->
        loop (Map.set values ~key:addr ~data) (Addr.succ addr)
      else Machine.return values
    in
    loop values lower

  let add_region ?(readonly = false) ?(executable = false) ?init ?generator
      ~lower ~upper () =
    Machine.gets Project.target >>| Theory.Target.bits >>= fun width ->
    get_curr
    >>| add_layer
          {
            perms = { readonly; executable };
            mem =
              Dynamic
                {
                  lower;
                  upper;
                  value =
                    (match generator with
                    | Some g -> g
                    | None -> Generator.Random.Seeded.lcg ~width ());
                };
          }
    >>= fun s ->
    match init with
    | None -> put_curr s
    | Some f ->
        initialize s.values lower upper f >>= fun values ->
        put_curr { s with values }

  let allocate ?readonly ?executable ?init ?generator base len =
    add_region () ?readonly ?executable ?init ?generator ~lower:base
      ~upper:(Addr.nsucc base (len - 1))

  let map ?(readonly = false) ?(executable = false) mem =
    update @@ add_layer { mem = Static mem; perms = { readonly; executable } }

  let add_text mem = map mem ~readonly:true ~executable:true
  let add_data mem = map mem ~readonly:false ~executable:false

  let store_bytes_unbacked addr data =
    Value.of_words
      (Array.init (String.length data) ~f:(fun i ->
           Word.of_int ~width:8 (Char.to_int data.[i])))
    >>= fun xs ->
    update @@ fun s ->
    let values =
      Array.foldi xs ~init:s.values ~f:(fun i values x ->
          Map.set values ~key:(Addr.nsucc addr i) ~data:x)
    in
    { s with values }

  let set_backing backing = Machine.Global.put Backing.state backing

  (* calls [f] with the backing of the current memory, if it has one *)
  let backing f =
    Machine.Global.get Backing.state >>= function
    | None -> Machine.return ()
    | Some b ->
        Machine.Local.get state >>= fun { curr } ->
        if String.equal curr.name b.memory then
          Machine.current () >>= fun id -> f b id
        else Machine.return ()

  let store_fetched =
    Machine.List.iter ~f:(fun (addr, data) -> store_bytes_unbacked addr data)

  (* the bytes from [addr], that the backing has, are stored, before
     the machine accesses them *)
  let fetch addr len =
    backing @@ fun b id ->
    let rec loop i =
      if i = len then Machine.return ()
      else
        let a = Addr.nsucc addr i in
        if b.pending id a then
          store_fetched (b.fetch id a) >>= fun () -> loop (i + 1)
        else loop (i + 1)
    in
    loop 0

  let stored addr data =
    backing @@ fun b id -> Machine.return (b.stored id addr data)

  let stored_value addr value =
    backing @@ fun b id ->
    let x = Value.to_word value in
    if Word.bitwidth x = 8 then
      b.stored id addr (String.of_char (Char.of_int_exn (Word.to_int_exn x)));
    Machine.return ()

  let get addr = fetch addr 1 >>= fun () -> get_curr >>= read addr

  let set addr value =
    fetch addr 1 >>= fun () ->
    get_curr >>= write addr value >>= put_curr >>= fun () ->
    stored_value addr value >>= fun () -> Track.stored addr value

  let set_never_fail addr value =
    fetch addr 1 >>= fun () ->
    get_curr >>| set_value addr value >>= put_curr >>= fun () ->
    stored_value addr value >>= fun () -> Track.stored addr value

  let del addr =
    fetch addr 1 >>= fun () ->
    update @@ fun s -> { s with values = Map.remove s.values addr }

  let load addr = get addr >>| Value.to_word
  let store addr value = Value.of_word value >>= set addr
  let store_never_fail addr value = Value.of_word value >>= set_never_fail addr
  let is_mapped addr = get_curr >>| is_mapped addr

  (* the permissions of the layer, a byte that was stored without a layer is
     writable, as well as a byte of a read-only layer that was stored *)
  let protection_of addr s =
    match find_protection addr s with
    | Some p when mapped addr s -> Some p
    | _ -> (
        match find_layer addr s with
        | Some { perms = { readonly; executable } } ->
            Some
              {
                readable = true;
                writable = (not readonly) || Map.mem s.values addr;
                executable;
              }
        | None when Map.mem s.values addr ->
            Some { readable = true; writable = true; executable = false }
        | None -> None)

  let protection addr = get_curr >>| protection_of addr

  let is_writable addr =
    protection addr >>| function Some p -> p.writable | None -> false

  let is_executable addr =
    protection addr >>| function Some p -> p.executable | None -> false

  let check_bytes name =
    memory >>| fun { size } ->
    if size <> 8 then
      invalid_argf "Memory.%s: the data of the memory are %d bits wide" name
        size ()

  (* the byte at [addr], which is mapped and readable, the generated
     value is remembered, as [read] does, but it is not an input, e.g.,
     of the symbolic executor, as it is a copy of the memory *)
  let read_byte ~quiet s addr =
    match Map.find s.values addr with
    | Some v -> Machine.return (Value.to_word v, s)
    | None -> (
        match find_layer addr s with
        | Some { mem = Static mem } -> Machine.return (read_word mem addr 8, s)
        (* the byte of the layer, whose generator is static, e.g., of the
           zeros of BSS, is its value, which is not remembered, as it is
           the same, when it is read again, and not tracked, which saves
           the map of the values of the large layers, e.g., which an
           emulator copies, see [load_bytes] *)
        | Some { mem = Dynamic { value = g } }
          when quiet && Option.is_some (Generator.fill g) ->
            Machine.return
              (Word.create (Option.value_exn (Generator.fill g)) 8, s)
        | Some { mem = Dynamic { value = g } } ->
            Generate.word g (Generator.width g)
            >>= remembered ~notify:false s addr
            >>= fun v ->
            get_curr >>| fun s -> (Value.to_word v, s)
        | None -> assert false)

  (* the bytes of the range in one layer, of a static generator, or of the
     image, at once, see [uniform_layer] *)
  let load_uniform addr len s =
    if len = 0 then None
    else
      match uniform_layer addr (Addr.nsucc addr (len - 1)) s with
      | None -> None
      | Some { mem; perms = { readonly; executable } } -> (
          let p = { readable = true; writable = not readonly; executable } in
          match mem with
          | Dynamic { value = g } -> (
              match Generator.fill g with
              | Some v ->
                  let c = Char.of_int_exn (Bitvec.to_int v land 0xFF) in
                  Some (Array.create ~len (Some (c, p)))
              | None -> None)
          | Static mem ->
              Some
                (Array.init len ~f:(fun i ->
                     let x = read_word mem (Addr.nsucc addr i) 8 in
                     Some (Char.of_int_exn (Word.to_int_exn x), p))))

  (* the bytes of the layers of the static generators are neither
     remembered, nor read one by one, unless the generated values are
     observed, e.g., by the symbolic executor, whose inputs they are, when
     they are read later, unless they were remembered, see [read] *)
  let load_bytes addr len =
    check_bytes "load_bytes" >>= fun () ->
    fetch addr len >>= fun () ->
    Machine.Observation.observed generated >>= fun observed ->
    let quiet = not observed in
    get_curr >>= fun s ->
    match if quiet then load_uniform addr len s else None with
    | Some bytes -> Machine.return bytes
    | None ->
        let bytes = Array.create ~len None in
        let rec loop i s =
          if i = len then Machine.return bytes
          else
            let a = Addr.nsucc addr i in
            match protection_of a s with
            | None -> loop (i + 1) s
            | Some p when not p.readable ->
                bytes.(i) <- Some ('\000', p);
                loop (i + 1) s
            | Some p ->
                read_byte ~quiet s a >>= fun (x, s) ->
                bytes.(i) <- Some (Char.of_int_exn (Word.to_int_exn x), p);
                loop (i + 1) s
        in
        loop 0 s

  let store_bytes addr data =
    check_bytes "store_bytes" >>= fun () ->
    fetch addr (String.length data) >>= fun () ->
    store_bytes_unbacked addr data >>= fun () -> stored addr data

  (* the range, that has the same protection, as the range before it, or
     after it, joins them, e.g., of the pages, that the program protects
     one at a time, and the ranges are at most as many, as Linux allows,
     see vm.max_map_count, as each access looks them up *)
  let protect ~lower ~upper protection =
    let joined s =
      let s = unprotect lower upper s in
      let lower, upper, others =
        List.fold s.protections ~init:(lower, upper, [])
          ~f:(fun (lower, upper, others) ((lo, hi, p) as range) ->
            if Poly.equal p protection && Addr.(succ hi = lower) then
              (lo, upper, others)
            else if Poly.equal p protection && Addr.(succ upper = lo) then
              (lower, hi, others)
            else (lower, upper, range :: others))
      in
      { s with protections = (lower, upper, protection) :: List.rev others }
    in
    get_curr >>= fun curr ->
    let s = joined curr in
    if List.length s.protections > max_protections then
      Machine.raise (Too_many_protections (lower, upper))
    else
      update (fun _ -> s) >>= fun () ->
      Machine.Observation.make on_protected (lower, upper, protection)

  let snapshot =
    (backing @@ fun b id -> store_fetched (b.fetch_all id)) >>= fun () ->
    Machine.Local.get state >>| fun { curr; mems } ->
    {
      Snapshot.curr;
      mems =
        Map.to_alist mems
        |> List.map ~f:(fun (desc, s) -> (desc, Snapshot.of_state s));
    }

  (* the values of all memories, with their identities *)
  let values =
    (backing @@ fun b id -> store_fetched (b.fetch_all id)) >>= fun () ->
    Machine.Local.get state >>| fun { mems; _ } ->
    Map.to_alist mems
    |> List.concat_map ~f:(fun (desc, (s : state)) ->
        Map.to_alist s.values |> List.map ~f:(fun (addr, x) -> (desc, addr, x)))

  let restore_state current (m : Snapshot.mem) =
    match
      Result.all (List.map m.layers ~f:(Snapshot.to_layer current.layers))
    with
    | Error exn -> Machine.raise exn
    | Ok layers ->
        Machine.List.map m.values ~f:(fun (addr, x) ->
            Value.of_word x >>| fun x -> (addr, x))
        >>| fun values ->
        let s = List.fold layers ~init:empty_state ~f:(Fn.flip add_layer) in
        {
          s with
          values = Addr.Map.of_alist_exn values;
          protections = m.protections;
        }

  (* the layers of the program are those of the machine, see
     [Snapshot.find_layer] *)
  let restore (snapshot : Snapshot.t) =
    Machine.Local.get state >>= fun { mems = current } ->
    Machine.List.map snapshot.mems ~f:(fun (desc, m) ->
        let s = Option.value (Map.find current desc) ~default:empty_state in
        restore_state s m >>| fun s -> (desc, s))
    >>= fun mems ->
    Machine.Local.put state
      { curr = snapshot.curr; mems = Descriptor.Map.of_alist_exn mems }
end
