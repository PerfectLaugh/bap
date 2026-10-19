open Core
open Bap_core_theory
open Bap.Std
open Format
open Bap_primus_types
module Generator = Bap_primus_generator
open Bap_primus_sexp

type exn += Pagefault of addr

let () =
  Exn.add_printer (function
    | Pagefault here -> Some (asprintf "Page fault at %a" Addr.pp_hex here)
    | _ -> None)

type dynamic = { lower : addr; upper : addr; value : Generator.t }
type region = Dynamic of dynamic | Static of mem
type perms = { readonly : bool; executable : bool }

type protection = { readable : bool; writable : bool; executable : bool }
[@@deriving equal]

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
      (if readable then "R" else "");
      (if writable then "W" else "");
      (if executable then "X" else "");
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

module Make (Machine : Machine) = struct
  open Machine.Syntax
  module Generate = Generator.Make (Machine)
  module Value = Bap_primus_value.Make (Machine)

  let memory = Machine.Local.get state >>| fun s -> s.curr
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

  let store_word arch bytesize ~addr word values =
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
      if not (Map.mem values key) then
        Machine.Observation.make on_generated (key, x)
      else Machine.return ()
    in
    let rec loop written ~key word values =
      if written < bytes then
        Value.of_word (bite word) >>= fun data ->
        notify_if_generated key data values >>= fun () ->
        loop (written + 1) ~key:(next key) (shift word)
          (Map.update values key ~f:(function
            | None -> data
            | Some data -> data))
      else Machine.return values
    in
    loop 0 ~key:addr word values

  let remembered s addr word =
    memory >>= fun { size } ->
    Machine.gets Project.arch >>= fun arch ->
    store_word arch size ~addr word s.values >>= fun values ->
    put_curr { s with values } >>| fun () -> Map.find_exn values addr

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
  let get addr = get_curr >>= read addr
  let set addr value = get_curr >>= write addr value >>= put_curr
  let set_never_fail addr value = get_curr >>| set_value addr value >>= put_curr
  let del addr = update @@ fun s -> { s with values = Map.remove s.values addr }
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

  let protect ~lower ~upper protection =
    update (fun s ->
        let s = unprotect lower upper s in
        { s with protections = (lower, upper, protection) :: s.protections })
    >>= fun () ->
    Machine.Observation.make on_protected (lower, upper, protection)
end
