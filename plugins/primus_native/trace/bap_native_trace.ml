type t
type pcs = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
type sizes = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

type modes =
  (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

type accesses = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array2.t

external create : int -> int -> bool -> int -> bool -> t
  = "bap_native_trace_create"

external count : t -> int64 = "bap_native_trace_count"
external read_values : t -> bool = "bap_native_trace_read_values"
external retained : t -> int = "bap_native_trace_retained"
external retained_accesses : t -> int = "bap_native_trace_retained_accesses"
external accesses_count : t -> int64 = "bap_native_trace_accesses_count"
external clear : t -> unit = "bap_native_trace_clear"

module State = struct
  type reg = int * int * int
  type field = int * int * int * int64 * int

  type record = {
    site : int64;
    index : int64;
    thread : int;
    regs : int64 array;
    fields : int64 option array;
  }

  external configure : t -> int64 array -> reg array -> field array -> unit
    = "bap_native_trace_state_configure"

  external records : t -> int -> record list = "bap_native_trace_state_records"
  external captures : t -> int64 -> bool = "bap_native_trace_state_captures"
  external enabled : t -> bool = "bap_native_trace_state_enabled"
  external registers : t -> reg array = "bap_native_trace_state_registers"
  external fields : t -> field array = "bap_native_trace_state_fields"

  let configure t sites regs fields =
    configure t (Array.of_list sites) (Array.of_list regs)
      (Array.of_list fields)

  let records ?(last = -1) t = records t last
end

module Snapshot = struct
  type state = {
    capacity : int;
    every : int;
    blocks : bool;
    access_capacity : int;
    read_values : bool;
    count : int64;
    skip : int64;
    thread : int64;
    pcs : int64 array;
    tids : int64 array;
    sizes : int32 array;
    modes : int array;
    accesses_count : int64;
    access_records : int64 array;
    bounds_count : int64;
    ranges_count : int64;
    bounds : int64 array;
    ranges : int64 array;
    capture_sites : int64 array;
    capture_regs : State.reg array;
    capture_fields : State.field array;
    captures_count : int64;
    captures : State.record array;
  }

  external create_exact : int -> int -> bool -> int -> bool -> t
    = "bap_native_trace_snapshot_create"

  external export_native : t -> state = "bap_native_trace_snapshot_export"

  external restore_native : t -> state -> unit
    = "bap_native_trace_snapshot_import"

  external prepare : t -> bool -> unit = "bap_native_trace_prepare"

  let export t =
    let state = export_native t in
    {
      state with
      capture_regs =
        Array.map
          (fun (id, offset, size) -> (id, offset, size))
          state.capture_regs;
      capture_fields =
        Array.map
          (fun (id, offset, size, at, field_size) ->
            (id, offset, size, at, field_size))
          state.capture_fields;
    }

  let bounds_capacity = 65536
  let ranges_capacity = 65536
  let max_capacity = 1 lsl 37

  let invalid field message =
    invalid_arg ("Bap_native_trace.Snapshot.import: " ^ field ^ ": " ^ message)

  let nonnegative field value =
    if Int64.compare value 0L < 0 then invalid field "negative count"

  let power_of_two field value =
    if value <= 0 || value land (value - 1) <> 0 then
      invalid field "not a positive power of two"

  let length field expected array =
    if Array.length array <> expected then
      invalid field
        (Printf.sprintf "expected %d elements, got %d" expected
           (Array.length array))

  let product field a b =
    if a <> 0 && b > max_int / a then invalid field "size overflow";
    a * b

  let retained count capacity =
    let count =
      if Int64.compare count (Int64.of_int capacity) < 0 then count
      else Int64.of_int capacity
    in
    Int64.to_int count

  let validate_reg (id, offset, size) =
    if id < 0 then invalid "capture register" "negative identifier";
    if Int64.compare (Int64.of_int id) 0x7fffffffL > 0 then
      invalid "capture register" "identifier exceeds native limits";
    if offset < 0 then invalid "capture register" "negative offset";
    if size < 1 || size > 8 then invalid "capture register" "invalid size";
    if
      offset > max_int - size
      || Int64.compare
           (Int64.add (Int64.of_int offset) (Int64.of_int size))
           0xffffffffL
         > 0
    then invalid "capture register" "offset exceeds native limits"

  let validate state =
    power_of_two "capacity" state.capacity;
    if state.capacity < 4 || state.capacity > max_capacity then
      invalid "capacity" "outside native allocation limits";
    if state.every < 1 then invalid "every" "not positive";
    if state.access_capacity <> 0 then (
      power_of_two "access capacity" state.access_capacity;
      if state.access_capacity < 2 || state.access_capacity > max_capacity then
        invalid "access capacity" "outside native allocation limits");
    List.iter
      (fun (field, value) -> nonnegative field value)
      [
        ("instruction count", state.count);
        ("access count", state.accesses_count);
        ("bounds count", state.bounds_count);
        ("ranges count", state.ranges_count);
        ("capture count", state.captures_count);
      ];
    if
      Int64.compare state.skip 1L < 0
      || Int64.compare state.skip (Int64.of_int state.every) > 0
    then invalid "sampling skip" "outside 1..every";
    length "pcs" state.capacity state.pcs;
    length "tids" state.capacity state.tids;
    length "sizes" (if state.blocks then state.capacity else 0) state.sizes;
    if
      Array.length state.modes <> 0
      && Array.length state.modes <> state.capacity
    then invalid "modes" "expected an empty array or one entry per ring slot";
    Array.iter
      (fun mode ->
        if mode <> 0 && mode <> 1 then invalid "modes" "invalid mode")
      state.modes;
    length "access records"
      (product "access records" state.access_capacity 7)
      state.access_records;
    length "bounds" (4 * bounds_capacity) state.bounds;
    length "ranges" (2 * ranges_capacity) state.ranges;
    Array.iter validate_reg state.capture_regs;
    Array.iter
      (fun (id, offset, size, _, field_size) ->
        validate_reg (id, offset, size);
        if field_size < 1 || field_size > 8 then
          invalid "capture field" "invalid field size")
      state.capture_fields;
    ignore
      (product "capture registers" state.capacity
         (Array.length state.capture_regs));
    ignore
      (product "capture fields" state.capacity
         (Array.length state.capture_fields));
    length "captures"
      (retained state.captures_count (state.capacity - 1))
      state.captures;
    Array.iter
      (fun record ->
        length "capture record registers"
          (Array.length state.capture_regs)
          record.State.regs;
        length "capture record fields"
          (Array.length state.capture_fields)
          record.State.fields)
      state.captures

  let import state =
    validate state;
    let trace =
      create_exact state.capacity state.every state.blocks state.access_capacity
        state.read_values
    in
    if Array.length state.modes <> 0 then prepare trace true;
    State.configure trace
      (Array.to_list state.capture_sites)
      (Array.to_list state.capture_regs)
      (Array.to_list state.capture_fields);
    restore_native trace state;
    trace
end

module Record = struct
  external prepare : t -> bool -> unit = "bap_native_trace_prepare"

  external record : t -> int64 -> int -> bool -> unit
    = "bap_native_trace_record"

  external extend : t -> int -> unit = "bap_native_trace_extend"

  external access : t -> bool -> int64 -> int -> int64 -> int64 -> int64 -> unit
    = "bap_native_trace_access_bytecode" "bap_native_trace_access"

  external unrun : t -> int64 -> unit = "bap_native_trace_unrun"

  external capture : t -> int64 -> int64 array -> int64 option array -> unit
    = "bap_native_trace_state_capture"

  external bound :
    t -> bool -> bool -> bool -> int64 -> int64 array -> bool -> unit
    = "bap_native_trace_bound_bytecode" "bap_native_trace_bound"
end

external blocks : t -> bool = "bap_native_trace_blocks"
external pcs : t -> int -> pcs = "bap_native_trace_pcs"
external tids : t -> int -> pcs = "bap_native_trace_tids"
external set_thread : t -> int -> unit = "bap_native_trace_set_thread"
external sizes : t -> int -> sizes = "bap_native_trace_sizes"
external modes : t -> int -> modes = "bap_native_trace_modes"
external accesses : t -> int -> accesses = "bap_native_trace_mem"
external save : t -> int -> string -> int64 = "bap_native_trace_save"
external bounds : t -> pcs = "bap_native_trace_bounds"
external ranges : t -> pcs = "bap_native_trace_ranges"

let create ?(every = 1) ?(blocks = false) ?(accesses = 0) ?(read_values = false)
    size =
  create size every blocks accesses read_values

let pcs ?(last = -1) t = pcs t last
let tids ?(last = -1) t = tids t last
let sizes ?(last = -1) t = sizes t last
let modes ?(last = -1) t = modes t last
let accesses ?(last = -1) t = accesses t last
let save ?(last = -1) t file = save t last file
