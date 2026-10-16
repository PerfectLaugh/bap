open Core

type typ = Int | Bool | Str [@@deriving equal, sexp_of]

type table = {
  name : string;
  types : typ array;
  offsets : int array;  (** the offsets of the fields in a row *)
  stride : int;  (** the size of a row *)
  rows : int;
  data : Bigstring.t;
  base : int;  (** the offset of the first row in [data] *)
  pool : int;  (** the offset of the string pool in [data] *)
}

type t = { tables : table String.Map.t; order : string list }

let version = 1
let size = function Int -> 8 | Bool -> 1 | Str -> 8

exception Malformed of string

let malformed fmt = ksprintf (fun msg -> raise (Malformed msg)) fmt

(* a cursor over the document, all reads are checked *)
module Reader = struct
  type t = { data : Bigstring.t; mutable pos : int }

  let need r n =
    if n < 0 || r.pos + n > Bigstring.length r.data then
      malformed "unexpected end of the document at %d" r.pos

  let u8 r =
    need r 1;
    let x = Bigstring.get_uint8 r.data ~pos:r.pos in
    r.pos <- r.pos + 1;
    x

  let u32 r =
    need r 4;
    let x = Bigstring.get_uint32_le r.data ~pos:r.pos in
    r.pos <- r.pos + 4;
    x

  let u64 r =
    need r 8;
    let x = Bigstring.get_int64_le_trunc r.data ~pos:r.pos in
    if x < 0 then malformed "a size at %d is too big" r.pos;
    r.pos <- r.pos + 8;
    x

  let bytes r n =
    need r n;
    let s = Bigstring.To_string.sub r.data ~pos:r.pos ~len:n in
    r.pos <- r.pos + n;
    s

  let skip r n =
    need r n;
    r.pos <- r.pos + n
end

let typ_of_int = function
  | 0 -> Int
  | 1 -> Bool
  | 2 -> Str
  | n -> malformed "unknown field type %d" n

let read_table r =
  let name = Reader.(bytes r (u32 r)) in
  let types =
    Array.init (Reader.u32 r) ~f:(fun _ -> typ_of_int (Reader.u8 r))
  in
  let offsets = Array.create ~len:(Array.length types) 0 in
  let stride =
    Array.foldi types ~init:0 ~f:(fun i off t ->
        offsets.(i) <- off;
        off + size t)
  in
  let rows = Reader.u32 r in
  let length = Reader.u64 r in
  if length <> rows * stride then
    malformed "the table %s has %d bytes for %d rows of %d bytes" name length
      rows stride;
  let base = r.pos in
  Reader.skip r length;
  { name; types; offsets; stride; rows; data = r.data; base; pool = 0 }

let get32 data pos = Bigstring.get_uint32_le data ~pos

(* checks that the strings of the table lie in the pool *)
let check_strings table ~pool_size =
  Array.iteri table.types ~f:(fun field t ->
      if equal_typ t Str then
        for row = 0 to table.rows - 1 do
          let pos = table.base + (row * table.stride) + table.offsets.(field) in
          let off = get32 table.data pos and len = get32 table.data (pos + 4) in
          if off + len > pool_size then
            malformed "a string of the table %s is out of the pool" table.name
        done)

let decode data =
  let r = { Reader.data; pos = 0 } in
  if not (String.equal (Reader.bytes r 4) "BAPT") then
    malformed "not a table document";
  let v = Reader.u32 r in
  if v <> version then malformed "unsupported version %d of the document" v;
  let tables = List.init (Reader.u32 r) ~f:(fun _ -> read_table r) in
  let pool_size = Reader.u64 r in
  let pool = r.pos in
  Reader.skip r pool_size;
  if r.pos <> Bigstring.length data then
    malformed "%d trailing bytes" (Bigstring.length data - r.pos);
  List.fold tables ~init:{ tables = String.Map.empty; order = [] }
    ~f:(fun doc table ->
      let table = { table with pool } in
      check_strings table ~pool_size;
      match Map.add doc.tables ~key:table.name ~data:table with
      | `Duplicate -> malformed "the table %s occurs twice" table.name
      | `Ok tables -> { tables; order = table.name :: doc.order })
  |> fun doc -> { doc with order = List.rev doc.order }

let of_bigstring data =
  try Ok (decode data)
  with Malformed msg -> Or_error.errorf "malformed loader document: %s" msg

let empty name types =
  {
    name;
    types = Array.of_list types;
    offsets = [||];
    stride = 0;
    rows = 0;
    data = Bigstring.create 0;
    base = 0;
    pool = 0;
  }

let table doc name types =
  match Map.find doc.tables name with
  | None -> Ok (empty name types)
  | Some t when [%equal: typ list] (Array.to_list t.types) types -> Ok t
  | Some t ->
      Or_error.errorf "the table %s has fields %s instead of %s" name
        (Sexp.to_string ([%sexp_of: typ array] t.types))
        (Sexp.to_string ([%sexp_of: typ list] types))

let name t = t.name
let length t = t.rows
let pos t row field = t.base + (row * t.stride) + t.offsets.(field)

let check t row field typ =
  if row < 0 || row >= t.rows then
    invalid_argf "%s: no row %d of %d" t.name row t.rows ();
  if field < 0 || field >= Array.length t.types then
    invalid_argf "%s: no field %d" t.name field ();
  if not (equal_typ t.types.(field) typ) then
    invalid_argf "%s: the field %d has a different type" t.name field ()

let int t row field =
  check t row field Int;
  Bigstring.get_int64_t_le t.data ~pos:(pos t row field)

let bool t row field =
  check t row field Bool;
  Bigstring.get_uint8 t.data ~pos:(pos t row field) <> 0

let str t row field =
  check t row field Str;
  let pos = pos t row field in
  Bigstring.To_string.sub t.data
    ~pos:(t.pool + get32 t.data pos)
    ~len:(get32 t.data (pos + 4))

(* the contents of a row, the strings are compared by their contents *)
let key t row =
  let b = Buffer.create 64 in
  Array.iteri t.types ~f:(fun field typ ->
      match typ with
      | Int | Bool ->
          let pos = pos t row field in
          for i = 0 to size typ - 1 do
            Buffer.add_char b (Bigstring.get t.data (pos + i))
          done
      | Str ->
          let s = str t row field in
          Buffer.add_string b (Int.to_string (String.length s));
          Buffer.add_char b ':';
          Buffer.add_string b s);
  Buffer.contents b

let facts t =
  let seen = Hash_set.create (module String) in
  List.fold (List.init t.rows ~f:Fn.id) ~init:[] ~f:(fun facts row ->
      let key = key t row in
      if Hash_set.mem seen key then facts
      else (
        Hash_set.add seen key;
        row :: facts))

let names doc = doc.order
