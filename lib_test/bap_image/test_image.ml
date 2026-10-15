open Core
open OUnit2
open Or_error
open Bap.Std

let ident = Int64.of_int

type segment = { addr : int; off : int; len : int }

let create_file () = Bytes.create 0x1000
let files : Bytes.t String.Table.t = String.Table.create ()

let data ?(base = 0) ?(gap = 0) f ss name =
  let addr_ref = ref base in
  List.map ss ~f:(fun data ->
      let data = f data in
      let addr = !addr_ref in
      let len = Bytes.length data in
      let dst = Hashtbl.find_or_add files name ~default:create_file in
      let off = addr - base in
      Bytes.blit ~src:data ~src_pos:0 ~dst ~dst_pos:off ~len;
      addr_ref := !addr_ref + len + gap;
      { addr; off; len })

let seq (n, m) : Bytes.t =
  Bytes.init (m - n + 1) ~f:(fun i -> Option.value_exn (Char.of_int (i + n)))

(* a readable and executable segment named [.test] *)
let provide_segment { addr; off; len } =
  let addr = Int64.of_int addr
  and size = Int64.of_int len
  and off = Int64.of_int off in
  Ogre.sequence
    [
      Ogre.provide Image.Scheme.segment addr size true false true;
      Ogre.provide Image.Scheme.mapped addr size off;
      Ogre.provide Image.Scheme.named_region addr size ".test";
    ]

let create ?(addr_size = `r32) ?(endian = LittleEndian) ss name =
  let arch =
    match (addr_size, endian) with
    | `r32, LittleEndian -> `mipsel
    | `r32, BigEndian -> `mips
    | `r64, LittleEndian -> `mips64el
    | `r64, BigEndian -> `mips64
  in
  let spec =
    Ogre.sequence
      [
        Ogre.provide Image.Scheme.entry_point 0L;
        Ogre.sequence (List.map (ss name) ~f:provide_segment);
      ]
  in
  let doc = ok_exn (Ogre.exec spec (Image.Spec.from_arch arch)) in
  let module Loader = struct
    let from_file _ = Ok (Some doc)
    let from_data _ = Ok (Some doc)
  end in
  (module Loader : Image.Loader)

let backends =
  let le = LittleEndian and be = BigEndian in
  List.fold ~init:[]
    ~f:(fun acc (n, secs) ->
      (n ^ "_32LE", create ~addr_size:`r32 ~endian:le secs)
      :: (n ^ "_32BE", create ~addr_size:`r32 ~endian:be secs)
      :: (n ^ "_64LE", create ~addr_size:`r64 ~endian:le secs)
      :: (n ^ "_64BE", create ~addr_size:`r64 ~endian:be secs)
      :: acc)
    [
      ("0-15", data seq [ (0, 15) ]);
      ("16x4", data seq [ (0, 15); (16, 31); (32, 47); (48, 63) ]);
      ("0-15_b", data ~base:0x1000FF seq [ (0, 15) ]);
      ( "16x4_b",
        data ~base:0x1000FF seq [ (0, 15); (16, 31); (32, 47); (48, 63) ] );
      ("0-15_g", data ~gap:0xFD seq [ (0, 15) ]);
      ("16x4_g", data ~gap:0xFD seq [ (0, 15); (16, 31); (32, 47); (48, 63) ]);
    ]

let () =
  List.iter
    ~f:(fun (name, backend) ->
      if Option.is_some (Image.find_loader name) then failwith name;
      Image.register_loader ~name (backend name))
    backends

let print_list r =
  let sexp_of_addr_list = sexp_of_list sexp_of_addr in
  Sexp.to_string_hum @@ Or_error.sexp_of_t sexp_of_addr_list r

let to_list ~word_size backend ~expect ctxt =
  let data = Hashtbl.find_exn files backend |> Bytes.to_string in
  let r =
    Image.of_string ~backend data >>| fun (img, warns) ->
    assert_bool "to_list: no warning" (List.is_empty warns);
    Table.to_sequence (Image.words img word_size)
    |> Seq.map ~f:snd |> Seq.to_list
  in
  let width = Size.in_bits word_size in
  let expect = List.map expect ~f:(Addr.of_int64 ~width) in
  assert_equal ~ctxt ~printer:print_list (Ok expect) r

let check ?(base = 0) backend ~f ctxt =
  let data = Hashtbl.find_exn files backend in
  let data = Bytes.to_string data in
  let r =
    Image.of_string ~backend data >>= fun (img, warns) ->
    assert_bool "check: no warning" (List.is_empty warns);
    f img >>= fun _ -> return ()
  in
  let printer err = Sexp.to_string_hum (Or_error.sexp_of_t sexp_of_unit err) in
  assert_equal ~ctxt ~msg:"Check failed" ~printer (Ok ()) r

let list_of_memory ?word_size m : (addr * word) list =
  Memory.foldi ?word_size m ~init:[] ~f:(fun addr word acc ->
      (addr, word) :: acc)
  |> List.rev

let assert_cont ~word_size img =
  let step = Size.in_bytes word_size in
  let words = Image.words img word_size in
  let base =
    match Table.min words with
    | Some (mem, _) -> Memory.min_addr mem
    | None -> invalid_arg "memory is empty"
  in
  Table.foldi words ~init:base ~f:(fun mem word a1 ->
      let a2 = Memory.min_addr mem in
      assert_bool "a1 = a2 -> a1 = base" (Addr.(a1 = a2) ==> Addr.(a1 = base));
      let s1 = Addr.of_int ~width:32 step in
      let () =
        match Addr.Int_err.(!$a2 - !$a1 - !$s1) with
        | Error err -> assert_string @@ Error.to_string_hum err
        | Ok diff ->
            assert_bool "a1 <> a2 -> a2 - a1 = (word_size)"
              (Word.(a1 <> a2) ==> Addr.is_zero diff)
      in
      a2)
  |> return

let suite () =
  "Image"
  >::: [
         "to_list:0-15/bytes_32LE"
         >:: to_list ~word_size:`r8 "0-15_32LE" ~expect:(List.init 16 ~f:ident);
         "to_list/0-15/bytes_32BE"
         >:: to_list ~word_size:`r8 "0-15_32BE" ~expect:(List.init 16 ~f:ident);
         "to_list/0-15/bytes_64LE"
         >:: to_list ~word_size:`r8 "0-15_64LE" ~expect:(List.init 16 ~f:ident);
         "to_list/0-15/bytes_64BE"
         >:: to_list ~word_size:`r8 "0-15_64BE" ~expect:(List.init 16 ~f:ident);
         "to_list/0-64/bytes_32LE"
         >:: to_list ~word_size:`r8 "16x4_32LE" ~expect:(List.init 64 ~f:ident);
         "to_list/0-15/int16_32LE"
         >:: to_list ~word_size:`r16 "0-15_32LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15/int16_32BE"
         >:: to_list ~word_size:`r16 "0-15_32BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15/int16_64LE"
         >:: to_list ~word_size:`r16 "0-15_64LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15/int16_64BE"
         >:: to_list ~word_size:`r16 "0-15_64BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15/int64_64LE"
         >:: to_list ~word_size:`r64 "0-15_64LE"
               ~expect:[ 0x0706050403020100L; 0x0f0e0d0c0b0a0908L ];
         "to_list/0-15/int64_64BE"
         >:: to_list ~word_size:`r64 "0-15_64BE"
               ~expect:[ 0x0001020304050607L; 0x08090a0b0c0d0e0fL ];
         "to_list/0-15_b/bytes_32LE"
         >:: to_list ~word_size:`r8 "0-15_b_32LE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_b/bytes_32BE"
         >:: to_list ~word_size:`r8 "0-15_b_32BE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_b/bytes_64LE"
         >:: to_list ~word_size:`r8 "0-15_b_64LE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_b/bytes_64BE"
         >:: to_list ~word_size:`r8 "0-15_b_64BE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-64/bytes_32LE"
         >:: to_list ~word_size:`r8 "16x4_b_32LE"
               ~expect:(List.init 64 ~f:ident);
         "to_list/0-15_b/int16_32LE"
         >:: to_list ~word_size:`r16 "0-15_b_32LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15_b/int16_32BE"
         >:: to_list ~word_size:`r16 "0-15_b_32BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15_b/int16_64LE"
         >:: to_list ~word_size:`r16 "0-15_b_64LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15_b/int16_64BE"
         >:: to_list ~word_size:`r16 "0-15_b_64BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15_b/int64_64LE"
         >:: to_list ~word_size:`r64 "0-15_b_64LE"
               ~expect:[ 0x0706050403020100L; 0x0f0e0d0c0b0a0908L ];
         "to_list/0-15_b/int64_64BE"
         >:: to_list ~word_size:`r64 "0-15_b_64BE"
               ~expect:[ 0x0001020304050607L; 0x08090a0b0c0d0e0fL ];
         "to_list/0-15_g/bytes_32LE"
         >:: to_list ~word_size:`r8 "0-15_g_32LE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_g/bytes_32BE"
         >:: to_list ~word_size:`r8 "0-15_g_32BE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_g/bytes_64LE"
         >:: to_list ~word_size:`r8 "0-15_g_64LE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-15_g/bytes_64BE"
         >:: to_list ~word_size:`r8 "0-15_g_64BE"
               ~expect:(List.init 16 ~f:ident);
         "to_list/0-64/bytes_32LE"
         >:: to_list ~word_size:`r8 "16x4_g_32LE"
               ~expect:(List.init 64 ~f:ident);
         "to_list/0-15_g/int16_32LE"
         >:: to_list ~word_size:`r16 "0-15_g_32LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15_g/int16_32BE"
         >:: to_list ~word_size:`r16 "0-15_g_32BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15_g/int16_64LE"
         >:: to_list ~word_size:`r16 "0-15_g_64LE"
               ~expect:
                 [
                   0x0100L;
                   0x0302L;
                   0x0504L;
                   0x0706L;
                   0x0908L;
                   0x0b0aL;
                   0x0d0cL;
                   0x0f0eL;
                 ];
         "to_list/0-15_g/int16_64BE"
         >:: to_list ~word_size:`r16 "0-15_g_64BE"
               ~expect:
                 [
                   0x0001L;
                   0x0203L;
                   0x0405L;
                   0x0607L;
                   0x0809L;
                   0x0a0bL;
                   0x0c0dL;
                   0x0e0fL;
                 ];
         "to_list/0-15_g/int64_64LE"
         >:: to_list ~word_size:`r64 "0-15_g_64LE"
               ~expect:[ 0x0706050403020100L; 0x0f0e0d0c0b0a0908L ];
         "to_list/0-15_g/int64_64BE"
         >:: to_list ~word_size:`r64 "0-15_g_64BE"
               ~expect:[ 0x0001020304050607L; 0x08090a0b0c0d0e0fL ];
         "addr/cont/8" >:: check "0-15_32LE" ~f:(assert_cont ~word_size:`r8);
         "addr/cont/16" >:: check "0-15_32LE" ~f:(assert_cont ~word_size:`r16);
         "addr/cont/32" >:: check "0-15_32LE" ~f:(assert_cont ~word_size:`r32);
         "addr/cont/64" >:: check "0-15_32LE" ~f:(assert_cont ~word_size:`r64);
         "addr/cont/8" >:: check "16x4_32LE" ~f:(assert_cont ~word_size:`r8);
         "addr/cont/16" >:: check "16x4_32LE" ~f:(assert_cont ~word_size:`r16);
         "addr/cont/32" >:: check "16x4_32LE" ~f:(assert_cont ~word_size:`r32);
         "addr/cont/64" >:: check "16x4_32LE" ~f:(assert_cont ~word_size:`r64);
         "addr/cont/8/b" >:: check "0-15_b_32LE" ~f:(assert_cont ~word_size:`r8);
         "addr/cont/16/b"
         >:: check "0-15_b_32LE" ~f:(assert_cont ~word_size:`r16);
         "addr/cont/32/b"
         >:: check "0-15_b_32LE" ~f:(assert_cont ~word_size:`r32);
         "addr/cont/64/b"
         >:: check "0-15_b_32LE" ~f:(assert_cont ~word_size:`r64);
         "addr/cont/8/b" >:: check "16x4_b_32LE" ~f:(assert_cont ~word_size:`r8);
         "addr/cont/16/b"
         >:: check "16x4_b_32LE" ~f:(assert_cont ~word_size:`r16);
         "addr/cont/32/b"
         >:: check "16x4_b_32LE" ~f:(assert_cont ~word_size:`r32);
         "addr/cont/64/b"
         >:: check "16x4_b_32LE" ~f:(assert_cont ~word_size:`r64);
         "max-min"
         >:: check "16x4_g_32LE" ~f:(fun img ->
             let words = Image.words img `r8 in
             let mx, mn =
               match (Table.max words, Table.min words) with
               | Some (mx, _), Some (mn, _) -> (mx, mn)
               | _ -> invalid_arg "empty table"
             in
             let mx, mn = Memory.(min_addr mx, min_addr mn) in
             let printer = Addr.to_string in
             assert_equal ~printer Addr.(mn ++ 0x336) mx;
             return ());
       ]
