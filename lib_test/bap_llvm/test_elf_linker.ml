open Core
open OUnit2
module Linker = Bap_llvm_elf_linker

let section ?(typ = 1) ?(align = 4L) index name ~flags ~off ~size =
  { Linker.index; name; typ; flags; off; size; align }

let text = section ~flags:6L
let data = section ~flags:3L

let symbol ?(value = 0L) ?(size = 0L) ?(typ = 0) ?(bind = 1) name shndx =
  { Linker.name; shndx; extended = false; value; size; typ; bind }

let rel ?(addend = 0L) section offset typ symbol =
  { Linker.section; offset; typ; symbol; addend; explicit = true }

let rel_implicit section offset typ symbol =
  { (rel section offset typ symbol) with explicit = false }

let link ?(little = true) ?(width = 64) ~machine ~base ~bytes sections symbols
    relocations =
  Linker.link
    {
      machine;
      width;
      little;
      base;
      data = Bigstring.of_string bytes;
      sections;
      symbols = Int.Map.of_alist_exn symbols;
      relocations;
    }

(* the input with the patches applied *)
let patched ~little bytes { Linker.patches } =
  let length =
    List.fold patches ~init:(String.length bytes) ~f:(fun len (off, size, _) ->
        max len (Int64.to_int_exn off + size))
  in
  let data = Bytes.make length '\000' in
  Bytes.From_string.blit ~src:bytes ~src_pos:0 ~dst:data ~dst_pos:0
    ~len:(String.length bytes);
  List.iter patches ~f:(fun (off, size, value) ->
      for i = 0 to size - 1 do
        let shift = 8 * if little then i else size - i - 1 in
        Int64.(shift_right_logical value shift land 0xffL)
        |> Int64.to_int_exn |> Char.of_int_exn
        |> Bytes.set data (Int64.to_int_exn off + i)
      done);
  data

let word ~little data off size =
  List.init size ~f:Fn.id
  |> List.fold ~init:0L ~f:(fun acc i ->
      let b = Int64.of_int (Char.to_int (Bytes.get data (off + i))) in
      let shift = 8 * if little then i else size - i - 1 in
      Int64.(acc lor shift_left b shift))

let assert_word ~ctxt ~little ~msg data off size expect =
  assert_equal ~ctxt ~msg ~printer:(sprintf "%#Lx") expect
    (word ~little data off size)

let assert_no_warnings { Linker.warnings } =
  assert_equal ~printer:(String.concat ~sep:"; ") [] warnings

(* x86-64: a call to an external function, a GOT load of its address,
   and an absolute pointer to the code *)
let x86_64 ctxt =
  let bytes = String.make 0x58 '\000' in
  let out =
    link ~machine:62 ~base:0x1000L ~bytes
      [
        text 1 ".text" ~off:0x40L ~size:16L ~align:16L;
        data 2 ".data" ~off:0x50L ~size:8L ~align:8L;
      ]
      [
        (1, symbol "" 1 ~typ:3 ~bind:0);
        (2, symbol "puts" 0);
        (3, symbol "f" 1 ~size:16L ~typ:2);
      ]
      [
        rel 1 1L 4 2 ~addend:(-4L);
        rel 1 8L 42 2 ~addend:(-4L);
        rel 2 0L 1 1 ~addend:5L;
      ]
  in
  assert_no_warnings out;
  let data = patched ~little:true bytes out in
  let assert_word = assert_word ~ctxt ~little:true data in
  assert_word ~msg:"PLT32" 0x41 4 0x13L;
  assert_word ~msg:"REX_GOTPCRELX" 0x48 4 0x14L;
  assert_word ~msg:"64" 0x50 8 0x1005L;
  assert_word ~msg:"GOT entry" 0x58 8 0x1018L;
  let regions =
    List.map out.regions ~f:(fun { Linker.name; addr; size; off } ->
        (name, addr, size, off))
  in
  assert_equal ~ctxt
    [
      (".text", 0x1000L, 16L, Some 0x40L);
      (".data", 0x1010L, 8L, Some 0x50L);
      ("EXTERNAL", 0x1018L, 8L, None);
      ("%got", 0x1020L, 8L, Some 0x58L);
    ]
    regions;
  assert_equal ~ctxt [ ("f", 0x1000L, 16L, 0x1000L) ] out.functions;
  assert_equal ~ctxt [ (0x1001L, "puts"); (0x1008L, "puts") ] out.references

(* MIPS: the HI16 relocation is applied with the addend of the
   following LO16 relocation *)
let mips_hi_lo ctxt =
  let bytes =
    String.make 0x40 '\000' ^ "\x3c\x02\x00\x01\x24\x42\x80\x00"
    ^ String.make 0x10 '\000'
  in
  let out =
    link ~machine:8 ~width:32 ~little:false ~base:0x10000L ~bytes
      [
        text 1 ".text" ~off:0x40L ~size:8L;
        data 2 ".data" ~off:0x48L ~size:0x10L;
      ]
      [ (1, symbol "" 2 ~typ:3 ~bind:0) ]
      [ rel_implicit 1 0L 5 1; rel_implicit 1 4L 6 1 ]
  in
  assert_no_warnings out;
  let data = patched ~little:false bytes out in
  let assert_word = assert_word ~ctxt ~little:false data in
  assert_word ~msg:"HI16" 0x40 4 0x3c020002L;
  assert_word ~msg:"LO16" 0x44 4 0x24428008L

(* RISC-V: the PCREL_LO12 relocation references the AUIPC instruction
   that holds the high part of the offset *)
let riscv_pcrel ctxt =
  let bytes = String.make 0x40 '\000' ^ "\x17\x05\x00\x00\x13\x05\x05\x00" in
  let out =
    link ~machine:243 ~base:0x10000L ~bytes
      [
        text 1 ".text" ~off:0x40L ~size:8L;
        data 2 ".data" ~off:0x48L ~size:0x1000L ~align:0x1000L;
      ]
      [
        (1, symbol "x" 2 ~value:0x900L ~typ:1);
        (2, symbol ".Lpcrel_hi0" 1 ~bind:0);
      ]
      [ rel 1 0L 23 1; rel 1 0L 51 0; rel 1 4L 24 2; rel 1 4L 51 0 ]
  in
  assert_no_warnings out;
  let data = patched ~little:true bytes out in
  let assert_word = assert_word ~ctxt ~little:true data in
  assert_word ~msg:"PCREL_HI20" 0x40 4 0x00002517L;
  assert_word ~msg:"PCREL_LO12_I" 0x44 4 0x90050513L

(* AArch64: ADRP+ADD of a data address and a backward call *)
let aarch64 ctxt =
  let bytes =
    String.make 0x40 '\000' ^ "\x00\x00\x00\x90\x00\x00\x00\x91\x00\x00\x00\x94"
  in
  let out =
    link ~machine:183 ~base:0x10000L ~bytes
      [
        text 1 ".text" ~off:0x40L ~size:12L;
        data 2 ".data" ~off:0x4cL ~size:0x20L ~align:0x1000L;
      ]
      [
        (1, symbol "x" 2 ~value:0x10L ~typ:1); (2, symbol "g" 1 ~size:12L ~typ:2);
      ]
      [ rel 1 0L 0x113 1; rel 1 4L 0x115 1; rel 1 8L 0x11b 2 ]
  in
  assert_no_warnings out;
  let data = patched ~little:true bytes out in
  let assert_word = assert_word ~ctxt ~little:true data in
  assert_word ~msg:"ADR_PREL_PG_HI21" 0x40 4 0xb0000000L;
  assert_word ~msg:"ADD_ABS_LO12_NC" 0x44 4 0x91004000L;
  assert_word ~msg:"CALL26" 0x48 4 0x97fffffeL

(* a relocation that starts inside of the section but ends past it is
   not applied, it would otherwise overwrite the GOT, which is stored
   right after the end of the file *)
let outside_of_section ctxt =
  let bytes = String.make 0x48 '\000' in
  let out =
    link ~machine:62 ~base:0x1000L ~bytes
      [ text 1 ".text" ~off:0x40L ~size:8L ]
      [ (1, symbol "puts" 0) ]
      [ rel 1 4L 9 1 ~addend:(-4L); rel 1 6L 1 1 ]
  in
  assert_equal ~ctxt ~printer:Int.to_string 1 (List.length out.warnings);
  let data = patched ~little:true bytes out in
  let assert_word = assert_word ~ctxt ~little:true data in
  assert_word ~msg:"GOTPCREL" 0x44 4 0x8L;
  assert_word ~msg:"GOT entry" 0x48 8 0x1008L;
  assert_word ~msg:"the last bytes of .text" 0x46 2 0x0L

(* an extended section index that coincides with SHN_ABS refers to a
   section, not to an absolute value *)
let extended_index ctxt =
  let bytes = String.make 0x50 '\000' in
  let shn_abs = 0xfff1 in
  let out =
    link ~machine:62 ~base:0x1000L ~bytes
      [
        text 1 ".text" ~off:0x40L ~size:8L;
        data shn_abs ".data" ~off:0x48L ~size:8L ~align:8L;
      ]
      [
        (1, { (symbol "x" shn_abs ~value:4L) with extended = true });
        (2, symbol "y" shn_abs ~value:4L);
      ]
      [ rel 1 0L 1 1; rel shn_abs 0L 1 2 ]
  in
  assert_no_warnings out;
  let data = patched ~little:true bytes out in
  let assert_word = assert_word ~ctxt ~little:true data in
  assert_word ~msg:"extended" 0x40 8 0x100cL;
  assert_word ~msg:"absolute" 0x48 8 0x4L

let unsupported_machine ctxt =
  let out =
    link ~machine:21 ~base:0L ~bytes:(String.make 0x48 '\000')
      [ text 1 ".text" ~off:0x40L ~size:8L ]
      [ (1, symbol "" 1 ~typ:3 ~bind:0) ]
      [ rel 1 0L 1 1 ]
  in
  assert_equal ~ctxt [] out.patches;
  assert_equal ~ctxt 1 (List.length out.warnings)

let suite =
  "ELF linker"
  >::: [
         "x86-64" >:: x86_64;
         "mips/hi-lo" >:: mips_hi_lo;
         "riscv/pcrel" >:: riscv_pcrel;
         "aarch64" >:: aarch64;
         "outside of section" >:: outside_of_section;
         "extended section index" >:: extended_index;
         "unsupported machine" >:: unsupported_machine;
       ]

let () = run_test_tt_main suite
