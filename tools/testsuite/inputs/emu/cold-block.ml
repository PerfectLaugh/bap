#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_core_theory
open Bap_primus.Std
module Emu = Bap_emu

let evaluations = ref 0

let eval f =
  incr evaluations;
  let result = ref None in
  Toplevel.exec KB.Syntax.(f >>| fun x -> result := Some x);
  Option.value_exn !result

let normalize text =
  let is_hex = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false
  in
  let rec loop i acc =
    if i = String.length text then String.of_char_list (List.rev acc)
    else if Char.equal text.[i] '%' then
      let rec skip i =
        if i < String.length text && is_hex text.[i] then skip (i + 1) else i
      in
      loop (skip (i + 1)) ('%' :: acc)
    else loop (i + 1) (text.[i] :: acc)
  in
  loop 0 []

let bir blks =
  String.concat ~sep:"\n" (List.map blks ~f:Blk.to_string)
  |> String.split_lines
  |> List.map ~f:(fun line ->
      let rec digits i =
        if i < String.length line then
          match line.[i] with
          | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> digits (i + 1)
          | _ -> i
        else i
      in
      let i = digits 0 in
      if i > 0 && i < String.length line && Char.equal line.[i] ':' then
        String.drop_prefix line i |> normalize
      else normalize line)
  |> String.concat ~sep:"\n"

let bytes proj addr length =
  let width = Theory.Target.code_addr_size (Project.target proj) in
  let addr = Addr.of_int64 ~width addr in
  Memmap.lookup (Project.memory proj) addr
  |> Seq.find_map ~f:(fun (mem, _) ->
      if Memory.contains mem addr then
        Some
          (Memory.view_exn ~from:addr ~words:length mem
          |> Memory.to_buffer |> Bigsubstring.to_string)
      else None)
  |> Option.value_exn

let parity ?encoding ?(budget = 64) ?(count = 8) ?(minimum = 1) label proj addr
    code =
  let initial = Toplevel.current () in
  evaluations := 0;
  let grouped =
    Exn.protect
      ~finally:(fun () -> Toplevel.set initial)
      ~f:(fun () ->
        eval (Primus.Lift.block ?encoding ~budget ~count proj addr code))
  in
  if !evaluations <> 1 then
    failwithf "%s: wrong block evaluation count" label ();
  if List.length grouped < minimum then
    failwithf "%s: got only %d instructions" label (List.length grouped) ();
  let used = List.fold grouped ~init:0 ~f:(fun n (size, _, _, _) -> n + size) in
  if used > budget || List.length grouped > count then
    failwithf "%s: unbounded block" label ();
  Exn.protect
    ~finally:(fun () -> Toplevel.set initial)
    ~f:(fun () ->
      let rec compare offset = function
        | [] -> ()
        | (size, coding, name, blks) :: rest ->
            let other =
              match
                eval
                  (Primus.Lift.named ?encoding proj
                     Int64.(addr + of_int offset)
                     (String.drop_prefix code offset))
              with
              | Some insn -> insn
              | None -> failwithf "%s: named failed at +%d" label offset ()
            in
            let size', name', blks' = other in
            if size <> size' || not (String.equal name name') then
              failwithf "%s: instruction metadata differs at +%d" label offset
                ();
            if not (String.equal (bir blks) (bir blks')) then
              failwithf "%s: BIR differs at +%d\n%s\n%s" label offset (bir blks)
                (bir blks') ();
            List.iter rest ~f:(fun (_, coding', _, _) ->
                if not (Theory.Language.equal coding coding') then
                  failwithf "%s: encoding changed inside the block" label ());
            compare (offset + size) rest
      in
      compare 0 grouped);
  if !evaluations <> List.length grouped + 1 then
    failwithf "%s: wrong named evaluation count" label ();
  printf "parity %s: %d instructions, 1 vs %d evaluations\n%!" label
    (List.length grouped) (!evaluations - 1)

let undefined proj =
  evaluations := 0;
  let code = "\x20\xd8\xa1\x5e" in
  let named = eval (Primus.Lift.named proj 0L code) in
  let grouped = eval (Primus.Lift.block ~budget:64 ~count:8 proj 0L code) in
  let name = eval (Primus.Lift.undefined proj 0L code) in
  if
    Option.is_some named || (not (List.is_empty grouped)) || Option.is_none name
  then failwith "undefined instruction parity failed";
  print_endline "undefined instruction: no BIR in named or block"

let trace_pcs trace =
  let pcs = Emu.Trace.insns trace in
  List.init (Bigarray.Array1.dim pcs) ~f:(Bigarray.Array1.get pcs)

let running file =
  let lifts =
    Stdlib.Filename.concat (Sys.getenv_exn "BAP_CACHE_DIR") "lifted/lifts"
  in
  (match Stdlib.Sys.readdir lifts with
  | files ->
      Array.iter files ~f:(fun file ->
          Stdlib.Sys.remove (Stdlib.Filename.concat lifts file))
  | exception Sys_error _ -> ());
  Caml_unix.putenv "BAP_LIFTED_STATS" "1";
  let emu = Emu.create ~engine:`Lifted (Bap_script.project file) in
  let entry = Emu.pc emu and callee = Int64.(Emu.pc emu + 0x100L) in
  let word x = Emu.AArch64.bytes x in
  let branch pc target = Emu.AArch64.bytes (Emu.AArch64.b ~pc target) in
  let call pc target =
    Int32.(0x94000000l lor (0x03ffffffl land Emu.AArch64.b ~pc target)) |> word
  in
  let stp = word 0xa9bf7bfdl and mov_fp = word 0x910003fdl in
  let ldp = word 0xa8c17bfdl and ret = word 0xd65f03c0l in
  let mov42 = word 0xd2800540l and mov9 = word 0xd2800120l in
  Emu.write emu entry
    (String.concat
       [
         stp;
         mov_fp;
         call Int64.(entry + 8L) callee;
         branch Int64.(entry + 12L) Int64.(entry + 0x20L);
         ldp;
         ret;
         ldp;
         ret;
         ldp;
         ret;
       ]);
  Emu.write emu callee (mov42 ^ ret);
  let stopped = ref false in
  Emu.on_code emu ~first:entry ~last:entry (fun emu _ ->
      if not !stopped then (
        stopped := true;
        Emu.stop emu));
  (match Emu.call emu entry with
  | None -> ()
  | _ -> failwith "the batched function did not pause");
  let first =
    Emu.insns emu |> List.filter ~f:(fun addr -> not (Int64.equal addr 0L))
  in
  if not (List.equal Int64.equal first [ entry ]) then
    failwithf "look-ahead entered history: %s"
      (String.concat ~sep:"," (List.map first ~f:(sprintf "%Lx")))
      ();
  let resumed = Emu.record emu (fun () -> Emu.run emu) in
  (match resumed.result with
  | Ok Emu.Paused when Option.equal Int64.equal (Emu.returned emu) (Some 42L) ->
      ()
  | _ -> failwith "the batched function did not return 42");
  let trajectory = trace_pcs resumed.trace in
  let expected =
    [
      entry;
      Int64.(entry + 4L);
      Int64.(entry + 8L);
      callee;
      Int64.(callee + 4L);
      Int64.(entry + 12L);
      Int64.(entry + 0x20L);
      Int64.(entry + 0x24L);
    ]
  in
  if not (List.equal Int64.equal trajectory expected) then
    failwithf "wrong trajectory: %s"
      (String.concat ~sep:"," (List.map trajectory ~f:(sprintf "%Lx")))
      ();
  (match Emu.call emu entry with
  | Some 42L -> ()
  | _ -> failwith "the warm batched function did not return 42");
  Emu.write emu callee (mov9 ^ ret);
  (match Emu.call emu entry with
  | Some 9L -> ()
  | _ -> failwith "the patched batched function did not return 9");
  Emu.write emu callee "\x20\xd8\xa1\x5e";
  (match Emu.call emu callee with
  | exception Failure msg
    when String.is_substring msg ~substring:"has no semantics" ->
      ()
  | _ -> failwith "an undefined instruction ran as a no-op");
  printf
    "running: %d instructions, identical call/jump trajectory, patched result 9\n\
     %!"
    (List.length trajectory)

let () =
  match Bap_script.args () with
  | [ x86; thumb; aarch64; powerpc ] ->
      let x86 = Bap_script.project x86
      and thumb = Bap_script.project thumb
      and aarch64 = Bap_script.project aarch64
      and powerpc = Bap_script.project powerpc in
      parity ~minimum:4 "x86 straight-line" x86 0x40076bL
        (bytes x86 0x40076bL 64);
      parity ~count:16 ~minimum:2 "x86 call" x86 0x40061dL
        (bytes x86 0x40061dL 64);
      parity ~budget:5 ~minimum:2 "x86 byte budget" x86 0x40076bL
        (bytes x86 0x40076bL 64);
      let encoding = Primus.Interworking.encoding ~thumb:true in
      parity ?encoding ~minimum:3 "Thumb IT" thumb 0x2028aL
        (bytes thumb 0x2028aL 64);
      parity ~minimum:2 "AArch64 little endian" aarch64 0x960L
        (bytes aarch64 0x960L 64);
      parity ~minimum:2 "PowerPC big endian" powerpc 0x10000420L
        (bytes powerpc 0x10000420L 64);
      undefined aarch64;
      running (List.nth_exn (Bap_script.args ()) 2)
  | _ -> failwith "expected X86 THUMB AARCH64 POWERPC"
