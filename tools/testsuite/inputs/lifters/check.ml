#require "bap-primus-native.emu"

(* Checks the semantics of the lifters against Unicorn: each instruction
   runs once in Unicorn, and once in Primus, which interprets its lifted
   semantics, see [Emu.interpret], from the same random state,
   whose registers are random, or point to a buffer of random bytes, so
   that the loads and the stores access it, and the registers, the
   flags, the buffer, the address of the next instruction, and the
   status, e.g., of a fault, are compared:

     bap script check.ml PROGRAM INSNS [thumb] [r6] [api=DIR] [seed=N]
       [runs=N] [flags=all] [engine=lifted]

   where PROGRAM is a program of the target, whose entry the
   instructions overwrite, and INSNS the file of the instructions, a line
   of their bytes in hex each, e.g., "48 01 d8", in the order of the
   memory, optionally followed by a comment after #. It prints the
   instructions, whose results differ, with their registers.

   With engine=lifted, the instructions run in the lifted engine, see
   Bap_lifted, rather than in Primus, from the same state in an emulator
   of their own, so that the engine is checked against Unicorn. *)

module Emu = Bap_emu
open Bap.Std

let args = Bap_script.args ()
let flag name = List.mem name args

let opt name default =
  List.fold_left
    (fun acc arg ->
      let prefix = name ^ "=" in
      if String.starts_with ~prefix arg then
        String.sub arg (String.length prefix)
          (String.length arg - String.length prefix)
      else acc)
    default args

let file, insns =
  match List.filter (fun a -> not (String.contains a '=')) args with
  | file :: insns :: _ -> (file, insns)
  | _ -> failwith "usage: check.ml PROGRAM INSNS [thumb] [api=DIR] [seed=N]"

let thumb = flag "thumb"

(* the flags differ also when they are undefined, e.g., AF of IMUL of
   x86, so they are compared with flags=all only *)
let all_flags = opt "flags" "" = "all"
let runs = int_of_string (opt "runs" "4")
let seed = int_of_string (opt "seed" "1")
let api = match opt "api" "" with "" -> [] | dir -> [ dir ]

let target = Filename.basename file
let mips = String.starts_with ~prefix:"mips" target
let starts prefix = String.starts_with ~prefix target
let numbered prefix first last = List.init (last - first + 1) (fun i -> Printf.sprintf "%s%d" prefix (first + i))

(* the registers, that the instructions read and write, without their
   aliases, the pointer of the stack, which points to the buffer, and
   the others *)
let sp, gprs, others =
  if starts "x86_64" then
    ( "RSP",
      [ "RAX"; "RBX"; "RCX"; "RDX"; "RSI"; "RDI"; "RBP" ] @ numbered "R" 8 15,
      [ "CF"; "PF"; "AF"; "ZF"; "SF"; "OF" ] @ numbered "YMM" 0 15 )
  else if starts "i686" || starts "x86-" then
    ( "ESP",
      [ "EAX"; "EBX"; "ECX"; "EDX"; "ESI"; "EDI"; "EBP" ],
      [ "CF"; "PF"; "AF"; "ZF"; "SF"; "OF" ] @ numbered "YMM" 0 7 )
  else if starts "aarch64" then
    ("SP", numbered "R" 0 30, [ "NF"; "ZF"; "CF"; "VF" ] @ numbered "Q" 0 31)
  else if starts "arm" then
    ( "SP",
      numbered "R" 0 12 @ [ "LR" ],
      [ "NF"; "ZF"; "CF"; "VF"; "QF" ] @ numbered "D" 0 31 )
  else if starts "mips" then
    ( "R29",
      numbered "R" 1 28 @ [ "R30"; "R31"; "HI"; "LO" ],
      numbered "F" 0 31 )
  else if starts "riscv" then
    ("X2", "X1" :: numbered "X" 3 31, numbered "F" 0 31)
  else if starts "powerpc" then
    ( "R1",
      "R0" :: numbered "R" 2 31,
      numbered "F" 0 31
      @ List.concat_map
          (fun n ->
            List.map (Printf.sprintf "CR%d%s" n) [ "LT"; "GT"; "EQ"; "UN" ])
          (List.init 8 Fun.id)
      @ [ "SO"; "OV"; "CA" ] )
  else failwith ("unknown target " ^ target)

let flags =
  [ "CF"; "PF"; "AF"; "ZF"; "SF"; "OF"; "NF"; "VF"; "QF" ]
  @ List.concat_map
      (fun n -> List.map (Printf.sprintf "CR%d%s" n) [ "LT"; "GT"; "EQ"; "UN" ])
      (List.init 8 Fun.id)
  @ [ "SO"; "OV"; "CA" ]

(* the release 6 of MIPS, whose compact branches have no delay slots,
   e.g., of the program mips32r6el with r6 *)
let r6 = flag "r6"

(* if the instruction of MIPS has a delay slot, by its encoding, as
   [Primus_native_executor.mips_delayed] tells *)
let word_of code =
  let b i = Char.code code.[if String.starts_with ~prefix:"mipsel" target || String.starts_with ~prefix:"mips64el" target || String.ends_with ~suffix:"el" target then 3 - i else i] in
  (b 0 lsl 24) lor (b 1 lsl 16) lor (b 2 lsl 8) lor b 3

let delayed code =
  String.length code = 4
  &&
  let word = word_of code in
  let op = (word lsr 26) land 0x3F and rs = (word lsr 21) land 0x1F in
  let rt = (word lsr 16) land 0x1F and funct = word land 0x3F in
  match op with
  | 0x02 | 0x03 | 0x04 | 0x05 -> true
  (* BLEZ and BGTZ, the others of their opcodes are compact *)
  | 0x06 | 0x07 when r6 -> rt = 0
  | 0x06 | 0x07 | 0x14 | 0x15 | 0x16 | 0x17 -> not r6
  | 0x01 when r6 -> List.mem rt [ 0x00; 0x01; 0x10; 0x11 ]
  | 0x01 -> List.mem rt [ 0x00; 0x01; 0x02; 0x03; 0x10; 0x11; 0x12; 0x13 ]
  | 0x00 -> funct = 0x08 || funct = 0x09
  | 0x11 when r6 -> rs = 0x09 || rs = 0x0d
  | 0x11 -> rs = 0x08
  | _ -> false

(* if the instruction is a conditional compact branch of the release 6,
   whose forbidden slot, after it, Unicorn runs with it, if it is not
   taken *)
let compact code =
  r6 && String.length code = 4 && (not (delayed code))
  && List.mem ((word_of code lsr 26) land 0x3F) [ 0x06; 0x07; 0x08; 0x16; 0x17; 0x18; 0x36; 0x3E ]

(* the nops, that follow the instruction *)
let nops =
  let nop =
    if starts "x86" || starts "i686" then "\x90"
    else if thumb then "\x00\xbf"
    else if starts "aarch64" then "\x1f\x20\x03\xd5"
    else if starts "arm" then "\x00\xf0\x20\xe3"
    else if starts "riscv" then "\x13\x00\x00\x00"
    else if starts "powerpc" then "\x60\x00\x00\x00"
    else "\x00\x00\x00\x00"
  in
  String.concat "" (List.init (16 / String.length nop) (fun _ -> nop))

let bytes_of_hex line =
  String.split_on_char ' ' line
  |> List.filter (fun s -> s <> "")
  |> List.map (fun h -> Char.chr (int_of_string ("0x" ^ h)))
  |> List.to_seq |> String.of_seq

let random_word width =
  let rec bits w =
    if w <= 0 then Word.zero 0
    else
      let n = min w 30 in
      let x = Word.of_int ~width:n (Random.bits () land ((1 lsl n) - 1)) in
      if w = n then x else Word.concat (bits (w - n)) x
  in
  (* the small values and the ones of the edges, too *)
  match Random.int 6 with
  | 0 -> Word.zero width
  | 1 -> Word.ones width
  | 2 -> Word.of_int ~width (Random.int 64 - 32)
  | 3 -> Word.of_int ~width (Random.int 3)
  | _ -> bits width

let status_name : Emu.status -> string = function
  | Paused -> "paused"
  | Running -> "running"
  | Exited c ->
      Printf.sprintf "exited %s"
        (match c with Some c -> string_of_int c | None -> "-")
  | Failed m -> "failed " ^ m

type state = {
  status : string;
  pc : int64;
  regs : (string * word) list;
  buffer : string;
}

let capture emu buf size status =
  let regs =
    List.filter_map
      (fun r ->
        match Emu.reg_word emu r with
        | x -> Some (r, x)
        | exception Invalid_argument _ -> None)
      ((sp :: gprs) @ others)
  in
  let pc, buffer =
    match status with
    | "paused" ->
        ( Int64.logand (Emu.pc emu) (if thumb then Int64.lognot 1L else -1L),
          try Emu.read emu buf size with _ -> "" )
    | _ -> (0L, "")
  in
  { status; pc; regs; buffer }

let engine = opt "engine" "" = "lifted"

let () =
  let emu =
    Emu.create ~engine:`Unicorn ~components:Emu.Taint.components
      (Bap_script.project ~api ~disassemble:true file)
  in
  let other =
    if engine then
      let other =
        Emu.create ~engine:`Lifted ~components:Emu.Taint.components
          (Bap_script.project ~api ~disassemble:true file)
      in
      (* the state, from which each instruction starts, as it may fault *)
      Some (other, Emu.snapshot other)
    else None
  in
  let entry = Int64.logand (Emu.pc emu) (Int64.lognot 1L) in
  let size = 0x4000 in
  let buf =
    Int64.logand
      (Int64.sub (Emu.reg emu sp) 0x20000L)
      (Int64.lognot 0xFFFL)
  in
  let lines =
    In_channel.with_open_text insns In_channel.input_lines
    |> List.filter_map (fun l ->
        let code, comment =
          match String.index_opt l '#' with
          | Some i -> (String.sub l 0 i, String.sub l (i + 1) (String.length l - i - 1))
          | None -> (l, "")
        in
        if String.trim code = "" then None
        else Some (bytes_of_hex code, String.trim comment, String.trim code))
  in
  let differ = ref 0 and total = ref 0 in
  List.iter
    (fun (code, comment, hex) ->
      incr total;
      (* the states of an instruction are the same in every list *)
      Random.full_init [| seed; Hashtbl.hash hex |];
      let failures = ref [] in
      for run = 1 to runs do
        let pointers = run mod 2 = 1 in
        (* the state, from which the instruction runs both times, with
           the nops after it, e.g., in the delay slot of MIPS, rather
           than the bytes of the previous instruction *)
        let data = String.init size (fun _ -> Char.chr (Random.int 256)) in
        let regs =
          List.filter_map
            (fun r ->
              match Emu.reg_word emu r with
              | exception Invalid_argument _ -> None
              | w ->
                  let width = Word.bitwidth w in
                  Some
                    ( r,
                      if pointers && List.mem r gprs then
                        Word.of_int64 ~width
                          (Int64.add buf
                             (Int64.of_int (0x1000 + (16 * Random.int 128))))
                      else random_word width ))
            (gprs @ others)
        in
        let prepare emu =
          Emu.write emu entry (code ^ nops);
          (* the instruction before it, of the program, isn't a branch of
             MIPS, whose delay slot the instruction would be *)
          if mips then Emu.write emu (Int64.sub entry 4L) "\000\000\000\000";
          Emu.write emu buf data;
          List.iter (fun (r, x) -> Emu.set_reg_word emu r x) regs;
          Emu.set_reg emu sp (Int64.add buf 0x2000L);
          Emu.set_pc emu (if thumb then Int64.logor entry 1L else entry)
        in
        prepare emu;
        let snapshot = Emu.snapshot emu in
        (* the step, that stopped at the instruction, as it faulted on a
           page, that Unicorn copies, continues *)
        let step emu =
          match Emu.step emu with
          | Paused
            when Int64.equal
                   (Int64.logand (Emu.pc emu)
                      (if thumb then Int64.lognot 1L else -1L))
                   entry ->
              Emu.step emu
          (* the branch of MIPS stops in its delay slot *)
          | Paused when mips && delayed code && Int64.equal (Emu.pc emu) (Int64.add entry 4L) ->
              Emu.step emu
          | status -> status
        in
        let native = capture emu buf size (status_name (step emu)) in
        Emu.restore emu snapshot;
        let lifted =
          match other with
          | Some (other, start) ->
              Emu.restore other start;
              prepare other;
              capture other buf size (status_name (step other))
          | None ->
        let status =
          match Emu.interpret emu with
          (* the branch of MIPS, that is not taken, runs its delay slot
             next *)
          | Paused when mips && (delayed code || compact code) && Int64.equal (Emu.pc emu) (Int64.add entry 4L) ->
              Emu.interpret emu
          | status -> status
        in
        let lifted = capture emu buf size (status_name status) in
        Emu.restore emu snapshot;
        lifted
        in
        let unchecked =
          String.starts_with ~prefix:"failed Unicorn: an invalid instruction"
            native.status
          (* the illegal instructions of RISC-V are its exception 2 *)
          || String.starts_with target ~prefix:"riscv"
             && String.starts_with ~prefix:"failed Unicorn: an unhandled interrupt 2 "
                  native.status
        in
        let diffs =
          if unchecked then [ "unchecked, as Unicorn doesn't have it" ]
          else
          (let fault s =
             String.starts_with ~prefix:"failed Segmentation fault" s
             (* the unaligned accesses, e.g., of MIPS, are the exceptions
                of Unicorn *)
             || String.starts_with ~prefix:"failed Unicorn: an unhandled interrupt" s
             (* the exceptions of the divisions, and of the traps, e.g.,
                teq of MIPS, which are intrinsic in Primus *)
             || String.starts_with ~prefix:"failed Division by zero" s
             || String.starts_with ~prefix:"failed unbound function intrinsic:trap" s
           in
           if native.status <> lifted.status
              && not (fault native.status && fault lifted.status)
           then
             [ Printf.sprintf "status %s / %s" native.status lifted.status ]
           else [])
          @ (if native.pc <> lifted.pc then
               [ Printf.sprintf "pc %Lx / %Lx" native.pc lifted.pc ]
             else [])
          @ List.filter_map
              (fun (r, x) ->
                match List.assoc_opt r lifted.regs with
                | Some y when not (Word.equal x y) && List.mem r flags && not all_flags -> None
                | Some y when not (Word.equal x y) ->
                    Some
                      (Format.asprintf "%s %a / %a" r Word.pp_hex x Word.pp_hex
                         y)
                | _ -> None)
              native.regs
          @
          if native.buffer <> lifted.buffer then
            let i = ref 0 in
            while
              !i < String.length native.buffer
              && !i < String.length lifted.buffer
              && native.buffer.[!i] = lifted.buffer.[!i]
            do
              incr i
            done;
            [ Printf.sprintf "memory at %Lx" (Int64.add buf (Int64.of_int !i)) ]
          else []
        in
        if diffs <> [] then
          failures :=
            Printf.sprintf "run %d (%s): %s" run
              (if pointers then "pointers" else "values")
              (String.concat "; " diffs)
            :: !failures
      done;
      match !failures with
      | [] -> ()
      | fs ->
          incr differ;
          Printf.printf "DIFF %s  # %s\n" hex comment;
          List.iter (Printf.printf "  %s\n") (List.rev fs))
    lines;
  Printf.printf "checked %d instructions, %d differ\n" !total !differ
