open Core
open Bap_core_theory
open Bap.Std

let package = "bap"

type r128
and r80
and r64
and r32
and r16
and r8

type 'a bitv = 'a Theory.Bitv.t Theory.Value.sort

let r128 : r128 bitv = Theory.Bitv.define 128
let r80 : r80 bitv = Theory.Bitv.define 80
let r64 : r64 bitv = Theory.Bitv.define 64
let r32 : r32 bitv = Theory.Bitv.define 32
let r16 : r16 bitv = Theory.Bitv.define 16
let r8 : r8 bitv = Theory.Bitv.define 8
let bool = Theory.Bool.t
let reg t n = Theory.Var.define t n

let gpr_names =
  [
    (*  0 *)
    "ZERO";
    (*  1 *)
    "AT";
    (*  2 *)
    "V0";
    "V1";
    (*  4 *)
    "A0";
    "A1";
    "A2";
    "A3";
    (*  8 *)
    "T0";
    "T1";
    "T2";
    "T3";
    "T4";
    "T5";
    "T6";
    "T7";
    (* 16 *)
    "S0";
    "S1";
    "S2";
    "S3";
    "S4";
    "S5";
    "S6";
    "S7";
    (* 24 *)
    "T8";
    "T9";
    (* 26 *)
    "K0";
    "K1";
    (* 28 *)
    "GP";
    (* 29 *)
    "SP";
    (* 30 *)
    "FP";
    (* 31 *)
    "RA";
  ]

let untyped = List.map ~f:Theory.Var.forget
let ( @< ) xs ys = untyped xs @ untyped ys

let name ?(release = "") size order =
  let ends = Theory.Endianness.name order in
  let size = if size = 32 then "" else "64" in
  sprintf "mips%s%s%s" size release
  @@
  if Theory.Endianness.(equal eb) order then ""
  else if Theory.Endianness.(equal le) order then "el"
  else KB.Name.unqualified ends

let parent = Theory.Target.declare ~package "mips-family"

let array ?(from = 0) bits pref n =
  List.init n ~f:(fun i -> reg bits (sprintf "%s%d" pref (i + from)))

(* the FPU of the release 6 is 64-bit (Status.FR = 1), also on MIPS32 *)
let define ?(parent = parent) ?(r6 = false) ?nicknames bits endianness =
  let size = Theory.Bitv.size bits in
  let gprs = array bits "R" 32 in
  let fprs =
    if r6 then untyped (array r64 "F" 32) else untyped (array bits "F" 32)
  in
  let mems = Theory.Mem.define bits r8 in
  let data = Theory.Var.define mems "mem" in
  let hilo = [ reg bits "HI"; reg bits "LO" ] in
  (* the hardware register 29, which rdhwr reads, e.g., the thread
     pointer of Linux *)
  let userlocal = reg bits "USERLOCAL" in
  (* the condition codes of the FPU, of FCSR, which c.cond.fmt sets, and
     bc1t, bc1f, movt, and movf read *)
  let fccs =
    List.init 8 ~f:(fun i ->
        Theory.Var.define Theory.Bool.t (sprintf "FCC%d" i))
  in
  let vars =
    untyped gprs @ fprs @ untyped hilo @< [ userlocal ] @< untyped fccs
    @ untyped [ data ]
  in
  let regs = List.map ~f:(fun name -> Theory.Var.forget (reg bits name)) in
  let aliases = List.map gpr_names ~f:(reg bits) in
  (* LLVM names the registers of the 64-bit operations, e.g., V0_64 *)
  let aliases64 =
    if size = 64 then List.map gpr_names ~f:(fun n -> reg bits (n ^ "_64"))
    else []
  in
  let args = if size = 32 then 4 else 8 in
  let iargs = array bits "R" ~from:4 args in
  (* the floating-point arguments and results are the registers of the
     FPU, which are 64-bit on the release 6 *)
  let fpr n = List.nth_exn fprs n in
  let fargs = List.init args ~f:(fun i -> fpr (i + 1)) in
  let aliasing =
    List.map2_exn gprs aliases ~f:(fun r p -> Theory.Alias.(def r [ reg p ]))
    @
    if size = 64 then
      List.map2_exn gprs aliases64 ~f:(fun r p ->
          Theory.Alias.(def r [ reg p ]))
    else []
  in
  let release = if r6 then "r6" else "" in
  Theory.Target.declare ~package
    (name ~release size endianness)
    ~parent ?nicknames ~bits:size ~endianness ~aliasing ~code:data ~data ~vars
    ~regs:
      Theory.Role.Register.
        [
          ([ general; integer ], regs gpr_names);
          ([ general; floating ], fprs);
          ([ special; integer ], untyped hilo);
          ( [ constant; zero; pseudo ],
            regs ([ "ZERO"; "R0" ] @ if size = 64 then [ "ZERO_64" ] else []) );
          ([ function_argument; integer ], untyped iargs);
          ([ function_argument; floating ], fargs);
          ([ function_return; integer ], regs [ "R2" ]);
          ([ function_return; floating ], [ fpr 0 ]);
          ([ stack_pointer ], regs [ "R29" ]);
          ([ frame_pointer ], regs [ "R30" ]);
          ([ link ], regs [ "R31" ]);
          ([ thread ], untyped [ userlocal ]);
          ([ status; floating ], untyped fccs);
          ([ alias ], untyped aliases @ untyped aliases64);
        ]

let mips32bi =
  define r32 Theory.Endianness.bi ~parent ~nicknames:[ "mipsbi"; "mips32bi" ]

let mips32eb =
  define r32 Theory.Endianness.eb ~parent
    ~nicknames:[ "mipseb"; "mips32eb"; "mipsbe"; "mips32be" ]

let mips32le =
  define r32 Theory.Endianness.le ~parent
    ~nicknames:[ "mipsle"; "mipsel"; "mips32le"; "mips32el" ]

let mips64bi = define r64 Theory.Endianness.bi ~parent ~nicknames:[ "mips64bi" ]

let mips64le =
  define r64 Theory.Endianness.le ~parent ~nicknames:[ "misp64le"; "mips64el" ]

let mips64eb =
  define r64 Theory.Endianness.eb ~parent
    ~nicknames:[ "mips64"; "mips64eb"; "mips64be" ]

(* the release 6, whose encodings of the branches differ, e.g., the
   compact branches, which have no delay slots, and whose FPU is 64-bit *)
let mips32r6eb =
  define r32 Theory.Endianness.eb ~r6:true
    ~nicknames:[ "mipsisa32r6"; "mips32r6eb"; "mips32r6be" ]

let mips32r6le =
  define r32 Theory.Endianness.le ~r6:true
    ~nicknames:[ "mipsisa32r6el"; "mips32r6le"; "mips32r6el" ]

let mips64r6eb =
  define r64 Theory.Endianness.eb ~r6:true
    ~nicknames:[ "mipsisa64r6"; "mips64r6eb"; "mips64r6be" ]

let mips64r6le =
  define r64 Theory.Endianness.le ~r6:true
    ~nicknames:[ "mipsisa64r6el"; "mips64r6le"; "mips64r6el" ]

let r6 = [ mips32r6eb; mips32r6le; mips64r6eb; mips64r6le ]
let is_r6 t = List.exists r6 ~f:(fun p -> Theory.Target.belongs p t)

let register_subtargets () =
  List.iter
    ([ mips32eb; mips32le; mips64eb; mips64le ] @ r6)
    ~f:(fun parent ->
      Theory.Target.register parent
        ~abis:Theory.Abi.[ unknown; gnu ]
        ~systems:Theory.System.[ unknown; linux; freebsd; openbsd ]
        ~filetypes:Theory.Filetype.[ unknown; elf ])

let is_mips arch =
  match Option.map ~f:String.lowercase arch with
  | None -> false
  | Some name -> String.is_prefix ~prefix:"mips" name

let is_32bit arch bits =
  match bits with
  | Some 64L -> false
  | Some 32L -> true
  | _ -> (
      match arch with
      | None -> true
      | Some name -> not (String.is_substring ~substring:"64" name))

let enable_loader () =
  KB.Rule.(
    declare ~package "mips-target"
    |> require Image.Spec.slot |> provide Theory.Unit.target
    |> comment "computes a target from the OGRE specification");
  let open KB.Syntax in
  let request_info doc =
    let open Ogre.Syntax in
    let request =
      Ogre.request Image.Scheme.arch >>| Option.map ~f:String.lowercase
      >>= fun arch ->
      Ogre.request Image.Scheme.is_little_endian >>= fun little ->
      Ogre.request Image.Scheme.bits >>= fun bits ->
      Ogre.request Image.Scheme.format >>= fun format ->
      Ogre.request Image.Scheme.subarch >>= fun subarch ->
      Ogre.return (arch, little, bits, format, subarch)
    in
    match Ogre.eval request doc with
    | Error _ -> (None, None, None, None, None)
    | Ok info -> info
  in
  KB.promise Theory.Unit.target @@ fun unit ->
  KB.collect Image.Spec.slot unit >>| request_info
  >>| fun (arch, is_little, bits, format, subarch) ->
  if is_mips arch then
    let abi, filetype =
      match format with
      | Some "elf" -> (Theory.Abi.gnu, Theory.Filetype.elf)
      | _ -> (Theory.Abi.unknown, Theory.Filetype.unknown)
    in
    let r6 = Option.equal String.equal subarch (Some "r6") in
    let parent =
      match (is_32bit arch bits, is_little) with
      | true, Some true -> if r6 then mips32r6le else mips32le
      | true, Some false -> if r6 then mips32r6eb else mips32eb
      | false, Some true -> if r6 then mips64r6le else mips64le
      | false, Some false -> if r6 then mips64r6eb else mips64eb
      | true, None -> mips32bi
      | false, None -> mips64bi
    in
    Theory.Target.select ~strict:true ~parent ~filetype ~abi ()
  else Theory.Target.unknown

let map_mips () =
  KB.Rule.(
    declare ~package "mips-arch"
    |> require Theory.Unit.target |> provide Arch.unit_slot
    |> comment "computes Arch.t from the unit's target");
  let open KB.Syntax in
  KB.promise Arch.unit_slot @@ fun unit ->
  KB.collect Theory.Unit.target unit >>| fun t ->
  if Theory.Target.belongs parent t then
    List.Assoc.find
      Theory.Endianness.
        [
          ((32, eb), `mips);
          ((32, le), `mipsel);
          ((64, eb), `mips64);
          ((64, le), `mips64el);
        ]
      Theory.Target.(bits t, endianness t)
      ~equal:[%equal: int * Theory.Endianness.t]
    |> function
    | None -> `unknown
    | Some r -> r
  else `unknown

module Dis = Disasm_expert.Basic

let llvm_mips32 = Theory.Language.declare ~package "llvm-mips32"
let llvm_mips64 = Theory.Language.declare ~package "llvm-mips64"
let llvm_mips32le = Theory.Language.declare ~package "llvm-mips32le"
let llvm_mips64le = Theory.Language.declare ~package "llvm-mips64le"
let llvm_mips32r6 = Theory.Language.declare ~package "llvm-mips32r6"
let llvm_mips64r6 = Theory.Language.declare ~package "llvm-mips64r6"
let llvm_mips32r6le = Theory.Language.declare ~package "llvm-mips32r6le"
let llvm_mips64r6le = Theory.Language.declare ~package "llvm-mips64r6le"

(* the release 2 instructions, e.g., ROTR, EXT and SEB, are decoded *)
let register encoding triple cpu =
  Dis.register encoding @@ fun _ -> Dis.create ~cpu ~backend:"llvm" triple

let enable_llvm_decoder () =
  let open KB.Syntax in
  register llvm_mips32 "mips" "mips32r2";
  register llvm_mips64 "mips64" "mips64r2";
  register llvm_mips32le "mipsel" "mips32r2";
  register llvm_mips64le "mips64el" "mips64r2";
  register llvm_mips32r6 "mips" "mips32r6";
  register llvm_mips64r6 "mips64" "mips64r6";
  register llvm_mips32r6le "mipsel" "mips32r6";
  register llvm_mips64r6le "mips64el" "mips64r6";
  KB.promise Theory.Label.encoding @@ fun label ->
  Theory.Label.target label >>| fun t ->
  if Theory.Target.belongs parent t then
    let dir = Theory.Target.endianness t in
    match (Theory.Target.bits t, Theory.Endianness.(equal dir le), is_r6 t) with
    | 32, true, false -> llvm_mips32le
    | 64, true, false -> llvm_mips64le
    | 32, _, false -> llvm_mips32
    | 64, _, false -> llvm_mips64
    | 32, true, true -> llvm_mips32r6le
    | 64, true, true -> llvm_mips64r6le
    | 32, _, true -> llvm_mips32r6
    | 64, _, true -> llvm_mips64r6
    | _ -> Theory.Language.unknown
  else Theory.Language.unknown

let pcode = Theory.Language.declare ~package:"bap" "pcode-mips"
let is_big t = Theory.Endianness.(Theory.Target.endianness t = eb)

let register_ghidra_backend () =
  Dis.register pcode @@ fun t ->
  let triple =
    match (Theory.Target.bits t = 32, is_big t) with
    | true, true -> "MIPS:BE:32:default"
    | true, false -> "MIPS:LE:32:default"
    | false, true -> "MIPS:BE:64:default"
    | false, false -> "MIPS:LE:64:default"
  in
  Dis.create ~backend:"ghidra" triple

let enable_pcode_decoder () =
  register_ghidra_backend ();
  let open KB.Syntax in
  KB.promise Theory.Label.encoding @@ fun label ->
  Theory.Label.target label >>| fun t ->
  if Theory.Target.belongs parent t then pcode else Theory.Language.unknown

let load ?(backend = "llvm") () =
  register_subtargets ();
  enable_loader ();
  map_mips ();
  match backend with
  | "llvm" -> enable_llvm_decoder ()
  | "ghidra" -> enable_pcode_decoder ()
  | s ->
      invalid_argf "unknown backend %S, expected %S or %S" s "llvm" "ghidra" ()
