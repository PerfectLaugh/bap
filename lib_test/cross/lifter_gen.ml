(* Generates the OCaml tests of the lifters from the specifications of the
   instructions, with the expected values computed by executing them.

   usage:
     lifter_gen.exe -runner DIR CONFIG SPEC SUITE
       prints the suite SUITE of the tests of the instructions in SPEC, or
       an empty suite if they can't be generated on this host, e.g.,
       without the compilers or QEMU, see the toolchains below
     lifter_gen.exe ndk-regenerate DIR
       regenerates the tests of DIR/ndk.sexp, whose instructions are
       assembled with the Android NDK, see [ndk_regenerate]

   CONFIG is an s-expression file, whose fields are
     (include FILE)       the fields of FILE, relative to CONFIG, which the
                          later fields override
     (toolchain native)   the instructions are assembled with GNU as and
                          executed natively by the runner, built with gcc
                          from DIR/runner.c and DIR/tramp<bits>.S
     (toolchain cross)    the instructions are assembled with llvm-mc and
                          executed under QEMU user mode by the runner, built
                          with clang and lld from DIR/runner.c and
                          DIR/arch-<arch>.S
     (bits N)             the native word size, 32 or 64
     (sp NAME)            the stack pointer, set to 0x208000, unless it is
                          an input
     (rename_xmm true)    the XMM registers in the outputs are the YMM ones
     (cc_target T) (cc_flags (F ...)) (arch A) (qemu Q) (qemu_cpu C)
     (mc_triple T) (mc_flags (F ...))
                          the cross toolchain, see [build_cross_runner]
     (prelude S)          the assembler directives before an instruction
     (mode M) (helpers H) the mode of the tests in the module of helpers
     (drop (L ...))       the outputs that are not compared
     (sets (NAME (V ...)) ...)
                          the sets of values, merged with the included ones
     (kinds ((PATTERN ...) SET) ...)
                          the sets of the registers whose names match the
                          glob patterns, the others are general purpose
     (gpr (V ...)) (gpr2 (V ...))
                          the values of the general purpose registers, when
                          there are fewer or more than one of them in the
                          inputs

   Each line of SPEC is "ASM | INPUTS | OUTPUTS" or "ASM | INPUTS | OUTPUTS |
   LANDINGS", see the runners for the locations and the landings. An input
   is NAME=VALUE, a fixed value, NAME, which takes each value of the set of
   its kind, or NAME@SET, which takes each value of SET. The vectors are all
   the combinations of the values of the inputs, the vectors where the
   instruction faults are dropped. Lines starting with # are section
   comments.

   The generator runs the tools directly, without a shell. *)

open Printf
module Sexp = Sexplib.Sexp

exception Failed of string

let fail fmt = ksprintf (fun msg -> raise (Failed msg)) fmt

(* {1 Processes and files} *)

let read_file file = In_channel.with_open_bin file In_channel.input_all
let write_file file data = Out_channel.with_open_bin file (fun ch -> output_string ch data)

let rec remove path =
  if Sys.file_exists path then
    if Sys.is_directory path then begin
      Array.iter (fun name -> remove (Filename.concat path name)) (Sys.readdir path);
      Sys.rmdir path
    end
    else Sys.remove path

(* runs [prog args] with the files as its standard channels, and returns
   its exit code *)
let exec ?stdin ?stdout ?stderr prog args =
  let openfile mode default = function
    | None -> (default, false)
    | Some file -> (Unix.openfile file mode 0o644, true)
  in
  let fin, cin = openfile [ Unix.O_RDONLY ] Unix.stdin stdin in
  let fout, cout =
    openfile [ Unix.O_WRONLY; O_CREAT; O_TRUNC ] Unix.stdout stdout
  in
  let ferr, cerr =
    openfile [ Unix.O_WRONLY; O_CREAT; O_TRUNC ] Unix.stderr stderr
  in
  let close () =
    List.iter
      (fun (fd, opened) -> if opened then Unix.close fd)
      [ (fin, cin); (fout, cout); (ferr, cerr) ]
  in
  match
    Unix.create_process prog (Array.of_list (prog :: args)) fin fout ferr
  with
  | exception Unix.Unix_error (err, _, _) ->
      close ();
      fail "%s: %s" prog (Unix.error_message err)
  | pid -> (
      close ();
      match snd (Unix.waitpid [] pid) with
      | Unix.WEXITED code -> code
      | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> 128)

(* runs the command and fails with its error output, if it fails *)
let exec_exn work what prog args =
  let err = Filename.concat work "err" in
  if exec ~stderr:err prog args <> 0 then
    fail "%s failed: %s" what (String.trim (read_file err))

let hex_of_file file =
  let data = read_file file in
  String.to_seq data
  |> Seq.map (fun c -> sprintf "%02x" (Char.code c))
  |> List.of_seq |> String.concat " "

(* {1 Strings} *)

let words s =
  String.split_on_char ' ' (String.map (function '\t' -> ' ' | c -> c) s)
  |> List.filter (( <> ) "")

let trim_spaces s =
  let n = String.length s in
  let i = ref 0 and j = ref n in
  while !i < n && s.[!i] = ' ' do incr i done;
  while !j > !i && s.[!j - 1] = ' ' do decr j done;
  String.sub s !i (!j - !i)

let starts_with ~prefix s = String.starts_with ~prefix s

let contains ~sub s =
  let n = String.length sub and m = String.length s in
  let rec at i = i + n <= m && (String.sub s i n = sub || at (i + 1)) in
  at 0

(* splits the line on the bars, the last field is the rest of the line *)
let fields n line =
  let rec split k s =
    if k = 1 then [ s ]
    else
      match String.index_opt s '|' with
      | None -> [ s ]
      | Some i ->
          String.sub s 0 i
          :: split (k - 1) (String.sub s (i + 1) (String.length s - i - 1))
  in
  let xs = split n line in
  xs @ List.init (n - List.length xs) (fun _ -> "")

let lines_of_file file =
  String.split_on_char '\n' (read_file file)
  |> List.map (fun l ->
      if String.ends_with ~suffix:"\r" l then String.sub l 0 (String.length l - 1)
      else l)

(* the glob patterns of the shell: *, ?, and [a-z] *)
let rec glob_match pat s i j =
  let n = String.length pat and m = String.length s in
  if i = n then j = m
  else
    match pat.[i] with
    | '*' -> glob_match pat s (i + 1) j || (j < m && glob_match pat s i (j + 1))
    | '?' -> j < m && glob_match pat s (i + 1) (j + 1)
    | '[' -> (
        match String.index_from_opt pat i ']' with
        | Some k when j < m ->
            let cls = String.sub pat (i + 1) (k - i - 1) in
            let rec member p =
              p < String.length cls
              && (if p + 2 < String.length cls && cls.[p + 1] = '-' then
                    (cls.[p] <= s.[j] && s.[j] <= cls.[p + 2]) || member (p + 3)
                  else cls.[p] = s.[j] || member (p + 1))
            in
            member 0 && glob_match pat s (k + 1) (j + 1)
        | _ -> j < m && s.[j] = '[' && glob_match pat s (i + 1) (j + 1))
    | c -> j < m && s.[j] = c && glob_match pat s (i + 1) (j + 1)

let glob pat s = glob_match pat s 0 0

(* {1 Configurations} *)

type toolchain = Native | Cross

type config = {
  toolchain : toolchain;
  bits : int;
  sp : string option;
  rename_xmm : bool;
  cc_target : string;
  cc_flags : string list;
  arch : string;
  qemu : string;
  qemu_cpu : string option;
  mc_triple : string;
  mc_flags : string list;
  prelude : string;
  mode : string;
  helpers : string;
  drop : string list;
  sets : (string * string list) list;
  kinds : (string list * string) list;
  gpr : string list;
  gpr2 : string list;
}

let atom = function
  | Sexp.Atom s -> s
  | s -> fail "expected an atom, got %s" (Sexp.to_string s)

let atoms = function Sexp.Atom s -> [ s ] | Sexp.List xs -> List.map atom xs

(* the fields of the file, with the included ones first *)
let rec load_fields file =
  Sexp.load_sexps file
  |> List.concat_map (function
    | Sexp.List [ Sexp.Atom "include"; Sexp.Atom name ] ->
        load_fields (Filename.concat (Filename.dirname file) name)
    | Sexp.List (Sexp.Atom key :: values) -> [ (key, values) ]
    | s -> fail "%s: bad field %s" file (Sexp.to_string s))

let load_config file =
  let fields = load_fields file in
  let last key =
    List.fold_left
      (fun acc (k, v) -> if k = key then Some v else acc)
      None fields
  in
  let get key f default =
    match last key with
    | None -> default
    | Some [ v ] -> f v
    | Some vs -> fail "%s: %s expects one value, got %d" file key (List.length vs)
  in
  let string key = get key atom "" in
  let list key = get key atoms [] in
  let sets =
    List.fold_left
      (fun acc (k, values) ->
        if k <> "sets" then acc
        else
          List.fold_left
            (fun acc -> function
              | Sexp.List [ Sexp.Atom name; vs ] ->
                  (name, atoms vs) :: List.remove_assoc name acc
              | s -> fail "%s: bad set %s" file (Sexp.to_string s))
            acc values)
      [] fields
  in
  let kinds =
    match last "kinds" with
    | None -> []
    | Some ks ->
        List.map
          (function
            | Sexp.List [ pats; Sexp.Atom set ] -> (atoms pats, set)
            | s -> fail "%s: bad kind %s" file (Sexp.to_string s))
          ks
  in
  {
    toolchain =
      get "toolchain"
        (function
          | Sexp.Atom "native" -> Native
          | Sexp.Atom "cross" -> Cross
          | s -> fail "%s: unknown toolchain %s" file (Sexp.to_string s))
        Cross;
    bits = get "bits" (fun v -> int_of_string (atom v)) 64;
    sp = get "sp" (fun v -> Some (atom v)) None;
    rename_xmm = get "rename_xmm" (fun v -> bool_of_string (atom v)) false;
    cc_target = string "cc_target";
    cc_flags = list "cc_flags";
    arch = string "arch";
    qemu = string "qemu";
    qemu_cpu = get "qemu_cpu" (fun v -> Some (atom v)) None;
    mc_triple = string "mc_triple";
    mc_flags = list "mc_flags";
    prelude = string "prelude";
    mode = string "mode";
    helpers = string "helpers";
    drop = list "drop";
    sets;
    kinds;
    gpr = list "gpr";
    gpr2 = list "gpr2";
  }

let kind cfg name =
  match
    List.find_opt
      (fun (pats, _) -> List.exists (fun p -> glob p name) pats)
      cfg.kinds
  with
  | Some (_, set) -> set
  | None -> "gpr"

(* {1 Vectors} *)

type values = Gpr | Values of string list

(* the input lines of the combinations of the values of the inputs *)
let expand cfg inputs =
  let fixed, vars, nvar =
    List.fold_left
      (fun (fixed, vars, nvar) t ->
        if String.contains t '=' then (fixed ^ " " ^ t, vars, nvar)
        else
          match String.rindex_opt t '@' with
          | Some i -> (
              let name = String.sub t 0 i in
              let set = String.sub t (i + 1) (String.length t - i - 1) in
              match List.assoc_opt set cfg.sets with
              | Some (_ :: _ as vs) -> (fixed, (name, Values vs) :: vars, nvar)
              | _ -> (fixed, (t, Gpr) :: vars, nvar + 1))
          | None -> (
              match kind cfg t with
              | "gpr" -> (fixed, (t, Gpr) :: vars, nvar + 1)
              | k ->
                  let vs = Option.value ~default:[] (List.assoc_opt k cfg.sets) in
                  (fixed, (t, Values vs) :: vars, nvar)))
      ("", [], 0) (words inputs)
  in
  let gpr = if nvar >= 2 then cfg.gpr2 else cfg.gpr in
  let vars =
    List.rev_map
      (fun (name, vs) -> (name, match vs with Gpr -> gpr | Values vs -> vs))
      vars
  in
  let rec combine acc = function
    | [] -> [ acc ]
    | (name, vs) :: rest ->
        List.concat_map (fun v -> combine (sprintf "%s %s=%s" acc name v) rest) vs
  in
  combine fixed vars

(* the outputs of x86 name the YMM registers, whose low halves are XMM *)
let rename_xmm line =
  let b = Buffer.create (String.length line) in
  let n = String.length line in
  let is_word c =
    match c with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false
  in
  let rec loop i =
    if i >= n then ()
    else if
      i + 3 < n
      && String.sub line i 3 = "XMM"
      && (i = 0 || not (is_word line.[i - 1]))
    then begin
      let j = ref (i + 3) in
      while !j < n && line.[!j] >= '0' && line.[!j] <= '9' do incr j done;
      if !j > i + 3 && !j < n && line.[!j] = '=' then begin
        Buffer.add_string b "YMM";
        Buffer.add_string b (String.sub line (i + 3) (!j - i - 3));
        loop !j
      end
      else begin
        Buffer.add_char b line.[i];
        loop (i + 1)
      end
    end
    else begin
      Buffer.add_char b line.[i];
      loop (i + 1)
    end
  in
  loop 0;
  Buffer.contents b

(* {1 Toolchains} *)

let build_native_runner cfg ~runner ~work =
  let run = Filename.concat work "run" in
  let src name = Filename.concat runner name in
  let args =
    if cfg.bits = 64 then
      [ "-O2"; "-static"; "-o"; run; src "runner.c"; src "tramp64.S" ]
    else
      [ "-m32"; "-O2"; "-no-pie"; "-o"; run; src "runner.c"; src "tramp32.S" ]
  in
  exec_exn work "building the runner" "gcc" args;
  run

let build_cross_runner cfg ~runner ~work =
  let run = Filename.concat work "run" in
  exec_exn work "building the runner" "clang"
    ([
       "--target=" ^ cfg.cc_target;
       "-ffreestanding";
       "-nostdlib";
       "-static";
       "-fno-pic";
       "-O2";
     ]
    @ cfg.cc_flags
    @ [
        sprintf "-DARCH_HEADER=\"arch-%s.h\"" cfg.arch;
        "-I" ^ runner;
        Filename.concat runner "runner.c";
        Filename.concat runner (sprintf "arch-%s.S" cfg.arch);
        "-fuse-ld=lld";
        "-Wl,--image-base=0x1000000";
        "-o";
        run;
      ]);
  run

(* the bytes of the instruction *)
let assemble cfg ~work asm =
  let src = Filename.concat work "a.s"
  and obj = Filename.concat work "a.o"
  and bin = Filename.concat work "a.bin" in
  let what = sprintf "assembling '%s'" asm in
  begin match cfg.toolchain with
  | Native ->
      write_file src (sprintf ".intel_syntax noprefix\n.text\n%s\n" asm);
      exec_exn work what "as" [ sprintf "--%d" cfg.bits; src; "-o"; obj ];
      exec_exn work what "objcopy"
        [ "-O"; "binary"; "--only-section=.text"; obj; bin ]
  | Cross ->
      write_file src (sprintf "%s\n.text\n%s\n" cfg.prelude asm);
      exec_exn work what "llvm-mc"
        ([ "--triple=" ^ cfg.mc_triple ]
        @ cfg.mc_flags
        @ [ "-filetype=obj"; src; "-o"; obj ]);
      exec_exn work what "llvm-objcopy"
        [ "-O"; "binary"; "--only-section=.text"; obj; bin ]
  end;
  hex_of_file bin

(* the outputs of the runner for the input lines *)
let execute cfg ~run ~work ~asm input =
  let inp = Filename.concat work "in"
  and out = Filename.concat work "out"
  and err = Filename.concat work "err" in
  write_file inp (String.concat "" (List.map (fun l -> l ^ "\n") input));
  let prog, args =
    match cfg.toolchain with
    | Native -> (run, [])
    | Cross ->
        ( cfg.qemu,
          (match cfg.qemu_cpu with Some c -> [ "-cpu"; c ] | None -> [])
          @ [ run ] )
  in
  if exec ~stdin:inp ~stdout:out ~stderr:err prog args <> 0 then
    fail "running '%s' failed: %s" asm
      (String.concat "\n"
         (List.filter
            (fun l -> not (contains ~sub:"uncaught target signal" l))
            (lines_of_file err)));
  lines_of_file out |> List.filter (( <> ) "")

(* {1 Suites} *)

let generate cfg ~runner ~spec ~suite =
  let work = Filename.temp_dir "bap-lifter-gen" "" in
  Fun.protect ~finally:(fun () -> remove work) @@ fun () ->
  let run =
    match cfg.toolchain with
    | Native -> build_native_runner cfg ~runner ~work
    | Cross -> build_cross_runner cfg ~runner ~work
  in
  let b = Buffer.create 4096 in
  let pr fmt = bprintf b fmt in
  pr "(* generated from gen/%s by lib_test/cross/lifter_gen.ml *)\n\n"
    (Filename.basename spec);
  pr "let mode = %s.%s\n\n" cfg.helpers cfg.mode;
  pr "let suite =\n  OUnit2.( >::: ) \"%s\"\n    [\n" suite;
  List.iter
    (fun line ->
      match fields 4 line with
      | [ asm; inputs; outputs; landings ] ->
          let asm = trim_spaces asm in
          if asm = "" then ()
          else if starts_with ~prefix:"#" asm then
            let comment =
              if starts_with ~prefix:"# " asm then
                String.sub asm 2 (String.length asm - 2)
              else asm
            in
            pr "      (* %s *)\n" comment
          else begin
            let code = assemble cfg ~work asm in
            let outputs =
              if cfg.drop = [] then outputs
              else
                " "
                ^ String.concat " "
                    (List.filter
                       (fun o -> not (List.mem o cfg.drop))
                       (words outputs))
                ^ " "
            in
            let inputs =
              match cfg.sp with
              | Some sp
                when not
                       (List.exists
                          (fun t ->
                            t = sp
                            || starts_with ~prefix:(sp ^ "=") t
                            || starts_with ~prefix:(sp ^ "@") t)
                          (words inputs)) ->
                  sprintf "%s=0x208000 %s" sp inputs
              | _ -> inputs
            in
            let input =
              List.map
                (fun vector ->
                  sprintf "%s |%s | %s | %s" code vector outputs landings)
                (expand cfg inputs)
            in
            match
              List.filter (( <> ) "FAULT") (execute cfg ~run ~work ~asm input)
            with
            | [] ->
                (* the instructions that fault for all inputs, e.g., those
                   that the processor does not implement, are skipped *)
                eprintf "warning: skipping '%s', it faults for all inputs\n%!"
                  asm
            | vectors ->
                let vectors =
                  if cfg.rename_xmm then List.map rename_xmm vectors
                  else vectors
                in
                pr "      Lifter_test.case mode \"%s\" \"%s\"\n" asm code;
                pr "        (Lifter_test.vectors\n           {|\n";
                List.iter (pr "%s\n") vectors;
                pr "|});\n"
          end
      | _ -> assert false)
    (lines_of_file spec);
  pr "    ]\n";
  Buffer.contents b

(* {1 The tests assembled with the Android NDK}

   The specifications in DIR/ndk.sexp, ((SPEC MODULE) ...), are
   regenerated into DIR/../test_SPEC.ml, which are formatted with
   ocamlformat. NDK_BIN is the toolchains/llvm/prebuilt/<host>/bin
   directory of the NDK. Each line of DIR/SPEC.spec is
   "MODE | ASM | INIT | EXPECT", where MODE is A64, A32, or T32, and INIT
   and EXPECT are space-separated NAME=VALUE pairs. *)

let generate_ndk ~ndk ~spec ~name =
  let work = Filename.temp_dir "bap-lifter-gen" "" in
  Fun.protect ~finally:(fun () -> remove work) @@ fun () ->
  let tool name = Filename.concat ndk name in
  let b = Buffer.create 4096 in
  let pr fmt = bprintf b fmt in
  let pairs s =
    String.concat ""
      (List.map
         (fun p ->
           match String.index_opt p '=' with
           | Some i ->
               sprintf "(\"%s\", \"%s\"); " (String.sub p 0 i)
                 (String.sub p (i + 1) (String.length p - i - 1))
           | None -> sprintf "(\"%s\", \"%s\"); " p p)
         (words s))
  in
  pr "(* generated by lib_test/cross/lifter_gen.ml from gen/%s, do not edit *)\n\n"
    (Filename.basename spec);
  pr "open Arm_tests_helpers\n\nlet suite =\n  OUnit2.( >::: ) \"%s\"\n    [\n"
    name;
  List.iter
    (fun line ->
      match fields 4 line with
      | [ mode; asm; init; expect ] ->
          let mode = String.concat " " (words mode) and asm = trim_spaces asm in
          if mode = "" then ()
          else if starts_with ~prefix:"#" mode then
            pr "      (* %s *)\n"
              (if starts_with ~prefix:"# " mode then
                 String.sub mode 2 (String.length mode - 2)
               else mode)
          else begin
            let target, flags, source =
              match mode with
              | "A64" -> ("aarch64-linux-android35", [], sprintf ".text\n%s\n" asm)
              | "A32" ->
                  ( "armv7a-linux-androideabi21",
                    [ "-marm"; "-mcpu=cortex-a15"; "-mfpu=vfpv4" ],
                    sprintf ".syntax unified\n.fpu vfpv4\n.arm\n.text\n%s\n" asm )
              | "T32" ->
                  ( "armv7a-linux-androideabi21",
                    [ "-mthumb"; "-mcpu=cortex-a15"; "-mfpu=vfpv4" ],
                    sprintf ".syntax unified\n.fpu vfpv4\n.thumb\n.text\n%s\n" asm
                  )
              | m -> fail "unknown mode %s" m
            in
            let src = Filename.concat work "a.s"
            and obj = Filename.concat work "a.o"
            and bin = Filename.concat work "a.bin" in
            write_file src source;
            let what = sprintf "assembling '%s'" asm in
            exec_exn work what (tool "clang")
              ([ "--target=" ^ target ] @ flags @ [ "-c"; src; "-o"; obj ]);
            exec_exn work what (tool "llvm-objcopy")
              [ "-O"; "binary"; "--only-section=.text"; obj; bin ];
            pr "      case %s \"%s\" \"%s\"\n" mode asm (hex_of_file bin);
            pr "        ~init:[ %s]\n" (pairs init);
            pr "        ~expect:[ %s];\n" (pairs expect)
          end
      | _ -> assert false)
    (lines_of_file spec);
  pr "    ]\n";
  Buffer.contents b

let ndk_regenerate dir =
  let ndk =
    match Sys.getenv_opt "NDK_BIN" with
    | Some d -> d
    | None -> fail "set NDK_BIN to the bin directory of the NDK toolchain"
  in
  List.iter
    (function
      | Sexp.List [ Sexp.Atom spec; Sexp.Atom name ] ->
          let out =
            Filename.concat (Filename.dirname dir) (sprintf "test_%s.ml" spec)
          in
          write_file out
            (generate_ndk ~ndk
               ~spec:(Filename.concat dir (spec ^ ".spec"))
               ~name);
          if exec "ocamlformat" [ "-i"; out ] <> 0 then
            fail "ocamlformat failed on %s" out
      | s -> fail "ndk.sexp: bad entry %s" (Sexp.to_string s))
    (Sexp.load_sexps (Filename.concat dir "ndk.sexp"))

let () =
  match Array.to_list Sys.argv with
  | [ _; "-expand"; config; inputs ] ->
      (* prints the vectors of the inputs, e.g., to check a specification *)
      List.iter print_endline (expand (load_config config) inputs)
  | [ _; "ndk-regenerate"; dir ] -> (
      try ndk_regenerate dir
      with Failed msg ->
        prerr_endline ("error: " ^ msg);
        exit 1)
  | [ _; "-runner"; runner; config; spec; suite ] -> (
      (* a bad configuration is an error, not a missing tool *)
      let cfg = load_config config in
      match generate cfg ~runner ~spec ~suite with
      | tests -> print_string tests
      | exception (Failed msg | Sys_error msg) ->
          eprintf "%s\nwarning: the %s tests are not generated, the suite is empty\n%!"
            msg suite;
          printf "let suite = OUnit2.( >::: ) \"%s\" []\n" suite)
  | _ ->
      prerr_endline
        "usage: lifter_gen.exe -runner DIR CONFIG SPEC SUITE\n\
        \       lifter_gen.exe ndk-regenerate DIR";
      exit 2
