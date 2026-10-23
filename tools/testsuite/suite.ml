open Printf
open OUnit2

(* with BAP_TESTSUITE_EXECUTOR=lifted, the cases run the native code in
   the lifted engine, see Bap_lifted: the commands run the executors of
   the lifted engine, e.g., bap:lifted-executor, with their options,
   rather than the ones of Unicorn, that they name, and with
   BAP_TESTSUITE_EXECUTOR=unicorn, the cases, that name no executor, run
   the ones of Unicorn, rather than the default, bap:lifted-executor, and
   the scripts make the emulators of the engine, see Bap_emu.create *)
let lifted = Sys.getenv_opt "BAP_TESTSUITE_EXECUTOR" = Some "lifted"
let unicorn = Sys.getenv_opt "BAP_TESTSUITE_EXECUTOR" = Some "unicorn"

type data = string

let data dir = dir
let path data name = Filename.concat data name

let files data dir select =
  Sys.readdir (path data dir)
  |> Array.to_list |> List.filter select |> List.sort String.compare
  |> List.map (Filename.concat dir)

type status = Exited of int | Signaled | Timeout | Stopped
type output = { text : string; status : status }

(* a command that a case ran, with the file of its output *)
type call = { command : string list; out : string; result : status }
type tools = { bap : string; mc : string }

type env = {
  dir : string;
  tools : tools;
  mutable calls : call list;
  mutable failed : string list;
}

let dir env = env.dir

(* the native separators, as bap prints them *)
let native name =
  if Sys.win32 then String.map (function '/' -> '\\' | c -> c) name else name

(* the names are relative to the directory of the case *)
let file env name = Filename.concat env.dir (native name)

let write env name data =
  let name = file env name in
  Out_channel.with_open_bin name (fun ch -> output_string ch data);
  name

let read name = In_channel.with_open_bin name In_channel.input_all

(* the output of a command, whose lines end with \r\n on Windows, as the
   programs print in the text mode, and with \n in the patterns *)
let read_output name =
  let text = read name in
  if Sys.win32 then Re.replace_string (Re.compile (Re.str "\r\n")) ~by:"\n" text
  else text

let null = if Sys.win32 then "NUL" else "/dev/null"

(* the cache of the Lisp programs, which the cases share, as their
   entries are of the files, that they validate, and their caches are of
   their own, see Bap_primus_lisp_cache *)
let lisp_cache = ref None

(* the variables that make the commands use the directories of the case *)
let variables env =
  let dir name = file env name in
  [
    ("BAP_CACHE_DIR", dir "cache");
    ("BAP_LOG_DIR", dir "log");
    (* the messages are plain text *)
    ("TERM", "dumb");
  ]
  @ (match !lisp_cache with
    | Some dir -> [ ("BAP_PRIMUS_LISP_CACHE", dir) ]
    | None -> [])
  @
  (* the engine of the scripts, and of the run pass, see [lifted] *)
  if lifted then [ ("BAP_EMU_ENGINE", "lifted") ]
  else if unicorn then
    [
      ("BAP_EMU_ENGINE", "unicorn"); ("BAP_RUN_SYSTEMS", "bap:unicorn-executor");
    ]
  else []

(* the environment of the commands, without the variables of BAP, e.g.,
   the options of the plugins, or BAP_PLUGIN_PATH, which the commands
   would read, so that they are the same in every environment, except
   the ones that the case sets *)
let environment ?(unset = []) vars =
  let names = List.map fst vars @ unset in
  Unix.environment () |> Array.to_list
  |> List.filter (fun var ->
      match String.index_opt var '=' with
      | Some i ->
          let name = String.sub var 0 i in
          not (List.mem name names || String.starts_with ~prefix:"BAP_" name)
      | None -> true)
  |> List.append (List.map (fun (name, value) -> name ^ "=" ^ value) vars)

let regexp str = Re.compile (Re.Perl.re ~opts:[ `Dotall ] str)

let rec waitpid flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid flags pid

let kill pid =
  (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
  ignore (waitpid [] pid)

let run_command ?(timeout = 600.) ?until ?(env = []) ?(unset = []) case prog
    args =
  let variables =
    List.filter (fun (name, _) -> not (List.mem name unset)) (variables case)
  in
  let n = List.length case.calls + 1 in
  let out = file case (sprintf "%d.out" n) in
  let fd =
    Unix.openfile out Unix.[ O_WRONLY; O_CREAT; O_TRUNC; O_CLOEXEC ] 0o644
  and stdin = Unix.openfile null Unix.[ O_RDONLY; O_CLOEXEC ] 0 in
  let pid =
    Fun.protect
      ~finally:(fun () ->
        Unix.close fd;
        Unix.close stdin)
      (fun () ->
        Spawn.spawn ~prog ~argv:(prog :: args)
          ~env:(Spawn.Env.of_list (environment ~unset (variables @ env)))
          ~cwd:(Spawn.Working_dir.Path case.dir) ~stdin ~stdout:fd ~stderr:fd ())
  in
  let until = Option.map regexp until in
  let deadline = Unix.gettimeofday () +. timeout in
  let rec wait delay =
    match waitpid [ Unix.WNOHANG ] pid with
    | 0, _ ->
        let matched =
          match until with
          | Some re -> Re.execp re (read_output out)
          | None -> false
        in
        if matched then (
          kill pid;
          Stopped)
        else if Unix.gettimeofday () > deadline then (
          kill pid;
          Timeout)
        else (
          Thread.delay delay;
          wait (Float.min 0.05 (delay *. 2.)))
    | _, Unix.WEXITED code -> Exited code
    | _, (Unix.WSIGNALED _ | Unix.WSTOPPED _) -> Signaled
  in
  let status = wait 0.001 in
  case.calls <- { command = prog :: args; out; result = status } :: case.calls;
  { text = read_output out; status }

(* [replace ~by pattern s] replaces the occurrences of [pattern] in [s] *)
let replace ~by pattern s =
  let n = String.length pattern and b = Buffer.create (String.length s) in
  let rec loop i =
    if i > String.length s - n then
      Buffer.add_string b (String.sub s i (String.length s - i))
    else if String.sub s i n = pattern then (
      Buffer.add_string b by;
      loop (i + n))
    else (
      Buffer.add_char b s.[i];
      loop (i + 1))
  in
  loop 0;
  Buffer.contents b

(* the arguments of bap, whose executors of Unicorn, and their options,
   are of the lifted engine, see [lifted], but the other arguments, e.g.,
   the paths of the files of the cases, whose names may have them *)
let executor args =
  let systems arg =
    List.fold_left
      (fun arg (unicorn, lifted) -> replace ~by:lifted unicorn arg)
      arg
      [
        ("bap:unicorn-executor", "bap:lifted-executor");
        ("bap:terminating-unicorn-executor", "bap:terminating-lifted-executor");
        ("bap:unicorn-binary-executor", "bap:lifted-binary-executor");
      ]
  in
  let option = "--primus-unicorn-" in
  if not lifted then args
  else
    List.map
      (fun arg ->
        if String.starts_with ~prefix:"--run-systems=" arg then systems arg
        else if String.starts_with ~prefix:option arg then
          "--primus-lifted-"
          ^ String.sub arg (String.length option)
              (String.length arg - String.length option)
        else if String.starts_with ~prefix:"bap:" arg then systems arg
        else arg)
      args

let bap ?timeout ?until ?env ?unset case args =
  run_command ?timeout ?until ?env ?unset case case.tools.bap (executor args)

let mc case args = run_command case case.tools.mc args
let check env name ok = if not ok then env.failed <- name :: env.failed
let matches output re = Re.execp (regexp re) output.text
let has env name output re = check env name (matches output re)
let lacks env name output re = check env name (not (matches output re))

(* the root of the source tree, which [main] finds *)
let root = ref (Sys.getcwd ())
let source name = Filename.concat !root name

(* the fixed files of the cases, e.g., the scripts, the Lisp files, and
   the inputs of the programs, which are in tools/testsuite/inputs, so
   that the cases are the same in every environment *)
let input name = native (source ("tools/testsuite/inputs/" ^ name))

(* the golden files may have \r\n, when git converts the ends of lines *)
let unix_lines text = String.concat "" (String.split_on_char '\r' text)

let golden env name text =
  let expected = source ("tools/testsuite/golden/" ^ name) in
  if Sys.getenv_opt "BAP_TESTSUITE_PROMOTE" <> None then (
    let rec mkdir dir =
      if not (Sys.file_exists dir) then (
        mkdir (Filename.dirname dir);
        (* the cases run in parallel and make the same directories *)
        try Sys.mkdir dir 0o755
        with Sys_error _ when Sys.is_directory dir -> ())
    in
    mkdir (Filename.dirname expected);
    Out_channel.with_open_bin expected (fun ch -> output_string ch text))
  else
    let actual = write env (Filename.basename name) text in
    check env
      (sprintf "%s is the same as %s" actual expected)
      (Sys.file_exists expected && unix_lines (read expected) = text)

let find str sub start =
  let n = String.length sub in
  let last = String.length str - n in
  let rec loop i =
    if i > last then None
    else if String.sub str i n = sub then Some i
    else loop (i + 1)
  in
  loop start

let contains env name output str =
  check env name (Option.is_some (find output.text str 0))

let count output str =
  let rec loop n start =
    match find output.text str start with
    | Some i -> loop (n + 1) (i + String.length str)
    | None -> n
  in
  if str = "" then 0 else loop 0 0

let sequence env output checks =
  let rec loop pos = function
    | [] -> ()
    | (name, re) :: checks -> (
        let re = Re.compile (Re.shortest (Re.Perl.re ~opts:[ `Dotall ] re)) in
        match Re.exec_opt ~pos re output.text with
        | Some group ->
            check env name true;
            loop (snd (Re.Group.offset group 0)) checks
        | None -> check env name false)
  in
  loop 0 checks

type case = { name : string; serial : bool; slow : bool; run : env -> unit }

let case ?(serial = false) ?(slow = false) name run =
  { name; serial; slow; run }

let rec remove name =
  match (Unix.lstat name).st_kind with
  | Unix.S_DIR ->
      Array.iter
        (fun entry -> remove (Filename.concat name entry))
        (Sys.readdir name);
      Unix.rmdir name
  | _ ->
      (* Windows doesn't remove the read-only files, e.g., the inputs,
         that the cases make read-only *)
      if Sys.win32 then Unix.chmod name 0o644;
      Sys.remove name
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> ()

let mkdir name = if not (Sys.file_exists name) then Sys.mkdir name 0o755

(* the name of the directory of the [n]th case *)
let dirname n name =
  String.map
    (function
      | ('a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '.' | '-' | '_') as c -> c
      | _ -> '_')
    name
  |> sprintf "%03d-%s" n

(* the cases share the installation of bap, which the serial cases change,
   so a serial case waits for the others to finish, and the others wait for
   it, while it runs or waits *)
module Installation = struct
  let lock = Mutex.create ()
  let changed = Condition.create ()
  let readers = ref 0
  let writing = ref false
  let writers = ref 0

  let finally f () =
    Mutex.protect lock f;
    Condition.broadcast changed

  let shared run =
    Mutex.protect lock (fun () ->
        while !writing || !writers > 0 do
          Condition.wait changed lock
        done;
        incr readers);
    Fun.protect ~finally:(finally (fun () -> decr readers)) run

  let exclusive run =
    Mutex.protect lock (fun () ->
        incr writers;
        while !writing || !readers > 0 do
          Condition.wait changed lock
        done;
        decr writers;
        writing := true);
    Fun.protect ~finally:(finally (fun () -> writing := false)) run
end

let print_status = function
  | Exited n -> sprintf "exited with %d" n
  | Signaled -> "was killed by a signal"
  | Timeout -> "ran out of time"
  | Stopped -> "was stopped, as its output matched"

let report env error =
  List.map (sprintf "failed: %s") (List.rev env.failed)
  @ Option.to_list (Option.map (sprintf "raised: %s") error)
  @ List.map
      (fun { command; out; result } ->
        sprintf "ran: %s\n  %s, the output is in %s"
          (String.concat " " command)
          (print_status result) out)
      (List.rev env.calls)
  |> String.concat "\n"

let bap_prog = Conf.make_string "bap" "bap" "PROG the bap to test"
let mc_prog = Conf.make_string "mc" "bap-mc" "PROG the bap-mc to test"

let absolute name =
  if Filename.is_relative name then Filename.concat (Sys.getcwd ()) name
  else name

(* the program [name] in the PATH *)
let locate name =
  let name = if Sys.win32 then name ^ ".exe" else name in
  let sep = if Sys.win32 then ';' else ':' in
  Option.value (Sys.getenv_opt "PATH") ~default:""
  |> String.split_on_char sep
  |> List.map (fun dir -> Filename.concat dir name)
  |> List.find_opt Sys.file_exists
  |> Option.value ~default:name

let resolve prog =
  if Filename.is_implicit prog then locate prog else absolute prog

(* the time that each case took *)
let times = ref []
let times_lock = Mutex.create ()

(* runs the [n]th case in its own directory, which is removed if the case
   passes *)
let run_case ~work n case ctxt =
  let tools = { bap = resolve (bap_prog ctxt); mc = resolve (mc_prog ctxt) } in
  let dir = Filename.concat work (dirname n case.name) in
  mkdir dir;
  List.iter
    (fun sub -> mkdir (Filename.concat dir sub))
    [ "cache"; "config"; "log" ];
  let env = { dir; tools; calls = []; failed = [] } in
  let start = Unix.gettimeofday () in
  let error =
    (if case.serial then Installation.exclusive else Installation.shared)
      (fun () ->
        match case.run env with
        | () -> None
        | exception exn -> Some (Printexc.to_string exn))
  in
  let time = Unix.gettimeofday () -. start in
  Mutex.protect times_lock (fun () -> times := (time, case.name) :: !times);
  if env.failed = [] && error = None then remove dir
  else assert_failure (report env error)

(* the tests of the numbered cases, whose names are split at the slashes:
   the cases that share the first part are the tests of the group of this
   label, in their order; the labels have no colons, which separate the
   labels of a path *)
let rec tree ~work cases =
  let labels =
    List.fold_left
      (fun labels (_, parts, _) ->
        match parts with
        | label :: _ when not (List.mem label labels) -> label :: labels
        | _ -> labels)
      [] cases
    |> List.rev
  in
  List.map
    (fun label ->
      let members =
        List.filter_map
          (fun (n, parts, case) ->
            match parts with
            | first :: rest when first = label -> Some (n, rest, case)
            | _ -> None)
          cases
      in
      let label = String.map (function ':' -> '.' | c -> c) label in
      match members with
      | [ (n, [], case) ] -> label >:: run_case ~work n case
      | members when List.exists (fun (_, parts, _) -> parts = []) members ->
          ksprintf failwith "the case %s is a group of cases" label
      | members -> label >::: tree ~work members)
    labels

(* the root of the source tree, which contains the build directory *)
let rec source_root dir =
  let parent = Filename.dirname dir in
  if Filename.basename dir = "_build" then Some parent
  else if parent = dir then None
  else source_root parent

let selected filters case =
  filters = []
  || List.exists
       (fun filter -> Option.is_some (find case.name filter 0))
       filters

let words var =
  Option.fold ~none:[] (Sys.getenv_opt var) ~some:(fun var ->
      String.split_on_char ' ' var |> List.filter (( <> ) ""))

let set_default var value =
  if Sys.getenv_opt var = None then Unix.putenv var value

let main tests =
  (* dune tells the source root to the actions, whatever the build
     directory is, e.g., with --build-dir, otherwise it is the parent of
     _build, when the runner runs in it *)
  (root :=
     match Sys.getenv_opt "DUNE_SOURCEROOT" with
     | Some dir when dir <> "" -> dir
     | _ -> Option.value (source_root (Sys.getcwd ())) ~default:(Sys.getcwd ()));
  let root = !root in
  (* the binaries of the testsuite, which are in the repository *)
  let dir = Filename.concat root "testsuite" in
  let keep = Sys.getenv_opt "BAP_TESTSUITE_WORK" <> None in
  let work =
    match Sys.getenv_opt "BAP_TESTSUITE_WORK" with
    | Some dir ->
        mkdir (absolute dir);
        absolute dir
    | None -> Filename.temp_dir "bap-testsuite" ""
  in
  lisp_cache := Some (Filename.concat work "primus-lisp");
  let cases =
    List.concat_map (fun test -> test dir) tests
    |> List.filter (selected (words "BAP_TESTS"))
  in
  (* the slow cases start first, the serial ones last *)
  let first, rest = List.partition (fun c -> c.slow) cases in
  let rest, last = List.partition (fun c -> not c.serial) rest in
  let cases =
    List.mapi
      (fun n case -> (n, String.split_on_char '/' case.name, case))
      (first @ rest @ last)
  in
  at_exit (fun () ->
      if !times <> [] then (
        printf "the slowest cases:\n";
        List.sort (fun x y -> compare y x) !times
        |> List.filteri (fun i _ -> i < 5)
        |> List.iter (fun (time, name) -> printf "  %5.0f s %s\n" time name));
      Option.iter remove !lisp_cache;
      if Sys.readdir work = [||] then (if not keep then Unix.rmdir work)
      else printf "the outputs of the failed cases are kept in %s\n" work);
  (* the cases wait for their commands, so they run in threads *)
  OUnitThreads.init ();
  set_default "OUNIT_RUNNER" "threads";
  set_default "OUNIT_SHARDS" "16";
  run_test_tt_main ("testsuite" >::: tree ~work cases)
