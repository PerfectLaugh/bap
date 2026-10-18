open Printf

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
  mutable passed : int;
  mutable failed : string list;
}

let dir env = env.dir
let file env name = Filename.concat env.dir name

let write env name data =
  let name = file env name in
  Out_channel.with_open_bin name (fun ch -> output_string ch data);
  name

let read name = In_channel.with_open_bin name In_channel.input_all
let null = if Sys.win32 then "NUL" else "/dev/null"

(* the variables that make the commands use the directories of the case *)
let variables env =
  let dir name = file env name in
  [
    ("HOME", env.dir);
    ("XDG_CACHE_HOME", dir "cache");
    ("XDG_CONFIG_HOME", dir "config");
    ("XDG_STATE_HOME", dir "state");
    ("BAP_LOG_DIR", dir "log");
    (* the messages are plain text *)
    ("TERM", "dumb");
  ]

let environment vars =
  let names = List.map fst vars in
  Unix.environment () |> Array.to_list
  |> List.filter (fun var ->
      match String.index_opt var '=' with
      | Some i -> not (List.mem (String.sub var 0 i) names)
      | None -> true)
  |> List.append (List.map (fun (name, value) -> name ^ "=" ^ value) vars)

let regexp str = Re.compile (Re.Perl.re ~opts:[ `Dotall ] str)

let rec waitpid flags pid =
  try Unix.waitpid flags pid
  with Unix.Unix_error (Unix.EINTR, _, _) -> waitpid flags pid

let kill pid =
  (try Unix.kill pid Sys.sigkill with Unix.Unix_error _ -> ());
  ignore (waitpid [] pid)

let run_command ?(timeout = 600.) ?until ?(env = []) case prog args =
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
          ~env:(Spawn.Env.of_list (environment (variables case @ env)))
          ~cwd:(Spawn.Working_dir.Path case.dir) ~stdin ~stdout:fd ~stderr:fd ())
  in
  let until = Option.map regexp until in
  let deadline = Unix.gettimeofday () +. timeout in
  let rec wait delay =
    match waitpid [ Unix.WNOHANG ] pid with
    | 0, _ ->
        let matched =
          match until with Some re -> Re.execp re (read out) | None -> false
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
  { text = read out; status }

let bap ?timeout ?until ?env case args =
  run_command ?timeout ?until ?env case case.tools.bap args

let mc case args = run_command case case.tools.mc args

let check env name ok =
  if ok then env.passed <- env.passed + 1 else env.failed <- name :: env.failed

let matches output re = Re.execp (regexp re) output.text
let has env name output re = check env name (matches output re)
let lacks env name output re = check env name (not (matches output re))

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

(* the outcome of a case *)
type result = { case : case; env : env; error : string option; time : float }

let failed { env; error; _ } = error <> None || env.failed <> []

let rec remove name =
  match (Unix.lstat name).st_kind with
  | Unix.S_DIR ->
      Array.iter
        (fun entry -> remove (Filename.concat name entry))
        (Sys.readdir name);
      Unix.rmdir name
  | _ -> Sys.remove name
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

let run_case ~work ~tools n case =
  let dir = Filename.concat work (dirname n case.name) in
  mkdir dir;
  List.iter
    (fun sub -> mkdir (Filename.concat dir sub))
    [ "cache"; "config"; "state"; "log" ];
  let env = { dir; tools; calls = []; passed = 0; failed = [] } in
  let start = Unix.gettimeofday () in
  let error =
    match case.run env with
    | () -> None
    | exception exn -> Some (Printexc.to_string exn)
  in
  { case; env; error; time = Unix.gettimeofday () -. start }

let print_status = function
  | Exited n -> sprintf "exited with %d" n
  | Signaled -> "was killed by a signal"
  | Timeout -> "ran out of time"
  | Stopped -> "was stopped, as its output matched"

let report { case; env; error; _ } =
  printf "FAIL: %s\n" case.name;
  List.iter (printf "  failed: %s\n") (List.rev env.failed);
  Option.iter (printf "  raised: %s\n") error;
  List.iter
    (fun { command; out; result } ->
      printf "  ran: %s\n    %s, the output is in %s\n"
        (String.concat " " command)
        (print_status result) out)
    (List.rev env.calls);
  flush stdout

(* runs the cases in [jobs] threads, each case in its own directory, which
   is removed if the case passes *)
let run_cases ~jobs ~work ~tools cases =
  let queue = Queue.of_seq (List.to_seq cases) in
  let lock = Mutex.create () in
  let results = ref [] in
  let worker () =
    let rec loop () =
      match Mutex.protect lock (fun () -> Queue.take_opt queue) with
      | None -> ()
      | Some (n, case) ->
          let result = run_case ~work ~tools n case in
          Mutex.protect lock (fun () ->
              results := result :: !results;
              if failed result then report result);
          if not (failed result) then remove result.env.dir;
          loop ()
    in
    loop ()
  in
  List.init (max 1 jobs) (fun _ -> Thread.create worker ())
  |> List.iter Thread.join;
  !results

(* the root of the source tree, which contains the build directory *)
let rec source_root dir =
  let parent = Filename.dirname dir in
  if Filename.basename dir = "_build" then Some parent
  else if parent = dir then None
  else source_root parent

let absolute name =
  if Filename.is_relative name then Filename.concat (Sys.getcwd ()) name
  else name

let rec run_git args =
  let pid = Spawn.spawn ~prog:(locate "git") ~argv:("git" :: args) () in
  match waitpid [] pid with _, Unix.WEXITED 0 -> true | _ -> false

(* the program [name] in the PATH *)
and locate name =
  let name = if Sys.win32 then name ^ ".exe" else name in
  let sep = if Sys.win32 then ';' else ':' in
  Option.value (Sys.getenv_opt "PATH") ~default:""
  |> String.split_on_char sep
  |> List.map (fun dir -> Filename.concat dir name)
  |> List.find_opt Sys.file_exists
  |> Option.value ~default:name

(* checks out the revision of the testsuite in [dir], which is written in
   tools/testsuite/REVISION with its repository *)
let fetch ~root dir =
  let url, rev =
    match
      read (Filename.concat root "tools/testsuite/REVISION")
      |> String.split_on_char '\n' |> List.map String.trim
      |> List.filter (( <> ) "")
    with
    | [ url; rev ] -> (url, rev)
    | _ -> failwith "tools/testsuite/REVISION: expected the URL and revision"
  in
  let git args = if not (run_git args) then failwith "git failed" in
  if not (Sys.file_exists dir) then git [ "clone"; url; dir ];
  if not (run_git [ "-C"; dir; "cat-file"; "-e"; rev ^ "^{commit}" ]) then
    git [ "-C"; dir; "fetch"; url ];
  git [ "-C"; dir; "checkout"; "-q"; rev ]

let selected filters case =
  filters = []
  || List.exists
       (fun filter -> Option.is_some (find case.name filter 0))
       filters

let main tests =
  let jobs = ref (min 16 (Domain.recommended_domain_count ()))
  and root = ref None
  and testsuite = ref None
  and bap = ref "bap"
  and mc = ref "bap-mc"
  and work = ref None
  and do_fetch = ref true
  and fetch_only = ref false
  and list = ref false
  and filters = ref [] in
  let set_some r x = r := Some x in
  let spec =
    [
      ("-j", Arg.Set_int jobs, "N the number of the cases that run at once");
      ("--root", Arg.String (set_some root), "DIR the root of the source tree");
      ( "--testsuite",
        Arg.String (set_some testsuite),
        "DIR the testsuite, ROOT/testsuite by default" );
      ("--bap", Arg.Set_string bap, "PROG the bap to test");
      ("--mc", Arg.Set_string mc, "PROG the bap-mc to test");
      ( "--work",
        Arg.String (set_some work),
        "DIR keep the directories of the failed cases in DIR" );
      ("--no-fetch", Arg.Clear do_fetch, " don't check out the testsuite");
      ("--fetch-only", Arg.Set fetch_only, " only check out the testsuite");
      ("--list", Arg.Set list, " list the cases instead of running them");
    ]
  in
  let usage =
    "run.exe [OPTION]... [FILTER]...\n\
     Runs the cases of the testsuite whose names contain one of the filters,\n\
     or all of them. BAP_TESTS adds the filters, BAP_TESTSUITE_JOBS sets -j,\n\
     BAP_TESTSUITE_WORK sets --work."
  in
  Arg.parse (Arg.align spec) (fun x -> filters := x :: !filters) usage;
  Option.iter
    (fun var ->
      String.split_on_char ' ' var
      |> List.filter (( <> ) "")
      |> List.iter (fun x -> filters := x :: !filters))
    (Sys.getenv_opt "BAP_TESTS");
  Option.iter
    (fun n -> Option.iter (( := ) jobs) (int_of_string_opt n))
    (Sys.getenv_opt "BAP_TESTSUITE_JOBS");
  Option.iter
    (fun dir -> work := Some dir)
    (Sys.getenv_opt "BAP_TESTSUITE_WORK");
  let root =
    match !root with
    | Some root -> absolute root
    | None ->
        Option.value (source_root (Sys.getcwd ())) ~default:(Sys.getcwd ())
  in
  let dir =
    match !testsuite with
    | Some dir -> absolute dir
    | None -> Filename.concat root "testsuite"
  in
  if !do_fetch then fetch ~root dir;
  if !fetch_only then exit 0;
  let tools =
    let resolve prog =
      if Filename.is_implicit prog then locate prog else absolute prog
    in
    { bap = resolve !bap; mc = resolve !mc }
  in
  let cases =
    List.concat_map (fun test -> test dir) tests
    |> List.filter (selected !filters)
  in
  if !list then (
    List.iter (fun case -> print_endline case.name) cases;
    exit 0);
  let keep = !work <> None in
  let work =
    match !work with
    | Some dir ->
        mkdir (absolute dir);
        absolute dir
    | None -> Filename.temp_dir "bap-testsuite" ""
  in
  let numbered = List.mapi (fun n case -> (n, case)) cases in
  let parallel, serial = List.partition (fun (_, c) -> not c.serial) numbered in
  let slow, fast = List.partition (fun (_, c) -> c.slow) parallel in
  let start = Unix.gettimeofday () in
  let results =
    run_cases ~jobs:!jobs ~work ~tools (slow @ fast)
    @ run_cases ~jobs:1 ~work ~tools serial
  in
  let failures = List.filter failed results in
  let passed, failed =
    List.fold_left
      (fun (p, f) { env; error; _ } ->
        ( p + env.passed,
          f + List.length env.failed
          + Option.fold ~none:0 ~some:(fun _ -> 1) error ))
      (0, 0) results
  in
  printf "\nthe slowest cases:\n";
  List.sort (fun x y -> Float.compare y.time x.time) results
  |> List.filteri (fun i _ -> i < 5)
  |> List.iter (fun { case; time; _ } -> printf "  %5.0f s %s\n" time case.name);
  printf "\n%d cases, %d checks passed, %d failed, in %.0f s\n"
    (List.length results) passed failed
    (Unix.gettimeofday () -. start);
  if failures = [] then (
    if not keep then remove work;
    exit 0)
  else (
    printf "%d cases failed, their outputs are kept in %s\n"
      (List.length failures) work;
    exit 1)
