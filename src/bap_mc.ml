let () =
  let args =
    Array.of_list
    @@
    match Array.to_list Sys.argv with
    | [] | [ _ ] -> [ "bap"; "mc" ]
    | _ :: args -> "bap" :: "mc" :: args
  in
  (* exec on Windows starts a new process and exits, so the caller wouldn't
     wait for bap *)
  if Sys.win32 then
    let pid =
      Unix.create_process "bap" args Unix.stdin Unix.stdout Unix.stderr
    in
    match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED code -> exit code
    | Unix.WSIGNALED _ | Unix.WSTOPPED _ -> exit 2
  else Unix.execvp "bap" args
