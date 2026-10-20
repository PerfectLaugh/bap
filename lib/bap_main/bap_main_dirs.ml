(* The directories of BAP don't depend on the directories of the user:
   the read-only data is in the sites of bap-common, and BAP writes its
   cache and its log only to the directories that the command line
   specifies, see the --cache-dir and --log-dir options. *)

let ( / ) = Filename.concat

(* the directory of the sites, e.g., share/bap-common *)
let share =
  match Bap_common.sites "api" with
  | dir :: _ -> Filename.dirname dir
  | [] -> Bap_main_config.datadir

let config = share / "config"
let cache : string option ref = ref None
