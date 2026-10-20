(* The directories of BAP don't depend on the directories of the user:
   the read-only data is in the sites of bap-common, and BAP reads the
   configuration files of the user and writes its cache and its log only
   in the directories that the command line specifies, see the
   --config-dir, --cache-dir, and --log-dir options. *)

let ( / ) = Filename.concat

(* the directory of the sites, e.g., share/bap-common *)
let share =
  match Bap_common.sites "api" with
  | dir :: _ -> Filename.dirname dir
  | [] -> Bap_main_config.datadir

let config = share / "config"
let user_config : string option ref = ref None
let cache : string option ref = ref None
