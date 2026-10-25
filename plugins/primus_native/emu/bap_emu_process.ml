external start_deadline : float -> int -> int64
  = "bap_emu_process_deadline_start"

external cancel_deadline : int64 -> unit = "bap_emu_process_deadline_cancel"
