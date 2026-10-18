external ghidra_init : string -> bool -> int = "disasm_ghidra_init_stub"

let init ?(paths = [ "/usr/share/ghidra" ]) ?(print_targets = false) () =
  (* the colon is a part of the paths on Windows, e.g., [C:\ghidra] *)
  let paths = String.concat "\n" paths in
  if ghidra_init paths print_targets < 0 then
    failwith "failed to initialize ghidra backend. See stderr for information"
