#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let create file = Emu.create ~args:[ "hello" ] (Bap_script.project file)

let test_override file =
  let emu = create file in
  Emu.on_import emu ~site:0x40075dL ~name:"strlen" (fun _ -> Return 42L);
  ignore (Emu.run emu ~until:0x400764L : Emu.status);
  printf "override result: %Lx\n" (Emu.reg emu "RAX");
  let events = Emu.relocation_journal emu in
  printf "relocation events: %d, %s\n" (List.length events)
    (List.map events ~f:(fun (event : Emu.event) -> event.detail)
    |> String.concat ~sep:";")

let test_default file =
  let emu = create file in
  Emu.on_import emu ~site:0x40075dL ~name:"strlen" (fun _ -> Default);
  ignore (Emu.run emu ~until:0x400764L : Emu.status);
  printf "default result: %Lx\n" (Emu.reg emu "RAX")

let test_stub file ~serviced =
  let emu = create file in
  let address = 0x40076bL in
  Emu.register_stub emu ~name:"synthetic" ~address;
  if serviced then Emu.on_call emu "synthetic" (fun _ -> Return 0L);
  ignore (Emu.call emu address : int64 option);
  printf "stub serviced: %b\n" serviced

let () =
  match Bap_script.args () with
  | [ file; "override" ] -> test_override file
  | [ file; "default" ] -> test_default file
  | [ file; "unserviced" ] -> test_stub file ~serviced:false
  | [ file; "serviced" ] -> test_stub file ~serviced:true
  | _ -> failwith "expected ECHO MODE"
