#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu
module Xrefs = Emu.Xrefs

let list a = List.init (Bigarray.Array1.dim a) ~f:(Bigarray.Array1.get a)

let () =
  match Bap_script.args () with
  | [ file; engine; blocks ] -> (
      let engine = if String.equal engine "unicorn" then `Unicorn else `Lifted in
      let blocks = String.equal blocks "blocks" in
      let proj = Bap_script.project ~disassemble:true file in
      let emu = Emu.create ~engine proj in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      let worker = addr "worker" in
      let counter = 0x203c00L in
      let trace =
        Emu.Trace.start ~size:(1 lsl 22) ~blocks ~accesses:(1 lsl 16) emu
      in
      ignore (Emu.run emu : Emu.status);
      let pcs = Emu.Trace.pcs trace and tids = Emu.Trace.tids trace in
      let pc_list = list pcs and tid_list = list tids in
      let threads = List.dedup_and_sort tid_list ~compare:Int64.compare in
      let accesses = Emu.Trace.accesses trace in
      let first = Int64.(Emu.Trace.count trace - of_int (List.length pc_list)) in
      let aligned =
        (not (List.is_empty accesses))
        && List.for_all accesses ~f:(fun a ->
            let i = Int64.(to_int_exn (a.insn - first)) in
            i >= 0 && i < List.length tid_list
            && Int64.equal (List.nth_exn tid_list i) (Int64.of_int a.thread))
      in
      let transitions =
        List.zip_exn
          (List.take pc_list (List.length pc_list - 1))
          (List.tl_exn pc_list)
        |> List.mapi ~f:(fun i (site, target) ->
            ( List.nth_exn tid_list i,
              site,
              target,
              Int64.equal
                (List.nth_exn tid_list i)
                (List.nth_exn tid_list (i + 1)) ))
      in
      let valid site target thread =
        List.exists transitions ~f:(fun (tid, from, into, same) ->
            same
            && Int64.equal tid (Int64.of_int thread)
            && Int64.(from = site && into = target))
      in
      let calls = Emu.Trace.calls trace in
      let branches = Emu.Trace.branches trace in
      let calls_valid =
        (not (List.is_empty calls))
        && (blocks
           || List.for_all calls ~f:(fun c ->
               List.for_all c.targets ~f:(fun (target, _) ->
                   valid c.site target c.thread)))
      in
      let branches_valid =
        (not (List.is_empty branches))
        && (blocks || List.for_all branches ~f:(fun b -> valid b.site b.target b.thread))
      in
      let regs = Emu.slice ~thread:2 trace [ Emu.Reg "RAX" ] in
      let register_slice =
        (not (List.is_empty regs.steps))
        && List.is_empty regs.gaps
        && List.for_all regs.steps ~f:(fun s -> s.thread = 2)
        && List.exists regs.steps ~f:(fun s ->
            Int64.(s.pc >= worker && s.pc < worker + 0x80L))
      in
      let indices =
        List.for_all regs.steps ~f:(fun s ->
            let i = Int64.(to_int_exn (s.index - first)) in
            i >= 0 && i < List.length tid_list
            && Int64.equal (List.nth_exn tid_list i) 2L)
      in
      let memory = Emu.slice ~thread:1 trace [ Emu.Mem (counter, 4) ] in
      let shared_gap =
        (not (List.is_empty memory.gaps))
        && List.for_all memory.steps ~f:(fun s -> s.thread = 1)
      in
      let xrefs = Xrefs.create proj in
      Xrefs.add_calls xrefs calls;
      let cloned = addr "cloned" in
      let callers = Xrefs.callers xrefs cloned in
      let recovered =
        List.exists callers ~f:(fun caller ->
            Option.equal String.equal (Xrefs.name xrefs caller) (Some "main"))
      in
      printf "tids %s; accesses %b; calls %b; branches %b\n"
        (String.concat ~sep:"," (List.map threads ~f:Int64.to_string))
        aligned calls_valid branches_valid;
      printf "register slice %b; indices %b; shared gap %b; callback %b\n"
        register_slice indices shared_gap recovered)
  | _ -> failwith "expected FILE ENGINE instructions|blocks"
