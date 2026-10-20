open Core
open Bap_main
open Bap.Std
open Regular.Std

let ver = "1.0"

let desc = function
  | `pb -> "protobuf, see bap_protobuf_ir.proto"
  | `json -> "JSON of protobuf, see bap_protobuf_ir.proto"

let name fmt = Sexp.to_string (Bil_proto.sexp_of_fmt fmt)

let writer to_string fmt =
  Data.Write.create ~to_bytes:(fun x -> Bytes.of_string (to_string fmt x)) ()

let reader of_string fmt =
  Data.Read.create ~of_bytes:(fun b -> of_string fmt (Bytes.to_string b)) ()

let register (type t) (module T : Data.S with type t = t) to_string of_string =
  List.iter Bil_proto.all_of_fmt ~f:(fun fmt ->
      let desc = desc fmt in
      T.add_writer ~desc ~ver (name fmt) (writer to_string fmt);
      T.add_reader ~desc ~ver (name fmt) (reader of_string fmt))

let () =
  Extension.declare ~doc:"serializes BIL and BIR in protobuf and JSON"
    ~provides:[ "serialization"; "protobuf"; "json" ]
  @@ fun _ ->
  register (module Exp) Bil_proto.exp_to_string Bil_proto.exp_of_string;
  register (module Stmt) Bil_proto.stmt_to_string Bil_proto.stmt_of_string;
  register (module Bil) Bil_proto.bil_to_string Bil_proto.bil_of_string;
  register
    (module Program)
    Bir_proto.program_to_string Bir_proto.program_of_string;
  register (module Sub) Bir_proto.sub_to_string Bir_proto.sub_of_string;
  register (module Blk) Bir_proto.blk_to_string Bir_proto.blk_of_string;
  register (module Arg) Bir_proto.arg_to_string Bir_proto.arg_of_string;
  register (module Phi) Bir_proto.phi_to_string Bir_proto.phi_of_string;
  register (module Def) Bir_proto.def_to_string Bir_proto.def_of_string;
  register (module Jmp) Bir_proto.jmp_to_string Bir_proto.jmp_of_string;
  (* the program of the project, e.g., bap --dump=bir.json *)
  List.iter Bil_proto.all_of_fmt ~f:(fun fmt ->
      Project.add_writer
        ~desc:("print program in " ^ desc fmt)
        ~ver
        ("bir." ^ name fmt)
        (writer
           (fun fmt proj ->
             Bir_proto.program_to_string fmt (Project.program proj))
           fmt));
  Ok ()
