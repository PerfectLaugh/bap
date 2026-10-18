(* Writes the flags that link the runtime of C++, which is linked
   statically on Windows, so that the programs and the plugins don't
   depend on the DLLs of the mingw-w64 toolchain, otherwise -lstdc++. *)

open Base
module C = Configurator.V1

let static_libraries =
  [ "libstdc++.a"; "libgcc.a"; "libgcc_eh.a"; "libwinpthread.a" ]

let static_runtime self =
  let cc = C.ocaml_config_var_exn self "c_compiler" in
  List.filter_map static_libraries ~f:(fun lib ->
      let path =
        String.strip
        @@ C.Process.run_capture_exn self cc [ "-print-file-name=" ^ lib ]
      in
      (* the compilers of the mingw-w64 toolchain of opam are Cygwin
         programs, which print the paths of Cygwin *)
      let path =
        if String.is_prefix path ~prefix:"/" then (
          match C.Process.run self "cygpath" [ "-m"; path ] with
          | { C.Process.exit_code = 0; stdout; _ } -> String.strip stdout
          | _ -> path
          | exception _ -> path)
        else path
      in
      Option.some_if
        ((not (Stdlib.Filename.is_relative path)) && Stdlib.Sys.file_exists path)
        path)

let () =
  C.main ~name:"cxx-runtime" @@ fun self ->
  C.Flags.write_sexp "cxx_runtime.flags"
  @@ if Stdlib.Sys.win32 then static_runtime self else [ "-lstdc++" ]
