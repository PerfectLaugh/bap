(* Writes the flags that link the runtime of C++ and of the compiler,
   which are linked statically on Windows and Linux, so that the programs
   and the plugins don't depend on the DLLs of the mingw-w64 toolchain or
   on the libstdc++, the libgcc_s, and the libatomic of the system, and
   dynamically on macOS, whose libc++ is a part of the system. The
   static libraries are passed by their paths, as the drivers of C link
   -lstdc++ dynamically. *)

open Base
module C = Configurator.V1

let static_libraries = function
  | "linux" -> [ "libstdc++.a"; "libatomic.a"; "libgcc_eh.a"; "libgcc.a" ]
  | _ -> [ "libstdc++.a"; "libgcc.a"; "libgcc_eh.a"; "libwinpthread.a" ]

let static_runtime self system =
  let cc = C.ocaml_config_var_exn self "c_compiler" in
  List.filter_map (static_libraries system) ~f:(fun lib ->
      let path =
        String.strip
        @@ C.Process.run_capture_exn self cc [ "-print-file-name=" ^ lib ]
      in
      (* the compilers of the mingw-w64 toolchain of opam are Cygwin
         programs, which print the paths of Cygwin *)
      let path =
        if String.is_prefix path ~prefix:"/" then
          match C.Process.run self "cygpath" [ "-m"; path ] with
          | { C.Process.exit_code = 0; stdout; _ } -> String.strip stdout
          | _ -> path
          | exception _ -> path
        else path
      in
      Option.some_if
        ((not (Stdlib.Filename.is_relative path)) && Stdlib.Sys.file_exists path)
        path)

let () =
  C.main ~name:"cxx-runtime" @@ fun self ->
  let system = C.ocaml_config_var_exn self "system" in
  C.Flags.write_sexp "cxx_runtime.flags"
  @@
  match system with
  | "linux" -> (
      (* the static libraries are optional on Linux, e.g., in the
         libstdc++-static package of Fedora *)
      match static_runtime self system with
      | runtime when List.length runtime = List.length (static_libraries system)
        ->
          runtime
      | _ -> [ "-lstdc++" ])
  | _ when Stdlib.Sys.win32 -> static_runtime self system
  | _ -> [ "-lstdc++" ]
