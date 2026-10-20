(* Writes the flags of the linker of OCaml, that the programs link with:
   the linker of Xcode 15 and later warns about the libraries, that it
   gets more than once, e.g., -lc++, which dune passes for each library
   with C++ stubs, or -lpthread, so it doesn't warn, if it accepts
   -no_warn_duplicate_libraries, which the older linkers reject. *)

module C = Configurator.V1

let flag = "-Wl,-no_warn_duplicate_libraries"

let () =
  C.main ~name:"link-flags" @@ fun self ->
  let accepted =
    C.c_test self ~link_flags:[ flag ] "int main(void) { return 0; }\n"
  in
  C.Flags.write_sexp "link_flags.sexp"
    (if accepted then [ "-ccopt"; flag ] else [])
