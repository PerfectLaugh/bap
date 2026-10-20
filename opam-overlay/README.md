The packages of opam-repository patched for BAP, which dune-workspace adds
to the repositories of the lock.

- base_bigstring.v0.17.0 builds on Windows: its package in opam-repository
  isn't available there, since the C runtime of Windows has no memmem,
  which files/windows-memmem.patch defines, and core depends on it.

- zarith.1.14 links GMP statically: files/static-gmp.sh builds GMP 6.3.0
  from its sources, fetched as an extra-source, into a static library with
  position independent code, which is installed next to zarith, so that the
  programs of BAP don't depend on the libgmp of the system (except on
  Windows, where the package is unchanged).

- pbrt.4.1 compiles its stubs in the large model on Windows, where it is
  loaded with the protobuf plugin, as BAP compiles the stubs of its
  plugins, see files/windows-large-model.patch: flexdll can't relocate
  the relative calls of the stubs to the runtime of OCaml in the program,
  when the plugin is loaded further than 2 GB from it.

Keep the files with LF line endings (see /.gitattributes), as the checksums
in extra-files and the patches depend on them.

Remove a package when a release of opam-repository has its patch.
