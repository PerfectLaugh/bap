The packages of opam-repository patched for BAP, which dune-workspace adds
to the repositories of the lock.

- base_bigstring.v0.17.0 builds on Windows: its package in opam-repository
  isn't available there, since the C runtime of Windows has no memmem,
  which files/windows-memmem.patch defines, and core depends on it.
- conf-binutils.0.3 finds binutils on Windows: its find-binutils.ml.in
  supported only Linux and macOS, split PATH on colons, didn't match the
  .exe suffix, and wrote the paths unescaped into OCaml string literals.
  dune.lock/conf-binutils.0.3.files has the same file.

Keep the files with LF line endings (see /.gitattributes), as the checksums
in extra-files and the patches depend on them.

Remove a package when a release of opam-repository has its patch.
