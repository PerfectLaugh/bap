The packages of opam-repository patched for BAP, which dune-workspace adds
to the repositories of the lock.

- base_bigstring.v0.17.0 builds on Windows: its package in opam-repository
  isn't available there, since the C runtime of Windows has no memmem,
  which files/windows-memmem.patch defines, and core depends on it.

Keep the files with LF line endings (see /.gitattributes), as the checksums
in extra-files and the patches depend on them.

Remove a package when a release of opam-repository has its patch.
