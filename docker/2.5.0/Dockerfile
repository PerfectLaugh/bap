# Installs the released BAP 2.5.0 from opam.

FROM ocaml/opam:debian-ocaml-4.14

WORKDIR /home/opam

RUN opam remote set-url default https://opam.ocaml.org \
 && opam update \
 && opam install --confirm-level=unsafe-yes -j 1 bap.2.5.0 \
 && opam clean -acrs

ENTRYPOINT ["opam", "exec", "--"]
