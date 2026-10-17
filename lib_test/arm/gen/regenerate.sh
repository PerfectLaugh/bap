#!/bin/bash
# regenerates the tests from the specs, see gen.sh for NDK_BIN
cd "$(dirname "$0")" || exit 1
for s in a64:A64 a64fp:A64_floating_point a32:A32 vfp:VFP t32:T32; do
  f=${s%%:*}
  ./gen.sh $f.spec "${s##*:}" > ../test_$f.ml || exit 1
  ocamlformat -i ../test_$f.ml
done
