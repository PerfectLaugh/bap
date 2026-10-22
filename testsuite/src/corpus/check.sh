#!/bin/sh
# runs check.ml on the instructions of INSNS, in the chunks of CHUNK (8), at
# most JOBS (6) at once, each in 10 seconds, and prints the instructions,
# whose results differ, and the chunks, that didn't finish:
#
#   check.sh PROGRAM INSNS [ARGS of check.ml]
set -e
here=$(cd "$(dirname "$0")" && pwd)
bap=${BAP:-bap}
program=$1 insns=$2
shift 2
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
split -l "${CHUNK:-8}" -d -a 4 "$insns" "$work/chunk."
ls "$work"/chunk.* | xargs -P "${JOBS:-6}" -I{} sh -c \
  'timeout 10 '"$bap"' script '"$here"'/check.ml '"$program"' {} '"$*"' > {}.out 2>&1 || echo "TIMEOUT or ERROR in {}: $(head -c 300 {})" >> {}.out'
cat "$work"/chunk.*.out | grep -v "^checked"
