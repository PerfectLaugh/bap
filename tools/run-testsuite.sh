#!/bin/bash
# run-testsuite.sh [JOBS [TOOL:FILE...]]: runs the tests of the bap and mc
# tools of the testsuite in testsuite/, JOBS test files at a time (8 by
# default). If test files are given, e.g., mc:x86-mov.exp, only they run.
#
# Each test file runs in its own directory, which links to the entries of
# the testsuite, since the tests write their outputs in the current
# directory, and with its own cache and log directories, since the tests
# change the cache. The outputs of the commands, *-result, are not
# linked, since each test file writes its own. The test files that
# change the files of the installation run alone, after the others.
# The directories are removed if all tests pass, and kept and printed
# otherwise.
set -u
jobs=${1:-8}
shift $(($# > 0 ? 1 : 0))
only="$*"
root=$(cd "$(dirname "$0")/.." && pwd)
ts=$root/testsuite
tools="bap mc"

# api-options adds and removes API files in the installed API directory
# and makes it unreadable, config writes a configuration file in the
# installed configuration directory, while the other tests read them
serial="bap:api-options.exp bap:config.exp"

# the slowest test files start first
slow="bap:taint.exp bap:symexec.exp"

if ! runtest -version > /dev/null 2>&1; then
  echo "Please, install runtest (dejagnu)" >&2
  exit 1
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/bap-testsuite.XXXXXX")
export ts work

run_one() {
  local tool=$1 exp=$2
  local dir=$work/$tool-${exp%.exp}
  mkdir -p "$dir"/xdg/cache "$dir"/xdg/state
  for entry in "$ts"/*; do
    case ${entry##*/} in
      logs | *.log | *.sum | *-result) ;;
      *) ln -s "$entry" "$dir"/ ;;
    esac
  done
  cd "$dir" || exit 1
  XDG_CACHE_HOME=$dir/xdg/cache XDG_STATE_HOME=$dir/xdg/state \
    runtest --status --tool="$tool" "$exp" > runtest.out 2>&1
  echo $? > status
}
export -f run_one

is_in() {
  case " $1 " in *" $2:$3 "*) true ;; *) false ;; esac
}

# the test files that run, all of them if none are given
selected() {
  [ -z "$only" ] || is_in "$only" "$1" "$2"
}

{
  for test in $slow; do
    selected ${test%%:*} ${test#*:} || continue
    echo "${test%%:*} ${test#*:}"
  done
  for tool in $tools; do
    for exp in "$ts/$tool.tests"/*.exp; do
      is_in "$serial $slow" $tool ${exp##*/} && continue
      selected $tool ${exp##*/} && echo "$tool ${exp##*/}"
    done
  done
} | xargs -P "$jobs" -L 1 bash -c 'run_one "$@"' run_one

for test in $serial; do
  selected ${test%%:*} ${test#*:} || continue
  (run_one ${test%%:*} ${test#*:})
done

status=0
for tool in $tools; do
  echo
  echo "		=== $tool Summary ==="
  echo
  cat "$work/$tool"-*/"$tool".sum 2> /dev/null |
    grep -oE '^(PASS|FAIL|XPASS|XFAIL|UNRESOLVED|UNTESTED|UNSUPPORTED|ERROR|WARNING)' |
    sort | uniq -c | while read -r n result; do
      printf '# of %-20s %d\n' "$result" "$n"
    done
done

for dir in "$work"/*/; do
  if [ "$(cat "$dir/status" 2> /dev/null)" != 0 ]; then
    status=1
    echo
    echo "failed in $dir:"
    grep -hE '^(FAIL|XPASS|UNRESOLVED|ERROR):' "$dir"/*.sum "$dir/runtest.out" |
      sort -u
  fi
done

if [ $status = 0 ]; then
  rm -rf "$work"
else
  echo
  echo "the outputs are kept in $work"
fi
exit $status
