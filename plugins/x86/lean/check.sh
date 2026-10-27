#!/usr/bin/env bash
set -euo pipefail

project_dir="$(CDPATH= cd -- "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
repo_dir="$(CDPATH= cd -- "$project_dir/../../.." && pwd -P)"
toolchain="$(< "$project_dir/lean-toolchain")"

if command -v elan >/dev/null 2>&1; then
    elan_command="$(command -v elan)"
elif [[ -x "${HOME:-}/.elan/bin/elan" ]]; then
    elan_command="$HOME/.elan/bin/elan"
else
    printf 'check.sh: elan was not found.\n' >&2
    exit 127
fi

cd -- "$project_dir"
"$elan_command" run "$toolchain" lake build
export LEAN_PATH="$project_dir/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
cd -- "$repo_dir"
dune build @plugins/x86/test/lean-tests
printf 'x86 Lean checks passed.\n'
