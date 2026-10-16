#!/bin/sh
# Runs the command in the environment of the BAP build, see build.sh.

set -eu

. "$HOME/.bap-env"
exec "$@"
