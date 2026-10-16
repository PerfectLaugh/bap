#!/bin/sh
# Installs the dune binary distribution to /usr/local/bin.
#
# usage: install-dune.sh VERSION SHA256

set -eu

VERSION=$1
SHA256=$2
TARGET=x86_64-unknown-linux-musl
URL=https://nightly.dune.build/stable/${VERSION}/${TARGET}

case $(uname -m) in
    x86_64) ;;
    *) echo "dune binaries are not available for $(uname -m)" >&2; exit 1 ;;
esac

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

curl -fsSL -o "$WORK/dune.tar.gz" "$URL"
echo "$SHA256  $WORK/dune.tar.gz" | sha256sum -c -
tar xzf "$WORK/dune.tar.gz" -C "$WORK"
install -m 755 "$WORK/dune-${VERSION}-${TARGET}/dune" /usr/local/bin/dune
dune --version
