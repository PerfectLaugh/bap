# Builds BAP from this source tree with dune package management.
#
# docker build -f docker/debian/testing/Dockerfile -t bap .
#
# Debian doesn't package radare2, so the radare2 plugin is built
# but radare2 itself is not installed.

FROM debian:testing

ARG DUNE_VERSION=3.24.2
ARG DUNE_SHA256=a663dc3d95d15e9cfba47fd1d723bbee4e8b4eee1023dd912d34eb766e5c00da

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      build-essential ca-certificates curl git llvm-dev m4 patch \
      python3 unzip \
 && rm -rf /var/lib/apt/lists/*

COPY docker/install-dune.sh /tmp/install-dune.sh
RUN sh /tmp/install-dune.sh "$DUNE_VERSION" "$DUNE_SHA256" \
 && rm /tmp/install-dune.sh

RUN useradd --create-home bap
WORKDIR /home/bap/bap
COPY --chown=bap:bap . .

# the system packages required by the locked dependencies
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      $(dune show depexts | grep -vx radare2) \
 && rm -rf /var/lib/apt/lists/* _build

USER bap
RUN sh docker/build.sh

ENTRYPOINT ["/home/bap/bap/docker/entrypoint.sh"]
CMD ["bap", "--help"]
