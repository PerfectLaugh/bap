# Builds BAP from this source tree with dune package management.
#
# docker build -f docker/debian/testing/Dockerfile -t bap .

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
      $(dune show depexts) \
 && rm -rf /var/lib/apt/lists/* _build

USER bap
RUN sh docker/build.sh

ENTRYPOINT ["/home/bap/bap/docker/entrypoint.sh"]
CMD ["bap", "--help"]
