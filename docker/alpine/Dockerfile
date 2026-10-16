# Builds BAP from this source tree with dune package management.
#
# docker build -f docker/alpine/Dockerfile -t bap .

FROM alpine:latest

ARG DUNE_VERSION=3.24.2
ARG DUNE_SHA256=a663dc3d95d15e9cfba47fd1d723bbee4e8b4eee1023dd912d34eb766e5c00da

RUN apk add --no-cache \
      bash build-base coreutils curl git linux-headers llvm-dev m4 \
      patch python3 unzip

COPY docker/install-dune.sh /tmp/install-dune.sh
RUN sh /tmp/install-dune.sh "$DUNE_VERSION" "$DUNE_SHA256" \
 && rm /tmp/install-dune.sh

RUN adduser -D bap
WORKDIR /home/bap/bap
COPY --chown=bap:bap . .

# the system packages required by the locked dependencies
RUN apk add --no-cache $(dune show depexts) \
 && rm -rf _build

USER bap
RUN sh docker/build.sh

ENTRYPOINT ["/home/bap/bap/docker/entrypoint.sh"]
CMD ["bap", "--help"]
