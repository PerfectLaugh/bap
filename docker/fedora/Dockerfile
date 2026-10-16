# Builds BAP from this source tree with dune package management.
#
# docker build -f docker/fedora/Dockerfile -t bap .

FROM fedora:latest

ARG DUNE_VERSION=3.24.2
ARG DUNE_SHA256=a663dc3d95d15e9cfba47fd1d723bbee4e8b4eee1023dd912d34eb766e5c00da

RUN dnf install -y \
      diffutils findutils gcc gcc-c++ git gzip llvm-devel m4 make \
      patch python3 tar unzip \
 && dnf clean all

COPY docker/install-dune.sh /tmp/install-dune.sh
RUN sh /tmp/install-dune.sh "$DUNE_VERSION" "$DUNE_SHA256" \
 && rm /tmp/install-dune.sh

RUN useradd --create-home bap
WORKDIR /home/bap/bap
COPY --chown=bap:bap . .

# the system packages required by the locked dependencies
RUN dnf install -y $(dune show depexts) \
 && dnf clean all \
 && rm -rf _build

USER bap
RUN sh docker/build.sh

ENTRYPOINT ["/home/bap/bap/docker/entrypoint.sh"]
CMD ["bap", "--help"]
