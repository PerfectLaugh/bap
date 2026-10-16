# Builds BAP from this source tree with dune package management.
#
# docker build -f docker/archlinux/Dockerfile -t bap .

FROM archlinux:latest

ARG DUNE_VERSION=3.24.2
ARG DUNE_SHA256=a663dc3d95d15e9cfba47fd1d723bbee4e8b4eee1023dd912d34eb766e5c00da

RUN pacman -Syu --noconfirm --needed \
      base-devel curl git llvm python unzip \
 && pacman -Scc --noconfirm

COPY docker/install-dune.sh /tmp/install-dune.sh
RUN sh /tmp/install-dune.sh "$DUNE_VERSION" "$DUNE_SHA256" \
 && rm /tmp/install-dune.sh

RUN useradd --create-home bap
WORKDIR /home/bap/bap
COPY --chown=bap:bap . .

# the system packages required by the locked dependencies
RUN pacman -S --noconfirm --needed $(dune show depexts) \
 && pacman -Scc --noconfirm \
 && rm -rf _build

USER bap
RUN sh docker/build.sh

ENTRYPOINT ["/home/bap/bap/docker/entrypoint.sh"]
CMD ["bap", "--help"]
