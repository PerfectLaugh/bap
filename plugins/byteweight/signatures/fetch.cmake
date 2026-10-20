# Downloads the byteweight signatures of a BAP release.
#
# usage: cmake [-DARCHIVE=<file>] -P fetch.cmake
#
# Writes byteweight.zip in the current directory, copying ARCHIVE, if it
# is specified (e.g., when opam has already fetched it as an
# extra-source), otherwise downloading it from GitHub. In both cases the
# checksum is verified.

cmake_minimum_required(VERSION 3.21)

set(SIGS_VERSION 2.5.0)
set(SIGS_URL
  https://github.com/BinaryAnalysisPlatform/bap/releases/download/v${SIGS_VERSION}/sigs.zip)
set(SIGS_SHA256
  9347ca6e56600d19adc0096af6b471655658639193244c5f25e6918f4493c934)
set(OUT "${CMAKE_CURRENT_SOURCE_DIR}/byteweight.zip")

if(ARCHIVE)
  file(SHA256 "${ARCHIVE}" sha256)
  if(NOT sha256 STREQUAL SIGS_SHA256)
    message(FATAL_ERROR "fetch.cmake: ${ARCHIVE} has a wrong checksum")
  endif()
  file(COPY_FILE "${ARCHIVE}" "${OUT}")
else()
  file(DOWNLOAD "${SIGS_URL}" "${OUT}"
    EXPECTED_HASH SHA256=${SIGS_SHA256}
    STATUS status)
  list(GET status 0 code)
  if(NOT code EQUAL 0)
    file(REMOVE "${OUT}")
    message(FATAL_ERROR "fetch.cmake: can't download ${SIGS_URL}: ${status}")
  endif()
endif()
