# Builds the Ghidra decompiler library and Sleigh processor specifications.
#
# usage: cmake -DLINK_PREFIX=<path> [-DTARBALL=<file>] [-DCC=<cc>]
#              [-DCXX=<c++>] [-DJOBS=<n>] -P build.cmake
#
# Produces in the current directory:
#   libdecomp.a     - the static decompiler library
#   include/ghidra/ - its headers
#   include/zlib/   - the headers of the zlib, that it bundles, which its
#                     headers include with LOCAL_ZLIB, as the stubs do
#   Processors/     - the compiled processor specifications
#   Processors.zip  - the same, installed on Windows instead
#   c.flags         - the flags of the stubs that call the library
#   link.flags      - the flags that link the library, whose directory is
#                     LINK_PREFIX relative to the root of the build context
#
# The Ghidra sources are taken from TARBALL, if it is specified (e.g.,
# when opam has already fetched it as an extra-source), otherwise they
# are downloaded from GitHub. In both cases the checksum is verified.
#
# The library and the Sleigh compiler are built from the lists of the
# sources of the POSIX Makefile of the decompiler with a CMake project,
# which builds on Windows too, with the compilers of OCaml, the CC and
# CXX commands, e.g., the %{cc} and %{cxx} of dune, whose flags are
# ignored. The build uses Ninja if it is installed, otherwise make,
# except on Windows, where it needs Ninja.

cmake_minimum_required(VERSION 3.21)

set(GHIDRA_VERSION 12.1.4)
set(GHIDRA_BASENAME Ghidra_${GHIDRA_VERSION}_build)
set(GHIDRA_URL
  https://github.com/NationalSecurityAgency/ghidra/archive/refs/tags/${GHIDRA_BASENAME}.tar.gz)
set(GHIDRA_SHA256
  2a858300c350f05ae2e729dff86b4f584d0b9a6b398879c55025574e67696cec)
set(GHIDRA_ROOT ghidra-${GHIDRA_BASENAME})
set(DECOMPILER ${GHIDRA_ROOT}/Ghidra/Features/Decompiler/src/decompile/cpp)
set(ZLIB ${GHIDRA_ROOT}/Ghidra/Features/Decompiler/src/decompile/zlib)

if(NOT LINK_PREFIX)
  message(FATAL_ERROR "build.cmake: LINK_PREFIX is not specified")
endif()
set(OUT "${CMAKE_CURRENT_SOURCE_DIR}")

if(NOT JOBS)
  cmake_host_system_information(RESULT JOBS QUERY NUMBER_OF_LOGICAL_CORES)
endif()

if(CMAKE_HOST_WIN32)
  file(TO_CMAKE_PATH "$ENV{TEMP}" TMP)
elseif(DEFINED ENV{TMPDIR})
  set(TMP "$ENV{TMPDIR}")
else()
  set(TMP /tmp)
endif()
string(RANDOM LENGTH 8 SUFFIX)
set(WORK "${TMP}/bap-ghidra-${SUFFIX}")
file(MAKE_DIRECTORY "${WORK}")

function(fail)
  file(REMOVE_RECURSE "${WORK}")
  message(FATAL_ERROR ${ARGN})
endfunction()

# runs the command quietly, but shows the end of its output if it fails
function(quietly name)
  execute_process(
    COMMAND ${ARGN}
    OUTPUT_FILE "${WORK}/${name}.log"
    ERROR_FILE "${WORK}/${name}.log"
    RESULT_VARIABLE status)
  if(NOT status EQUAL 0)
    file(STRINGS "${WORK}/${name}.log" lines)
    list(LENGTH lines total)
    if(total GREATER 100)
      math(EXPR first "${total} - 100")
      list(SUBLIST lines ${first} 100 lines)
    endif()
    list(JOIN lines "\n" tail)
    fail("${name} of Ghidra failed (${status}):\n${tail}")
  endif()
endfunction()

if(TARBALL)
  file(SHA256 "${TARBALL}" sum)
  if(NOT sum STREQUAL GHIDRA_SHA256)
    fail("checksum mismatch for ${TARBALL}: got ${sum}")
  endif()
else()
  set(TARBALL "${WORK}/ghidra.tar.gz")
  file(DOWNLOAD "${GHIDRA_URL}" "${TARBALL}"
    EXPECTED_HASH SHA256=${GHIDRA_SHA256}
    TLS_VERIFY ON
    STATUS status)
  list(GET status 0 code)
  if(NOT code EQUAL 0)
    fail("failed to download ${GHIDRA_URL}: ${status}")
  endif()
endif()

file(ARCHIVE_EXTRACT
  INPUT "${TARBALL}"
  DESTINATION "${WORK}"
  PATTERNS
    ${DECOMPILER}
    ${ZLIB}
    ${GHIDRA_ROOT}/Ghidra/Processors)
set(SRC "${WORK}/${DECOMPILER}")

# the lists of the modules of the Makefile of the decompiler, e.g., CORE
file(READ "${SRC}/Makefile" makefile)
string(REGEX REPLACE "\\\\\r?\n" " " makefile "${makefile}")
string(REPLACE ";" "" makefile "${makefile}")
string(REGEX REPLACE "\r?\n" ";" makefile "${makefile}")

file(GLOB coreext RELATIVE "${SRC}" "${SRC}/coreext_*.cc")
file(GLOB ghidraext RELATIVE "${SRC}" "${SRC}/ghidraext_*.cc")
list(TRANSFORM coreext REPLACE "\\.cc$" "")
list(TRANSFORM ghidraext REPLACE "\\.cc$" "")

function(modules var)
  set(found FALSE)
  foreach(line ${makefile})
    if(line MATCHES "^${var}[ \t]*=(.*)$")
      set(names "${CMAKE_MATCH_1}")
      set(found TRUE)
      break()
    endif()
  endforeach()
  if(NOT found)
    fail("the Makefile of the decompiler has no ${var}")
  endif()
  string(REPLACE "$(COREEXT_NAMES)" "${coreext}" names "${names}")
  string(REPLACE "$(GHIDRAEXT_NAMES)" "${ghidraext}" names "${names}")
  separate_arguments(names UNIX_COMMAND "${names}")
  set(${var} ${names} PARENT_SCOPE)
endfunction()

foreach(var CORE DECCORE SLEIGH GHIDRA SLACOMP SPECIAL)
  modules(${var})
endforeach()

# the modules that depend on the GNU BFD library, they are only used by
# the command-line decompiler, so they are left out to avoid requiring
# the binutils development files
set(NO_BFD analyzesigs bfd_arch codedata loadimage_bfd)

# EXTRA of the Makefile, i.e., the rest of the modules, without NO_BFD
file(GLOB all RELATIVE "${SRC}" "${SRC}/*.cc")
list(TRANSFORM all REPLACE "\\.cc$" "")
set(EXTRA ${all})
list(REMOVE_ITEM EXTRA
  ${CORE} ${DECCORE} ${SLEIGH} ${GHIDRA} ${SLACOMP} ${SPECIAL} ${NO_BFD})

set(LIBDECOMP ${CORE} ${DECCORE} ${EXTRA} ${SLEIGH})
set(SLEIGH_COMPILER ${CORE} ${SLEIGH} ${SLACOMP})
list(TRANSFORM LIBDECOMP REPLACE "(.+)" "${SRC}/\\1.cc")
list(TRANSFORM SLEIGH_COMPILER REPLACE "(.+)" "${SRC}/\\1.cc")

# the sources of zlib, which the decompiler bundles and selects with
# LOCAL_ZLIB, are compiled into the library, so that it doesn't depend
# on the zlib of the system
set(ZLIB_SRC "${WORK}/${ZLIB}")
file(GLOB ZLIB "${ZLIB_SRC}/*.c")

# the first word of a dune compiler command, without its flags
function(compiler var cmd default)
  if(cmd)
    separate_arguments(words NATIVE_COMMAND "${cmd}")
    list(GET words 0 cmd)
  else()
    set(cmd ${default})
  endif()
  set(${var} ${cmd} PARENT_SCOPE)
endfunction()

compiler(CC "${CC}" cc)
compiler(CXX "${CXX}" c++)

# dune's C++ compiler is the C compiler of OCaml, e.g., gcc, whose
# driver doesn't link the C++ runtime, so its C++ driver is used
get_filename_component(dir "${CXX}" DIRECTORY)
get_filename_component(name "${CXX}" NAME)
if(name MATCHES "^(.*)gcc(-[0-9.]+)?(\\.exe)?$")
  set(name "${CMAKE_MATCH_1}g++${CMAKE_MATCH_2}${CMAKE_MATCH_3}")
elseif(name MATCHES "^(.*)clang(-[0-9.]+)?(\\.exe)?$")
  set(name "${CMAKE_MATCH_1}clang++${CMAKE_MATCH_2}${CMAKE_MATCH_3}")
elseif(name MATCHES "^cc(\\.exe)?$")
  set(name "c++${CMAKE_MATCH_1}")
endif()
if(dir)
  set(CXX "${dir}/${name}")
else()
  set(CXX "${name}")
endif()

find_program(NINJA ninja)
if(NINJA)
  set(GENERATOR Ninja)
elseif(CMAKE_HOST_WIN32)
  fail("building Ghidra on Windows requires Ninja")
else()
  set(GENERATOR "Unix Makefiles")
endif()

# the decompiler has a Windows port, selected with _WINDOWS, and the
# terminal of the command-line decompiler, __TERMINAL__ (COMMANDLINE_OPT
# of the Makefile), is POSIX-only
if(CMAKE_HOST_WIN32)
  set(LIBDECOMP_DEFINITIONS _WINDOWS)
  # the medium model, the default of mingw-w64, refers to the external
  # data through the .refptr sections, of which flexlink makes a section
  # of the plugin each, and the decompiler has so many of them, that the
  # headers of the plugin overlap its code, which Windows doesn't load.
  # The decompiler refers only to its data and to the runtime of C++,
  # which are in the plugin, so it is in the small model
  set(LIBDECOMP_OPTIONS -mcmodel=small)
  set(SLEIGH_DEFINITIONS _WINDOWS)
  # the Sleigh compiler runs during the build, so it doesn't depend on
  # the DLLs of the mingw-w64 toolchain
  set(SLEIGH_LINK_OPTIONS -static)
else()
  set(LIBDECOMP_DEFINITIONS __TERMINAL__)
  set(LIBDECOMP_OPTIONS)
  set(SLEIGH_DEFINITIONS)
  set(SLEIGH_LINK_OPTIONS)
endif()

file(WRITE "${WORK}/project/CMakeLists.txt" "
cmake_minimum_required(VERSION 3.20)
project(decompiler C CXX)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
# the library is linked into the plugin, a shared library
set(CMAKE_POSITION_INDEPENDENT_CODE ON)
# the subset of zlib, that the decompiler bundles, has no gzip, as in
# the build of Ghidra
set_source_files_properties(${ZLIB} PROPERTIES COMPILE_DEFINITIONS NO_GZIP)
add_library(decomp STATIC ${LIBDECOMP} ${ZLIB})
target_compile_definitions(decomp PRIVATE LOCAL_ZLIB ${LIBDECOMP_DEFINITIONS})
target_compile_options(decomp PRIVATE ${LIBDECOMP_OPTIONS})
add_executable(sleigh_opt ${SLEIGH_COMPILER} ${ZLIB})
target_compile_definitions(sleigh_opt PRIVATE LOCAL_ZLIB ${SLEIGH_DEFINITIONS})
target_link_options(sleigh_opt PRIVATE ${SLEIGH_LINK_OPTIONS})
")

message(STATUS "Building Ghidra ${GHIDRA_VERSION} with ${CXX} in ${WORK}")
quietly(configure "${CMAKE_COMMAND}"
  -G ${GENERATOR}
  -S "${WORK}/project"
  -B "${WORK}/build"
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_C_COMPILER=${CC}
  -DCMAKE_CXX_COMPILER=${CXX})
quietly(build "${CMAKE_COMMAND}" --build "${WORK}/build" --parallel ${JOBS})
quietly(sleigh "${WORK}/build/sleigh_opt${CMAKE_EXECUTABLE_SUFFIX}"
  -a "${WORK}/${GHIDRA_ROOT}/Ghidra")

file(COPY_FILE "${WORK}/build/libdecomp.a" "${OUT}/libdecomp.a")
file(MAKE_DIRECTORY "${OUT}/include/ghidra")
file(GLOB headers "${SRC}/*.h" "${SRC}/*.hh")
file(COPY ${headers} DESTINATION "${OUT}/include/ghidra")
# the headers of the library include the headers of the bundled zlib as
# ../zlib/zlib.h, see compression.hh, so that the stubs don't need the
# zlib of the system, which the mingw-w64 toolchain of Windows lacks
file(MAKE_DIRECTORY "${OUT}/include/zlib")
file(GLOB zlib_headers "${ZLIB_SRC}/*.h")
file(COPY ${zlib_headers} DESTINATION "${OUT}/include/zlib")
file(COPY "${WORK}/${GHIDRA_ROOT}/Ghidra/Processors" DESTINATION "${OUT}")

# dune can't install directories on Windows, where it copies them as
# files, so the specifications are installed there in an archive, which
# the plugin extracts, see plugins/ghidra/ghidra_main.ml
quietly(archive "${CMAKE_COMMAND}" -E chdir "${WORK}/${GHIDRA_ROOT}/Ghidra"
  "${CMAKE_COMMAND}" -E tar cf "${OUT}/Processors.zip" --format=zip
  Processors)

# writes the list of flags as an s-expression for dune's :include
function(write_flags file)
  set(sexp "(")
  foreach(flag ${ARGN})
    string(REPLACE "\\" "/" flag "${flag}")
    string(APPEND sexp " \"${flag}\"")
  endforeach()
  file(WRITE "${OUT}/${file}" "${sexp})\n")
endfunction()

if(CMAKE_HOST_WIN32)
  # the stubs call the functions of the program, e.g., of the runtime of
  # OCaml and of the disassembler of BAP, which flexdll can't relocate
  # when the plugin is further than 2 GB from it, as the calls are
  # relative, so they are absolute in the large model
  write_flags(c.flags -mcmodel=large)
else()
  write_flags(c.flags)
endif()
# the runtime of C++ is linked with the flags of
# lib/bap_disasm/config/cxx_runtime.ml
write_flags(link.flags -L${LINK_PREFIX} -ldecomp)

file(REMOVE_RECURSE "${WORK}")
