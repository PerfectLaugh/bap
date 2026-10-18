# Builds the LLVM libraries that the LLVM backend of BAP links.
#
# usage: cmake -DOUT=<dir> [-DTARBALL=<file>] [-DCC=<cc>] [-DCXX=<c++>]
#              [-DJOBS=<n>] -P build.cmake
#
# Installs into OUT:
#   bin/llvm-config - reports the flags to compile and link with LLVM
#   include/        - the LLVM headers
#   lib/            - the static LLVM libraries
#
# The LLVM sources are taken from TARBALL, if it is specified (e.g., when
# opam has already fetched it as an extra-source), otherwise they are
# downloaded from GitHub. In both cases the checksum is verified.
#
# CC and CXX are the commands of the C and C++ compilers, e.g., the
# %{cc} and %{cxx} of dune, whose flags are ignored, so that LLVM is
# built with the compilers of OCaml. The build uses Ninja if it is
# installed, otherwise make, except on Windows, where it needs Ninja.
#
# It is a CMake script, not a shell script, as building LLVM requires
# CMake anyway, which downloads, verifies, and extracts the sources the
# same way on every system, including Windows, which has no POSIX shell.

cmake_minimum_required(VERSION 3.20)

set(LLVM_VERSION 23.1.3)
set(LLVM_SHA256
  c44186a7762ed28954be72e5ff6df9808e0779d4f1bf014ecc4e7e211d31ee34)
set(LLVM_ROOT llvm-project-${LLVM_VERSION}.src)
set(LLVM_URL
  https://github.com/llvm/llvm-project/releases/download/llvmorg-${LLVM_VERSION}/${LLVM_ROOT}.tar.xz)

# the targets of the architectures that BAP lifts
set(LLVM_TARGETS AArch64 ARM Mips PowerPC RISCV SystemZ X86)

if(NOT OUT)
  message(FATAL_ERROR "build.cmake: OUT is not specified")
endif()
get_filename_component(OUT "${OUT}" ABSOLUTE)

if(NOT JOBS)
  cmake_host_system_information(RESULT JOBS QUERY NUMBER_OF_LOGICAL_CORES)
endif()

# the build directory is outside of the dune tree, as its paths are
# long, and the build of LLVM has paths too long for Windows inside it
if(CMAKE_HOST_WIN32)
  file(TO_CMAKE_PATH "$ENV{TEMP}" TMP)
elseif(DEFINED ENV{TMPDIR})
  set(TMP "$ENV{TMPDIR}")
else()
  set(TMP /tmp)
endif()
string(RANDOM LENGTH 8 SUFFIX)
set(WORK "${TMP}/bap-llvm-${SUFFIX}")
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
    fail("${name} of LLVM failed (${status}):\n${tail}")
  endif()
endfunction()

if(TARBALL)
  file(SHA256 "${TARBALL}" sum)
  if(NOT sum STREQUAL LLVM_SHA256)
    fail("checksum mismatch for ${TARBALL}: got ${sum}")
  endif()
else()
  set(TARBALL "${WORK}/${LLVM_ROOT}.tar.xz")
  file(DOWNLOAD "${LLVM_URL}" "${TARBALL}"
    EXPECTED_HASH SHA256=${LLVM_SHA256}
    TLS_VERIFY ON
    STATUS status)
  list(GET status 0 code)
  if(NOT code EQUAL 0)
    fail("failed to download ${LLVM_URL}: ${status}")
  endif()
endif()

# llvm/utils/mlgo-utils has symbolic links, which are skipped on Windows
# with a warning, but the build doesn't need them. LLVM includes the
# common headers of libc, so it is extracted too
file(ARCHIVE_EXTRACT
  INPUT "${TARBALL}"
  DESTINATION "${WORK}"
  PATTERNS
    ${LLVM_ROOT}/cmake
    ${LLVM_ROOT}/libc
    ${LLVM_ROOT}/llvm
    ${LLVM_ROOT}/third-party)

if(CMAKE_HOST_WIN32)
  # the compilers of the mingw-w64 toolchain of opam are Cygwin programs,
  # which split the command line of Windows, and expand the response
  # files, differently, so the quotes of the string of the definition
  # CMAKE_CFG_INTDIR="Release" of llvm-config merge its arguments. The
  # definition is only used when llvm-config runs in the build tree, and
  # llvm-config.cpp checks that it is defined, so it is removed
  set(file "${WORK}/${LLVM_ROOT}/llvm/tools/llvm-config/CMakeLists.txt")
  file(READ "${file}" text)
  set(definition [[add_compile_definitions(CMAKE_CFG_INTDIR="$<CONFIG>")]])
  string(FIND "${text}" "${definition}" found)
  if(found EQUAL -1)
    fail("${file} doesn't have ${definition}")
  endif()
  string(REPLACE "${definition}" "" text "${text}")
  file(WRITE "${file}" "${text}")
endif()

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
  fail("building LLVM on Windows requires Ninja")
else()
  set(GENERATOR "Unix Makefiles")
endif()

# the lists are passed in an initial cache, as their semicolons would
# split them into several arguments of the commands
set(INITIAL_CACHE "${WORK}/cache.cmake")
file(WRITE "${INITIAL_CACHE}"
  "set(LLVM_TARGETS_TO_BUILD \"${LLVM_TARGETS}\" CACHE STRING \"\")\n")

set(CONFIGURE
  -G ${GENERATOR}
  -C "${INITIAL_CACHE}"
  -S "${WORK}/${LLVM_ROOT}/llvm"
  -B "${WORK}/build"
  -DCMAKE_BUILD_TYPE=Release
  "-DCMAKE_INSTALL_PREFIX=${OUT}"
  -DCMAKE_C_COMPILER=${CC}
  -DCMAKE_CXX_COMPILER=${CXX}
  # the static libraries, which are linked into the plugin
  -DLLVM_ENABLE_PIC=ON
  -DLLVM_BUILD_LLVM_DYLIB=OFF
  -DLLVM_LINK_LLVM_DYLIB=OFF
  # the tools must be enabled to install llvm-config, but only it, the
  # headers, and the libraries are built and installed, see below
  -DLLVM_BUILD_TOOLS=ON
  # the shared libraries that install-llvm-libraries installs too
  -DLLVM_TOOL_LTO_BUILD=OFF
  -DLLVM_TOOL_REMARKS_SHLIB_BUILD=OFF
  -DLLVM_INCLUDE_TESTS=OFF
  -DLLVM_INCLUDE_BENCHMARKS=OFF
  -DLLVM_INCLUDE_EXAMPLES=OFF
  -DLLVM_INCLUDE_DOCS=OFF
  -DLLVM_INCLUDE_UTILS=OFF
  -DLLVM_ENABLE_BINDINGS=OFF
  -DLLVM_ENABLE_ASSERTIONS=OFF
  # no dependencies on the system libraries, so that BAP links only
  # the libraries that it already depends on
  -DLLVM_ENABLE_ZLIB=OFF
  -DLLVM_ENABLE_ZSTD=OFF
  -DLLVM_ENABLE_LIBXML2=OFF
  -DLLVM_ENABLE_LIBEDIT=OFF
  -DLLVM_ENABLE_LIBPFM=OFF
  -DLLVM_ENABLE_CURL=OFF
  -DLLVM_ENABLE_HTTPLIB=OFF
  -DLLVM_PARALLEL_LINK_JOBS=2)

if(CMAKE_HOST_WIN32)
  # the tools that run during the build, e.g., llvm-tblgen, would load
  # the first libstdc++ DLL in PATH, which may be of another version of
  # GCC, so the tools link the runtime of MinGW statically
  list(APPEND CONFIGURE -DCMAKE_EXE_LINKER_FLAGS=-static)
endif()

message(STATUS "Building LLVM ${LLVM_VERSION} with ${CXX} in ${WORK}")
quietly(configure "${CMAKE_COMMAND}" ${CONFIGURE})
quietly(build "${CMAKE_COMMAND}" --build "${WORK}/build"
  --target install-llvm-headers install-llvm-libraries install-llvm-config
  --parallel ${JOBS})

file(REMOVE_RECURSE "${WORK}")
