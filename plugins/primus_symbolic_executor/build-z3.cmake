# Builds the static Z3 library and the sources of its OCaml bindings.
#
# usage: cmake -DSRC=<z3> -DOUT=<dir> -DLINK_PREFIX=<path> [-DCC=<cc>]
#              [-DCXX=<c++>] [-DJOBS=<n>] -P build-z3.cmake
#
# Produces in OUT:
#   lib/libz3.a - the static Z3 library
#   include/    - the headers of the C API of Z3
#   ml/         - the sources of the OCaml bindings and their C stubs
#   c.flags     - the flags of the C stubs of the bindings
#   link.flags  - the flags that link the bindings, with OUT as LINK_PREFIX,
#                 the path of OUT relative to the root of the build context
#
# SRC is the checkout of Z3 (the git submodule), which isn't modified, as
# Z3 is built in a temporary directory with its CMake build, which, unlike
# its scripts/mk_make.py, builds with the mingw-w64 toolchain on Windows.
#
# CC and CXX are the commands of the C and C++ compilers, e.g., the
# %{cc} and %{cxx} of dune, whose flags are ignored, so that Z3 is built
# with the compilers of OCaml. The build uses Ninja if it is installed,
# otherwise make, except on Windows, where it needs Ninja.

cmake_minimum_required(VERSION 3.21)

foreach(var SRC OUT LINK_PREFIX)
  if(NOT ${var})
    message(FATAL_ERROR "build-z3.cmake: ${var} is not specified")
  endif()
endforeach()
get_filename_component(SRC "${SRC}" ABSOLUTE)
get_filename_component(OUT "${OUT}" ABSOLUTE)

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
set(WORK "${TMP}/bap-z3-${SUFFIX}")
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
    fail("${name} of Z3 failed (${status}):\n${tail}")
  endif()
endfunction()

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
  fail("building Z3 on Windows requires Ninja")
else()
  set(GENERATOR "Unix Makefiles")
endif()

# Z3 generates its sources, and the bindings, with Python, which is the
# path of its interpreter, as the python3 of Windows may be the alias of
# the Microsoft Store, which the build tools can't run
set(PYTHON)
foreach(name python3 python py)
  find_program(PYTHON_${name} ${name})
  if(PYTHON_${name} AND NOT PYTHON)
    execute_process(
      COMMAND "${PYTHON_${name}}" -c
        "import sys; assert sys.version_info >= (3, 6); print(sys.executable)"
      RESULT_VARIABLE status OUTPUT_VARIABLE path
      OUTPUT_STRIP_TRAILING_WHITESPACE ERROR_QUIET)
    if(status EQUAL 0 AND EXISTS "${path}")
      file(TO_CMAKE_PATH "${path}" PYTHON)
    endif()
  endif()
endforeach()
if(NOT PYTHON)
  fail("building Z3 requires Python 3.6 or newer")
endif()

set(CONFIGURE
  -G ${GENERATOR}
  -S "${SRC}"
  -B "${WORK}/build"
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_C_COMPILER=${CC}
  -DCMAKE_CXX_COMPILER=${CXX}
  "-DPython3_EXECUTABLE=${PYTHON}"
  # the static library, which is linked into the plugin
  -DZ3_BUILD_LIBZ3_SHARED=OFF
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON
  -DZ3_BUILD_EXECUTABLE=OFF
  -DZ3_BUILD_TEST_EXECUTABLES=OFF
  -DZ3_ENABLE_EXAMPLE_TARGETS=OFF
  -DZ3_BUILD_DOCUMENTATION=OFF
  # the checkout of the submodule may be shallow, or have no git at all
  -DZ3_INCLUDE_GIT_HASH=OFF
  -DZ3_INCLUDE_GIT_DESCRIBE=OFF)

message(STATUS "Building Z3 with ${CXX} in ${WORK}")
quietly(configure "${CMAKE_COMMAND}" ${CONFIGURE})
quietly(build "${CMAKE_COMMAND}" --build "${WORK}/build"
  --target libz3 --parallel ${JOBS})

file(REMOVE_RECURSE "${OUT}")
file(MAKE_DIRECTORY "${OUT}/lib" "${OUT}/include" "${OUT}/ml")

file(GLOB library "${WORK}/build/libz3${CMAKE_STATIC_LIBRARY_SUFFIX}"
  "${WORK}/build/libz3.a")
if(NOT library)
  fail("the build of Z3 has no static library in ${WORK}/build")
endif()
list(GET library 0 library)
file(COPY_FILE "${library}" "${OUT}/lib/libz3.a")
file(GLOB headers "${SRC}/src/api/z3*.h")
file(COPY ${headers} DESTINATION "${OUT}/include" FOLLOW_SYMLINK_CHAIN)

# the bindings, as the OCaml bindings of the CMake build of Z3 require
# ocamlfind and install them with it, see src/api/ml/CMakeLists.txt
set(API z3_api.h z3_ast_containers.h z3_algebraic.h z3_polynomial.h
  z3_rcf.h z3_fixedpoint.h z3_optimization.h z3_fpa.h z3_spacer.h)
list(TRANSFORM API PREPEND "${SRC}/src/api/")
quietly(bindings "${PYTHON}" "${SRC}/scripts/update_api.py" ${API}
  --ml-src-dir "${SRC}/src/api/ml" --ml-output-dir "${OUT}/ml")
quietly(enums "${PYTHON}" "${SRC}/scripts/mk_consts_files.py" ${API}
  --ml-output-dir "${OUT}/ml")
file(COPY
  "${SRC}/src/api/ml/z3.ml"
  "${SRC}/src/api/ml/z3.mli"
  "${SRC}/src/api/ml/z3native_stubs.h"
  DESTINATION "${OUT}/ml" FOLLOW_SYMLINK_CHAIN)

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
  # the stubs call the runtime of OCaml in the program, which flexdll
  # can't relocate when the plugin is further than 2 GB from it, as the
  # calls are relative, so they are absolute in the large model
  write_flags(c.flags -mcmodel=large)
else()
  write_flags(c.flags)
endif()
# the runtime of C++ is linked with the flags of
# lib/bap_disasm/config/cxx_runtime.ml
write_flags(link.flags -L${LINK_PREFIX}/lib -lz3)

file(REMOVE_RECURSE "${WORK}")
