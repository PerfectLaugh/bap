# Builds the static Unicorn library that the primus-unicorn plugin links.
#
# usage: cmake -DOUT=<dir> [-DTARBALL=<file>] [-DCC=<cc>] [-DJOBS=<n>]
#              -P build.cmake
#
# Installs into OUT:
#   include/unicorn/ - the Unicorn headers
#   lib/libunicorn.a - the library with the engines of the architectures
#                      that BAP lifts
#
# The Unicorn sources are taken from TARBALL, if it is specified (e.g.,
# when opam has already fetched it as an extra-source), otherwise they
# are downloaded from GitHub. In both cases the checksum is verified.
#
# CC is the command of the C compiler, e.g., the %{cc} of dune, whose
# flags are ignored, so that Unicorn is built with the compiler of OCaml.
# The build uses Ninja if it is installed, otherwise make, except on
# Windows, where it needs Ninja.

cmake_minimum_required(VERSION 3.20)

set(UNICORN_VERSION 2.1.4)
set(UNICORN_SHA256
  ea8863f095a0136388694e5a6063afd9bb7650e30243dd6251af59c5ce5601f4)
set(UNICORN_ROOT unicorn-${UNICORN_VERSION})
set(UNICORN_URL
  https://github.com/unicorn-engine/unicorn/archive/refs/tags/${UNICORN_VERSION}.tar.gz)

# the engines of the architectures that BAP lifts
set(UNICORN_ARCHES x86 arm aarch64 mips ppc riscv)

if(NOT OUT)
  message(FATAL_ERROR "build.cmake: OUT is not specified")
endif()
get_filename_component(OUT "${OUT}" ABSOLUTE)

if(NOT JOBS)
  cmake_host_system_information(RESULT JOBS QUERY NUMBER_OF_LOGICAL_CORES)
endif()

# the build directory is outside of the dune tree, as its paths are long
if(CMAKE_HOST_WIN32)
  file(TO_CMAKE_PATH "$ENV{TEMP}" TMP)
elseif(DEFINED ENV{TMPDIR})
  set(TMP "$ENV{TMPDIR}")
else()
  set(TMP /tmp)
endif()
string(RANDOM LENGTH 8 SUFFIX)
set(WORK "${TMP}/bap-unicorn-${SUFFIX}")
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
    fail("${name} of Unicorn failed (${status}):\n${tail}")
  endif()
endfunction()

if(TARBALL)
  file(SHA256 "${TARBALL}" sum)
  if(NOT sum STREQUAL UNICORN_SHA256)
    fail("checksum mismatch for ${TARBALL}: got ${sum}")
  endif()
else()
  set(TARBALL "${WORK}/${UNICORN_ROOT}.tar.gz")
  file(DOWNLOAD "${UNICORN_URL}" "${TARBALL}"
    EXPECTED_HASH SHA256=${UNICORN_SHA256}
    TLS_VERIFY ON
    STATUS status)
  list(GET status 0 code)
  if(NOT code EQUAL 0)
    fail("failed to download ${UNICORN_URL}: ${status}")
  endif()
endif()

file(ARCHIVE_EXTRACT INPUT "${TARBALL}" DESTINATION "${WORK}")

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

# replaces the text in a file of the Unicorn sources, and fails if it is
# not there, e.g., when the version of Unicorn changes
function(patch file text replacement)
  set(path "${WORK}/${UNICORN_ROOT}/${file}")
  file(READ "${path}" contents)
  string(REPLACE "${text}" "${replacement}" patched "${contents}")
  if(patched STREQUAL contents)
    fail("failed to patch ${file} of Unicorn")
  endif()
  file(WRITE "${path}" "${patched}")
endfunction()

if(CMAKE_HOST_WIN32)
  execute_process(COMMAND ${CC} -dumpmachine
    OUTPUT_VARIABLE machine
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  if(NOT machine MATCHES "^x86_64-.*mingw")
    fail("building Unicorn on Windows requires x86_64 mingw-w64, got ${CC}")
  endif()
  # the winpthreads of mingw-w64 no longer defines it, and Windows has no
  # signals to mask
  set(UNICORN_C_FLAGS "-Dpthread_sigmask(how,set,old)=0")
  # the archive is also linked as unicorn.o, which Windows can't do without
  # the privilege of symbolic links, so it is copied there
  patch(cmake/bundle_static.cmake
    "-E create_symlink \"$<TARGET_FILE_NAME:"
    "-E copy \"$<TARGET_FILE:")
  # the CPUs of some targets, e.g., MIPS and RISC-V, are allocated with the
  # alignment of 8, which mingw-w64 honors exactly, but the compiler aligns
  # them to 16, as the allocators of the other systems do, and its SSE
  # stores to them fault
  patch(qemu/util/oslib-posix.c
    "__mingw_aligned_malloc(size, alignment)"
    "__mingw_aligned_malloc(size, alignment < 16 ? 16 : alignment)")
endif()

# After each memory access, Unicorn exits, if an exit is requested, and
# restores the instruction of the access, so that it runs again, when the
# emulation continues, which repeats a store, e.g., when uc_emu_stop is
# called from another thread, e.g., by the timeout of Unicorn, or by the
# watcher of the signals of the plugin. The check after an access exits
# only if the access was invalid, and the other requests exit at the next
# check, e.g., at the start of the next block, at its address.
patch(qemu/tcg/tcg-op.c
  "check_exit_request(tcg_ctx);"
  "check_exit_request_mem(tcg_ctx);")
patch(qemu/tcg/tcg-op.c
  "static void tcg_gen_req_mo(TCGContext *tcg_ctx, TCGBar type)\n"
  [=[// BAP: after a memory access, the emulation exits only if the access
// was invalid, see build.cmake
static void check_exit_request_mem(TCGContext *tcg_ctx)
{
    if (tcg_ctx->uc->no_exit_request) {
        return;
    }

    TCGv_ptr puc = tcg_const_ptr(tcg_ctx, tcg_ctx->uc);
    TCGv_i32 tmp = tcg_const_i32(tcg_ctx, 0);
    if (tcg_ctx->delay_slot_flag != NULL) {
        tcg_gen_mov_i32(tcg_ctx, tmp, tcg_ctx->delay_slot_flag);
    }
    tcg_gen_ori_i32(tcg_ctx, tmp, tmp, 0x80000000);
    gen_helper_check_exit_request(tcg_ctx, puc, tmp);
    tcg_temp_free_i32(tcg_ctx, tmp);
    tcg_temp_free_ptr(tcg_ctx, puc);
}

static void tcg_gen_req_mo(TCGContext *tcg_ctx, TCGBar type)
]=])
# BAP: SO, OV, and CA of XER of PowerPC are the fields of their own of
# QEMU, which are merged, as cpu_read_xer and cpu_write_xer do, so that
# the carry, e.g., of adde, is the one of the register, that is written.
# They are merged here, as the functions of the 32-bit and the 64-bit
# targets have the same names, so that one target may call the other's
patch(qemu/target/ppc/unicorn.c
  "*(uint32_t *)value = env->xer;"
  [=[*(uint32_t *)value =
                env->xer | (env->so << XER_SO) | (env->ov << XER_OV) |
                (env->ca << XER_CA) |
                (is_isa300(env) ? (env->ov32 << XER_OV32) |
                                      (env->ca32 << XER_CA32)
                                : 0);]=])
patch(qemu/target/ppc/unicorn.c
  "env->xer = *(uint32_t *)value;"
  [=[{
                uint32_t xer = *(uint32_t *)value;
                env->so = (xer >> XER_SO) & 1;
                env->ov = (xer >> XER_OV) & 1;
                env->ca = (xer >> XER_CA) & 1;
                env->ov32 = (xer >> XER_OV32) & 1;
                env->ca32 = (xer >> XER_CA32) & 1;
                env->xer = xer & ~((1u << XER_SO) | (1u << XER_OV) |
                                   (1u << XER_CA) | (1u << XER_OV32) |
                                   (1u << XER_CA32));
            }]=])
# BAP: the store to the memory, that is not mapped, or not writable, which
# the hooks don't handle, exits at the instruction, which runs again, as
# the loads do, rather than dropping the store, as the instruction, whose
# store is in a helper, e.g., fstpt of x86, or stvewx of PowerPC, would
# complete without it. The stores of MIPS, which are not in helpers, exit
# after the access, as the branch, whose delay slot it is, must not run
# again, see check_exit_request_mem
patch(qemu/accel/tcg/cputlb.c
  [=[            // printf("***** Invalid memory write at " TARGET_FMT_lx "\n", addr);
            cpu_exit(uc->cpu);
            return;]=]
  [=[            // printf("***** Invalid memory write at " TARGET_FMT_lx "\n", addr);
            cpu_exit(uc->cpu);
            if (uc->nested_level > 0 && !uc->cpu->stopped &&
                uc->arch != UC_ARCH_MIPS) {
                cpu_loop_exit_restore(uc->cpu, retaddr);
            }
            return;]=])
patch(qemu/accel/tcg/cputlb.c
  [=[            // printf("***** Invalid memory write (ro) at " TARGET_FMT_lx "\n", addr);
            cpu_exit(uc->cpu);
            return;]=]
  [=[            // printf("***** Invalid memory write (ro) at " TARGET_FMT_lx "\n", addr);
            cpu_exit(uc->cpu);
            if (uc->nested_level > 0 && !uc->cpu->stopped &&
                uc->arch != UC_ARCH_MIPS) {
                cpu_loop_exit_restore(uc->cpu, retaddr);
            }
            return;]=])
# BAP: the conversions of PowerPC to the integers, e.g., fctiwz, saturate,
# as softfloat does, and as the Power ISA tells, and only the NaNs are the
# values of the invalid conversions, rather than every invalid conversion
patch(qemu/target/ppc/fpu_helper.c
  "            ret = nanval;                                              \\"
  "            ret = float64_is_any_nan(arg) ? nanval : ret;              \\")
# BAP: the PC, that is written, starts anew, outside of a delay slot of
# MIPS, as the branch, whose delay slot it was, e.g., of another thread,
# that ran, is not pending, while uc_emu_start keeps it, so that the
# emulation, that stopped in a delay slot, continues there
patch(qemu/target/mips/unicorn.c
  "            env->active_tc.PC = *(mipsreg_t *)value & ~1ULL;"
  "            env->active_tc.PC = *(mipsreg_t *)value & ~1ULL;
            env->hflags &= ~MIPS_HFLAG_BMASK;")
patch(qemu/accel/tcg/tcg-runtime.c
  "    if (cpu_loop_exit_requested(uc->cpu) && !in_delay_slot) {"
  [=[    // BAP: the high bit marks the check after a memory access, which
    // exits only if the access was invalid, see build.cmake
    bool after_access = in_delay_slot & 0x80000000;
    in_delay_slot &= 0x7fffffff;
    if (cpu_loop_exit_requested(uc->cpu) && !in_delay_slot &&
        (!after_access || uc->invalid_error != UC_ERR_OK)) {]=])

# On Windows, Unicorn generates its configuration headers with the
# configure script of QEMU, which needs a POSIX shell, and when there is
# none it leaves them empty. So after it is configured, we write the
# headers that configure generates for mingw-w64 ourselves. The headers of
# the targets don't depend on the compiler, so they are the ones that
# Unicorn ships for MSVC.
function(write_config_headers)
  file(WRITE "${WORK}/build/config-host.h"
    "#define HOST_X86_64 1\n"
    "#define CONFIG_WIN32 1\n"
    "#define CONFIG_SEM_TIMEDWAIT 1\n"
    "#define CONFIG_TCG 1\n"
    "#define CONFIG_AVX2_OPT 1\n"
    "#define CONFIG_PRAGMA_DIAGNOSTIC_AVAILABLE 1\n"
    "#define CONFIG_CPUID_H 1\n"
    "#define CONFIG_INT128 1\n"
    "#define CONFIG_CMPXCHG128 1\n"
    "#define CONFIG_ATOMIC64 1\n"
    "#define CONFIG_ATTRIBUTE_ALIAS 1\n"
    "#define CONFIG_STATIC_ASSERT 1\n"
    "#define CONFIG_THREAD_SETNAME_BYTHREAD 1\n"
    "#define CONFIG_PTHREAD_SETNAME_NP_W_TID 1\n")
  file(GLOB targets LIST_DIRECTORIES true
    "${WORK}/${UNICORN_ROOT}/msvc/*-softmmu")
  file(COPY ${targets} DESTINATION "${WORK}/build")
endfunction()

find_program(NINJA ninja)
if(NINJA)
  set(GENERATOR Ninja)
elseif(CMAKE_HOST_WIN32)
  fail("building Unicorn on Windows requires Ninja")
else()
  set(GENERATOR "Unix Makefiles")
endif()

# the list is passed in an initial cache, as its semicolons would split
# it into several arguments of the commands
set(INITIAL_CACHE "${WORK}/cache.cmake")
file(WRITE "${INITIAL_CACHE}"
  "set(UNICORN_ARCH \"${UNICORN_ARCHES}\" CACHE STRING \"\")\n")
if(UNICORN_C_FLAGS)
  file(APPEND "${INITIAL_CACHE}"
    "set(CMAKE_C_FLAGS \"${UNICORN_C_FLAGS}\" CACHE STRING \"\")\n")
endif()

set(CONFIGURE
  -G ${GENERATOR}
  -C "${INITIAL_CACHE}"
  -S "${WORK}/${UNICORN_ROOT}"
  -B "${WORK}/build"
  -DCMAKE_BUILD_TYPE=Release
  "-DCMAKE_INSTALL_PREFIX=${OUT}"
  -DCMAKE_INSTALL_LIBDIR=lib
  -DCMAKE_C_COMPILER=${CC}
  # one static archive, which is linked into the plugin, so its code
  # must be position independent
  -DBUILD_SHARED_LIBS=OFF
  -DUNICORN_LEGACY_STATIC_ARCHIVE=ON
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON
  -DUNICORN_BUILD_TESTS=OFF
  -DUNICORN_INSTALL=ON)

message(STATUS "Building Unicorn ${UNICORN_VERSION} with ${CC} in ${WORK}")
quietly(configure "${CMAKE_COMMAND}" ${CONFIGURE})
if(CMAKE_HOST_WIN32)
  write_config_headers()
else()
  # the atomic accesses of 16 bytes are calls to libatomic, which isn't
  # position independent on some systems, e.g., Fedora, so it can't be
  # linked statically into the plugin. The TCG of Unicorn runs on one
  # thread, so they are disabled, and QEMU falls back to cmpxchg16b
  file(READ "${WORK}/build/config-host.h" config)
  string(REPLACE "#define CONFIG_ATOMIC128 1\n" "" config "${config}")
  file(WRITE "${WORK}/build/config-host.h" "${config}")
endif()
quietly(build "${CMAKE_COMMAND}" --build "${WORK}/build" --parallel ${JOBS})
quietly(install "${CMAKE_COMMAND}" --install "${WORK}/build")

file(REMOVE_RECURSE "${WORK}")
