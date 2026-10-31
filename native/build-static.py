#!/usr/bin/env python3
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
NATIVE = ROOT / "native"
BUILD = NATIVE / "build"
DEPS = ROOT / "_deps"
WINDOWS = os.name == "nt"
JOBS = int(os.environ.get("JOBS", os.cpu_count() or 1))
LLVM_VERSION = "23.1.4"
Z3_VERSION = "4.13.0"
LLVM_SOURCE = DEPS / "src" / f"llvm-project-llvmorg-{LLVM_VERSION}"
Z3_SOURCE = DEPS / "src" / f"z3-z3-{Z3_VERSION}"
LLVM_BUILD = DEPS / f"llvm-{LLVM_VERSION}-pic-build"
Z3_BUILD = DEPS / "z3-pic-build"
Z3_INSTALL = DEPS / "z3-pic"
LLVM_INSTALL = DEPS / f"llvm-{LLVM_VERSION}-pic"
# Lean links with its own MinGW sysroot, which has only part of what LLVM imports.
WINDOWS_IMPORT_LIBRARIES = ["psapi", "shell32", "ole32", "uuid", "advapi32", "ws2_32", "ntdll",
                            "version"]


def run(args, *, env=None):
    command = [os.fspath(arg) for arg in args]
    print("+", shlex.join(command), flush=True)
    subprocess.run(command, cwd=ROOT, env=env, check=True)


def tool(name, fallback):
    path = os.environ.get(name) or shutil.which(fallback)
    if not path:
        raise RuntimeError(f"required tool not found: {fallback}")
    return path


def fetch_source(url, archive, source, directories=None):
    if source.is_dir():
        return
    if not archive.exists():
        urllib.request.urlretrieve(url, archive)
    with tarfile.open(archive) as contents:
        members = contents.getmembers()
        if directories is not None:
            members = [member for member in members
                       if member.name.partition("/")[2].partition("/")[0] in directories]
        contents.extractall(DEPS / "src", members=members)


def patch_z3():
    replacements = {
        "src/math/lp/static_matrix.h": [
            ("v.m_matrix.get(v.m_row, v.m_col)", "v.m_matrix.get_elem(v.m_row, v.m_col)")
        ],
        "src/math/lp/column_info.h": [("c.m_low_bound", "c.m_lower_bound")],
        "src/math/lp/static_matrix_def.h": [
            ("A.get_value_of_column_cell(col)", "A.get_val(col)")
        ],
    }
    for relative, edits in replacements.items():
        path = Z3_SOURCE / relative
        original = path.read_text()
        text = original
        for old, new in edits:
            text = text.replace(old, new)
        if text != original:
            path.write_text(text)


def quote(value):
    return f'"{value}"'


def ensure_libcxx_headers(cmake, cxx_include):
    """Generates the libc++ headers from the LLVM sources, if nothing provides them."""
    if WINDOWS or (cxx_include / "cstddef").exists():
        return
    if "BAP_LIBCXX_INCLUDE" in os.environ:
        raise RuntimeError(f"no libc++ headers in BAP_LIBCXX_INCLUDE={cxx_include}")
    build = DEPS / "libcxx-headers-build"
    env = os.environ.copy()
    env.setdefault("CC", "clang")
    env.setdefault("CXX", "clang++")
    run([cmake, "-S", LLVM_SOURCE / "runtimes", "-B", build, "-G", "Ninja",
         "-DLLVM_ENABLE_RUNTIMES=libcxx", "-DLIBCXX_CXX_ABI=none",
         "-DLIBCXX_INCLUDE_TESTS=OFF", "-DLIBCXX_INCLUDE_BENCHMARKS=OFF",
         "-DLLVM_INCLUDE_TESTS=OFF", f"-DCMAKE_INSTALL_PREFIX={DEPS / 'sysroot' / 'usr'}"], env=env)
    run([cmake, "--build", build, "--target", "install-cxx-headers"])


def posix(path):
    return Path(path).as_posix()


def copy_import_libraries(cxx, lean_prefix):
    for name in WINDOWS_IMPORT_LIBRARIES:
        library = f"lib{name}.a"
        if (lean_prefix / "lib" / library).exists():
            continue
        found = Path(subprocess.check_output(
            [cxx, f"-print-file-name={library}"], text=True).strip())
        if not found.is_absolute() or not found.exists():
            raise RuntimeError(f"import library not found: {library}")
        shutil.copy2(found, BUILD / library)


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    (DEPS / "src").mkdir(parents=True, exist_ok=True)
    lean = tool("LEAN", "lean")
    lake = tool("LAKE", "lake")
    cmake = tool("CMAKE", "cmake")
    cxx = tool("CXX", "clang++")
    ar = os.environ.get("AR") or shutil.which("llvm-ar") or shutil.which("ar")
    if not ar:
        raise RuntimeError("required tool not found: llvm-ar or ar")
    lean_prefix = Path(subprocess.check_output(
        [lean, "--print-prefix"], text=True).strip())
    cxx_include = Path(os.environ.get(
        "BAP_LIBCXX_INCLUDE", DEPS / "sysroot" / "usr" / "include" / "c++" / "v1"))

    fetch_source(
        f"https://github.com/llvm/llvm-project/archive/refs/tags/llvmorg-{LLVM_VERSION}.tar.gz",
        DEPS / f"llvmorg-{LLVM_VERSION}.tar.gz", LLVM_SOURCE,
        directories={"llvm", "cmake", "libc", "third-party"} if WINDOWS else None)
    fetch_source(
        f"https://github.com/Z3Prover/z3/archive/refs/tags/z3-{Z3_VERSION}.tar.gz",
        DEPS / f"z3-{Z3_VERSION}.tar.gz", Z3_SOURCE)
    patch_z3()
    ensure_libcxx_headers(cmake, cxx_include)

    cmake_env = os.environ.copy()
    cmake_env.setdefault("CC", "clang")
    cmake_env.setdefault("CXX", "clang++")
    cxx_flags = []
    exe_link_flags = []
    if not WINDOWS:
        cxx_flags = ["-nostdinc++", "-include", quote(NATIVE / "glibc-compat.h"),
                     f"-I{quote(cxx_include)}"]
        exe_link_flags = ["-stdlib=libc++", f"-L{quote(lean_prefix / 'lib')}",
                          f"-Wl,-rpath,{quote(lean_prefix / 'lib')}"]

    run([cmake, "-S", Z3_SOURCE, "-B", Z3_BUILD, "-G", "Ninja",
         "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_POSITION_INDEPENDENT_CODE=ON",
         f"-DCMAKE_INSTALL_PREFIX={posix(Z3_INSTALL)}",
         f"-DCMAKE_CXX_FLAGS={' '.join(cxx_flags)}",
         f"-DCMAKE_EXE_LINKER_FLAGS={' '.join(exe_link_flags)}",
         "-DZ3_BUILD_LIBZ3_SHARED=OFF", "-DZ3_BUILD_EXECUTABLE=OFF",
         "-DZ3_BUILD_TEST_EXECUTABLES=OFF", "-DZ3_USE_LIB_GMP=OFF",
         "-DZ3_THREAD_SAFE=OFF"], env=cmake_env)
    run([cmake, "--build", Z3_BUILD, "--target", "install", "-j", str(JOBS)])

    llvm_options = [
        "-DLLVM_TARGETS_TO_BUILD=X86;AArch64;ARM;RISCV;Mips;PowerPC;SystemZ;Sparc",
        "-DLLVM_INCLUDE_TESTS=OFF", "-DLLVM_INCLUDE_TOOLS=OFF",
        "-DLLVM_INCLUDE_EXAMPLES=OFF", "-DLLVM_INCLUDE_BENCHMARKS=OFF",
        "-DLLVM_ENABLE_LIBCXX=OFF", "-DLLVM_ENABLE_ZLIB=OFF",
        "-DLLVM_ENABLE_ZSTD=OFF", "-DLLVM_ENABLE_LIBXML2=OFF",
        "-DLLVM_ENABLE_TERMINFO=OFF",
    ]
    if not WINDOWS:
        llvm_options += ["-DCMAKE_REQUIRED_LIBRARIES=unwind", "-DHAVE_MALLINFO2=OFF", "-DHAVE_MALLINFO=OFF",
                         "-DHAVE_DECL_ARC4RANDOM=0"]
    run([cmake, "-S", LLVM_SOURCE / "llvm", "-B", LLVM_BUILD, "-G", "Ninja",
         "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_POSITION_INDEPENDENT_CODE=ON",
         f"-DCMAKE_INSTALL_PREFIX={posix(LLVM_INSTALL)}",
         f"-DCMAKE_CXX_FLAGS={' '.join(cxx_flags)}",
         f"-DCMAKE_EXE_LINKER_FLAGS={' '.join(exe_link_flags)}",
         *llvm_options], env=cmake_env)
    run([cmake, "--build", LLVM_BUILD, "-j", str(JOBS)])

    native_flags = ["-std=c++17", "-O2", "-Wall", "-Wextra", "-Werror"]
    if not WINDOWS:
        native_flags += ["-fPIC", "-nostdinc++", f"-I{cxx_include}"]
    native_flags.append(f"-I{lean_prefix / 'include'}")
    llvm_includes = [f"-I{LLVM_BUILD / 'include'}", f"-I{LLVM_SOURCE / 'llvm' / 'include'}"]
    objects = {}
    for name, includes in [
        ("bap_llvm", llvm_includes),
        ("bap_jit", llvm_includes),
        ("bap_z3", [f"-I{Z3_INSTALL / 'include'}"]),
    ]:
        output = BUILD / f"{name}.o"
        run([cxx, *native_flags, *includes, "-c", NATIVE / f"{name}.cpp", "-o", output])
        objects[name] = output

    llvm_archive = BUILD / "libbap_llvm.a"
    z3_archive = BUILD / "libbap_z3.a"
    run([ar, "rcs", llvm_archive, objects["bap_llvm"], objects["bap_jit"]])
    run([ar, "rcs", z3_archive, objects["bap_z3"]])

    z3_candidates = [Z3_INSTALL / "lib64" / "libz3.a", Z3_INSTALL / "lib" / "libz3.a"]
    z3_library = next((path for path in z3_candidates if path.exists()), None)
    if z3_library is None:
        raise RuntimeError("installed static Z3 library not found")
    llvm_libraries = sorted((LLVM_BUILD / "lib").glob("libLLVM*.a"))
    if not llvm_libraries:
        raise RuntimeError("static LLVM libraries not found")

    link_args = [f"-L{quote(posix(path))}" for path in
                 [BUILD, LLVM_BUILD / "lib", z3_library.parent]]
    link_args += ["-lbap_llvm", "-lbap_z3", "-lz3", "-Wl,--start-group"]
    link_args += [f"-l{path.stem.removeprefix('lib')}" for path in llvm_libraries]
    link_args.append("-Wl,--end-group")
    if WINDOWS:
        copy_import_libraries(cxx, lean_prefix)
        link_args += [f"-l{name}" for name in WINDOWS_IMPORT_LIBRARIES]
    else:
        link_args += ["-lm", "-ldl", "-lpthread", "-lrt"]
    (NATIVE / "static-link.rsp").write_text("\n".join(link_args) + "\n")

    executable_suffix = ".exe" if WINDOWS else ""
    for name in ["bap", "bap-tests"]:
        (ROOT / ".lake" / "build" / "bin" / f"{name}{executable_suffix}").unlink(missing_ok=True)
    lean_env = os.environ.copy()
    lean_env["LEAN_NUM_THREADS"] = str(JOBS)
    run([lake, "build"], env=lean_env)


if __name__ == "__main__":
    try:
        main()
    except (subprocess.CalledProcessError, RuntimeError) as error:
        print(f"build failed: {error}", file=sys.stderr)
        sys.exit(1)
