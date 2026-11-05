# Building and testing BAP in Lean. `just` alone lists what there is.

# What there is
default:
    @just --list

# The first build: fetches LLVM and Z3 and builds them into _deps (which takes a while), then the native code and all of the Lean
setup:
    python3 native/build-static.py

# The C++ of native/ again, after a change to it, linked into every executable (Lake doesn't see it change by itself)
native:
    python3 native/build-static.py --objects

# The library, the proofs and the executables
build:
    lake build

# The test suite
test: build
    .lake/build/bin/bap-tests

# Builds and runs the test suite
all: build test

# Each instruction of TARGETs on the machine or qemu-user and through the lifter, compared: `just difftest x86_64`, see tools/difftest/difftest.py
difftest *args:
    lake build bap-difftest
    python3 tools/difftest/difftest.py {{args}}

# The opcodes of each target that decode and lift, see tools/smoke.py
smoke *args:
    lake build bap-smoke
    python3 tools/smoke.py {{args}}

# What Lake built, but not LLVM and Z3 in _deps
clean:
    lake clean
