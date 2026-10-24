# The changes of BAP to Unicorn

The files of this folder replace the files of the sources of Unicorn,
whose version and checksum are in `../build.cmake`, at the same paths,
before it is built. They are the originals of that version with the
changes below, each marked with a `BAP:` comment. When the version of
Unicorn changes, the changes are merged into its new files, e.g., with

    diff -ru unicorn-OLD unicorn-OLD-with-overlay > bap.diff
    cd unicorn-NEW && patch -p1 < ../bap.diff

and the files of the new version, with the changes, replace these. The
fixes of the platforms, e.g., of Windows, and the changes of the files,
that are too large to keep, e.g., the translators of QEMU, of about a
megabyte, are the patches of `build.cmake`.

## The exits after the accesses of the memory

`qemu/tcg/tcg-op.c`, `qemu/accel/tcg/tcg-runtime.c`

After each memory access, Unicorn exits, if an exit is requested, and
restores the instruction of the access, so that it runs again, when the
emulation continues, which repeats a store, e.g., when `uc_emu_stop` is
called from another thread, e.g., by the timeout of Unicorn, or by the
watcher of the signals of the plugin. The check after an access, which
sets the high bit of its argument, exits only if the access was invalid,
and the other requests exit at the next check, e.g., at the start of the
next block, at its address.

## The stops from the other threads

`qemu/softmmu/cpus.c`

The stop, that `uc_emu_stop` requests in another thread, e.g., by the
timeout of Unicorn, whose thread starts before the CPU is resumed, sets
the exit request of the CPU, which the resume, and the continuation
after a quit request, reset, after they checked the stop, so that the
stop was lost, and the emulation, that nothing else stopped, ran
forever, e.g., a thread, whose slice ended, while it spun on a lock of
another thread. The CPU exits again, if the stop was requested, after
the exit request is reset. The short timeouts, e.g., at the ends of the
slices, on Windows, whose `usleep` of the timer doesn't sleep, lost it
often.

## The stores of the helpers

`qemu/accel/tcg/cputlb.c`

The store to the memory, that is not mapped, or not writable, which the
hooks don't handle, exits at its instruction, which runs again, as the
loads do, rather than dropping the store, as the instruction, whose
store is in a helper, e.g., `fstpt` of x86, or `stvewx` of PowerPC,
would complete without it. The stores of MIPS, which are not in
helpers, exit after the access, as the branch, whose delay slot it is,
must not run again.

## The delay slots of MIPS

`qemu/target/mips/unicorn.c`

The PC, that is written, starts anew, outside of a delay slot, as the
branch, whose delay slot it was, e.g., of another thread, that ran, is
not pending, while `uc_emu_start` keeps it, so that the emulation, that
stopped in a delay slot, continues there.

## XER of PowerPC

`qemu/target/ppc/unicorn.c`

SO, OV, and CA of XER are the fields of their own of QEMU, which are
merged, as `cpu_read_xer` and `cpu_write_xer` do, so that the carry,
e.g., of `adde`, is the one of the register, that is written. They are
merged in place, as those functions of the 32-bit and of the 64-bit
targets have the same names, so that one target would call the other's.

## The conversions of PowerPC to the integers

`qemu/target/ppc/fpu_helper.c`

The conversions, e.g., `fctiwz`, saturate, as softfloat does, and as the
Power ISA tells, and only the NaNs are the values of the invalid
conversions, rather than every invalid conversion.

## The PC-relative instructions of MIPS

`qemu/target/mips/translate.c`, a patch of `build.cmake`

The instructions of the release 6, `addiupc`, `auipc`, `aluipc`,
`lwpc`, `lwupc`, and `ldpc`, raised the reserved instruction, as the
switches of `gen_pcrel` were on the masks of `unsigned long`, while
the opcodes of their cases are the negative `int`s, e.g., `0x3B << 26`,
which differ, when they are converted to it. The switches are on the
32 bits.

## The single floats of RISC-V

`qemu/target/riscv/fpu_helper.c`,
`qemu/target/riscv/insn_trans/trans_rvf.inc.c`

The single floats are NaN-boxed, as RISC-V tells, and as the later
versions of QEMU do: the operations of the single floats read the value
of a register, whose upper 32 bits are not all ones, as the canonical
NaN, and set them in their results, e.g., of `fadd.s`, `fcvt.s.d`, or
`fmv.w.x`, and the sign of `fneg.s`, `fabs.s`, and `fsgnjx.s` is the
bit 31, rather than `INT32_MIN`, whose upper bits are ones, too, which
changed them.
