#!/usr/bin/env python3
# Makes a program of x86_64 whose interpreter is bigger than 252 KiB, as musl's libc.so is when it is the interpreter: a program that does
# nothing, and an interpreter of one segment of 1 MiB that says so and exits, which Linux runs as the program starts (testBigInterpreter).
#   make.py OUTPUT-DIRECTORY [INTERPRETER-PATH]
# which writes ld-big.so and big-interp there; the test has them as testsuite/bin/x86_64-linux-ld-big, as .so is ignored, and
# testsuite/bin/x86_64-linux-big-interp.
import struct, sys

def elf(kind, entry, segments, interp=None):
    # One ELF64 of x86_64: its program headers, an interpreter if it has one, and its segments of (vaddr, bytes, memsz, flags).
    count = len(segments) + (1 if interp else 0)
    header = 64
    table = header + 56 * count
    body = bytearray()
    entries = []
    offset = (table + 0xfff) & ~0xfff
    blobs = []
    if interp:
        prelude = interp.encode() + b'\0'
        # The path comes right after the program headers.
        entries.append((3, 4, table, 0, 0, len(prelude), len(prelude), 1))
    else:
        prelude = b''
    for vaddr, data, memsz, flags in segments:
        entries.append((1, flags, offset, vaddr, vaddr, len(data), memsz, 0x1000))
        blobs.append((offset, data))
        offset = (offset + len(data) + 0xfff) & ~0xfff
    out = bytearray(b'\x7fELF' + bytes([2, 1, 1, 0]) + bytes(8))
    out += struct.pack('<HHIQQQIHHHHHH', kind, 62, 1, entry, header, 0, 0, header, 56, count, 64, 0, 0)
    for entry_ in entries:
        out += struct.pack('<IIQQQQQQ', *entry_)
    out += prelude
    for at, data in blobs:
        out += bytes(at - len(out)) + data
    return bytes(out)

message = b'the interpreter ran\n'
# lea rsi, [rip + message]; mov edi, 1; mov edx, len; mov eax, 1; syscall; mov edi, 0; mov eax, 231; syscall; message
code = bytearray()
code += b'\x48\x8d\x35' + struct.pack('<i', 0)  # patched below
code += b'\xbf\x01\x00\x00\x00' + b'\xba' + struct.pack('<I', len(message)) + b'\xb8\x01\x00\x00\x00' + b'\x0f\x05'
code += b'\xbf\x00\x00\x00\x00' + b'\xb8\xe7\x00\x00\x00' + b'\x0f\x05'
code[3:7] = struct.pack('<i', len(code) - 7)
code += message
interpreter = elf(3, 0, [(0, bytes(code), 1 << 20, 5)])
program = elf(2, 0x400000, [(0x400000, b'\xf4', 1, 5)], interp=sys.argv[2] if len(sys.argv) > 2 else '/lib/ld-big.so')
open(sys.argv[1] + '/ld-big.so', 'wb').write(interpreter)
open(sys.argv[1] + '/big-interp', 'wb').write(program)
