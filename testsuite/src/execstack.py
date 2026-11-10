#!/usr/bin/env python3
# Marks the PT_GNU_STACK of an ELF64 little-endian file executable, as `-z execstack` would have: execstack.py FILE
import struct, sys
data = bytearray(open(sys.argv[1], 'rb').read())
offset = struct.unpack_from('<Q', data, 0x20)[0]
size, count = struct.unpack_from('<HH', data, 0x36)
for index in range(count):
    at = offset + index * size
    kind, flags = struct.unpack_from('<II', data, at)
    if kind == 0x6474e551:
        struct.pack_into('<I', data, at + 4, flags | 1)
open(sys.argv[1], 'wb').write(data)
