#!/usr/bin/env python3
"""An independent model of the integer behaviour of the x86 instructions that BapTests/LLVM.lean checks in `testX86Rest`.

It computes the results from what the architecture manuals say, on its own integers, and has nothing of the semantics. It
prints the Lean list of the cases. `tools/x86_model.py > cases.txt`, and that goes between the markers of `BapTests/LLVM.lean`.
"""
import random

rng = random.Random(0x5eed)
M = lambda n: (1 << n) - 1


def rnd(bits):
    return rng.getrandbits(bits)


def lanes(value, e, n):
    return [(value >> (e * i)) & M(e) for i in range(n)]


def join(parts, e):
    return sum((p & M(e)) << (e * i) for i, p in enumerate(parts))


def sx(value, e):
    value &= M(e)
    return value - (1 << e) if value >> (e - 1) else value


# the state of the cases, in which RBX is small for XLAT and the operations with it are of its value

ZMM = {n: rnd(512) for n in range(8)}
# equal elements for the intersections to find
for i in (1, 5, 11):
    ZMM[2] = (ZMM[2] & ~(M(32) << (32 * i))) | (((ZMM[3] >> (32 * (i + 2))) & M(32)) << (32 * i))
for i in (0, 3, 6):
    ZMM[2] = (ZMM[2] & ~(M(64) << (64 * i))) | (((ZMM[3] >> (64 * ((i + 1) % 8))) & M(64)) << (64 * i))
K = {1: 0x5a3c96f01e78d2b5, 2: 0, 3: 0xf0f0cc33aa5581c7, 4: 0xffff00ff, 5: 0}
RCX = 0x10
RDX = rnd(64)
RBX = 0x1008
MEM = rnd(1024 * 8)
BASE = 0x1000

# the tiles: 3 rows of 16 bytes in TMM1, TMM2 and TMM3, and 4 rows of 12 and 8 bytes in others
ROWS = [0, 3, 3, 3, 4, 2, 0, 0]
COLS = [0, 16, 16, 16, 12, 8, 0, 0]
CFG = 1 | sum(c << (8 * (16 + 2 * i)) for i, c in enumerate(COLS)) | sum(r << (8 * (48 + i)) for i, r in enumerate(ROWS))
TMM = {}
for n in range(8):
    value = 0
    for r in range(ROWS[n]):
        value |= (rnd(COLS[n] * 8)) << (512 * r)
    TMM[n] = value


def mem(offset, bits):
    return (MEM >> (8 * offset)) & M(bits)


# encodings

def evex(mapping, pp, w, ll, reg, vvvv, rm, opcode, aaa=0, z=0, b=0, imm=(), modrm=None):
    """Registers below 8; `rm` None takes `modrm`, the bytes of memory."""
    p0 = 0xf0 | mapping
    p1 = w << 7 | (~vvvv & 15) << 3 | 4 | pp
    p2 = z << 7 | ll << 5 | b << 4 | 8 | aaa
    rest = [0xc0 | reg << 3 | rm] if rm is not None else [reg << 3 | modrm[0]] + list(modrm[1:])
    return [0x62, p0, p1, p2, opcode] + rest + list(imm)


def vex(mapping, pp, w, l, reg, vvvv, rm, opcode, modrm=None, rex=0xe0):
    b1 = rex | mapping
    b2 = w << 7 | (~vvvv & 15) << 3 | l << 2 | pp
    rest = [0xc0 | reg << 3 | rm] if rm is not None else [reg << 3 | modrm[0]] + list(modrm[1:])
    return [0xc4, b1, b2, opcode] + rest


cases = []


def case(name, encoding, registers=(), flags=(), stored=None):
    cases.append((name, encoding, list(registers), list(flags), stored))


RAX = [0]  # [rax]


# VP2INTERSECT, from the SDM: each bit says whether its lane is equal to any lane of the other

def intersect(e, x, y, n):
    a, b = lanes(x, e, n), lanes(y, e, n)
    return sum(1 << i for i, v in enumerate(a) if v in b), sum(1 << j for j, v in enumerate(b) if v in a)


for (name, e, ll, w, bits) in (("vp2intersectd z", 32, 2, 0, 512), ("vp2intersectq z", 64, 2, 1, 512), ("vp2intersectd y", 32, 1, 0, 256), ("vp2intersectq x", 64, 0, 1, 128)):
    k0, k1 = intersect(e, ZMM[2], ZMM[3], bits // e)
    case(name, evex(2, 3, w, ll, 4, 2, 3, 0x68), [("K4", k0), ("K5", k1)])
k0, k1 = intersect(32, ZMM[2], mem(0, 512), 16)
case("vp2intersectd mem", evex(2, 3, 0, 2, 2, 2, None, 0x68, modrm=RAX), [("K2", k0), ("K3", k1)])
elem = mem(0, 64)
k0, k1 = intersect(64, ZMM[2], join([elem] * 8, 64), 8)
case("vp2intersectq broadcast", evex(2, 3, 1, 2, 2, 2, None, 0x68, b=1, modrm=RAX), [("K2", k0), ("K3", k1)])


# VBMAC, from AMD 69192

def bmac(c, a, b, xor):
    groups = []
    for g in range(len(a) // 16):
        for i in range(16):
            value = c[g * 16 + i]
            for j in range(16):
                bit = (value >> j) & 1
                for k in range(16):
                    row = (a[g * 16 + i] >> k) & 1
                    col = (b[g * 16 + k] >> j) & 1
                    bit = bit ^ (row & col) if xor else bit | (row & col)
                value = (value & ~(1 << j)) | (bit << j)
            groups.append(value)
    return groups


def masked(result, old, k, mode):
    out = []
    for i, value in enumerate(result):
        if mode == 0 or (k >> i) & 1:
            out.append(value)
        else:
            out.append(old[i] if mode == 1 else 0)
    return out


for (name, xor, w) in (("vbmacor", False, 0), ("vbmacxor", True, 1)):
    for (suffix, ll, words) in ((" y", 1, 16), (" z", 2, 32)):
        c, a, b = lanes(ZMM[1], 16, words), lanes(ZMM[2], 16, words), lanes(ZMM[3], 16, words)
        case(name + suffix, evex(6, 0, w, ll, 1, 2, 3, 0x80), [("ZMM1", join(bmac(c, a, b, xor), 16))])
    c, a, b = lanes(ZMM[1], 16, 32), lanes(ZMM[2], 16, 32), lanes(mem(0, 512), 16, 32)
    case(name + " mem", evex(6, 0, w, 2, 1, 2, None, 0x80, modrm=RAX), [("ZMM1", join(bmac(c, a, b, xor), 16))])
    b = [mem(0, 16)] * 32
    case(name + " broadcast", evex(6, 0, w, 2, 1, 2, None, 0x80, b=1, modrm=RAX), [("ZMM1", join(bmac(c, a, b, xor), 16))])
    b = lanes(ZMM[3], 16, 32)
    case(name + " merge", evex(6, 0, w, 2, 1, 2, 3, 0x80, aaa=1), [("ZMM1", join(masked(bmac(c, a, b, xor), c, K[1], 1), 16))])
    case(name + " zero", evex(6, 0, w, 2, 1, 2, 3, 0x80, aaa=1, z=1), [("ZMM1", join(masked(bmac(c, a, b, xor), c, K[1], 2), 16))])


# VMPSADBW, from the SDM: of each 128 bits, with imm[2:0] and then imm[5:3] in turn

def mpsadbw(x, y, field):
    a, b = lanes(x, 8, 16), lanes(y, 8, 16)
    src = field >> 2 & 1
    dst = field & 3
    out = []
    for j in range(8):
        out.append(sum(abs(a[src * 4 + j + t] - b[dst * 4 + t]) for t in range(4)))
    return join(out, 16)


def vmpsadbw(x, y, imm, bits):
    out = 0
    for g in range(bits // 128):
        field = imm & 7 if g % 2 == 0 else (imm >> 3) & 7
        out |= mpsadbw((x >> (128 * g)) & M(128), (y >> (128 * g)) & M(128), field) << (128 * g)
    return out


for (name, ll, bits) in (("vmpsadbw x", 0, 128), ("vmpsadbw y", 1, 256), ("vmpsadbw z", 2, 512)):
    for imm in (0x2d, 0x12):
        case(f"{name} {imm:#x}", evex(3, 2, 0, ll, 1, 2, 3, 0x42, imm=[imm]), [("ZMM1", vmpsadbw(ZMM[2], ZMM[3], imm, bits))])
result = lanes(vmpsadbw(ZMM[2], mem(0, 512), 0x2d, 512), 16, 32)
case("vmpsadbw mem", evex(3, 2, 0, 2, 1, 2, None, 0x42, modrm=RAX, imm=[0x2d]), [("ZMM1", join(result, 16))])
case("vmpsadbw mem merge", evex(3, 2, 0, 2, 1, 2, None, 0x42, modrm=RAX, imm=[0x2d], aaa=3),
     [("ZMM1", join(masked(result, lanes(ZMM[1], 16, 32), K[3], 1), 16))])
case("vmpsadbw mem zero", evex(3, 2, 0, 2, 1, 2, None, 0x42, modrm=RAX, imm=[0x2d], aaa=3, z=1),
     [("ZMM1", join(masked(result, lanes(ZMM[1], 16, 32), K[3], 2), 16))])


# VP4DPWSSD, from the SDM: a block of the four registers that holds zmm2+3, and four dwords of memory

def dp4(dest, block, memory, saturate):
    out = []
    for i in range(16):
        value = sx(dest >> (32 * i), 32)
        for m in range(4):
            t = (ZMM[block + m] >> (32 * i)) & M(32)
            s = (memory >> (32 * m)) & M(32)
            total = sx(t, 16) * sx(s, 16) + sx(t >> 16, 16) * sx(s >> 16, 16)
            value += total
            value = max(-(1 << 31), min((1 << 31) - 1, value)) if saturate else sx(value, 32)
        out.append(value & M(32))
    return out


for (name, op, saturate) in (("vp4dpwssd", 0x52, False), ("vp4dpwssds", 0x53, True)):
    # zmm5 names the block from zmm4, zmm0 ... zmm7 has only four from zmm4
    result = dp4(ZMM[1], 4, mem(0, 128), saturate)
    case(name, evex(2, 3, 0, 2, 1, 5, None, op, modrm=RAX), [("ZMM1", join(result, 32))])
    case(name + " merge", evex(2, 3, 0, 2, 1, 4, None, op, modrm=RAX, aaa=1),
         [("ZMM1", join(masked(result, lanes(ZMM[1], 32, 16), K[1], 1), 32))])
    case(name + " zero", evex(2, 3, 0, 2, 1, 4, None, op, modrm=RAX, aaa=1, z=1),
         [("ZMM1", join(masked(result, lanes(ZMM[1], 32, 16), K[1], 2), 32))])


# CMPCCXADD, from the SDM: the flags of the old memory less the register

def cmp_flags(a, b, bits):
    diff = (a - b) & M(bits)
    return {
        "CF": int(a < b),
        "ZF": int(diff == 0),
        "SF": diff >> (bits - 1),
        "OF": ((a ^ b) & (a ^ diff)) >> (bits - 1),
        "AF": ((a ^ b ^ diff) >> 4) & 1,
        "PF": int(bin(diff & 255).count("1") % 2 == 0),
    }


CONDITIONS = {
    0: lambda f: f["OF"], 1: lambda f: 1 - f["OF"], 2: lambda f: f["CF"], 3: lambda f: 1 - f["CF"], 4: lambda f: f["ZF"], 5: lambda f: 1 - f["ZF"],
    6: lambda f: f["CF"] | f["ZF"], 7: lambda f: 1 - (f["CF"] | f["ZF"]), 8: lambda f: f["SF"], 9: lambda f: 1 - f["SF"], 10: lambda f: f["PF"], 11: lambda f: 1 - f["PF"],
    12: lambda f: f["SF"] ^ f["OF"], 13: lambda f: 1 - (f["SF"] ^ f["OF"]), 14: lambda f: f["ZF"] | (f["SF"] ^ f["OF"]), 15: lambda f: 1 - (f["ZF"] | (f["SF"] ^ f["OF"])),
}

for (bits, w) in ((32, 0), (64, 1)):
    for cc in (4, 5, 2, 3, 12, 15):
        old = mem(0, bits)
        flags = cmp_flags(old, RDX & M(bits), bits)
        new = (old + RCX) & M(bits) if CONDITIONS[cc](flags) else old
        stored = (MEM & M(512) & ~M(bits)) | new
        # cmp<cc>xadd [rax], rdx, rcx: reg RDX, vvvv RCX, the condition is of the opcode
        encoding = vex(2, 1, w, 0, 2, 1, None, 0xe0 + cc, modrm=RAX)
        case(f"cmpccxadd{bits} {cc}", encoding, [("RDX", old)], sorted(flags.items()), stored)
# one that is equal
old = mem(0, 32)


# AMX, from the SDM: LDTILECFG, TILELOADD, TILESTORED, TDPB*

def tile_load(t, stride):
    value = 0
    for r in range(ROWS[t]):
        for c in range(COLS[t]):
            value |= mem(r * stride + c, 8) << (512 * r + 8 * c)
    return value


def tile_dot(d, a, b, sa, sb):
    out = 0
    for m in range(ROWS[d]):
        for n in range(COLS[d] // 4):
            total = (TMM[d] >> (512 * m + 32 * n)) & M(32)
            for k in range(COLS[a] // 4):
                x = (TMM[a] >> (512 * m + 32 * k)) & M(32)
                y = (TMM[b] >> (512 * k + 32 * n)) & M(32)
                for j in range(4):
                    p = (x >> (8 * j)) & 255
                    q = (y >> (8 * j)) & 255
                    total += (sx(p, 8) if sa else p) * (sx(q, 8) if sb else q)
            out |= (total & M(32)) << (512 * m + 32 * n)
    return out


SIB_RAX_RCX = [0x04, 0x08]  # [rax + rcx]
case("ldtilecfg", vex(2, 0, 0, 0, 0, 0, None, 0x49, modrm=RAX), [("TILECFG", mem(0, 512)), ("TMM1", 0), ("TMM7", 0)])
case("sttilecfg", vex(2, 1, 0, 0, 0, 0, None, 0x49, modrm=RAX), [("TILECFG", CFG), ("TMM1", TMM[1])], [], CFG)
case("tilerelease", [0xc4, 0xe2, 0x78, 0x49, 0xc0], [("TILECFG", 0), ("TMM1", 0), ("TMM2", 0), ("TMM7", 0)])
case("tilezero", vex(2, 3, 0, 0, 2, 0, None, 0x49, modrm=[0xc0]), [("TMM2", 0), ("TMM1", TMM[1])])
case("tileloadd", vex(2, 3, 0, 0, 1, 0, None, 0x4b, modrm=SIB_RAX_RCX), [("TMM1", tile_load(1, RCX))])
case("tileloaddt1", vex(2, 1, 0, 0, 4, 0, None, 0x4b, modrm=SIB_RAX_RCX), [("TMM4", tile_load(4, RCX))])
case("tileloaddrs", vex(2, 3, 0, 0, 5, 0, None, 0x4a, modrm=SIB_RAX_RCX), [("TMM5", tile_load(5, RCX))])
# rows of 8 bytes at each 16 bytes: what is between them stays
stored = MEM & M(512)
for r in range(ROWS[5]):
    for c in range(COLS[5]):
        offset = r * RCX + c
        stored = (stored & ~(255 << (8 * offset))) | (((TMM[5] >> (512 * r + 8 * c)) & 255) << (8 * offset))
case("tilestored", vex(2, 2, 0, 0, 5, 0, None, 0x4b, modrm=SIB_RAX_RCX), [], [], stored)
for (name, pp, sa, sb) in (("tdpbssd", 3, True, True), ("tdpbsud", 2, True, False), ("tdpbusd", 1, False, True), ("tdpbuud", 0, False, False)):
    # dest, r/m, vvvv
    case(name, vex(2, pp, 0, 0, 1, 3, 2, 0x5e), [("TMM1", tile_dot(1, 2, 3, sa, sb))])
    case(name + " other sizes", vex(2, pp, 0, 0, 5, 3, 4, 0x5e), [("TMM5", tile_dot(5, 4, 3, sa, sb))])


def movrow(t, r):
    r &= 15
    if r >= ROWS[t]:
        return 0
    value = (TMM[t] >> (512 * r)) & M(512)
    return value & M(8 * COLS[t])


for r in (1, 2, 3, 0x11, 15):
    case(f"tilemovrow imm {r}", evex(3, 1, 0, 2, 1, 0, 4, 0x07, imm=[r]), [("ZMM1", movrow(4, r))])
case("tilemovrow reg", evex(2, 1, 0, 2, 1, 1, 5, 0x4a), [("ZMM1", movrow(5, RCX))])


# SHA-NI, from the SDM. The rounds are checked against hashlib below.

def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M(32)


def ror(x, n):
    return ((x >> n) | (x << (32 - n))) & M(32)


def sha1rnds4(x, y, imm):
    def f(k, b, c, d):
        return [(b & c) ^ (~b & d), b ^ c ^ d, (b & c) ^ (b & d) ^ (c & d), b ^ c ^ d][k] & M(32)
    k = [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6][imm & 3]
    a, b, c, d = [(x >> (32 * i)) & M(32) for i in (3, 2, 1, 0)]
    e = 0
    for w in [(y >> (32 * i)) & M(32) for i in (3, 2, 1, 0)]:
        a, b, c, d, e = (f(imm & 3, b, c, d) + rol(a, 5) + w + e + k) & M(32), a, rol(b, 30), c, d
    return a << 96 | b << 64 | c << 32 | d


def sha1nexte(x, y):
    return (y & M(96)) | ((((y >> 96) + rol((x >> 96) & M(32), 30)) & M(32)) << 96)


def sha1msg1(x, y):
    w = [(x >> 96) & M(32), (x >> 64) & M(32), (x >> 32) & M(32), x & M(32), (y >> 96) & M(32), (y >> 64) & M(32)]
    return (w[2] ^ w[0]) << 96 | (w[3] ^ w[1]) << 64 | (w[4] ^ w[2]) << 32 | (w[5] ^ w[3])


def sha1msg2(x, y):
    w16 = rol(((x >> 96) ^ (y >> 64)) & M(32), 1)
    w17 = rol(((x >> 64) ^ (y >> 32)) & M(32), 1)
    w18 = rol(((x >> 32) ^ y) & M(32), 1)
    w19 = rol((x ^ w16) & M(32), 1)
    return w16 << 96 | w17 << 64 | w18 << 32 | w19


def s0(x):
    return ror(x, 7) ^ ror(x, 18) ^ (x >> 3)


def s1(x):
    return ror(x, 17) ^ ror(x, 19) ^ (x >> 10)


def sha256msg1(x, y):
    w = [(x >> (32 * i)) & M(32) for i in range(4)] + [y & M(32)]
    return sum((((w[i] + s0(w[i + 1])) & M(32)) << (32 * i)) for i in range(4))


def sha256msg2(x, y):
    w14, w15 = (y >> 64) & M(32), (y >> 96) & M(32)
    w16 = (x + s1(w14)) & M(32)
    w17 = ((x >> 32) + s1(w15)) & M(32)
    w18 = ((x >> 64) + s1(w16)) & M(32)
    w19 = ((x >> 96) + s1(w17)) & M(32)
    return w19 << 96 | w18 << 64 | w17 << 32 | w16


def sha256rnds2(x, y, k):
    a, b, c, d = (y >> 96) & M(32), (y >> 64) & M(32), (x >> 96) & M(32), (x >> 64) & M(32)
    e, f, g, h = (y >> 32) & M(32), y & M(32), (x >> 32) & M(32), x & M(32)
    for i in range(2):
        t = (h + (ror(e, 6) ^ ror(e, 11) ^ ror(e, 25)) + ((e & f) ^ (~e & g & M(32))) + ((k >> (32 * i)) & M(32))) & M(32)
        a, b, c, d, e, f, g, h = (t + (ror(a, 2) ^ ror(a, 13) ^ ror(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) & M(32), a, b, c, (t + d) & M(32), e, f, g
    return a << 96 | b << 64 | e << 32 | f


def check_sha_model():
    """The model of each instruction, in the sequence of Intel's guide for them, gives what hashlib does of one block."""
    import hashlib
    import struct
    message = b"abc" + b"\x80" + bytes(52) + struct.pack(">Q", 24)
    words = list(struct.unpack(">16I", message))
    # SHA-1: each group of four rounds has the W of the next, whose E is added by SHA1NEXTE
    h = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
    abcd = h[0] << 96 | h[1] << 64 | h[2] << 32 | h[3]
    e = h[4] << 96
    schedule = [words[i] << 96 | words[i + 1] << 64 | words[i + 2] << 32 | words[i + 3] for i in range(0, 16, 4)]
    for t in range(20):
        if t >= 4:
            m = sha1msg2(sha1msg1(schedule[t - 4], schedule[t - 3]) ^ schedule[t - 2], schedule[t - 1])
            schedule.append(m)
        w = (schedule[t] + (e & (M(32) << 96))) & M(128) if t == 0 else sha1nexte(e, schedule[t])
        e = abcd
        abcd = sha1rnds4(abcd, w, t // 5)
    out = [(abcd >> 96) & M(32), (abcd >> 64) & M(32), (abcd >> 32) & M(32), abcd & M(32), rol((e >> 96) & M(32), 30)]
    assert struct.pack(">5I", *[(a + b) & M(32) for a, b in zip(out, h)]) == hashlib.sha1(b"abc").digest(), "SHA-1 model"
    # SHA-256
    k = [int(x, 16) for x in (
        "428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 ab1c5ed5 d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe 9bdc06a7 c19bf174 "
        "e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f 4a7484aa 5cb0a9dc 76f988da 983e5152 a831c66d b00327c8 bf597fc7 c6e00bf3 d5a79147 06ca6351 14292967 "
        "27b70a85 2e1b2138 4d2c6dfc 53380d13 650a7354 766a0abb 81c2c92e 92722c85 a2bfe8a1 a81a664b c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070 "
        "19a4c116 1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3 748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 c67178f2").split()]
    h = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
    state0 = h[0] << 96 | h[1] << 64 | h[4] << 32 | h[5]
    state1 = h[2] << 96 | h[3] << 64 | h[6] << 32 | h[7]
    w = [words[i + 3] << 96 | words[i + 2] << 64 | words[i + 1] << 32 | words[i] for i in range(0, 16, 4)]
    for t in range(16):
        if t >= 4:
            shifted = ((w[t - 2] >> 32) | (w[t - 1] << 96)) & M(128)
            partial = sha256msg1(w[t - 4], w[t - 3])
            w.append(sha256msg2(sum((((((partial >> (32 * i)) & M(32)) + ((shifted >> (32 * i)) & M(32))) & M(32)) << (32 * i)) for i in range(4)), w[t - 1]))
        kw = sum((((((w[t] >> (32 * i)) & M(32)) + k[4 * t + i]) & M(32)) << (32 * i)) for i in range(4))
        state1 = sha256rnds2(state1, state0, kw)
        state0 = sha256rnds2(state0, state1, kw >> 64)
    out = [(state0 >> 96) & M(32), (state0 >> 64) & M(32), (state1 >> 96) & M(32), (state1 >> 64) & M(32),
           (state0 >> 32) & M(32), state0 & M(32), (state1 >> 32) & M(32), state1 & M(32)]
    assert struct.pack(">8I", *[(a + b) & M(32) for a, b in zip(out, h)]) == hashlib.sha256(b"abc").digest(), "SHA-256 model"


check_sha_model()


def legacy(escape, opcode, reg, rm, imm=(), prefix=()):
    return list(prefix) + escape + [opcode, 0xc0 | reg << 3 | rm] + list(imm)


def legacy_mem(escape, opcode, reg, imm=(), prefix=()):
    return list(prefix) + escape + [opcode, reg << 3] + list(imm)


X1, X2 = ZMM[1] & M(128), ZMM[2] & M(128)
HIGH1 = ZMM[1] & ~M(128)
for name, escape, opcode, f in (
        ("sha1nexte", [0x0f, 0x38], 0xc8, sha1nexte), ("sha1msg1", [0x0f, 0x38], 0xc9, sha1msg1), ("sha1msg2", [0x0f, 0x38], 0xca, sha1msg2),
        ("sha256msg1", [0x0f, 0x38], 0xcc, sha256msg1), ("sha256msg2", [0x0f, 0x38], 0xcd, sha256msg2)):
    case(name, legacy(escape, opcode, 1, 2), [("ZMM1", HIGH1 | f(X1, X2))])
    case(name + " mem", legacy_mem(escape, opcode, 1), [("ZMM1", HIGH1 | f(X1, mem(0, 128)))])
for imm in range(4):
    case(f"sha1rnds4 {imm}", legacy([0x0f, 0x3a], 0xcc, 1, 2, [imm]), [("ZMM1", HIGH1 | sha1rnds4(X1, X2, imm))])
case("sha256rnds2", legacy([0x0f, 0x38], 0xcb, 1, 2), [("ZMM1", HIGH1 | sha256rnds2(X1, X2, ZMM[0] & M(128)))])
case("sha256rnds2 mem", legacy_mem([0x0f, 0x38], 0xcb, 1), [("ZMM1", HIGH1 | sha256rnds2(X1, mem(0, 128), ZMM[0] & M(128)))])


# PCLMULQDQ and GFNI of the legacy encodings, whose upper bits stay

def clmul(a, b):
    out = 0
    for i in range(64):
        if (b >> i) & 1:
            out ^= a << i
    return out


def gfmul(a, b):
    out = 0
    for i in range(8):
        if (b >> i) & 1:
            out ^= a << i
    for i in range(14, 7, -1):
        if (out >> i) & 1:
            out ^= 0x11b << (i - 8)
    return out


def affine(x, a, imm):
    out = 0
    for b in range(8):
        row = (a >> (8 * (7 - b))) & 255
        out |= ((bin(row & x).count("1") + (imm >> b)) & 1) << b
    return out


for imm in (0x00, 0x01, 0x10, 0x11):
    a = (X1 >> (64 if imm & 1 else 0)) & M(64)
    b = (X2 >> (64 if imm & 16 else 0)) & M(64)
    case(f"pclmulqdq {imm:#x}", legacy([0x0f, 0x3a], 0x44, 1, 2, [imm], [0x66]), [("ZMM1", HIGH1 | clmul(a, b))])
case("gf2p8mulb", legacy([0x0f, 0x38], 0xcf, 1, 2, (), [0x66]),
     [("ZMM1", HIGH1 | join([gfmul(p, q) for p, q in zip(lanes(X1, 8, 16), lanes(X2, 8, 16))], 8))])
case("gf2p8affineqb", legacy([0x0f, 0x3a], 0xce, 1, 2, [0x35], [0x66]),
     [("ZMM1", HIGH1 | join([affine(p, (X2 >> (64 * (i // 8))) & M(64), 0x35) for i, p in enumerate(lanes(X1, 8, 16))], 8))])


# MMX

MM = {n: rnd(64) for n in range(8)}


def sat(value, bits, signed=True):
    if signed:
        return max(-(1 << (bits - 1)), min((1 << (bits - 1)) - 1, value)) & M(bits)
    return max(0, min(M(bits), value))


def pack(x, y, e, signed):
    return join([sat(sx(v, e), e // 2, signed) for v in lanes(x, e, 64 // e) + lanes(y, e, 64 // e)], e // 2)


T = [0x0f]
case("mmx packsswb", legacy(T, 0x63, 1, 2), [("MM1", pack(MM[1], MM[2], 16, True))])
case("mmx packuswb", legacy(T, 0x67, 1, 2), [("MM1", pack(MM[1], MM[2], 16, False))])
case("mmx packssdw", legacy(T, 0x6b, 1, 2), [("MM1", pack(MM[1], MM[2], 32, True))])
case("mmx pmuludq", legacy(T, 0xf4, 1, 2), [("MM1", (MM[1] & M(32)) * (MM[2] & M(32)))])
shuffled = lanes(MM[2], 16, 4)
case("mmx pshufw", legacy(T, 0x70, 1, 2, [0x1b]), [("MM1", join([shuffled[(0x1b >> (2 * i)) & 3] for i in range(4)], 16))])
inserted = lanes(MM[1], 16, 4)
inserted[2] = RDX & M(16)
case("mmx pinsrw", legacy(T, 0xc4, 1, 2, [2]), [("MM1", join(inserted, 16))])
case("mmx pextrw", legacy(T, 0xc5, 1, 2, [3]), [("RCX", (MM[2] >> 48) & M(16))])
case("mmx movq store", legacy_mem(T, 0x7f, 2), [], [], (MEM & M(512) & ~M(64)) | MM[2])
case("emms", [0x0f, 0x77], [("FPU_TAG", 0xffff)])


# the gathers of AVX2, whose indices are in ZMM8

INDEX32 = join([rng.randrange(0, 12) for _ in range(16)], 32)
INDEX64 = join([rng.randrange(0, 12) for _ in range(8)], 64)
ZMM[8] = INDEX32
ZMM[9] = INDEX64
for (name, opcode, w, l, e, ie, index, n) in (("vpgatherdd", 0x90, 0, 0, 32, 32, 8, 4), ("vpgatherdd y", 0x90, 0, 1, 32, 32, 8, 8), ("vpgatherdq", 0x90, 1, 1, 64, 32, 8, 4),
                                              ("vpgatherqd", 0x91, 0, 1, 32, 64, 9, 4), ("vpgatherqq", 0x91, 1, 1, 64, 64, 9, 4)):
    out = []
    for i in range(n):
        if (ZMM[2] >> (e * i + e - 1)) & 1:
            out.append(mem(4 * ((ZMM[index] >> (ie * i)) & M(ie)), e))
        else:
            out.append((ZMM[1] >> (e * i)) & M(e))
    sib = 2 << 6 | (index & 7) << 3
    case(name, [0xc4, 0xa2, w << 7 | (~2 & 15) << 3 | l << 2 | 1, opcode, 1 << 3 | 4, sib], [("ZMM1", join(out, e)), ("ZMM2", 0)])


# what is simple: XLAT, the bases of the segments, the moves to memory and the atomic operations

case("xlat", [0xd7], [("RAX", (BASE & ~255) | mem(8, 8))])
case("rdfsbase", [0xf3, 0x48, 0x0f, 0xae, 0xc1], [("RCX", 0x7000)])
case("rdgsbase", [0xf3, 0x0f, 0xae, 0xc9], [("RCX", 0x9000)])
case("wrfsbase", [0xf3, 0x48, 0x0f, 0xae, 0xd2], [("FS_BASE", RDX)])
case("wrgsbase", [0xf3, 0x0f, 0xae, 0xda], [("GS_BASE", RDX & M(32))])
case("aadd", [0x48, 0x0f, 0x38, 0xfc, 0x10], [], [], (MEM & M(512) & ~M(64)) | ((mem(0, 64) + RDX) & M(64)))
case("axor", [0xf3, 0x48, 0x0f, 0x38, 0xfc, 0x10], [], [], (MEM & M(512) & ~M(64)) | (mem(0, 64) ^ RDX))
case("movdiri", [0x48, 0x0f, 0x38, 0xf9, 0x10], [], [], (MEM & M(512) & ~M(64)) | RDX)
case("movdir64b", [0x66, 0x0f, 0x38, 0xf8, 0x40, 0x10], [], [], mem(16, 512))
case("adcx mem", [0x66, 0x0f, 0x38, 0xf6, 0x08], [("RCX", (RCX + mem(0, 32) + 1) & M(32))])
case("movrs", [0x48, 0x0f, 0x38, 0x8b, 0x08], [("RCX", mem(0, 64))])
case("push2", [0x62, 0xf4, 0x7c | 0, 0x18, 0xff, 0xf2], [("RSP", 0x2000 - 16)])


# APX: a new destination, no flags, and the conditional comparisons

def apx(reg, vvvv, rm, opcode, w=1, pp=0, nd=1, nf=0, modrm=None, imm=(), extra=0, aaa=None):
    p1 = w << 7 | (~vvvv & 15) << 3 | 4 | pp
    p2 = nd << 4 | 8 | nf << 2 | (aaa or 0)
    rest = [0xc0 | reg << 3 | rm] if rm is not None else [reg << 3 | modrm]
    return [0x62, 0xf4, p1, p2, opcode] + rest + list(imm)


def add_flags(a, b, bits, carry=0):
    total = a + b + carry
    r = total & M(bits)
    return r, {"CF": total >> bits, "ZF": int(r == 0), "SF": r >> (bits - 1), "OF": ((a ^ r) & (b ^ r)) >> (bits - 1),
               "AF": ((a ^ b ^ r) >> 4) & 1, "PF": int(bin(r & 255).count("1") % 2 == 0)}


FLAGS = {"CF": 1, "ZF": 0, "SF": 1, "OF": 0, "AF": 1, "PF": 0}
# ADD64rr_ND rcx <- rdx + rbx: vvvv is the destination, r/m the first source
r, f = add_flags(RDX, RBX, 64)
case("add nd", apx(3, 1, 2, 0x01), [("RCX", r), ("RDX", RDX), ("RBX", RBX)], sorted(f.items()))
case("add nf nd", apx(3, 1, 2, 0x01, nf=1), [("RCX", r)], sorted(FLAGS.items()))
case("add nf", apx(3, 0, 2, 0x01, nd=0, nf=1), [("RDX", r)], sorted(FLAGS.items()))
r, f = add_flags(RDX & M(16), RBX & M(16), 16)
case("add16 nd clears", apx(3, 1, 2, 0x01, w=0, pp=1), [("RCX", r)], sorted(f.items()))
r, f = add_flags(RDX & M(8), RBX & M(8), 8)
case("add8 nd clears", apx(3, 1, 2, 0x00, w=0), [("RCX", r)], sorted(f.items()))
r, f = add_flags(RDX & M(32), RBX & M(32), 32, 1)
case("adc32 nd", apx(3, 1, 2, 0x11, w=0), [("RCX", r)], sorted(f.items()))
r, f = add_flags(mem(0, 64), RBX, 64)
case("add mr nd", apx(3, 1, None, 0x01, modrm=0), [("RCX", r)], sorted(f.items()), MEM & M(512))
r, f = add_flags(mem(0, 16), RBX & M(16), 16)
case("add16 mr nd", apx(3, 1, None, 0x01, modrm=0, w=0, pp=1), [("RCX", r)], sorted(f.items()), MEM & M(512))
r, f = add_flags(mem(0, 64), (-5) & M(64), 64)
case("add64 mi32 nd", apx(0, 1, None, 0x81, modrm=0, imm=[0xfb, 0xff, 0xff, 0xff]), [("RCX", r)], sorted(f.items()), MEM & M(512))
r, f = add_flags(RDX, (-5) & M(64), 64)
case("add64 ri32 nd", apx(0, 1, 2, 0x81, imm=[0xfb, 0xff, 0xff, 0xff]), [("RCX", r)], sorted(f.items()))
# SHL by CL, of which RCX is 16
case("shl rcl nd", apx(4, 3, 2, 0xd3), [("RBX", (RDX << 16) & M(64))])
case("shl mcl nd", apx(4, 3, None, 0xd3, modrm=0), [("RBX", (mem(0, 64) << 16) & M(64))], [], MEM & M(512))
case("shl nf", apx(4, 0, 2, 0xd3, nd=0, nf=1), [("RDX", (RDX << 16) & M(64))], sorted(FLAGS.items()))
case("neg m nd", apx(3, 1, None, 0xf7, modrm=0), [("RCX", (-mem(0, 64)) & M(64))], [], MEM & M(512))
# the conditions from FLAGS: B holds as CF is set, and NB doesn't
for (name, opcode, cc, dcf, f) in (("ccmp holds", 0x39, 2, 0b1010, True), ("ccmp not", 0x39, 3, 0b1010, False), ("ccmpt", 0x39, 10, 0b1010, True), ("ccmpf", 0x39, 11, 0b1010, False)):
    p1 = 1 << 7 | dcf << 3 | 4
    p2 = cc
    flags = cmp_flags(RDX, RBX, 64) if f else {"OF": 1, "SF": 0, "ZF": 1, "CF": 0, "PF": 0, "AF": 0}
    case(name, [0x62, 0xf4, p1, p2, opcode, 0xc0 | 3 << 3 | 2], [], sorted(flags.items()))
# SETZU, of which the whole register is written
case("setzub", [0x62, 0xf4, 0x7f, 0x18, 0x42, 0xc1], [("RCX", 1)])
# the registers of APX: R17 from the upper bits of the fields
case("add r17 nd", [0x62, 0xf4, 0xf4 & 0xf7 | (~1 & 15) << 3, 0x10, 0x01, 0xc0 | 3 << 3 | 2], [("R17", (RDX + RBX) & M(64))])
case("add r17d nd", [0x62, 0xf4, 0x74 & 0x07 | (~1 & 15) << 3, 0x10, 0x01, 0xc0 | 3 << 3 | 2], [("R17", (RDX + RBX) & M(32))])


# the opcodes of VEX that are families of AVX-512: no mask, and the upper bits of the vector clear

def vnni_w(x, y, z, n):
    out = []
    for i in range(n):
        p = sum(sx(y >> (32 * i + 16 * j), 16) * sx(z >> (32 * i + 16 * j), 16) for j in range(2))
        out.append((sx(x >> (32 * i), 32) + p) & M(32))
    return join(out, 32)


case("vpdpwssd vex", vex(2, 1, 0, 0, 1, 2, 3, 0x52), [("ZMM1", vnni_w(ZMM[1], ZMM[2], ZMM[3], 4))])
case("vpdpwssd vex y", vex(2, 1, 0, 1, 1, 2, 3, 0x52), [("ZMM1", vnni_w(ZMM[1], ZMM[2], ZMM[3], 8))])
madd = [((x + (((y & M(52)) * (z & M(52))) & M(52))) & M(64)) for x, y, z in zip(lanes(ZMM[1], 64, 2), lanes(ZMM[2], 64, 2), lanes(ZMM[3], 64, 2))]
case("vpmadd52luq vex", vex(2, 1, 1, 0, 1, 2, 3, 0xb4), [("ZMM1", join(madd, 64))])
case("vgf2p8mulb vex y", vex(2, 1, 0, 1, 1, 2, 3, 0xcf),
     [("ZMM1", join([gfmul(p, q) for p, q in zip(lanes(ZMM[2], 8, 32), lanes(ZMM[3], 8, 32))], 8))])
case("vpclmulqdq vex y", vex(3, 1, 0, 1, 1, 2, 3, 0x44) + [0x11],
     [("ZMM1", join([clmul((ZMM[2] >> (128 * g + 64)) & M(64), (ZMM[3] >> (128 * g + 64)) & M(64)) for g in range(2)], 128))])

print("/-- The state of `x86RestCases`, from `tools/x86_model.py`. -/")
print("private def x86RestState : List (String × Nat × Nat) :=")
state = [(f"ZMM{n}", 512, ZMM[n]) for n in range(10)] + [(f"K{n}", 64, K[n]) for n in sorted(K)] + [("RCX", 64, RCX), ("RDX", 64, RDX), ("RBX", 64, RBX)]
state += [(f"TMM{n}", 8192, TMM[n]) for n in range(8)] + [("TILECFG", 512, CFG)]
state += [(f"MM{n}", 64, MM[n]) for n in range(8)] + [("FS_BASE", 64, 0x7000), ("GS_BASE", 64, 0x9000), ("RSP", 64, 0x2000), ("FPU_TAG", 16, 0)]
state += [("R17", 64, rnd(64))] + [(name, 1, value) for name, value in sorted(FLAGS.items())]
print("  [" + ",\n    ".join(f'("{n}", {w}, {v:#x})' for n, w, v in state) + "]")
print("")
print("private def x86RestMemory : Nat := " + hex(MEM & M(1024)))
print("")
print("/-- The cases, from `tools/x86_model.py`: an independent model of what the manuals say, not from the semantics. -/")
print("private def x86RestCases : List (String × List Nat × List (String × Nat) × List (String × Nat) × Option Nat) := [")
lines = []
for name, encoding, registers, flags, stored in cases:
    regs = ", ".join(f'("{r}", {v:#x})' for r, v in registers)
    fl = ", ".join(f'("{r}", {v})' for r, v in flags)
    st = f"some {stored:#x}" if stored is not None else "none"
    lines.append(f'  ("{name}", [{", ".join(hex(b) for b in encoding)}], [{regs}], [{fl}], {st})')
print(",\n".join(lines))
print("]")
