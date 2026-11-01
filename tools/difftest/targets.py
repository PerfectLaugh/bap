"""What each target is to the differential test: its registers, how to run it, and its instructions, see difftest.py."""
import dataclasses
import os
import re
import struct

ALL = ["x86_64", "i686", "aarch64", "arm", "thumb", "riscv64", "riscv32", "mips", "mipsel", "mips64", "mipsr6", "mips64r6", "ppc", "ppc64", "ppc64le"]
# lists of instructions, a corpus of operand forms only: what they expect isn't used
CORPUS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "corpus")


def case_type():
    from difftest import Case

    return Case


def uppercase_stem(name):
    """The mnemonics that an LLVM opcode name might be of, e.g., `ADD`, `VPADDB` of `ADD64rm`, `VPADDBYrr`."""
    stem = re.match(r"[A-Z0-9_]+", name)
    if not stem:
        return []
    raw = stem.group(0)
    stem = raw.rstrip("0123456789_")
    result = {stem, raw}
    for suffix in ("Y", "Z", "X", "W", "S", "D", "Q", "L", "H", "B"):
        if stem.endswith(suffix):
            result.add(stem[:-1])
    return sorted(result)


def corpus_lines(name):
    """The bytes and the assembly of the upstream's list of instructions, which are a corpus of operand forms only."""
    path = os.path.join(CORPUS, name + ".insns")
    if not os.path.exists(path):
        return []
    result = []
    with open(path) as handle:
        for line in handle:
            line = line.strip()
            if line.startswith("#"):
                line = line.lstrip("# ")
                if not re.match(r"[0-9a-f]{2}( |$)", line):
                    continue
            if not line or "#" not in line:
                continue
            code, _, text = line.partition("#")
            try:
                data = bytes.fromhex(code.replace(";", " "))
            except ValueError:
                continue
            result.append((data, text.strip()))
    return result


class Target:
    """The common part: a state is a dictionary from the names of the Lean variables to their values."""

    def policy_of(self, differ):
        """The name of what the runner is known to do otherwise than the semantics, where neither is wrong, if that is all that differs. What
        differs is (name, runner, lifter)."""
        return None

    name = ""
    word = 8
    endian = "<"
    runner = []
    cflags = []
    lean = ""
    mc_triple = ""
    mc_args = []
    asm_prelude = ""
    nop = b"\x90"
    gprs = []
    flags = []
    vectors = []
    aux = {}
    default_pins = {}
    semantics = []
    pc_mask = 0

    def __init__(self, scratch):
        self.scratch = scratch
        self.compared = [(n, w) for n, w in self.gprs] + [(f[0], 1) for f in self.flags] + self.compared_vectors()
        self.all_widths = list(self.gprs) + [(f[0], 1) for f in self.flags] + list(self.vectors)
        aux_vars = [(n, w) for n, (v, w) in self.aux_spec().items()]
        self.aux = {n: v for n, (v, w) in self.aux_spec().items()}
        self.lean_vars = self.all_widths + aux_vars
        self.lean_order = [n for n, _ in self.lean_vars]

    def compared_vectors(self):
        return list(self.vectors)

    def aux_spec(self):
        return {}

    def shape(self, case, values, index, rng):
        pass

    def relevant(self, name):
        return True

    def traps(self, opcode):
        """Whether the opcode can take a trap, of which the signal of the run and the effect of the lifter are compared."""
        return False

    def pad_prefix(self, code):
        return b""

    undefined = None

    def excluded(self, opcode, case):
        return None

    def word_bytes(self, value):
        return value.to_bytes(self.word, "big" if self.endian == ">" else "little")

    def cases(self, opcodes, assemble, layout):
        raise NotImplementedError

    def from_shapes(self, opcodes, assemble, mnemonics, shapes, pins):
        """All the mnemonics in all the shapes, those the assembler takes. `pins` says what a text's registers are held to."""
        Case = case_type()
        lines = [(shape.replace("{m}", mnemonic) if "{m}" in shape else f"{mnemonic} {shape}").strip() for mnemonic in sorted(mnemonics) for shape in shapes]
        result = []
        for index, code in assemble(self, lines):
            result.append(Case(code=code, text=lines[index], pins=pins(lines[index])))
        return result


# x86 ---------------------------------------------------------------------------------------------------------------------

X86_FLAGS = [("CF", 0), ("PF", 2), ("AF", 4), ("ZF", 6), ("SF", 7), ("DF", 10), ("OF", 11)]

CONDS = ["o", "no", "b", "ae", "e", "ne", "be", "a", "s", "ns", "p", "np", "l", "ge", "le", "g"]

X86_SKIP_PREFIX = ("SYSCALL", "SYSENTER", "SYSEXIT", "SYSRET", "INT", "HLT", "CPUID", "RDTSC", "RDRAND", "RDSEED", "XGETBV", "RDPID",
    "RDPMC", "RDPKRU", "WRPKRU", "IN8", "IN16", "IN32", "OUT8", "OUT16", "OUT32", "INSB", "INSW", "INSL", "OUTSB", "OUTSW", "OUTSL", "CLI", "STI", "FX", "XSAVE",
    "XRSTOR", "LDMXCSR", "VLDMXCSR", "FRNDINT", "LAR", "LSL", "SGDT", "SIDT", "SLDT", "STR", "SMSW", "IRET", "UD", "WBINVD", "INVD", "VER", "ARPL", "LGS", "LFS",
    "LSS", "LDS", "LES", "MOVSEG", "MOV16sr", "MOV32sr", "MOV64sr", "POPDS", "POPES", "POPFS", "POPGS", "POPSS", "PUSHCS", "PUSHDS", "PUSHES", "PUSHFS", "PUSHGS",
    "PUSHSS", "LRET", "FARCALL", "FARJMP", "MONITOR", "MWAIT", "PREFETCH", "CLFLUSH", "CLWB", "CLZERO", "ENCL", "XBEGIN", "XEND", "XABORT", "XTEST",
    "RDFSBASE", "RDGSBASE", "WRFSBASE", "WRGSBASE", "WRSSD", "WRSSQ", "RDSSP", "INCSSP", "SAVEPREV", "RSTOR", "SETSSBSY", "CLRSSBSY", "SWAPGS", "LLDT", "LTR", "LIDT", "LGDT", "LMSW",
    "WRUSS")

def x86_shapes(long):
    r64, r32, r16, r8 = ("rsi", "r9", "r10"), ("esi", "r9d", "r10d"), ("si", "r9w", "r10w"), ("sil", "r9b", "r10b")
    if not long:
        r32, r16, r8 = ("esi", "edi", "ebp"), ("si", "di", "bp"), ("dl", "ah", "bh")
        r64 = None
    base = "[rbx+8]" if long else "[ebx+8]"
    indexed = "[rbx+r15*2+4]" if long else "[ebx+edi*2+4]"
    shapes = [""]
    widths = [("byte ptr", r8, 1), ("word ptr", r16, 2), ("dword ptr", r32, 4)]
    if long:
        widths.append(("qword ptr", r64, 8))
    for ptr, reg, size in widths:
        m, m2 = f"{ptr} {base}", f"{ptr} {indexed}"
        a, b, c = reg
        shapes += [a, m, f"{a}, {b}", f"{a}, {m}", f"{m}, {a}", f"{a}, {m2}", f"{a}, 5", f"{a}, -1", f"{a}, 1000", f"{m}, 5", f"{m}, -1", f"{m}, 1000",
            f"{a}, cl", f"{m}, cl", f"{a}, 1", f"{m}, 1", f"{a}, 3", f"{m}, 3",
            f"{a}, {b}, {c}", f"{a}, {m}, {c}", f"{a}, {b}, {m}", f"{a}, {b}, 5", f"{a}, {b}, 1000", f"{a}, {m}, 5", f"{a}, {m}, 1000",
            f"{a}, {b}, cl", f"{m}, {b}, cl", f"{a}, {b}, 3", f"{m}, {b}, 3"]
        for ptr2, reg2, _ in widths:
            if ptr2 != ptr:
                shapes += [f"{a}, {reg2[1]}", f"{a}, {ptr2} {base}"]
    mm = "qword ptr " + base
    shapes += ["mm1, mm2", f"mm1, {mm}", f"{mm}, mm1", "mm1, 3", "mm1, 200", "mm1, mm2, 3", f"mm1, {mm}, 3", "mm1, esi", "esi, mm1", f"mm1, dword ptr {base}", f"dword ptr {base}, mm1", "esi, mm1, 1", "mm1, esi, 1", "xmm1, mm2", "mm1, xmm2", "mm1", "mm1, xmm2, 1"]
    if long:
        shapes += ["mm1, rsi", "rsi, mm1"]
    qm = "qword ptr " + base
    shapes += [f"xmm1, {qm}", f"{qm}, xmm1", f"xmm1, xmm2, {qm}", f"ymm1, {qm}", qm, f"xmm1, {qm}, xmm3", f"xmm1, xmm2, {qm}, 1", f"xmm1, {qm}, 1", f"xmm1, xmm2, xmm3", f"xmm1, {qm}, xmm3, 1"]
    shapes += ["al, 5", "al, -1", "ax, 1000", "ax, -1", "eax, 1000", "eax, -1", "eax, 100000"] + (["rax, 1000", "rax, -1", "rax, 100000"] if long else [])
    shapes += ["ax, si", "si, ax", "eax, esi", "esi, eax"] + (["rax, rsi", "rsi, rax", "esi, r9"] if long else [])
    x, x2, x3, x4 = ("xmm1", "xmm2", "xmm3", "xmm4")
    shapes += ["xmm1, xmm9", "xmm9, xmm1", "xmm9, xmm10", "xmm9, xmm10, xmm11"] if long else []
    y, y2, y3, y4 = ("ymm1", "ymm2", "ymm3", "ymm4")
    xm, ym = f"xmmword ptr {base}", f"ymmword ptr {base}"
    shapes += [x, y, xm, ym, f"{x}, {x2}", f"{y}, {y2}", f"{x}, {xm}", f"{xm}, {x}", f"{y}, {ym}", f"{ym}, {y}",
        f"{x}, {x2}, {x3}", f"{x}, {x2}, {xm}", f"{y}, {y2}, {y3}", f"{y}, {y2}, {ym}", f"{y}, {y2}, {x3}", f"{y}, {y2}, {xm}",
        f"{x}, 3", f"{y}, 3", f"{x}, 200", f"{x}, {x2}, 3", f"{y}, {y2}, 3", f"{x}, {xm}, 3", f"{y}, {ym}, 3", f"{x}, {x2}, 27", f"{y}, {y2}, 27",
        f"{x}, {x2}, {x3}, 3", f"{x}, {x2}, {xm}, 3", f"{y}, {y2}, {y3}, 3", f"{y}, {y2}, {ym}, 3", f"{y}, {y2}, {x3}, 1", f"{y}, {y2}, {xm}, 1",
        f"{x}, {y2}, 1", f"{xm}, {y2}, 1", f"{y}, {x2}", f"{x}, {y2}", f"{y}, {xm}", f"{x}, {x2}, {x3}, {x4}", f"{y}, {y2}, {y3}, {y4}",
        f"{x}, {x2}, {xm}, {x4}", f"{y}, {y2}, {ym}, {y4}", f"{xm}, {x2}, {x3}", f"{ym}, {y2}, {y3}", f"{x}, {x2}, xmm0", f"{x}, {xm}, xmm0", f"{y}, {y2}, {y3}, 200", f"{x}, {x2}, {x3}, 200"]
    for ptr, reg, _ in widths:
        a, b = reg[0], reg[1]
        shapes += [f"{{load}} {{m}} {a}, {b}", f"{{store}} {{m}} {a}, {b}"]
    shapes += [f"{{load}} {{m}} {x}, {x2}", f"{{store}} {{m}} {x}, {x2}", f"{{load}} {{m}} {y}, {y2}", f"{{store}} {{m}} {y}, {y2}", f"{{store}} {{m}} {x}, {x2}, {x3}", f"{{load}} {{m}} {x}, {x2}, {x3}"]
    for ptr, reg, _ in widths:
        m = f"{ptr} {base}"
        a = reg[0]
        shapes += [f"{x}, {a}", f"{a}, {x}", f"{y}, {a}", f"{a}, {y}", f"{x}, {m}", f"{m}, {x}", f"{y}, {m}", f"{m}, {y}", f"{x}, {x2}, {m}",
            f"{m}, {x}, 1", f"{a}, {x}, 1", f"{x}, {a}, 1", f"{x}, {m}, 1", f"{x}, {x2}, {a}", f"{x}, {x2}, {a}, 1", f"{x}, {x2}, {m}, 1",
            f"{a}, {y}, 1", f"{y}, {x2}, {m}", f"{x}, {m}, {x3}", f"{y}, {m}, {y3}", f"{m}, {x}, {x3}", f"{m}, {y}, {y3}"]
    return shapes


def x86_pins(long):
    def pins(text):
        result = {}
        if long:
            if "rbx" in text:
                result["RBX"] = "window+248"
            if "r15" in text:
                result["R15"] = 8
        else:
            if "ebx" in text:
                result["EBX"] = "window+248"
            if "edi*" in text:
                result["EDI"] = 8
        return result

    return pins


EFLAGS_AUX = {name: (1 if name == "EFLAGS_1" else 0, 1) for name in ["AI", "AES", "EFLAGS_29", "EFLAGS_28", "EFLAGS_27", "EFLAGS_26", "EFLAGS_25", "EFLAGS_24",
    "EFLAGS_23", "EFLAGS_22", "ID", "VIP", "VIF", "AC", "VM", "RF", "MD", "NT", "IOPLH", "IOPLL", "TF", "EFLAGS_5", "EFLAGS_3", "EFLAGS_1"]}


class X86(Target):
    nop = b"\x90"
    semantics = ["x86/x86-arith.lisp", "x86/x86-shift.lisp", "x86/x86-bits.lisp", "x86/x86-bmi.lisp", "x86/x86-control.lisp", "x86/x86-move.lisp",
        "x86/x86-sse.lisp", "x86/x86-simd.lisp", "x86/x86-pcmpstr.lisp", "x86/x86-sse-intrinsics.lisp", "x86/x86-common.lisp", "x86/x86-32.lisp", "x86/x86-64.lisp"]
    flags = X86_FLAGS
    asm_prelude = ".intel_syntax noprefix\n"
    mc_args = ["--mattr=+avx2,+bmi,+bmi2,+lzcnt,+popcnt,+adx,+movbe,+sse4a,+sha,+aes,+pclmul,+fma,+f16c,+rdrnd,+xop,+tbm,+fsgsbase,+clzero,+rdseed"]
    long = True

    def decode_flags(self, value):
        return {name: (value >> bit) & 1 for name, bit in X86_FLAGS}

    def encode_flags(self, values):
        word = 0x202
        for name, bit in X86_FLAGS:
            word |= values[name] << bit
        return word

    def excluded(self, opcode, case):
        if opcode in ("JRCXZ", "JECXZ", "JCXZ"):
            return None
        for prefix in X86_SKIP_PREFIX:
            if opcode.startswith(prefix):
                return "system, or depends on what isn't in the state"
        if "fs:" in case.text or "gs:" in case.text:
            return "segment"
        if "_F" in opcode:
            return "x87, which isn't in the state"
        if opcode.startswith(("ST_", "LD_", "ADD_", "SUB_", "MUL_", "DIV_", "COM_", "UCOM_", "CH", "ABS_", "FP", "FN", "FL", "FS", "FI", "FC", "FD", "FE", "FU", "FA", "FM", "F2", "WAIT", "XCH_F", "XAM_F", "TST_F", "SQRT_F", "SIN_F", "COS_F", "IST", "ILD", "DIVR_", "SUBR_", "TAN")):
            return "x87, which isn't in the state"
        if "EVEX" in opcode or re.search(r"Z(128|256)?(r|m|k|$)", opcode) or opcode.startswith("K"):
            return "AVX-512, which this machine doesn't have"
        return None

    def undefined(self, case, values, final):
        return undefined_x86(self, case, values, final)

    def _mnemonics(self, opcodes):
        names = set()
        for name in opcodes:
            names.update(s.lower() for s in uppercase_stem(name))
        return names | {"movd", "movq", "vmovd", "vmovq", "movsxd", "enter", "movsb", "movdq2q", "movq2dq"}

    def _extra(self, layout):
        """What the shapes can't reach: conditions, the implicit operands, string operations, control."""
        Case = case_type()
        result = []
        rel = lambda size: (0x40 - size).to_bytes(4, "little", signed=True)
        for cc in range(16):
            result.append(Case(code=bytes([0x70 + cc, 0x40 - 2]), text=f"j{CONDS[cc]} short taken"))
            result.append(Case(code=bytes([0x0F, 0x80 + cc]) + rel(6), text=f"j{CONDS[cc]} taken"))
        result.append(Case(code=bytes([0xEB, 0x40 - 2]), text="jmp short taken"))
        result.append(Case(code=b"\xE9" + rel(5), text="jmp taken"))
        result.append(Case(code=b"\xE8" + rel(5), text="call taken"))
        counts = lambda index, rng: rng.choice([0, 1, 2, 3, 7])
        count_reg = "RCX" if self.long else "ECX"
        result.append(Case(code=bytes([0xE3, 0x40 - 2]), text="jrcxz taken", pins={count_reg: lambda i, r: r.choice([0, 1])}))
        result.append(Case(code=bytes([0xE2, 0x40 - 2]), text="loop taken", pins={count_reg: counts}))
        result.append(Case(code=bytes([0xE1, 0x40 - 2]), text="loope taken", pins={count_reg: counts}))
        result.append(Case(code=bytes([0xE0, 0x40 - 2]), text="loopne taken", pins={count_reg: counts}))
        # the other encodings of an instruction, and those of the absolute address of memory
        address = layout["window"] + 256
        word = 8 if self.long else 4
        for prefix in ([b"", b"\x66", b"\x48"] if self.long else [b"", b"\x66"]):
            for op in [0xA0, 0xA1, 0xA2, 0xA3]:
                if op in (0xA0, 0xA2) and prefix:
                    continue
                result.append(Case(code=prefix + bytes([op]) + address.to_bytes(word, "little"), text=f"mov moffs {op:x}"))
                if self.long:
                    result.append(Case(code=b"\x67" + prefix + bytes([op]) + address.to_bytes(4, "little"), text=f"mov moffs32 {op:x}"))
                else:
                    pass
        result.append(Case(code=bytes.fromhex("c6c605"), text="mov8ri alt"))
        result.append(Case(code=bytes.fromhex("66c7c6e803"), text="mov16ri alt"))
        result.append(Case(code=bytes.fromhex("c7c6e8030000"), text="mov32ri alt"))
        result.append(Case(code=bytes.fromhex("660fbff1"), text="movsx16rr16"))
        result.append(Case(code=bytes.fromhex("660fb7f1"), text="movzx16rr16"))
        result.append(Case(code=bytes.fromhex("666a05"), text="push16i8"))
        result.append(Case(code=bytes.fromhex("6668e803"), text="push16i"))
        result.append(Case(code=bytes.fromhex("ffc6" if self.long else "ffc6"), text="inc32 alt"))
        result.append(Case(code=bytes.fromhex("ff" + "f6"), text="push rmr"))
        result.append(Case(code=bytes.fromhex("66fff6"), text="push16 rmr"))
        result.append(Case(code=bytes.fromhex("8fc6"), text="pop rmr"))
        result.append(Case(code=bytes.fromhex("668fc6"), text="pop16 rmr"))
        low = self.long and b"\x40" or b""
        for base in [0x00, 0x08, 0x10, 0x18, 0x20, 0x28, 0x30, 0x38, 0x88]:
            load = base + 2 if base != 0x88 else 0x8A
            result.append(Case(code=low + bytes([load, 0xF1]), text=f"rev8 {load:x}"))
            result.append(Case(code=bytes([0x66, load + 1, 0xF1]), text=f"rev16 {load:x}"))
            result.append(Case(code=bytes([load + 1, 0xF1]), text=f"rev32 {load:x}"))
            if self.long:
                result.append(Case(code=bytes([0x48, load + 1, 0xF1]), text=f"rev64 {load:x}"))
        for code in ["0f28ca", "0f29ca", "660f29ca", "660f7fca", "f30f7fca", "0f11ca", "660f11ca", "f20f11ca", "f30f11ca", "0f7fca", "c5f829ca", "c5fc29ca", "c5f929ca", "c5fd29ca",
                "c5f97fca", "c5fd7fca", "c5fa7fca", "c5fe7fca", "c5f811ca", "c5fc11ca", "c5f911ca", "c5fd11ca", "c5eb11ca", "c5ea11ca", "c4e37d06d31b", "f20fd6ca", "f30fd6ca", "f30f7eca", "660fd6ca", "c5f9d6ca"]:
            result.append(Case(code=bytes.fromhex(code), text=f"raw {code}"))
        if not self.long:
            # the group of the 8-bit immediates that only the 32-bit mode has
            for op in range(8):
                result.append(Case(code=bytes([0x82, 0xC0 | (op << 3) | 6, 5]), text=f"grp1 82 /{op} r"))
                result.append(Case(code=bytes([0x82, 0x43 | (op << 3), 8, 5]), text=f"grp1 82 /{op} m", pins={"EBX": "window+248"}))
            result.append(Case(code=bytes.fromhex("60"), text="pusha", pins={"ESP": "window+300"}))
            result.append(Case(code=bytes.fromhex("61"), text="popa", pins={"ESP": "window+128"}))
            result.append(Case(code=bytes.fromhex("6660"), text="pushaw", pins={"ESP": "window+300"}))
            result.append(Case(code=bytes.fromhex("6661"), text="popaw", pins={"ESP": "window+128"}))
            for code in ["27", "2f", "37", "3f", "d40a", "d505", "d410", "d510"]:
                result.append(Case(code=bytes.fromhex(code), text=f"bcd {code}"))
        result.append(Case(code=b"\x9c", text="pushf"))
        result.append(Case(code=b"\x66\x9c", text="pushf16"))
        safe = lambda index, rng: rng.getrandbits(16) & 0xCD5 | 0x202
        result.append(Case(code=b"\x9d", text="popf", pinmem={256: (safe, word)}))
        result.append(Case(code=b"\x66\x9d", text="popf16", pinmem={256: (safe, 2)}))
        return result

    def _text_cases(self, assemble):
        """The families whose operands are implicit or have a condition."""
        Case = case_type()
        long = self.long
        ax, bx, cx, si, di, sp, bp = ("RAX", "RBX", "RCX", "RSI", "RDI", "RSP", "RBP") if long else ("EAX", "EBX", "ECX", "ESI", "EDI", "ESP", "EBP")
        rb = "rbx" if long else "ebx"
        lines = []
        widths = ["byte ptr", "word ptr", "dword ptr"] + (["qword ptr"] if long else [])
        r32 = ("esi", "ecx", "edx")
        counts = lambda index, rng: rng.choice([0, 1, 2, 3, 7])
        spec = {}

        def add(text, **pins):
            lines.append(text)
            spec[text] = pins

        for cc in CONDS:
            add(f"set{cc} sil" if long else f"set{cc} dl")
            add(f"set{cc} byte ptr [{rb}+8]", **{bx: "window+248"})
            for reg in ([("esi", "edi")] + ([("rsi", "r9"), ("si", "r9w")] if long else [("si", "di")])):
                add(f"cmov{cc} {reg[0]}, {reg[1]}")
            for ptr, reg in [("dword ptr", "esi"), ("word ptr", "si")] + ([("qword ptr", "rsi")] if long else []):
                add(f"cmov{cc} {reg}, {ptr} [{rb}+8]", **{bx: "window+248"})
        for op, letters in [("movs", "bwdq"), ("stos", "bwdq"), ("lods", "bwdq"), ("scas", "bwdq"), ("cmps", "bwdq")]:
            for letter in letters:
                if letter == "q" and not long:
                    continue
                for prefix in ["", "rep ", "repne "]:
                    if prefix == "repne " and op not in ("scas", "cmps"):
                        continue
                    add(f"{prefix}{op}{letter}", **{si: "window+128", di: "window+300", cx: counts})
        for text in ["cbw", "cwde", "cwd", "cdq", "clc", "stc", "cmc", "cld", "std", "lahf", "sahf", "nop", "xlatb", "pause", "endbr64" if long else "endbr32"]:
            if text == "xlatb":
                add(text, **{bx: "window+128"})
            else:
                add(text)
        if long:
            add("cqo")
            add("cdqe")
        add("leave", **{bp: "window+200"})
        add("push rsi" if long else "push esi")
        add("pop rsi" if long else "pop esi")
        add("push 5")
        add("push 1000")
        add("enter 8, 0")
        # registers that are both operands, or views of each other, or the stack pointer
        if long:
            for text in ["add ah, bl", "add bh, ch", "mov ah, dh", "movzx esi, ah", "movsx rsi, bh", "xchg ah, al", "shl dh, cl", "sub ah, ah", "cmp ah, bl", "mov ah, 5", "rol ch, 1", "not bh", "neg ah", "inc ch", "mul ah", "div bh",
                    "add rax, rax", "sub esi, esi", "xor rsi, rsi", "xchg rsi, rsi", "xchg esi, esi", "xchg rax, rax", "imul rsi, rsi", "mul rax", "xadd rsi, rsi", "cmpxchg rax, rax", "cmpxchg rsi, rsi", "bsf rsi, rsi", "tzcnt rsi, rsi",
                    "shld rsi, rsi, 3", "shld rcx, rcx, cl", "shl rcx, cl", "ror cx, cl", "bt rsi, rsi", "bts rsi, rsi", "cmovne rsi, rsi", "cmovne esi, esi", "mov rsi, rsi", "mov esi, esi", "movzx esi, si", "movsxd rsi, esi", "bswap esi", "bswap rsi",
                    "mov rsi, rsp", "mov esi, esp", "add rsp, 8", "sub rsp, 8", "lea rsp, [rsp+8]", "xchg rsi, rsp", "push rsp", "pop rsp", "and rsp, -16", "mov rsp, rsp",
                    "mulx rsi, rsi, r9", "mulx rsi, r9, rsi", "mulx rdx, rsi, r9", "adcx rsi, rsi", "adox rsi, rsi", "pdep rsi, rsi, rsi", "pext rsi, rsi, rsi", "andn rsi, rsi, rsi", "blsr rsi, rsi", "blsi rsi, rsi", "blsmsk rsi, rsi", "bzhi rsi, rsi, rsi", "bextr rsi, rsi, rsi", "rorx rsi, rsi, 3", "sarx rsi, rsi, rsi", "shlx rsi, rsi, rsi", "shrx rsi, rsi, rsi", "popcnt rsi, rsi", "lzcnt rsi, rsi"]:
                add(text)
        add("enter 8, 1")
        add("enter 8, 3", **{bp: "window+200"})
        add("enter 8, 33", **{bp: "window+200"})
        for text in ["ret", "ret 8"]:
            add(text)
        for reg, pin in [("rsi" if long else "esi", si)]:
            add(f"jmp {reg}", **{pin: "taken"})
            add(f"call {reg}", **{pin: "taken"})
        word = "qword ptr" if long else "dword ptr"
        if long:
            high = lambda value: (lambda index, rng: (rng.getrandbits(32) << 32) | value)
            base = self.layout["window"] + 248
            for text in ["mov esi, dword ptr [eax+8]", "mov dword ptr [eax+8], esi", "add esi, dword ptr [eax+8]", "mov sil, byte ptr [eax+ecx*2+8]"]:
                add(text, RAX=high(base), RCX=high(0))
            add("lea rsi, [eax+ecx*2+4]")
            add("lea rsi, [eax]")
        else:
            add("lea esi, [bx+si+16]")
            add("lea esi, [bp+di-16]")
            add("lea si, [bx+si+16]")
            add("lea esi, [bx]")
        add(f"lea rsi, [rbx+r15*4+16]" if long else "lea esi, [ebx+edi*4+16]")
        add(f"lea esi, [rbx+r15*4+16]" if long else "lea si, [ebx+edi*4+16]")
        add(f"lea si, [rbx+r15*4+16]" if long else "lea esi, [bx+di+16]")
        if long:
            add("lea rsi, [rip+64]")
            add("lea esi, [eax+ecx*2+4]")
        result = []
        for index, code in assemble(self, lines):
            case = Case(code=code, text=lines[index], pins=dict(spec.get(lines[index], {})))
            if case.text.startswith("ret"):
                case.pinmem = {256: ("taken", 8 if long else 4)}
            result.append(case)
        for text, pin in [(f"jmp {word} [{rb}+8]", bx), (f"call {word} [{rb}+8]", bx)]:
            for index, code in assemble(self, [text]):
                result.append(Case(code=code, text=text, pins={pin: "window+248"}, pinmem={256: ("taken", 8 if long else 4)}))
        return result

    def _corpus(self, name):
        Case = case_type()
        result = []
        for code, text in corpus_lines(name):
            if len(code) > 15:
                continue
            found = list(re.finditer(r"(-?0x[0-9a-f]+)?\(%(\w+)(?:,%(\w+),(\d))?\)", text))
            if "rip" in text or "eip" in text or "%fs" in text or "%gs" in text or "<" in text:
                continue
            pins = {}
            good = True
            for match in found:
                disp = int(match.group(1), 16) if match.group(1) else 0
                reg = match.group(2).upper()
                if reg not in dict(self.gprs):
                    good = False
                    continue
                pins[reg] = f"window+{248 - disp}"
                if match.group(3):
                    pins[match.group(3).upper()] = 8
                if not (-200 <= disp <= 200):
                    good = False
            if good:
                result.append(Case(code=code, text=text, pins=pins))
        return result

    def cases(self, opcodes, assemble, layout):
        result = self._text_cases(assemble) + self._extra(layout)
        for case in result:
            case.always = True
        result += self.from_shapes(opcodes, assemble, self._mnemonics(opcodes), x86_shapes(self.long), x86_pins(self.long))
        result += self._corpus(self.corpus_name)
        return result


class X8664(X86):
    name = "x86_64"
    word = 8
    runner = []
    cflags = ["--target=x86_64-linux-gnu", "-mno-red-zone"]
    lean = "x86_64"
    mc_triple = "x86_64-linux-gnu"
    corpus_name = "x86_64"
    pc_mask = 0
    gprs = [(n, 64) for n in ["RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]]
    vectors = [(f"ZMM{i}", 256) for i in range(16)] + [(f"MM{i}", 64) for i in range(8)]
    default_pins = {"RSP": "window+256"}

    def __init__(self, scratch):
        super().__init__(scratch)
        # the variables are of 512 bits; the input has them zero above what this machine has
        self.lean_vars = [(n, 512 if n.startswith("ZMM") else w) for n, w in self.lean_vars]

    def aux_spec(self):
        spec = {"MXCSR": (0x1F80, 32), "FPU_CONTROL": (0x37F, 16), "IF": (1, 1), "FS_BASE": (0, 64), "GS_BASE": (0, 64), "RIP": (0, 64), **EFLAGS_AUX}
        for i in range(16, 32):
            spec[f"ZMM{i}"] = (0, 512)
        return spec

    def shape(self, case, values, index, rng):
        x86_shape(case, values, index, "RAX", "RDX", "RCX")

    def encode(self, values, size):
        out = b"".join(struct.pack("<Q", values[n]) for n, _ in self.gprs)
        out += struct.pack("<Q", self.encode_flags(values))
        for i in range(16):
            out += values[f"ZMM{i}"].to_bytes(32, "little")
        for i in range(8):
            out += values[f"MM{i}"].to_bytes(8, "little")
        return out

    def decode(self, data):
        out = {}
        for i, (n, _) in enumerate(self.gprs):
            out[n] = struct.unpack_from("<Q", data, i * 8)[0]
        out.update(self.decode_flags(struct.unpack_from("<Q", data, 128)[0]))
        for i in range(16):
            out[f"ZMM{i}"] = int.from_bytes(data[136 + 32 * i : 136 + 32 * i + 32], "little")
        for i in range(8):
            out[f"MM{i}"] = int.from_bytes(data[648 + 8 * i : 656 + 8 * i], "little")
        return out


class X8632(X86):
    def relevant(self, name):
        # what only the 64-bit mode has
        return re.search(r"64|^(CDQE|CQO|SYSRET|SWAPGS|LODSQ|STOSQ|SCASQ|CMPSQ|MOVSQ|CMPXCHG16B|V?PEXTRQ|V?PINSRQ|RDSSPQ|INCSSPQ|WRSSQ|WRUSSQ|LEAVE64)", name) is None

    name = "i686"
    word = 4
    long = False
    runner = []
    cflags = ["--target=i386-linux-gnu", "-m32"]
    lean = "i686"
    mc_triple = "i386-linux-gnu"
    corpus_name = "i686"
    gprs = [(n, 32) for n in ["EAX", "ECX", "EDX", "EBX", "ESP", "EBP", "ESI", "EDI"]]
    vectors = [(f"ZMM{i}", 256) for i in range(8)] + [(f"MM{i}", 64) for i in range(8)]
    default_pins = {"ESP": "window+256"}

    def __init__(self, scratch):
        super().__init__(scratch)
        self.lean_vars = [(n, 512 if n.startswith("ZMM") else w) for n, w in self.lean_vars]

    def aux_spec(self):
        return {"MXCSR": (0x1F80, 32), "FPU_CONTROL": (0x37F, 16), "IF": (1, 1), "FS_BASE": (0, 32), "GS_BASE": (0, 32), "EIP": (0, 32), **EFLAGS_AUX}

    def shape(self, case, values, index, rng):
        x86_shape(case, values, index, "EAX", "EDX", "ECX")

    def encode(self, values, size):
        out = b"".join(struct.pack("<I", values[n]) for n, _ in self.gprs)
        out += struct.pack("<I", self.encode_flags(values))
        for i in range(8):
            out += values[f"ZMM{i}"].to_bytes(32, "little")
        for i in range(8):
            out += values[f"MM{i}"].to_bytes(8, "little")
        return out

    def decode(self, data):
        out = {}
        for i, (n, _) in enumerate(self.gprs):
            out[n] = struct.unpack_from("<I", data, i * 4)[0]
        out.update(self.decode_flags(struct.unpack_from("<I", data, 32)[0]))
        for i in range(8):
            out[f"ZMM{i}"] = int.from_bytes(data[36 + 32 * i : 36 + 32 * i + 32], "little")
        for i in range(8):
            out[f"MM{i}"] = int.from_bytes(data[292 + 8 * i : 300 + 8 * i], "little")
        return out


def x86_shape(case, values, index, ax, dx, cx):
    """A division whose quotient fits on half of its runs, so a run isn't only of the fault."""
    if case.opcode.startswith(("DIV", "IDIV")) and index % 2 == 0:
        values[dx] = 0
        values[ax] &= 0x7FFFFFFF
        if case.opcode.endswith(("8r", "8m")):
            values[ax] &= 0xFF
        elif "16" in case.opcode:
            values[ax] &= 0x7FFF
    # the offset of a bit string in memory stays in the window
    if re.match(r"BT[SRC]?(16|32|64)mr", case.opcode):
        for name in ("RSI", "ESI"):
            if name in values:
                values[name] = ((-96 + (index * 37) % 192) & 0xFFFFFFFFFFFFFFFF) & ((1 << (64 if name[0] == "R" else 32)) - 1)
    # counts: often in the edge of the size of the operation
    if case.opcode.endswith("CL") and index % 3:
        values[cx] = (values[cx] & ~0xFF) | [0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 0xFF][index % 16]


def operand_bits(opcode):
    found = re.search(r"(8|16|32|64)", opcode)
    return int(found.group(1)) if found else 0


def last_immediate(text):
    found = re.findall(r"(?:^|[ ,])(-?(?:0x[0-9a-f]+|\d+))(?:$|\s)", text)
    return int(found[-1], 0) if found else None


# Flags that the Intel SDM (and the AMD manual) leave undefined, from memory of them, not read off the text, see Bap/Proofs.lean.
UNDEFINED_LOGIC = {"AF"}
UNDEFINED_MUL = {"SF", "ZF", "AF", "PF"}
UNDEFINED_DIV = {"CF", "OF", "SF", "ZF", "AF", "PF"}


def undefined_x86(cfg, case, values, final):
    op = case.opcode
    cx = "RCX" if "RCX" in values else "ECX"
    if re.match(r"(LOCK_)?(AND|OR|XOR|TEST)(8|16|32|64)", op) or re.match(r"(AND|OR|XOR)\d", op):
        return UNDEFINED_LOGIC
    if re.match(r"(MUL|IMUL)(8|16|32|64)", op):
        return UNDEFINED_MUL
    if re.match(r"(DIV|IDIV)(8|16|32|64)", op):
        return UNDEFINED_DIV
    match = re.match(r"(SHL|SHR|SAR|ROL|ROR|RCL|RCR)(8|16|32|64)", op)
    if match:
        family, bits = match.group(1), int(match.group(2))
        if op.endswith("CL"):
            raw = values[cx] & 0xFF
        elif op.endswith(("r1", "m1")):
            raw = 1
        else:
            raw = (last_immediate(case.asm) or 0) & 0xFF
        count = raw & (63 if bits == 64 else 31)
        if count == 0:
            return set()
        out = set()
        if count != 1:
            out.add("OF")
        if family in ("SHL", "SHR", "SAR"):
            out.add("AF")
            if count >= bits and family != "SAR":
                out.add("CF")
        return out
    match = re.match(r"(SHLD|SHRD)(16|32|64)", op)
    if match:
        bits = int(match.group(2))
        raw = (values[cx] & 0xFF) if op.endswith("CL") else (last_immediate(case.asm) or 0) & 0xFF
        count = raw & (63 if bits == 64 else 31)
        if count == 0:
            return set()
        out = {"AF"}
        if count != 1:
            out.add("OF")
        if count > bits:
            # the result too, which is in the memory or in the destination, see `dest_of`
            out |= {"CF", "SF", "ZF", "PF", "OF"} | dest_of(case)
        return out
    if re.match(r"(BSF|BSR)(16|32|64)", op):
        out = {"CF", "OF", "SF", "AF", "PF"}
        if final["ZF"]:
            out |= dest_of(case)
        return out
    if re.match(r"(BT|BTS|BTR|BTC)(16|32|64)", op):
        return {"OF", "SF", "AF", "PF"}
    if re.match(r"(ANDN|BLSI|BLSMSK|BLSR|BZHI)(32|64)", op):
        return {"AF", "PF"}
    if re.match(r"BEXTR(32|64)", op):
        return {"AF", "SF", "PF"}
    if re.match(r"(TZCNT|LZCNT)(16|32|64)", op):
        return {"OF", "SF", "PF", "AF"}
    if op.startswith(("AAA", "AAS")):
        return {"OF", "SF", "ZF", "PF"}
    if op.startswith(("DAA", "DAS")):
        return {"OF"}
    if op.startswith(("AAM", "AAD")):
        return {"OF", "AF", "CF"}
    if re.match(r"BSWAP16", op):
        return dest_of(case)
    return set()


LOW_TO_BASE = {}
for base, names in {"RAX": "rax eax ax al ah", "RBX": "rbx ebx bx bl bh", "RCX": "rcx ecx cx cl ch", "RDX": "rdx edx dx dl dh", "RSI": "rsi esi si sil",
        "RDI": "rdi edi di dil", "RBP": "rbp ebp bp bpl", "RSP": "rsp esp sp spl"}.items():
    for low in names.split():
        LOW_TO_BASE[low] = base
for number in range(8, 16):
    for suffix in ["", "d", "w", "b"]:
        LOW_TO_BASE[f"r{number}{suffix}"] = f"R{number}"


def dest_of(case):
    first = case.asm.split(" ", 1)
    if len(first) < 2:
        return set()
    operand = first[1].split(",")[0].strip()
    base = LOW_TO_BASE.get(operand)
    if not base:
        return {"memory"}
    # the register of either mode, of which the state has one
    return {base, "E" + base[1:]}


TARGETS = {"x86_64": X8664, "i686": X8632}


def config(name, scratch):
    return TARGETS[name](scratch)


# The load and store architectures: the registers are written with a word of the machine each -------------------------------


class Risc(Target):
    """A target whose state is `NGPR` words, then `flag_words` words, then vectors, and whose base and index registers
    in its shapes are held to the window."""

    gpr_slots = []  # the Lean variable of each word of the registers, or None
    extra_slots = 0
    vector_bytes = 0
    cond_shapes = ()

    def encode(self, values, size):
        out = bytearray(size)
        for index, name in enumerate(self.gpr_slots):
            if name:
                out[index * self.word : (index + 1) * self.word] = self.word_bytes(values[name])
        self.encode_extra(values, out)
        return bytes(out)

    def decode(self, data):
        result = {}
        for index, name in enumerate(self.gpr_slots):
            if name:
                result[name] = int.from_bytes(data[index * self.word : (index + 1) * self.word], "big" if self.endian == ">" else "little")
        self.decode_extra(data, result)
        return result

    def encode_extra(self, values, out):
        pass

    def decode_extra(self, data, result):
        pass

    def extra_word(self, data, index):
        offset = (len(self.gpr_slots) + index) * self.word
        return int.from_bytes(data[offset : offset + self.word], "big" if self.endian == ">" else "little")

    def set_extra_word(self, out, index, value):
        offset = (len(self.gpr_slots) + index) * self.word
        out[offset : offset + self.word] = self.word_bytes(value)

    def _pinned(self, _text):
        return dict(self.base_pins)

    base_pins = {}
    mnemonics_of = None
    shape_list = []
    corpus_name = ""
    excluded_prefix = ()

    def excluded(self, opcode, case):
        for prefix in self.excluded_prefix:
            if opcode.startswith(prefix):
                return "system, or depends on what isn't in the state"
        return None

    def hand(self, assemble, layout):
        return []

    def corpus_memory(self, text):
        """The registers to hold for the upstream's forms, or None if it can't be run here."""
        return {}

    def corpus_code(self, code):
        return code

    def cases(self, opcodes, assemble, layout):
        Case = case_type()
        result = self.hand(assemble, layout)
        for case in result:
            case.always = True
        names = set()
        for name in opcodes:
            names.update(self.mnemonics_of(name))
        result += self.from_shapes(opcodes, assemble, names, self.shape_list, self._pinned)
        for code, text in corpus_lines(self.corpus_name):
            pins = self.corpus_memory(text)
            if pins is not None:
                result.append(Case(code=self.corpus_code(code), text=text, pins=pins))
        return result

    def text_cases(self, assemble, items):
        """`(assembly, pins, pinmem)`."""
        Case = case_type()
        lines = [item[0] for item in items]
        result = []
        for index, code in assemble(self, lines):
            item = items[index]
            result.append(Case(code=code, text=item[0], pins=item[1] if len(item) > 1 else {}, pinmem=item[2] if len(item) > 2 else {}))
        return result


# AArch64 -----------------------------------------------------------------------------------------------------------------


def aarch64_stems(name):
    stem = re.match(r"[A-Z0-9_]+", name)
    if not stem:
        return []
    stem = stem.group(0)
    result = {stem.lower(), stem.rstrip("0123456789_").lower()}
    structure = re.match(r"(LD|ST)[1-4]R?", name)
    if structure:
        result.add(structure.group(0).lower())
    if name.startswith("SHA") or name.startswith("SM"):
        result.add(re.sub(r"(rrr|rr)$", "", name).lower())
    for suffix in ("W", "X", "S", "D", "Q", "B", "H", "WB", "SB", "SH", "SW", "BB", "HH", "XW", "WX"):
        if stem.endswith(suffix):
            result.add(stem[: -len(suffix)].lower())
    return sorted(s for s in result | {r + "2" for r in result} if s)


def aarch64_shapes():
    shapes = [""]
    for x, y, z, u in [("x1", "x2", "x3", "x4"), ("w1", "w2", "w3", "w4")]:
        shapes += [x, f"{x}, {y}", f"{x}, {y}, {z}", f"{x}, {y}, {z}, {u}", f"{x}, #5", f"{x}, {y}, #5", f"{x}, {y}, #3, #9", f"{x}, {y}, {z}, #5",
            f"{x}, {y}, {z}, lsl #3", f"{x}, {y}, {z}, lsr #3", f"{x}, {y}, {z}, asr #3", f"{x}, {y}, {z}, ror #3",
            f"{x}, {y}, #0xff", f"{x}, {y}, #0xf0", f"{x}, #5, lsl #16", f"{x}, {y}, lsl #3", f"{x}, {y}, #5, lsl #12", f"{x}, {y}, w3, uxtw #2", f"{x}, {y}, w3, sxtw #2",
            f"{x}, {y}, w3, uxtb #1", f"{x}, {y}, w3, sxth #1", f"{x}, {y}, x3, sxtx #1", f"{x}, {y}, x3, uxtx #1", f"{x}, {y}, {z}, eq", f"{x}, {y}, {z}, lt", f"{x}, {y}, eq", f"{x}, eq",
            f"{x}, {y}, #5, eq", f"{y}, {z}, #5, ne", f"{x}, #5, #5, eq", f"{x}, {y}, #5, hi",
            f"{x}, [x5, #8]", f"{x}, [x5], #8", f"{x}, [x5, #8]!", f"{x}, [x5, x6]", f"{x}, [x5, x6, lsl #{3 if x[0] == 'x' else 2}]", f"{x}, [x5, w6, uxtw]", f"{x}, [x5, x6, sxtx]", f"{x}, [x5]",
            f"{x}, [x5, #-8]", f"{x}, {y}, [x5]", f"{x}, {y}, [x5, #16]", f"{x}, {y}, [x5], #16", f"{x}, {y}, [x5, #16]!", f"{x}, {y}, {z}, [x5]"]
    shapes += ["x1, w2", "x1, w2, w3", "x1, w2, w3, x4", "x1, x2, w3", "x1, x2, x3, lsl #1", "x1, sp", "sp, x1", "x1, sp, #16", "sp, sp, #16", "x1, x2, #3", "w1, x2", "w1, w2, x3"]
    sizes = ["8b", "16b", "4h", "8h", "2s", "4s", "1d", "2d"]
    for t in sizes:
        v1, v2, v3, v4 = (f"v{i}.{t}" for i in (1, 2, 3, 4))
        shapes += [f"{v1}, {v2}, {v3}", f"{v1}, {v2}", f"{v1}, {v2}, #3", f"{v1}, {v2}, {v3}, #1", f"{v1}, #5", f"{v1}, #5, lsl #8", v1, f"{v1}, x2", f"{v1}, w2",
            f"{v1}, v2.b[1]", f"{v1}, v2.h[1]", f"{v1}, v2.s[1]", f"{v1}, v2.d[1]", f"{v1}, v2.b[0]", f"{v1}, {v2}, #0", f"{v1}, #5, msl #8", f"{v1}, {v2}, {v3}, {v4}", f"{v1}, {v2}, v3.2d",
            f"{v1}, {v2}, v3.h[1]", f"{v1}, {v2}, v3.s[1]", f"{v1}, {v2}, v3.d[1]",
            f"{{ {v1} }}, [x5]", f"{{ {v1}, {v2} }}, [x5]", f"{{ {v1}, {v2}, {v3} }}, [x5]", f"{{ {v1}, {v2}, {v3}, {v4} }}, [x5]", f"{{ {v1} }}, [x5], x6", f"{{ {v1}, {v2} }}, [x5], x6", f"{{ {v1}, {v2}, {v3} }}, [x5], x6", f"{{ {v1}, {v2}, {v3}, {v4} }}, [x5], x6",
            *[f"{{ {v1}{''.join(', ' + o for o in others)} }}, [x5], #{(8 if t in ('8b','4h','2s','1d') else 16) * (len(others) + 1)}" for others in ([], [v2], [v2, v3], [v2, v3, v4])],
 f"{v1}, {{ {v2.split('.')[0]}.16b }}, {v3}", f"{v1}, {{ {v2.split('.')[0]}.16b, {v3.split('.')[0]}.16b }}, {v4}"]
        for s in sizes:
            if s != t:
                shapes += [f"{v1}, v2.{s}", f"{v1}, v2.{s}, v3.{s}", f"{v1}, v2.{s}, #3", f"{v1}, {v2}, v3.{s}", f"{v1}, v2.{s}, v3.h[1]", f"{v1}, v2.{s}, v3.s[1]",
                    f"{v1}, v2.{s}, #8", f"{v1}, v2.{s}, #16", f"{v1}, v2.{s}, #32"]
    for reg, *_ in [("b",), ("h",), ("s",), ("d",), ("q",)]:
        a, b, c = f"{reg}1", f"{reg}2", f"{reg}3"
        shapes += [a, f"{a}, {b}", f"{a}, {b}, {c}", f"{a}, {b}, #3", f"{a}, [x5, #8]", f"{a}, [x5], #8", f"{a}, [x5, #8]!", f"{a}, [x5, x6]", f"{a}, [x5]", f"{a}, {b}, [x5]", f"{a}, {b}, [x5, #16]",
            f"{a}, w2", f"{a}, x2", f"w1, {a}", f"x1, {a}", f"{a}, {b}, {c}, {reg}4", f"{a}, v2.16b", f"{a}, v2.8h", f"{a}, v2.4s", f"{a}, v2.2d", f"{a}, v2.2s", f"{a}, v2.8b", f"{a}, v2.4h",
            f"{a}, v2.b[1]", f"{a}, v2.h[1]", f"{a}, v2.s[1]", f"{a}, v2.d[1]", f"{a}, h2", f"{a}, s2", f"{a}, d2", f"{a}, {b}, v3.h[1]", f"{a}, {b}, v3.s[1]", f"{a}, {b}, v3.d[1]", f"{a}, {b}, #0", f"{a}, #1.0", f"{a}, #0.0", f"{a}, {b}, #5, eq", f"{a}, {b}, {c}, eq", f"{a}, w2, #3", f"{a}, x2, #3", f"w1, {a}, #3", f"x1, {a}, #3",
            f"{a}, s2, v3.4s", f"{a}, {b}, v3.4s", f"{a}, v2.4s, v3.4s", f"{a}, #0xff", f"{a}, h2, h3", f"{a}, s2, s3", f"{a}, h2, v3.h[1]", f"{a}, s2, v3.s[1]", f"{a}, h2, s3", f"{a}, s2, d3"]
    for lane, r, idx in [("b", "w2", 1), ("h", "w2", 1), ("s", "w2", 1), ("d", "x2", 1)]:
        shapes += [f"v1.{lane}[{idx}], {r}", f"w1, v2.{lane}[{idx}]", f"x1, v2.{lane}[{idx}]", f"v1.{lane}[{idx}], v2.{lane}[0]", f"{{ v1.{lane} }}[{idx}], [x5]"]
    return shapes


def aarch64_zero_forms():
    """The zero register in each position of a source, whose width is that of the instruction: the shapes never use it."""
    forms = []
    for r, z in [("w", "wzr"), ("x", "xzr")]:
        a, b, c = f"{r}1", f"{r}2", f"{r}3"
        for op in ["add", "adds", "sub", "subs", "and", "ands", "orr", "orn", "eor", "eon", "bic", "bics", "adc", "adcs", "sbc", "sbcs", "lsl", "lsr", "asr", "ror", "mul", "udiv", "sdiv"]:
            forms += [f"{op} {a}, {z}, {b}", f"{op} {a}, {b}, {z}"]
        for op in ["add", "adds", "sub", "subs", "and", "ands", "orr", "orn", "eor", "eon", "bic", "bics"]:
            forms += [f"{op} {a}, {z}, {b}, lsr #1"]
        for op in ["cmp", "cmn", "tst"]:
            forms += [f"{op} {z}, {b}", f"{op} {b}, {z}", f"{op} {z}, {b}, lsr #1"]
        for op in ["csel", "csinc", "csinv", "csneg"]:
            forms += [f"{op} {a}, {z}, {b}, eq", f"{op} {a}, {b}, {z}, ne", f"{op} {a}, {z}, {z}, eq"]
        for op in ["ccmp", "ccmn"]:
            forms += [f"{op} {z}, {b}, #5, eq", f"{op} {b}, {z}, #5, ne", f"{op} {z}, #3, #5, ne"]
        for op in ["madd", "msub"]:
            forms += [f"{op} {a}, {z}, {b}, {c}", f"{op} {a}, {b}, {z}, {c}", f"{op} {a}, {b}, {c}, {z}"]
        for op in ["rev", "rbit", "clz", "cls", "mov", "mvn", "neg", "negs", "sxtb", "sxth", "uxtb", "uxth"]:
            forms += [f"{op} {a}, {z}"]
        forms += [f"ubfx {a}, {z}, #1, #3", f"sbfx {a}, {z}, #1, #3", f"bfi {a}, {z}, #3, #5", f"bfxil {a}, {z}, #3, #5", f"extr {a}, {z}, {b}, #5", f"extr {a}, {b}, {z}, #5"]
        forms += [f"dup v1.2d, {z}" if r == "x" else f"dup v1.4s, {z}", f"ins v1.d[1], {z}" if r == "x" else f"ins v1.s[1], {z}", f"fmov d1, {z}" if r == "x" else f"fmov s1, {z}"]
        forms += [f"scvtf d1, {z}", f"ucvtf s1, {z}"]
    forms += ["crc32b w1, wzr, w2", "crc32w w1, w2, wzr", "crc32x w1, wzr, x2", "crc32x w1, w2, xzr", "smull x1, wzr, w2", "umull x1, w2, wzr", "smaddl x1, wzr, w2, x3", "umsubl x1, w2, wzr, x3", "smaddl x1, w2, w3, xzr",
        "add x1, x2, wzr, uxtw #2", "sub x1, x2, wzr, sxtw", "adds x1, x2, wzr, uxtb", "cmp x2, wzr, uxtw", "sxtw x1, wzr", "smulh x1, xzr, x2", "umulh x1, x2, xzr"]
    return forms


SVE_PREDICATES = [f"P{i}" for i in range(16)] + ["FFR"]


class AArch64(Risc):
    name = "aarch64"
    word = 8
    # SVE has a vector length of 128 bits in the lifter, see semantics/arm/aarch64-sve.lisp
    runner = ["qemu-aarch64", "-cpu", "max,sve-max-vq=1"]
    cflags = ["--target=aarch64-linux-gnu"]
    lean = "aarch64"
    mc_triple = "aarch64-linux-gnu"
    mc_args = ["--mattr=+v8.1a,+v8.2a,+v8.3a,+fullfp16,+aes,+sha2,+sha3,+sm4,+crc,+lse,+rdm,+dotprod,+fp16fml,+flagm,+rand,+pauth,+jsconv,+complxnum,+rcpc,+fptoint,+sb"]
    corpus_name = "aarch64"
    nop = bytes.fromhex("1f2003d5")
    gpr_slots = [f"X{i}" for i in range(31)] + ["SP"]
    gprs = [(f"X{i}", 64) for i in range(31)] + [("SP", 64)]
    flags = [("NF", 31), ("ZF", 30), ("CF", 29), ("VF", 28)]
    vectors = [(f"Q{i}", 128) for i in range(32)] + [(f"P{i}", 16) for i in range(16)] + [("FFR", 16)]
    default_pins = {"SP": "window+256"}
    base_pins = {"X5": "window+248", "X6": 8}
    semantics = ["arm/aarch64-arithmetic.lisp", "arm/aarch64-atomic.lisp", "arm/aarch64-branch.lisp", "arm/aarch64-data-movement.lisp", "arm/aarch64-float.lisp",
        "arm/aarch64-logical.lisp", "arm/aarch64-pstate.lisp", "arm/aarch64-simd.lisp", "arm/aarch64-special.lisp", "arm/aarch64-sve.lisp"]
    mnemonics_of = staticmethod(aarch64_stems)
    excluded_prefix = ("SVC", "HVC", "SMC", "BRK", "HLT", "HINT", "SYS", "MSR", "MRS", "DCPS", "ERET", "DRPS", "CLREX", "WFE", "WFI", "PAC", "AUT", "XPAC", "RET", "BLRA", "BRA", "ERETA", "LDRAA", "LDRAB", "UDF", "GCS", "RNDR", "TSB", "CSDB", "PSB")
    pc_mask = 0

    def __init__(self, scratch):
        self.shape_list = aarch64_shapes()
        super().__init__(scratch)

    def aux_spec(self):
        return {"XZR": (0, 64), "EXCLUSIVE_MONITOR": (0, 64), "FPCR": (0, 32), "FPSR": (0, 32), "DAIF": (0, 4), "SPSel": (0, 1), "PAN": (0, 1), "UAO": (0, 1), "TPIDR_EL0": (0, 64), "TPIDRRO_EL0": (0, 64),
            "SP_EL0": (0, 64), "SP_EL1": (0, 64), "CNTVCT_EL0": (0, 64)}

    def encode_extra(self, values, out):
        word = 0
        for name, bit in self.flags:
            word |= values[name] << bit
        self.set_extra_word(out, 0, word)
        base = (32 + 2) * 8
        for index in range(32):
            out[base + index * 16 : base + (index + 1) * 16] = values[f"Q{index}"].to_bytes(16, "little")
        base += 32 * 16
        for index, name in enumerate(SVE_PREDICATES):
            out[base + index * 2 : base + (index + 1) * 2] = values[name].to_bytes(2, "little")

    def decode_extra(self, data, result):
        word = self.extra_word(data, 0)
        for name, bit in self.flags:
            result[name] = (word >> bit) & 1
        base = (32 + 2) * 8
        for index in range(32):
            result[f"Q{index}"] = int.from_bytes(data[base + index * 16 : base + (index + 1) * 16], "little")
        base += 32 * 16
        for index, name in enumerate(SVE_PREDICATES):
            result[name] = int.from_bytes(data[base + index * 2 : base + (index + 1) * 2], "little")

    def shape(self, case, values, index, rng):
        """The predicates: of each size of an element, of the edges, and any. FFR is monotonic, as what writes it must be."""
        for name in SVE_PREDICATES[:-1]:
            values[name] = rng.choice([0xFFFF, 0x5555, 0x1111, 0x0101, 0, (1 << rng.randrange(17)) - 1, rng.getrandbits(16), rng.getrandbits(16)])
        values["FFR"] = (1 << rng.randrange(17)) - 1
        # what a first-fault load leaves after a clear bit of FFR is constrained unpredictable
        if case.text.startswith(("ldff1", "ldnf1")):
            values["FFR"] = 0xFFFF
            # qemu 10.2 reads all zeros, with FFR as it was, if the element 0 of a contiguous one is inactive, which the Arm ARM
            # doesn't allow, so that isn't compared; gathers don't do this
            if "z" not in re.search(r"\[[^\]]*\]", case.text).group(0):
                governing = "P" + re.search(r"p(\d+)/z", case.text).group(1)
                values[governing] |= 1
        written = re.match(r"wrffr\s+p(\d+)", case.text)
        if written:
            values[f"P{written.group(1)}"] = (1 << rng.randrange(17)) - 1

    def cases(self, opcodes, assemble, layout):
        # the operand forms of the assembler are of the others, SVE has a corpus of its own
        self.sve_opcodes = {name for name, path in opcodes.items() if path.endswith("-sve.lisp")}
        Case = case_type()
        result = super().cases({name: path for name, path in opcodes.items() if name not in self.sve_opcodes}, assemble, layout)
        for code, text in corpus_lines("aarch64-sve"):
            pins = self.sve_memory(text, layout)
            if pins is not None:
                result.append(Case(code=code, text=text, pins=pins))
        result += [dataclasses.replace(case, always=True) for case in self.text_cases(assemble, [(line,) for line in aarch64_zero_forms()])]
        return result

    def excluded(self, opcode, case):
        return None if opcode in self.sve_opcodes else super().excluded(opcode, case)

    def sve_memory(self, text, layout):
        """The registers of the addressing of an SVE instruction, held to the window, or None if it can't be run here."""
        found = re.search(r"\[([^\]]*)\]", text)
        if not found or text.startswith(("adr", "prf")):
            return {}
        parts = [part.strip() for part in found.group(1).split(",")]
        base, pins = parts[0], {}

        def number(token):
            return int(token.lstrip("#"), 0)

        def lanes(register, make):
            bits = {"s": 32, "d": 64}[register.split(".")[1]]

            def value(index, rng):
                return sum((make(rng) & ((1 << bits) - 1)) << (lane * bits) for lane in range(128 // bits))

            return {"Q" + register.split(".")[0][1:]: value}

        if base.startswith("z"):
            # the elements of the vector are the addresses, and the immediate goes up to 248
            window = layout["window"]
            pins.update(lanes(base, lambda rng: window + rng.randrange(128)))
            return pins
        offset = parts[1] if len(parts) > 1 else ""
        if offset.startswith("z"):
            # the offsets are small either way, a scale is up to 8
            low = 0 if "uxtw" in found.group(1) else -16
            pins.update(lanes(offset, lambda rng: rng.randrange(low, 24)))
            displacement = 128
        elif offset.startswith(("x", "w")):
            if offset == base:
                return None
            pins[offset.upper()] = 8
            displacement = 240
        elif offset:
            displacement = 240 - number(offset) * (16 if "mul" in found.group(1) else 1)
            if not 0 <= displacement <= 400:
                return None
        else:
            displacement = 240
        if base != "sp":
            pins[base.upper()] = f"window+{displacement}"
        elif displacement != 240:
            pins["SP"] = f"window+{displacement}"
        return pins

    def hand(self, assemble, layout):
        conds = ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", "al", "nv"]
        items = [("b #64",), ("bl #64",), ("br x1", {"X1": "taken"}), ("blr x1", {"X1": "taken"}), ("ret x1", {"X1": "taken"}), ("ret", {"X30": "taken"})]
        items += [(f"b.{c} #64",) for c in conds]
        items += [("cbz x1, #64",), ("cbnz x1, #64",), ("cbz w1, #64",), ("cbnz w1, #64",), ("tbz x1, #33, #64",), ("tbnz x1, #33, #64",), ("tbz w1, #3, #64",), ("tbnz w1, #3, #64",)]
        items += [("adr x1, #64",), ("adrp x1, #4096",), ("nop",), ("cfinv",), ("rmif x1, #3, #5",), ("setf8 w1",), ("setf16 w1",)]
        for c in conds:
            items += [(f"csel x1, x2, x3, {c}",), (f"csinc w1, w2, w3, {c}",), (f"csinv x1, x2, x3, {c}",), (f"csneg w1, w2, w3, {c}",), (f"ccmp x1, x2, #5, {c}",), (f"ccmn w1, #3, #9, {c}",), (f"cset x1, {c}",), (f"fcsel d1, d2, d3, {c}",)]
        items += [("mrs x1, nzcv",), ("msr nzcv, x1",), ("ldr x1, #8",), ("ldr w1, #8",), ("ldrsw x1, #8",), ("ldr q1, #8",), ("ldr d1, #8",), ("ldr s1, #8",)]
        cases = self.text_cases(assemble, items)
        # the edges that random inputs rarely reach: a memory that holds the pair a CASP compares with half of the time, and the
        # doubles and the halves on the bounds of what FJCVTZS and FRECPX tell apart
        first, second = 0x1122334455667788, 0x99AABBCCDDEEFF00
        holds = lambda word, bits=64: (lambda index, rng: word if index % 2 == 0 else rng.getrandbits(bits))
        doubles = [0, 1 << 63, 1, 0x3FE0000000000000, 0x3FF8000000000000, 0xBFF8000000000000, 0x41DFFFFFFFC00000, 0x41E0000000000000, 0xC1E0000000000000, 0xC1E0000000200000,
            0x41E0000000200000, 0x4330000000000001, 0x4340000000000001, 0x4450000000000001, 0x4530000000000001, 0x4630000000000000, 0x7FF0000000000000, 0xFFF0000000000000,
            0x7FF8000000000000, 0x7FF0000000000001, 0x000FFFFFFFFFFFFF, 0x41DFFFFFFFFFFFFF, 0xC1DFFFFFFFFFFFFF, 0x41F0000000000000, 0xC1F0000000000001]
        halves = [0, 0x8000, 1, 0x3FF, 0x400, 0x3C00, 0xFC00, 0x7C00, 0x7C01, 0x7E01, 0xFFFF]
        singles = [0, 1 << 31, 1, 0x7FFFFF, 0x800000, 0x3F800000, 0xFF800000, 0x7F800000, 0x7F800001, 0x7FC00001, 0xFFFFFFFF]
        wide = [0, 1 << 63, 1, 0xFFFFFFFFFFFFF, 1 << 52, 0x3FF0000000000000, 0xFFF0000000000000, 0x7FF0000000000000, 0x7FF0000000000001, 0x7FF8000000000001, (1 << 64) - 1]
        among = lambda values: (lambda index, rng: values[index % len(values)])
        extra = [("fjcvtzs w1, d2", {"Q2": among(doubles)}), ("frecpx h1, h2", {"Q2": among(halves)}), ("frecpx s1, s2", {"Q2": among(singles)}), ("frecpx d1, d2", {"Q2": among(wide)})]
        for text in ("casp x0, x1, x2, x3, [x5]", "caspal x0, x1, x2, x3, [x5]"):
            extra.append((text, {"X0": first, "X1": second, "X5": "window+240"}, {240: (holds(first), 8), 248: (holds(second), 8)}))
        for text in ("casp w0, w1, w2, w3, [x5]", "caspal w0, w1, w2, w3, [x5]"):
            extra.append((text, {"X0": first, "X1": second, "X5": "window+248"}, {248: (holds(first & 0xFFFFFFFF, 32), 4), 252: (holds(second & 0xFFFFFFFF, 32), 4)}))
        extra.append(("casp x30, xzr, x2, x3, [x5]", {"X30": first, "X5": "window+240"}, {240: (holds(first), 8), 248: (holds(0), 8)}))
        extras = self.text_cases(assemble, extra)
        for case in extras:
            case.always = True
        return extras + cases

    def corpus_memory(self, text):
        if "<" in text:
            return None
        pins = {}
        for match in re.finditer(r"\[(x\d+|sp)(?:, #(-?(?:0x)?[0-9a-f]+))?(?:, ([xw])(\d+)[^\]]*)?\]", text):
            if match.group(1) == "sp":
                continue
            disp = int(match.group(2), 0) if match.group(2) else 0
            if abs(disp) > 200:
                return None
            # a CASP of X registers needs an address aligned to 16, and faults otherwise
            base = 240 if re.match(r"casp[al]*\s+x", text) else 248
            pins[match.group(1).upper()] = f"window+{base - disp}"
            if match.group(4):
                pins[f"X{match.group(4)}"] = 8
        return pins


# ARM ---------------------------------------------------------------------------------------------------------------------


def arm_stems(name):
    name = re.sub(r"^t2", "", name)
    name = re.sub(r"^t(?=[A-Z])", "", name)
    stem = re.match(r"[A-Z0-9_]+", name)
    if not stem:
        return []
    raw = stem.group(0).split("_")[0]
    stem = raw.rstrip("0123456789_")
    result = {stem, raw}
    # VREV32d8, VLD1d8, VTBL3 and QADD8 have digits of their mnemonics; VCMPEZD is of VCMPE
    if name.startswith("VCMP"):
        result |= {"VCMP", "VCMPE"}
    if name.startswith("VTO"):
        result |= {"VCVT", "VCVTR"}
    if name.endswith("TOS") or name.startswith("VSITO") or name.startswith("VUITO"):
        result.add("VCVT")
    if stem.endswith(("W", "S", "D", "Q")):
        result.add(stem[:-1])
    return sorted(r.lower() for r in result)


def arm_shapes(thumb):
    # r5 and r6 are held to the window, the rest are low for the 16-bit encodings
    shapes = [""]
    r = ("r1", "r2", "r3", "r4")
    a, b, c, d = r
    shapes += [a, f"{a}, {b}", f"{a}, {b}, {c}", f"{a}, {b}, {c}, {d}", f"{a}, #5", f"{a}, #200", f"{a}, {b}, #5", f"{a}, {b}, #200", f"{a}, {a}, #5", f"{a}, {a}, {c}", f"{a}, {b}, #3, #5", f"{a}, #5, {b}", f"{a}, #5, {b}, lsl #3",
        f"{a}, {b}, lsl #3", f"{a}, {b}, lsr #3", f"{a}, {b}, asr #3", f"{a}, {b}, ror #3", f"{a}, {b}, rrx", f"{a}, {b}, lsl {c}", f"{a}, {b}, asr {c}", f"{a}, {b}, lsr {c}", f"{a}, {b}, ror {c}",
        f"{a}, {b}, {c}, lsl #3", f"{a}, {b}, {c}, lsr #3", f"{a}, {b}, {c}, asr #3", f"{a}, {b}, {c}, ror #3", f"{a}, {b}, {c}, rrx", f"{a}, {b}, {c}, lsl {d}", f"{a}, {b}, {c}, asr {d}", f"{a}, {b}, {c}, lsr {d}", f"{a}, {b}, {c}, ror {d}", f"{a}, {b}, ror #8", f"{a}, {b}, {c}, ror #8",
        f"{a}, [r5]", f"{a}, [r5, #8]", f"{a}, [r5, #-8]", f"{a}, [r5, #8]!", f"{a}, [r5], #8", f"{a}, [r5, r6]", f"{a}, [r5, r6, lsl #2]", f"{a}, [r5, -r6]", f"{a}, [r5, r6]!", f"{a}, [r5], r6", f"{a}, {b}, [r5]", f"{a}, {b}, [r5, #8]", f"{a}, {b}, [r5, r6]", f"{a}, {b}, [r5, #8]!", f"{a}, {b}, [r5], #8", f"{a}, {b}, {c}, [r5]",
        f"r5, {{r1, r2, r3}}", f"r5!, {{r1, r2, r3}}", "{r1, r2, r3}", "r1, #3, #5", "r1, r2, r3, lsl r4", "r1, r2, [r5], #8", "r1, r2, [r5], r6", "r1, [r5], #8", f"{a}, {b}, [r5]", f"{a}, {b}, #3", f"{a}, #3, {b}", f"{a}, #3, {b}, lsl #1", f"{a}, #3, {b}, asr #1"]
    t = (".i8", ".i16", ".i32", ".i64", ".s8", ".s16", ".s32", ".s64", ".u8", ".u16", ".u32", ".u64", ".8", ".16", ".32", ".64", ".p8", ".f32", ".f64", "")
    neon = ["d1, d2, d3", "q1, q2, q3", "d1, d2", "q1, q2", "q1, d2, d3", "d1, q2, q3", "q1, q2, d3", "q1, d2", "d1, q2", "d1, d2, #3", "q1, q2, #3", "d1, d2, d3, #3", "q1, q2, q3, #3", "q1, d2, #3", "d1, q2, #3", "d1, d2, d3[1]", "q1, q2, d3[1]", "q1, d2, d3[1]", "d1, d2[1]", "q1, d2[1]", "s1, s2, s3", "s1, s2", "d1, r2, r3", "r1, r2, d3", "r1, d2[1]", "d1[1], r2", "d1, r2", "q1, r2", "d1, #5", "q1, #5", "s1, r2", "r1, s2", "d1, d2, #0", "q1, q2, #0", "{d1}, [r5]", "{d1, d2}, [r5]", "{d1, d2, d3}, [r5]", "{d1, d2, d3, d4}, [r5]", "{d1[0]}, [r5]", "{d1[]}, [r5]", "d1, [r5, #8]", "s1, [r5, #8]", "r5, {d1, d2}", "r5!, {d1, d2}", "r5, {s1, s2}", "r5!, {s1, s2}", "d1, {d2}, d3", "d1, {d2, d3}, d4", "d1, {d2, d3, d4}, d5", "d1, {d2, d3, d4, d5}, d6", "{d1}, [r5]!", "{d1}, [r5], r6", "{d1, d2}, [r5]!", "{d1, d2}, [r5], r6", "{d1, d2, d3}, [r5]!", "{d1, d2, d3}, [r5], r6", "{d1, d2, d3, d4}, [r5]!", "{d1, d2, d3, d4}, [r5], r6", "{d2, d3}, [r5]", "{d2, d3}, [r5]!", "{d2, d3}, [r5], r6", "{d1, d2, d3, d4}, [r5]", "{d1[0]}, [r5]!", "{d1[0]}, [r5], r6", "{d1[]}, [r5]!", "{d1[]}, [r5], r6", "{d1[], d2[]}, [r5]", "{d1[], d2[]}, [r5]!", "{d1[], d2[]}, [r5], r6", "q1, q2, r3", "d1, s2, s3", "r1, r2, s3, s4", "s3, s4, r1, r2", "d1, #1.0", "s1, #1.0", "q1, #1.0", "s1, #0", "d1, #0", "s1, d2", "d1, s2", "s1, s2, #16", "d1, d2, #16", "r5, {d1}", "r5!, {d1}", "r5, {s1}", "r5!, {s1}", "d1, d2, #16", "q1, q2, #16"]
    return shapes, t, neon


class Arm32(Risc):
    word = 4
    cflags = []
    mc_args = ["--mattr=+hwdiv,+hwdiv-arm,+vfp4,+neon,+dsp,+v7,+crc,+aes,+sha2"]
    gpr_slots = [f"R{i}" for i in range(13)] + ["SP", "LR", None]
    gprs = [(f"R{i}", 32) for i in range(13)] + [("SP", 32), ("LR", 32)]
    flags = [("NF", 31), ("ZF", 30), ("CF", 29), ("VF", 28), ("QF", 27), ("GE3", 19), ("GE2", 18), ("GE1", 17), ("GE0", 16)]
    vectors = [(f"D{i}", 64) for i in range(32)]
    runner = ["qemu-arm", "-cpu", "max"]
    default_pins = {"SP": "window+256"}
    base_pins = {"R5": "window+248", "R6": 8}
    semantics = ["arm/arm-a32.lisp", "arm/arm-a32-mem.lisp", "arm/arm-a32-multiple.lisp", "arm/arm-bits.lisp", "arm/arm-float.lisp", "arm/arm-vfp.lisp", "arm/thumb.lisp", "arm/thumb2.lisp", "arm/thumb-multiple.lisp", "arm/thumb-vfp.lisp"]
    excluded_prefix = ("SVC", "tSVC", "t2SVC", "BKPT", "tBKPT", "UDF", "tUDF", "t2UDF", "HLT", "tHLT", "MRC", "MCR", "t2MRC", "t2MCR", "MRS", "MSR", "t2MRS", "t2MSR", "VMRS", "VMSR", "HINT", "tHINT", "t2HINT", "CLREX", "t2CLREX", "DMB", "DSB", "ISB", "t2DMB", "t2DSB", "t2ISB", "CPS", "tCPS", "t2CPS", "SETEND", "tSETEND", "RFE", "SRS", "t2RFE", "t2SRS", "PLD", "PLI", "t2PLD", "t2PLI", "tIT", "t2IT", "t2TBB", "t2TBH", "LDC", "STC", "t2LDC", "t2STC", "CDP", "t2CDP", "STLEX", "LDAEX", "t2STLEX", "t2LDAEX")

    def aux_spec(self):
        spec = {"Nil": (0, 32), "EXCLUSIVE_MONITOR": (0, 32), "ISET": (0, 1), "CPSR": (0, 32), "FPSCR": (0, 32), "TPIDRURO": (0, 32), "TPIDRURW": (0, 32), "PC": (0, 32)}
        return spec

    def encode_extra(self, values, out):
        word = 0
        for name, bit in self.flags:
            word |= values[name] << bit
        self.set_extra_word(out, 0, word)
        base = (16 + 2) * 4
        for index in range(32):
            out[base + index * 8 : base + (index + 1) * 8] = values[f"D{index}"].to_bytes(8, "little")

    def decode_extra(self, data, result):
        word = self.extra_word(data, 0)
        for name, bit in self.flags:
            result[name] = (word >> bit) & 1
        base = (16 + 2) * 4
        for index in range(32):
            result[f"D{index}"] = int.from_bytes(data[base + index * 8 : base + (index + 1) * 8], "little")

    pc_mask = 1

    def from_shapes(self, opcodes, assemble, mnemonics, shapes, pins):
        base, types, neon = arm_shapes(self.thumb)
        Case = case_type()
        lines = []
        for mnemonic in sorted(mnemonics):
            variants = [mnemonic, mnemonic + "s"] + ([mnemonic + ".w", mnemonic + "s.w"] if self.thumb else [])
            for variant in variants:
                lines += [f"{variant} {shape}".strip() for shape in base]
            if mnemonic.startswith("v"):
                for suffix in types:
                    lines += [f"{mnemonic}{suffix} {shape}" for shape in neon]
        # a load of the pc beyond the slot reads the stub, not the state
        lines = [line for line in lines if not re.match(r"ldr\S* r1, #", line)]
        result = []
        for index, code in assemble(self, lines):
            result.append(Case(code=code, text=lines[index], pins=pins(lines[index])))
        return result

    def relevant(self, name):
        thumbish = name.startswith(("t2", "tB", "tA", "tC", "tE", "tL", "tM", "tN", "tO", "tP", "tR", "tS", "tT", "tU", "tH", "tI"))
        return thumbish == self.thumb or (not thumbish and name.startswith("V"))

    def corpus_memory(self, text):
        if "<" in text or "pc" in text:
            return None
        pins = {}
        for match in re.finditer(r"\[(r\d+|fp|sl|ip|lr)(?:, #(-?(?:0x)?[0-9a-f]+))?(?:, (r\d+)[^\]]*)?\]", text):
            base = {"fp": "R11", "sl": "R10", "ip": "R12", "lr": "LR"}.get(match.group(1), match.group(1).upper())
            disp = int(match.group(2), 0) if match.group(2) else 0
            if abs(disp) > 200:
                return None
            pins[base] = f"window+{248 - disp}"
            if match.group(3):
                pins[match.group(3).upper()] = 8
        if re.match(r"(ldm|stm|pop|push|vldm|vstm|fldm|fstm)", text) and not pins:
            found = re.match(r"\w+\s+(r\d+)", text)
            if found:
                pins[found.group(1).upper()] = "window+248"
        return pins


class Arm(Arm32):
    name = "arm"
    thumb = False
    cflags = ["--target=armv7a-linux-gnueabihf", "-marm", "-mfpu=neon-vfpv4"]
    lean = "arm"
    mc_triple = "armv7-linux-gnueabihf"
    corpus_name = "arm"
    nop = bytes.fromhex("00f020e3")
    mnemonics_of = staticmethod(arm_stems)

    def hand(self, assemble, layout):
        conds = ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le", ""]
        items = [(f"b{c} #56",) for c in conds] + [("bl #56",), ("bx r1", {"R1": "taken"}), ("blx r1", {"R1": "taken"}), ("bxj r1", {"R1": "taken"}), ("mov pc, r1", {"R1": "taken"}), ("bx lr", {"LR": "taken"}), ("pop {pc}", {}, {256: ("taken", 4)}), ("ldr pc, [r5, #8]", {"R5": "window+248"}, {256: ("taken", 4)})]
        for c in conds[:-1]:
            items += [(f"add{c} r1, r2, r3",), (f"mov{c}s r1, r2",), (f"ldr{c} r1, [r5, #8]", {"R5": "window+248"})]
        items += [("adr r1, #16",), ("add r1, pc, #16",), ("mov r1, pc",), ("ldr r1, [pc, #4]",), ("ldrb r1, [pc, #4]",), ("ldrh r1, [pc, #4]",), ("ldrsb r1, [pc, #4]",), ("ldrsh r1, [pc, #4]",), ("vldr d1, [pc, #4]",), ("vldr s1, [pc, #4]",), ("add r1, r2, pc",), ("add r1, pc, r2",), ("cmp r1, pc",), ("str pc, [r5, #8]", {"R5": "window+248"}), ("ldr r1, [pc, r2]", {"R2": 4}), ("adds r1, pc, r2",), ("sub r1, pc, #4",)]
        return self.text_cases(assemble, items)


class Thumb(Arm32):
    name = "thumb"
    thumb = True
    cflags = ["--target=armv7a-linux-gnueabihf", "-mthumb", "-mfpu=neon-vfpv4"]
    lean = "thumb"
    mc_triple = "thumbv7-linux-gnueabihf"
    corpus_name = "thumb"
    nop = bytes.fromhex("00bf")
    mnemonics_of = staticmethod(arm_stems)

    def hand(self, assemble, layout):
        conds = ["eq", "ne", "hs", "lo", "mi", "pl", "vs", "vc", "hi", "ls", "ge", "lt", "gt", "le"]
        items = [(f"b{c} #60",) for c in conds] + [(f"b{c}.w #60",) for c in conds]
        items += [("b #60",), ("b.w #60",), ("bl #60",), ("cbz r1, #60",), ("cbnz r1, #60",), ("bx r1", {"R1": "takenbit"}), ("blx r1", {"R1": "takenbit"}), ("bx lr", {"LR": "takenbit"}), ("bxj r1", {"R1": "takenbit"}), ("mov pc, r1", {"R1": "takenbit"}), ("pop {pc}", {}, {256: ("takenbit", 4)}), ("ldr.w pc, [r5, #8]", {"R5": "window+248"}, {256: ("takenbit", 4)}), ("adr r1, #16",), ("adr.w r1, #16",), ("mov r1, pc",), ("add r1, pc",), ("ldr r1, [pc, #4]",), ("ldr.w r1, [pc, #4]",), ("ldrb.w r1, [pc, #4]",), ("ldrh.w r1, [pc, #4]",), ("ldrsb.w r1, [pc, #4]",), ("ldrsh.w r1, [pc, #4]",), ("vldr d1, [pc, #4]",), ("vldr s1, [pc, #4]",), ("cmp r1, pc",), ("add r1, r1, pc",), ("add r8, pc",), ("mov r8, pc",), ("adr r1, #4",), ("add.w r1, pc, #4",)]
        return self.text_cases(assemble, items)


# RISC-V ------------------------------------------------------------------------------------------------------------------


def riscv_stems(name):
    base = name.rstrip("0123456789") if not name.startswith(("SH", "C_SH")) else name
    text = name.lower()
    text = text.replace("c_", "c.", 1) if text.startswith("c_") else text
    forms = {text.replace("_", "."), base.lower().replace("_", ".")}
    forms |= {f.replace(".inx", "").replace(".in32x", "") for f in forms}
    return sorted(forms)


class Riscv(Risc):
    nop = bytes.fromhex("13000000")
    extra_slots = 0
    base_pins = {"X15": "window+248", "X14": 8}
    semantics = ["riscv/riscv.lisp"]
    mnemonics_of = staticmethod(riscv_stems)
    excluded_prefix = ("ECALL", "EBREAK", "C_EBREAK", "WFI", "SRET", "MRET", "URET", "CSRR", "FENCE", "SFENCE", "HFENCE", "HLV", "HSV", "VSET", "CBO", "PREFETCH", "DRET")
    shape_list = ["", "a0, a1, a2", "a0, a1", "a0", "a0, a1, 5", "a0, a1, 3", "a0, a1, -1", "a0, a1, 1000", "a0, 5", "a0, -1", "a0, 1000", "a1, 8(a5)", "a1, -8(a5)", "a1, (a5)", "a1, 0(a5)", "a1, a2, (a5)", "a1, (a5)", "a1, a2, a3", "a1, a2, 3",
        "a0, a0", "a0, a0, a2", "a0, a0, 5", "a0, 8", "a0, 16", "a0, 4096", "sp, 16", "a0, sp, 16", "s0, s1", "s0, s0, 3", "s0, 5", "s0, s0", "a1, 8(a5)", "s0, 8(a5)", "s1, 8(a5)", "a1, 16(sp)", "sp, sp, 16", "a2, 8(a5)", "a1, 8(s1)", "s0, 8(s1)"]
    corpus_name = "riscv64"

    def pad_prefix(self, code):
        # a compressed instruction, so the no-ops after it are of whole words
        return bytes.fromhex("0100") if len(code) % 4 == 2 else b""

    def __init__(self, scratch):
        self.gpr_slots = [None] + [f"X{i}" for i in range(1, 32)]
        self.gprs = [(f"X{i}", self.word * 8) for i in range(1, 32)]
        self.vectors = [(f"F{i}", 64) for i in range(31)]
        super().__init__(scratch)

    def encode_extra(self, values, out):
        base = 32 * self.word
        for index in range(31):
            out[base + index * 8 : base + (index + 1) * 8] = values[f"F{index}"].to_bytes(8, "little")

    def decode_extra(self, data, result):
        base = 32 * self.word
        for index in range(31):
            result[f"F{index}"] = int.from_bytes(data[base + index * 8 : base + (index + 1) * 8], "little")

    def excluded(self, opcode, case):
        return super().excluded(opcode, case)

    def traps(self, opcode):
        return opcode in ("UNIMP", "C_UNIMP")

    def _pinned(self, text):
        pins = dict(self.base_pins)
        if "(s1)" in text:
            pins["X9"] = "window+248"
        return pins

    default_pins = {"X2": "window+256"}

    def aux_spec(self):
        return {"XZR": (0, self.word * 8), "EXCLUSIVE_MONITOR": (0, self.word * 8), "FCSR": (0, 32), "VXRM": (0, 32), "F31": (0, 64)}

    def hand(self, assemble, layout):
        items = [(f"{op} a0, a1, 64",) for op in ["beq", "bne", "blt", "bge", "bltu", "bgeu"]]
        items += [("jal ra, 64",), ("jal a0, 64",), ("jalr ra, a5, 0", {"X15": "taken"}), ("jalr a0, a5, 8", {"X15": "window+0"}), ("auipc a0, 5",), ("lui a0, 5",)]
        items += [("c.j 64",), ("c.beqz a0, 64",), ("c.bnez a0, 64",), ("c.jr a5", {"X15": "taken"}), ("c.jalr a5", {"X15": "taken"})]
        items += [("c.unimp",)] + ([("c.jal 64",)] if self.word == 4 else [])
        cases = self.text_cases(assemble, items)
        # the assembler compresses `unimp`
        cases.append(case_type()(code=(0xC0001073).to_bytes(4, "little"), text="unimp"))
        for case in cases:
            if case.text == "jalr a0, a5, 8":
                case.pins = {"X15": "taken-8"}
        return cases


class Riscv64(Riscv):
    name = "riscv64"
    word = 8
    runner = ["qemu-riscv64", "-cpu", "max"]
    cflags = ["--target=riscv64-linux-gnu", "-march=rv64gc", "-mabi=lp64d", "-mno-relax"]
    lean = "riscv64"
    mc_triple = "riscv64-linux-gnu"
    mc_args = ["--mattr=+a,+c,+d,+f,+m,+zba,+zbb,+zbs,+zbc,+zbkb,+zicond"]

    def corpus_memory(self, text):
        return riscv_corpus(text)


class Riscv32(Riscv):
    name = "riscv32"
    word = 4
    runner = ["qemu-riscv32", "-cpu", "max"]
    cflags = ["--target=riscv32-linux-gnu", "-march=rv32gc", "-mabi=ilp32d", "-mno-relax"]
    lean = "riscv32"
    mc_triple = "riscv32-linux-gnu"
    mc_args = ["--mattr=+a,+c,+d,+f,+m,+zba,+zbb,+zbs,+zbc,+zbkb,+zicond"]
    corpus_name = "none"


RISCV_REGS = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4, "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9, **{f"a{i}": 10 + i for i in range(8)}, **{f"s{i}": 16 + i for i in range(2, 12)},
    **{f"t{i}": 25 + i for i in range(3, 7)}}


def riscv_corpus(text):
    if "<" in text or re.match(r"(b|j|c\.j|c\.b|auipc)", text):
        return None
    pins = {}
    for match in re.finditer(r"(-?\d+)?\((\w+)\)", text):
        disp = int(match.group(1) or 0)
        reg = RISCV_REGS.get(match.group(2))
        if reg is None:
            return None
        if reg != 2:
            pins[f"X{reg}"] = f"window+{248 - disp}"
    return pins


# MIPS --------------------------------------------------------------------------------------------------------------------


def mips_stems(name):
    base = name.split("_")[0]
    forms = {name.lower(), base.lower(), base.rstrip("0123456789").lower()}
    # the floating point ones have the format after a dot: FADD_D32, C_EQ_S, CVT_D32_S, MOVN_I_S
    plain = re.sub(r"(D32|D64)", "D", name)
    plain = re.sub(r"^F(ADD|SUB|MUL|DIV|SQRT|ABS|NEG|MOV)", r"\1", plain)
    plain = plain.replace("_I64", "").replace("_I_", "_").replace("_I", "")
    forms.add(plain.lower().replace("_", "."))
    if plain.startswith("CMP_"):
        forms.add("cmp." + plain[4:].lower().replace("_", "."))
    forms.add(re.sub(r"_R6$", "", name).lower())
    return sorted(forms)


class Mips(Risc):
    nop = bytes(4)

    def policy_of(self, differ):
        # Legacy qemu is in default-NaN mode, and gives 0x7FBFFFFF for a quiet NaN that the manual has go through: see semantics/mips/mips.lisp.
        defaults = ("7fbfffff", "ffbfffff", "7ff7ffff", "fff7ffff")
        if not self.release6 and all(name.startswith("F") and (ours == "ffffffff" or any(d in ours for d in defaults)) for name, ours, _ in differ):
            return "qemu's default NaN"
        return None
    asm_prelude = ".set noreorder\n.set noat\n"
    semantics = ["mips/mips.lisp", "mips/mips-r6.lisp"]
    mnemonics_of = staticmethod(mips_stems)
    base_pins = {"R5": "window+248", "R6": 8}
    default_pins = {"R29": "window+256"}
    excluded_prefix = ("SYSCALL", "BREAK", "RDHWR", "SDBBP", "WAIT", "ERET", "DERET", "EI", "DI", "MFC0", "MTC0", "CACHE")
    shape_list = ["", "$2, $3, $4", "$2, $3, 5", "$2, $3, 200", "$2, $3, -1", "$2, $3", "$2", "$2, 5", "$2, 1000", "$2, 8($5)", "$2, -8($5)", "$2, ($5)", "$2, $3, 5, 6", "$2, $3, 3, 5", "$6($5)", "$2, $6($5)", "$f2, $f4", "$f2, $f4, $f6", "$f2, $f4, $f6, $f8", "$f2, $6($5)", "$f2, 8($5)", "$f2, $f4, $3", "$f2, $f4, $fcc1", "$2, $3, $fcc1", "$2, $f2", "$f2, $2", "$2, $3, $4, 2", "$2, $3, $4, 1", "$2, 8", "$f2, $f4, 1", "$f2, $f4, $f6", "$2, $3, 8", "$2, 8", "8", "$f2, 8", "$2, $3, $4, 1", "$2, $3, 8", "$2, $3, 3, 8"]
    corpus_name = ""

    def __init__(self, scratch):
        self.gpr_slots = [None] + [f"R{i}" for i in range(1, 32)]
        self.gprs = [(f"R{i}", self.word * 8) for i in range(1, 32)] + [("FCSR", self.word * 8)]
        if not self.release6:
            self.gprs = self.gprs + [("HI", self.word * 8), ("LO", self.word * 8)]
            self.flags = [(f"FCC{i}",) for i in range(8)]
        self.fpr_bytes = 8 if self.release6 else self.word
        self.vectors = [(f"F{i}", self.fpr_bytes * 8) for i in range(31)]
        super().__init__(scratch)

    def relevant(self, name):
        only_r6 = re.search(r"_R6|^(CMP_|SEL|MAX|MIN|CLASS|RINT|BC1EQZ|BC1NEZ|AUI|ALIGN|BITSWAP|ADDIUPC|ALUIPC|LWPC|LWUPC|LDPC|NAL|JIC|JIALC|BALC?$|B[A-Z]+C(64)?$|BOVC|BNVC|MUH|MULU|MOD|MADDF|MSUBF|DMUH|DMUL|DMOD|DALIGN|DBITSWAP|DAHI|DATI|DAUI|DLSA|LSA)|^(SDIV|UDIV|DSDIV|DUDIV|DIV|DIVU)$", name) is not None
        only_old = re.search(r"^(MADD|MSUB|MFHI|MFLO|MTHI|MTLO|MULT|MOVF|MOVT|MOVN|MOVZ|LWL|LWR|SWL|SWR|LDL|LDR|SDL|SDR|BC1F|BC1T|B[A-Z]+L$|BLTZAL|BGEZAL|C_|LWXC1|LDXC1|LUXC1|SWXC1|SDXC1|SUXC1|NMADD|NMSUB|CLO$|CLZ$|DCLO$|DCLZ$|SUB$|SUBi|ADDi$)", name) is not None
        only_64 = re.search(r"64|^D[A-Z]|^(LD|SD|LWu|LLD|SCD|LDL|LDR|SDL|SDR)$", name) is not None
        if self.release6 and only_old:
            return False
        if not self.release6 and only_r6:
            return False
        return self.word == 8 or not only_64

    def aux_spec(self):
        spec = {"XZR": (0, self.word * 8), "EXCLUSIVE_MONITOR": (0, self.word * 8), "USERLOCAL": (0, self.word * 8), "F31": (0, 64 if self.release6 else self.word * 8)}
        if self.release6:
            spec["HI"], spec["LO"] = (0, self.word * 8), (0, self.word * 8)
            for i in range(8):
                spec[f"FCC{i}"] = (0, 1)
        return spec

    release6 = False

    def traps(self, opcode):
        return MIPS_TRAPS.match(opcode) is not None

    def shape(self, case, values, index, rng):
        if self.word == 8 and MIPS_WORD_OPERATIONS.match(case.opcode):
            for name in ("R2", "R3", "R4", "HI", "LO"):
                if name in values:
                    values[name] = word_value(values[name])
        # what the stub can start with: no Cause nor Enables, as those would fault in the stub
        values["FCSR"] &= 0x0100007F
        # to nearest, and subnormals kept: the semantics say that they don't look at FCSR.RM and FS
        if case.opcode not in ("CTC1", "CFC1"):
            values["FCSR"] &= 0x0000007C
        # the comparisons of the traps, on the edge of being true, in R2 and in the immediate or R3
        if self.traps(case.opcode) and case.opcode != "CTC1":
            mask = (1 << (self.word * 8)) - 1
            step = [0, 1, -1, 0][index % 4]
            immediate = last_immediate(case.text) if case.opcode.endswith(("I", "IU")) else None
            if immediate is not None:
                values["R2"] = (immediate + step) & mask
            else:
                values["R3"] = (values["R2"] + step) & mask

    def encode_extra(self, values, out):
        self.set_extra_word(out, 0, values.get("HI", 0))
        self.set_extra_word(out, 1, values.get("LO", 0))
        fcc = 0 if self.release6 else values["FCC0"] << 23 | sum(values[f"FCC{i}"] << (24 + i) for i in range(1, 8))
        self.set_extra_word(out, 2, values["FCSR"] | fcc)
        base = 35 * self.word
        for index in range(31):
            out[base + index * self.fpr_bytes : base + (index + 1) * self.fpr_bytes] = values[f"F{index}"].to_bytes(self.fpr_bytes, "big" if self.endian == ">" else "little")

    def decode_extra(self, data, result):
        if not self.release6:
            result["HI"] = self.extra_word(data, 0)
        if not self.release6:
            result["LO"] = self.extra_word(data, 1)
        fcsr = self.extra_word(data, 2)
        # NAN2008 and ABS2008 are of the release and can't be written, see the semantics
        result["FCSR"] = fcsr & 0x0103FFFF
        if not self.release6:
            result["FCC0"] = fcsr >> 23 & 1
            for i in range(1, 8):
                result[f"FCC{i}"] = fcsr >> (24 + i) & 1
        base = 35 * self.word
        for index in range(31):
            result[f"F{index}"] = int.from_bytes(data[base + index * self.fpr_bytes : base + (index + 1) * self.fpr_bytes], "big" if self.endian == ">" else "little")

    def hand(self, assemble, layout):
        Case = case_type()
        word = lambda value: value.to_bytes(4, "big" if self.endian == ">" else "little")
        result = []
        for op, name in [(4, "beq"), (5, "bne"), (20, "beql"), (21, "bnel")]:
            result.append(Case(code=word((op << 26) | (2 << 21) | (3 << 16) | 15), text=f"{name} $2, $3, .+64"))
        for op, name in [(6, "blez"), (7, "bgtz"), (22, "blezl"), (23, "bgtzl")]:
            result.append(Case(code=word((op << 26) | (2 << 21) | 15), text=f"{name} $2, .+64"))
        for rt, name in [(0, "bltz"), (1, "bgez"), (2, "bltzl"), (3, "bgezl"), (16, "bltzal"), (17, "bgezal"), (18, "bltzall"), (19, "bgezall")]:
            result.append(Case(code=word((1 << 26) | (2 << 21) | (rt << 16) | 15), text=f"{name} $2, .+64"))
        target = (layout["taken"] >> 2) & 0x3FFFFFF
        result.append(Case(code=word((2 << 26) | target), text="j taken"))
        result.append(Case(code=word((3 << 26) | target), text="jal taken"))
        items = [("jr $2", {"R2": "taken"}), ("jalr $2", {"R2": "taken"}), ("jalr $4, $2", {"R2": "taken"})]
        items += [("seb $2, $3",), ("seh $2, $3",), ("wsbh $2, $3",), ("clz $2, $3",), ("clo $2, $3",), ("mfhi $2",), ("mflo $2",), ("mthi $2",), ("mtlo $2",), ("movz $2, $3, $4",), ("movn $2, $3, $4",)]
        # the instructions without an effect, and the conditional moves, also to the zero register
        memory = {"R5": "window+248"}
        items += [("pause",), ("ssnop",), ("sync 0",), ("synci 8($5)", memory), ("pref 1, 8($5)", memory), ("pref 30, 8($5)", memory)]
        items += [("movn $0, $3, $4",), ("movz $0, $3, $4",)]
        for op in ("movt", "movf"):
            items += [(f"{op} $2, $3, $fcc0",), (f"{op} $2, $3, $fcc5",), (f"{op} $0, $3, $fcc1",)]
        # the traps
        for op in ("teq", "tne", "tge", "tgeu", "tlt", "tltu"):
            items += [(f"{op} $2, $3, 7",), (f"{op} $2, $3",), (f"{op} $0, $0",)]
        for op in ("teqi", "tnei", "tgei", "tgeiu", "tlti", "tltiu"):
            items += [(f"{op} $2, {immediate}",) for immediate in (5, -1, 1000)]
        # the control registers, written with what the manual allows of each, half of the time without an exception
        no_cause = lambda mask: (lambda index, rng: rng.getrandbits(32) & mask & (0xFFFC0FFF if index % 2 == 0 else 0xFFFFFFFF))
        items += [(f"cfc1 $2, ${number}",) for number in (25, 26, 28, 31)]
        items += [("ctc1 $2, $25", {"R2": no_cause(0xFF)}), ("ctc1 $2, $26", {"R2": no_cause(0x3F07C)}), ("ctc1 $2, $28", {"R2": no_cause(0xF87)}), ("ctc1 $2, $31", {"R2": no_cause(0xFFFFFFFF)})]
        items += [("mthc1 $2, $f4",), ("mfhc1 $2, $f4",), ("mthc1 $0, $f4",)]
        if self.word == 8 and not self.release6:
            # paired singles, also with a destination that is an operand
            for op in ("pll.ps", "plu.ps", "pul.ps", "puu.ps", "cvt.ps.s"):
                items += [(f"{op} $f2, $f4, $f6",), (f"{op} $f2, $f2, $f6",), (f"{op} $f2, $f4, $f2",), (f"{op} $f2, $f2, $f2",)]
            for op in ("cvt.s.pl", "cvt.s.pu"):
                items += [(f"{op} $f2, $f4",), (f"{op} $f2, $f2",)]
        return result + self.text_cases(assemble, items)

    def corpus_memory(self, text):
        # a base register of a run isn't where the form addressed: those are of `hand` and the shapes
        return None if "(" in text else {}

    def cases(self, opcodes, assemble, layout):
        # only `hand` has the numbers of the control registers that exist: the manual leaves the others unpredictable
        return [case for case in super().cases(opcodes, assemble, layout) if case.always or not case.text.startswith(("cfc1", "ctc1"))]


def mips_undefined(self, case, values, final):
    # the Flags and the Cause of FCSR, that the operations set and the semantics don't model
    return set() if case.opcode in ("CTC1", "CFC1") else {"FCSR"}


Mips.undefined = mips_undefined


class MipsBe(Mips):
    name = "mips"
    corpus_name = "mips"
    word = 4
    endian = ">"
    runner = ["qemu-mips", "-cpu", "24Kf"]
    cflags = ["--target=mips-linux-gnu", "-mno-abicalls", "-mno-gpopt", "-march=mips32r2", "-modd-spreg", "-mfp32"]
    lean = "mips"
    mc_triple = "mips-linux-gnu"
    mc_args = ["--mattr=+mips32r2"]


class MipsLe(Mips):
    name = "mipsel"
    word = 4
    endian = "<"
    runner = ["qemu-mipsel", "-cpu", "24Kf"]
    cflags = ["--target=mipsel-linux-gnu", "-mno-abicalls", "-mno-gpopt", "-march=mips32r2", "-modd-spreg", "-mfp32"]
    lean = "mipsel"
    mc_triple = "mipsel-linux-gnu"
    mc_args = ["--mattr=+mips32r2"]


MIPS_TRAPS = re.compile(r"(TEQ|TNE|TGE|TGEU|TLT|TLTU|TEQI|TNEI|TGEI|TGEIU|TLTI|TTLTIU|CTC1)$")
# of the 64-bit machine, these are of the word that is sign-extended, and UNPREDICTABLE of any other value
MIPS_WORD_OPERATIONS = re.compile(r"(ADD|ADDi|ADDu|ADDiu|SUB|SUBu|SLL|SLLV|SRL|SRLV|SRA|SRAV|ROTR|ROTRV|MUL|MULT|MULTu|DIV|DIVU|SDIV|UDIV|MADD|MADDu|MSUB|MSUBu|CLZ|CLO|SEB|SEH|WSBH|MUH|MUHU|MULU|MOD|MODU|EXT|INS)(_MM|_R6|64)?$")


def word_value(value):
    low = value & 0xFFFFFFFF
    return low | (0xFFFFFFFF00000000 if low >> 31 else 0)


class Mips64(Mips):
    name = "mips64"
    corpus_name = "mips64"
    word = 8
    endian = ">"
    runner = ["qemu-mips64", "-cpu", "MIPS64R2-generic"]
    cflags = ["--target=mips64-linux-gnuabi64", "-mno-abicalls", "-mno-gpopt", "-march=mips64r2"]
    lean = "mips64"
    mc_triple = "mips64-linux-gnuabi64"
    mc_args = ["--mattr=+mips64r2"]


# PowerPC -----------------------------------------------------------------------------------------------------------------


def powerpc_stems(name):
    record = name.endswith("_rec")
    stem = name[:-4] if record else name
    stem = re.sub(r"(8|4|_32|_64|_NOP|_nop)+$", "", stem)
    forms = {stem.lower(), stem.rstrip("0123456789").lower()}
    if stem.endswith(("O", "o")):
        forms.add(stem.lower())
    return sorted(f + "." if record else f for f in forms)


class Ppc(Risc):

    def policy_of(self, differ):
        # qemu has 1/±0 as ±0.5 in fre and fres, and infinity for what is nearly zero, and the manual has it as infinity.
        half, infinity = ("3fe0000000000000", "bfe0000000000000"), ("7ff0000000000000", "fff0000000000000")
        if all(name.startswith("F") and ours in half and theirs in infinity for name, ours, theirs in differ):
            return "qemu's reciprocal of zero"
        return None
    base_pins = {"R5": "window+248", "R6": 8}
    default_pins = {"R1": "window+256"}
    semantics = ["powerpc/powerpc.lisp", "powerpc/powerpc-vector.lisp", "powerpc/powerpc-vsx.lisp", "powerpc/powerpc-decimal.lisp"]
    mnemonics_of = staticmethod(powerpc_stems)
    excluded_prefix = ("SC", "TW", "TD", "TRAP", "ATTN", "MFMSR", "MTMSR", "MFSPR", "MTSPR", "MFTB", "SYNC", "ISYNC", "EIEIO", "DCB", "ICB", "MFVSCR", "MTVSCR", "MFFS", "MTFS", "MCRFS", "RFI", "TLB", "HRFID", "NAP", "MFOCRF", "MTOCRF", "DSS", "MSG", "WAIT", "DARN", "HASH", "CP_", "TBEGIN", "TEND", "TABORT", "TCHECK", "TSR", "RFEBB", "CLRBHRB", "MFBHRBE", "MFUDSCR", "MTUDSCR")
    shape_list = ["", "3, 4, 7", "3, 4", "3", "3, 4, 100", "3, 4, -1", "3, 4, 1000", "3, 100", "3, -1", "3, 8(5)", "3, -8(5)", "3, 0(5)", "3, 5, 6", "3, 4, 7, 8", "3, 4, 7, 8, 9", "3, 4, 5, 6, 7", "3, 4, 3, 5, 7", "3, 4, 3, 5", "3, 4, 3", "3, 4, 7, 5", "0, 3, 4", "3, 3, 4", "0, 0, 3, 4", "0, 1, 3, 4", "0, 1, 3, 100", "0, 3, 100", "0, 3", "2, 3, 4", "1, 3, 4", "1, 3", "3, 0", "3, 1", "7, 1, 2, 3", "1, 2, 3"]
    corpus_name = "powerpc"

    def _pinned(self, _text):
        return dict(self.base_pins)

    def corpus_code(self, code):
        """The corpus has the words in the big-endian order."""
        if self.endian == ">":
            return code
        return b"".join(code[index : index + 4][::-1] for index in range(0, len(code), 4))

    def corpus_memory(self, text):
        return dict(self.base_pins)

    def __init__(self, scratch):
        self.gpr_slots = [f"R{i}" for i in range(32)]
        self.gprs = [(f"R{i}", self.word * 8) for i in range(32)]
        self.flags = [(f"CR{field}{bit}", 31 - (4 * field + index)) for field in range(8) for index, bit in enumerate(["LT", "GT", "EQ", "UN"])]
        self.xer = [("SO", 31), ("OV", 30), ("CA", 29)]
        self.flags = self.flags + self.xer + self.xer32()
        self.gprs = self.gprs + [("LR", self.word * 8), ("CTR", self.word * 8)]
        self.vectors = [(f"F{i}", 64) for i in range(32)] + [(f"V{i}", 128) for i in range(32)] + self.vsx_low()
        super().__init__(scratch)

    def xer32(self):
        return []

    def vsx_low(self):
        """The second doublewords of the VSX registers 0 to 31, of the machines that have VSX."""
        return [(f"F{i}L", 64) for i in range(32)] if self.word == 8 else []

    # what writes a scalar in F0 to F31 and whose second doubleword the ISA leaves undefined: qemu clears it for the first
    # group and keeps it for the second, and the lifter keeps it in the first and clears it in the second, as ISA 3.0 does
    undefined_second = re.compile(r"F(ABS|NABS|NEG|MR|CTI|CFID|ADD|SUB|MUL|DIV|SQRT|MADD|MSUB|NMADD|NMSUB|RE|RSQRTE|RSP|SEL|RI|CPSGN)|LF[SDI]|PLF[SD]|MFFS|LXS(DX|SPX|IBZX|IHZX|IWAX|IWZX)$|MTVSR(D|WA|WZ)$")

    def undefined(self, case, values, final):
        """The extended division whose quotient doesn't fit has an undefined result, and the ISA says OV is set, which
        qemu-user doesn't, on a positive quotient of the upper half of the 64 bits, so qemu is no evidence here."""
        numbers = re.findall(r"\d+", case.asm)
        masked = set()
        if self.undefined_second.match(case.opcode) and numbers:
            masked.add(f"F{numbers[0]}L")
        # CR1 of the record forms has the exception bits of FPSCR, that the arithmetic doesn't model
        if case.opcode.endswith("_rec") and case.opcode.startswith(("F", "D", "MTFS", "MFFS")) and not case.opcode.startswith("DIV"):
            masked |= {"CR1LT", "CR1GT", "CR1EQ", "CR1UN"}
        # the offsets of the element out of the register are undefined, and qemu wraps them around
        size = {"VEXTUH": 2, "VEXTUW": 4}.get(case.opcode[:6])
        if size and values[f"R{numbers[1]}"] & 15 > 16 - size:
            masked.add(f"R{numbers[0]}")
        size = {"VINSH": 2, "VINSW": 4, "VINSD": 8}.get(case.opcode[:5])
        if size and case.opcode[5:] in ("LX", "RX", "VLX", "VRX") and values[f"R{numbers[1]}"] & 15 > 16 - size:
            masked.add(f"V{numbers[0]}")
        # qemu takes a small number, that would be a denormal single, as of any class that DCMX has, not only of the two
        if case.opcode == "XSTSTDCSP" and 0 < (values[f"F{numbers[1]}"] >> 52) & 0x7FF < 0x381:
            masked.add(f"CR{numbers[0]}EQ")
        # the quotient of an extended division that doesn't fit is undefined
        if re.match(r"VDIVE[SU][DQ]$", case.opcode):
            masked.add(f"V{numbers[0]}")
        if not case.opcode.startswith("DIVDE") or case.opcode.startswith("DIVDEU"):
            return masked
        signed = lambda value: value - (1 << 64) if value >> 63 else value
        rt, ra, rb = re.findall(r"\d+", case.asm)[:3]
        rt, ra, rb = f"R{rt}", signed(values[f"R{ra}"]), signed(values[f"R{rb}"])
        if rb == 0:
            return masked
        magnitude = (abs(ra) << 64) // abs(rb)
        quotient = -magnitude if (ra < 0) != (rb < 0) else magnitude
        if -(1 << 63) <= quotient < (1 << 63):
            return masked
        return masked | {rt, "OV", "SO", "OV32", "CR0LT", "CR0GT", "CR0EQ", "CR0UN"}

    def aux_spec(self):
        spec = {"XZR": (0, self.word * 8), "EXCLUSIVE_MONITOR": (0, self.word * 8), "TAR": (0, self.word * 8), "FL": (0, 1), "FG": (0, 1), "FE": (0, 1), "FU": (0, 1), "OV32": (0, 1), "CA32": (0, 1), "FPSCR": (0, 64), "VSCR": (0, 32)}
        return {k: v for k, v in spec.items() if k not in dict(self.xer32())}

    def encode_extra(self, values, out):
        cr = 0
        for name, bit in self.flags:
            if name.startswith("CR"):
                cr |= values[name] << bit
        xer = 0
        for name, bit in self.xer + self.xer32():
            xer |= values[name] << bit
        self.set_extra_word(out, 0, cr)
        self.set_extra_word(out, 1, xer)
        self.set_extra_word(out, 2, values["LR"])
        self.set_extra_word(out, 3, values["CTR"])
        base = 36 * self.word
        for index in range(32):
            out[base + index * 8 : base + (index + 1) * 8] = values[f"F{index}"].to_bytes(8, "big" if self.endian == ">" else "little")
        base += 256
        for index in range(32):
            out[base + index * 16 : base + (index + 1) * 16] = values[f"V{index}"].to_bytes(16, "big" if self.endian == ">" else "little")
        base += 512
        for index in range(32 if self.vsx_low() else 0):
            out[base + index * 8 : base + (index + 1) * 8] = values[f"F{index}L"].to_bytes(8, "big" if self.endian == ">" else "little")

    def decode_extra(self, data, result):
        cr = self.extra_word(data, 0)
        xer = self.extra_word(data, 1)
        for name, bit in self.flags:
            if name.startswith("CR"):
                result[name] = (cr >> bit) & 1
        for name, bit in self.xer + self.xer32():
            result[name] = (xer >> bit) & 1
        result["LR"] = self.extra_word(data, 2)
        result["CTR"] = self.extra_word(data, 3)
        base = 36 * self.word
        for index in range(32):
            result[f"F{index}"] = int.from_bytes(data[base + index * 8 : base + (index + 1) * 8], "big" if self.endian == ">" else "little")
        base += 256
        for index in range(32):
            result[f"V{index}"] = int.from_bytes(data[base + index * 16 : base + (index + 1) * 16], "big" if self.endian == ">" else "little")
        base += 512
        for index in range(32 if self.vsx_low() else 0):
            result[f"F{index}L"] = int.from_bytes(data[base + index * 8 : base + (index + 1) * 8], "big" if self.endian == ">" else "little")

    def hand(self, assemble, layout):
        Case = case_type()
        result = []
        endian = "big" if self.endian == ">" else "little"
        word = lambda value: value.to_bytes(4, endian)
        result.append(Case(code=word(0x48000000 | 64), text="b .+64"))
        result.append(Case(code=word(0x48000001 | 64), text="bl .+64"))
        ctr = lambda i, r: r.choice([0, 1, 2, 5])
        for bo, bi in [(12, 2), (4, 2), (12, 0), (4, 0), (12, 1), (4, 1), (12, 3), (12, 30), (4, 30), (16, 0), (18, 0), (8, 0), (0, 0), (10, 0), (2, 0), (24, 0), (25, 0), (26, 0), (27, 0), (14, 2), (15, 2), (6, 2), (7, 2)]:
            result.append(Case(code=word(0x40000000 | (bo << 21) | (bi << 16) | 64), text=f"bc {bo},{bi},.+64", pins={"CTR": ctr}))
            result.append(Case(code=word(0x40000001 | (bo << 21) | (bi << 16) | 64), text=f"bcl {bo},{bi},.+64", pins={"CTR": ctr}))
            result.append(Case(code=word(0x4C000020 | (bo << 21) | (bi << 16)), text=f"bclr {bo},{bi}", pins={"CTR": ctr, "LR": "taken"}))
            result.append(Case(code=word(0x4C000021 | (bo << 21) | (bi << 16)), text=f"bclrl {bo},{bi}", pins={"CTR": ctr, "LR": "taken"}))
            if bo & 4:
                result.append(Case(code=word(0x4C000420 | (bo << 21) | (bi << 16)), text=f"bcctr {bo},{bi}", pins={"CTR": "taken"}))
                result.append(Case(code=word(0x4C000421 | (bo << 21) | (bi << 16)), text=f"bcctrl {bo},{bi}", pins={"CTR": "taken"}))
        result.append(Case(code=word(0x4E800020), text="blr", pins={"LR": "taken"}))
        result.append(Case(code=word(0x4E800021), text="blrl", pins={"LR": "taken"}))
        result.append(Case(code=word(0x4E800420), text="bctr", pins={"CTR": "taken"}))
        result.append(Case(code=word(0x4E800421), text="bctrl", pins={"CTR": "taken"}))
        result.append(Case(code=word(0x4C820020), text="bnelr", pins={"LR": "taken"}))
        result.append(Case(code=word(0x4D820020), text="beqlr", pins={"LR": "taken"}))
        result.append(Case(code=word(0x4C820420), text="bnectr", pins={"CTR": "taken"}))
        return result + self.text_cases(assemble, [("mflr 3",), ("mtlr 3",), ("mfctr 3",), ("mtctr 3",), ("mfcr 3",), ("mtcrf 255, 3",), ("mtcrf 128, 3",), ("mtcrf 1, 3",), ("crand 2, 3, 4",), ("cror 2, 3, 4",), ("crxor 2, 3, 4",), ("crnor 2, 3, 4",), ("creqv 2, 3, 4",), ("crnand 2, 3, 4",), ("crandc 2, 3, 4",), ("crorc 2, 3, 4",), ("mcrf 2, 3",), ("mfxer 3",), ("mtxer 3",),
            ("lmw 28, 8(5)", {"R5": "window+248"}), ("stmw 28, 8(5)", {"R5": "window+248"}), ("nop",)])


class Ppc32(Ppc):
    name = "ppc"
    word = 4
    endian = ">"
    runner = ["qemu-ppc", "-cpu", "7457"]
    cflags = ["--target=powerpc-linux-gnu"]
    lean = "ppc"
    mc_triple = "powerpc-linux-gnu"
    nop = bytes.fromhex("60000000")

    def excluded(self, opcode, case):
        # of the later ISAs, which this CPU doesn't have: qemu runs other instructions of its own on their encodings
        if opcode in ("VCMPEQUD", "VCMPEQUD_rec", "VCMPGTSD", "VCMPGTSD_rec", "VCMPGTUD", "VCMPGTUD_rec", "VCNTMBB", "VCNTMBD", "VCNTMBH", "VCNTMBW", "VDIVESW", "VDIVUQ",
                      "VINSBRX", "VINSBVLX", "VINSBVRX", "VINSD", "VINSERTB", "VINSERTH", "VINSERTW", "VINSHVLX", "VINSHVRX", "VINSW", "VINSWVLX", "VINSWVRX", "VRLDNM",
                      "VSTRIBL", "VSTRIBL_rec", "VSTRIBR", "VSTRIBR_rec", "VSTRIHL", "VSTRIHL_rec", "VSTRIHR", "VSTRIHR_rec"):
            return "of a later ISA than the CPU of qemu-ppc"
        return super().excluded(opcode, case)


class Ppc64(Ppc):
    name = "ppc64"
    word = 8
    endian = ">"
    runner = ["qemu-ppc64", "-cpu", "power10"]
    cflags = ["--target=powerpc64-linux-gnu", "-mabi=elfv2"]
    lean = "ppc64"
    mc_triple = "powerpc64-linux-gnu"
    nop = bytes.fromhex("60000000")

    def xer32(self):
        return [("OV32", 19), ("CA32", 18)]


class Ppc64Le(Ppc):
    name = "ppc64le"
    word = 8
    endian = "<"
    runner = ["qemu-ppc64le", "-cpu", "power10"]
    cflags = ["--target=powerpc64le-linux-gnu"]
    lean = "ppc64le"
    mc_triple = "powerpc64le-linux-gnu"
    nop = bytes.fromhex("00000060")

    def xer32(self):
        return [("OV32", 19), ("CA32", 18)]


class MipsR6(Mips):
    name = "mipsr6"
    word = 4
    endian = ">"
    release6 = True
    runner = ["qemu-mips", "-cpu", "mips32r6-generic"]
    cflags = ["--target=mips-linux-gnu", "-mno-abicalls", "-mno-gpopt", "-march=mips32r6", "-mfp64"]
    lean = "mipsr6"
    mc_triple = "mipsisa32r6-linux-gnu"
    mc_args = []


class Mips64R6(Mips):
    name = "mips64r6"
    word = 8
    endian = ">"
    release6 = True
    runner = ["qemu-mips64", "-cpu", "I6400"]
    cflags = ["--target=mips64-linux-gnuabi64", "-mno-abicalls", "-mno-gpopt", "-march=mips64r6"]
    lean = "mips64r6"
    mc_triple = "mipsisa64r6-linux-gnuabi64"
    mc_args = []


TARGETS.update({"mipsr6": MipsR6, "mips64r6": Mips64R6, "aarch64": AArch64, "arm": Arm, "thumb": Thumb, "riscv64": Riscv64, "riscv32": Riscv32, "mips": MipsBe, "mipsel": MipsLe, "mips64": Mips64,
    "ppc": Ppc32, "ppc64": Ppc64, "ppc64le": Ppc64Le})
