#!/usr/bin/env python3
"""The smoke test of what the lifters cover: `tools/smoke.py TARGET... [--work DIR]`, from lean/.

It makes encodings of a target from what LLVM has: the records of its instructions (for x86, each record is encoded from its
fields, and a wider search is made for the records nothing reached) and the encodings in LLVM's own MC tests (every target),
and random words for the targets of fixed sizes. `bap-smoke` decodes and lifts them. The report has, for each target, how many
opcodes can be disassembled at all, how many were reached, how many lift, what doesn't lift by family, and what wasn't reached.

Everything is a function of the arguments and the seed. `lake build bap-smoke` first.
"""
import argparse, collections, json, os, random, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LLVM = os.path.join(ROOT, "_deps/src/llvm-project-llvmorg-23.1.4/llvm")
BUILD = os.path.join(ROOT, "_deps/llvm-23.1.4-pic-build")

# target of the harness: the backend, its top level TableGen file, directories of tests
TARGETS = {
    "x86_64": ("X86", "X86.td", ["X86"]),
    "i386": ("X86", "X86.td", ["X86"]),
    "aarch64": ("AArch64", "AArch64.td", ["AArch64"]),
    "riscv64": ("RISCV", "RISCV.td", ["RISCV"]),
    "riscv32": ("RISCV", "RISCV.td", ["RISCV"]),
    "powerpc64le": ("PowerPC", "PPC.td", ["PowerPC"]),
    "powerpc": ("PowerPC", "PPC.td", ["PowerPC"]),
    "mips64": ("Mips", "Mips.td", ["Mips"]),
    "mips": ("Mips", "Mips.td", ["Mips"]),
    "armv7": ("ARM", "ARM.td", ["ARM"]),
    "thumbv7": ("ARM", "ARM.td", ["ARM"]),
}
FIXED_WORD = {"aarch64": 4, "powerpc64le": 4, "powerpc": 4, "mips64": 4, "mips": 4, "armv7": 4, "riscv64": 4, "riscv32": 4, "thumbv7": 4}
BIG_ENDIAN = {"powerpc", "mips64", "mips"}


def records(backend, top, work):
    """The instructions of a backend from TableGen: a name to its fields, without those too large to keep."""
    compact = os.path.join(work, backend + ".records.json")
    if os.path.exists(compact):
        return json.load(open(compact))
    dump = os.path.join(work, backend + ".json")
    target = os.path.join(LLVM, "lib/Target", backend)
    subprocess.check_call([os.path.join(BUILD, "bin/llvm-tblgen"), "-I", os.path.join(LLVM, "include"), "-I", os.path.join(BUILD, "include"),
                           "-I", target, os.path.join(target, top), "--dump-json", "-o", dump])
    data = json.load(open(dump))
    fields = ["Opcode", "OpMap", "OpPrefix", "OpEnc", "OpSize", "AdSize", "Form", "ImmT", "hasEVEX_B", "hasEVEX_K", "hasEVEX_L2", "hasEVEX_NF",
              "hasEVEX_RC", "hasEVEX_U", "hasEVEX_Z", "hasREX_W", "hasVEX_4V", "hasVEX_L", "hasLockPrefix", "hasREPPrefix", "isCodeGenOnly",
              "ForceDisassemble", "isAsmParserOnly", "isPseudo", "Predicates", "AsmString", "DecoderNamespace", "mayLoad", "mayStore", "hasSideEffects"]
    out = {}
    for name in data["!instanceof"]["Instruction"]:
        record, entry = data[name], {}
        for field in fields:
            value = record.get(field)
            if isinstance(value, dict):
                value = value.get("def")
            if field == "Opcode" and isinstance(value, list):
                value = sum((bit or 0) << index for index, bit in enumerate(value))
            if field == "Predicates" and value is not None:
                value = [p["def"] for p in value]
            entry[field] = value
        out[name] = entry
    json.dump(out, open(compact, "w"))
    os.remove(dump)
    return out


def decodable(record):
    """Whether a disassembler can have the opcode, as `X86RecognizableInstr` and the emitters of the others say."""
    if record.get("isPseudo") or record.get("Form") == "Pseudo":
        return False
    if record.get("isCodeGenOnly") and not record.get("ForceDisassemble"):
        return False
    return not record.get("isAsmParserOnly")


# LLVM's tests, of any target

ENCODING = re.compile(r"encoding:\s*\[([^\]]*)\]")
HEXLINE = re.compile(r"^\s*((?:0x[0-9a-fA-F]{1,2}[\s,]+)*0x[0-9a-fA-F]{1,2})\s*(?:[#;/].*)?$")


def hex_byte(token):
    """A byte of an encoding: what isn't all known is a fixup, of which the bits that are known are enough."""
    match = re.match(r"0x[0-9a-fA-F]+", token)
    return int(match.group(0), 16) if match else 0


def harvest(directories, word):
    """The encodings of the MC tests of the directories; the order of the bytes of a word may be either."""
    found = set()
    for directory in directories:
        for kind in ("test/MC", "test/MC/Disassembler"):
            base = os.path.join(LLVM, kind, directory)
            for path, _, files in os.walk(base):
                for file in files:
                    if not file.endswith((".s", ".txt", ".S", ".mc")):
                        continue
                    for line in open(os.path.join(path, file), errors="replace"):
                        bytes_ = []
                        match = ENCODING.search(line)
                        if match:
                            bytes_ = [token.strip() for token in match.group(1).split(",")]
                            # what a fixup fills in is a letter
                            bytes_ = [hex_byte(token) for token in bytes_ if token]
                            if any(value > 255 for value in bytes_):
                                bytes_ = []
                        else:
                            match = HEXLINE.match(line)
                            if match:
                                bytes_ = [int(token, 16) for token in re.split(r"[\s,]+", match.group(1)) if token]
                        if bytes_:
                            found.add(bytes(bytes_))
                            if word and len(bytes_) in (2, 4):
                                found.add(bytes(reversed(bytes_)))
    return found


# x86: an encoding from the fields of a record

MAPS = {"TB": 1, "T8": 2, "TA": 3, "T_MAP4": 4, "T_MAP5": 5, "T_MAP6": 6, "T_MAP7": 7, "XOP8": 8, "XOP9": 9, "XOPA": 10}
PP = {"PD": 1, "XS": 2, "XD": 3}
ESCAPE = {"TB": [0x0f], "T8": [0x0f, 0x38], "TA": [0x0f, 0x3a], "T_MAP4": [], "OB": [], "ThreeDNow": [0x0f, 0x0f]}


def modrms(form, wide):
    """The bytes after the opcode, as lists from the first: what the form says, with memory operands of each kind."""
    memory = [[0x00 | 1 << 3], [0x04 | 1 << 3, 0x24], [0x04 | 1 << 3, 0x48], [0x44 | 1 << 3, 0x24, 0x10], [0x84 | 1 << 3, 0x88, 0, 1, 0, 0]]
    register = [[0xc0 | 1 << 3 | 2], [0xc0 | 3 << 3 | 4]]
    if wide:
        register = [[0xc0 | v] for v in range(64)]
        memory = [[m << 6 | v, s, 0, 0, 0, 0] for m in range(3) for v in range(64) for s in (0x24, 0x48)]
    match = re.fullmatch(r"MRM([0-7])([mrX])", form)
    if match:
        digit, kind = int(match.group(1)), match.group(2)
        if kind == "m":
            return [[(b[0] & 0xc7) | digit << 3] + b[1:] for b in memory]
        if kind == "r":
            return [[(b[0] & 0xc7) | digit << 3] + b[1:] for b in register]
        return [[(b[0] & 0xc7) | digit << 3] + b[1:] for b in register + memory]
    match = re.fullmatch(r"MRM_([0-9A-F]{2})", form)
    if match:
        return [[int(match.group(1), 16)]]
    if form in ("RawFrm", "AddRegFrm", "AddCCFrm", "RawFrmMemOffs", "RawFrmSrc", "RawFrmDst", "RawFrmDstSrc", "RawFrmImm8", "RawFrmImm16", "PrefixByte"):
        return [[]]
    if "Mem" in form or form in ("MRMXm", "MRMXmCC"):
        return memory
    if "Reg" in form or form in ("MRMXr", "MRMXrCC", "MRMr0"):
        return register
    return register + memory


def x86_prefixes(record, bits):
    out = []
    if record["OpPrefix"] == "PD" or (record["OpSize"] == "OpSize16" and bits == 64) or (record["OpSize"] == "OpSize32" and bits == 16):
        out.append(0x66)
    if record["AdSize"] == "AdSize32" and bits == 64 or record["AdSize"] == "AdSize16" and bits == 32:
        out.append(0x67)
    if record["OpPrefix"] == "XS":
        out.append(0xf3)
    if record["OpPrefix"] == "XD":
        out.append(0xf2)
    return out


def x86_encodings(record, wide, bits):
    """The encodings of a record, which the decoder will have the last word on."""
    tail = [0x11] * 12
    opcode = record["Opcode"]
    enc = record["OpEnc"]
    if record["Form"] == "AddCCFrm":
        pass
    for rest in modrms(record["Form"], wide):
        if enc == "EncEVEX":
            mapping = MAPS.get(record["OpMap"], 1)
            pp = PP.get(record["OpPrefix"], 0)
            ws = [record["hasREX_W"] or 0] if not wide else [0, 1]
            lls = [(record["hasEVEX_L2"] or 0) * 2 + (record["hasVEX_L"] or 0)]
            if wide or record["hasEVEX_RC"]:
                lls = [0, 1, 2, 3]
            bs = [record["hasEVEX_B"] or 0] if not wide else [0, 1]
            ks = [1 if record["hasEVEX_K"] else 0] if not wide else [0, 1, 4]
            zs = [record["hasEVEX_Z"] or 0] if not wide else [0, 1]
            us = [1] if not (wide or record["hasEVEX_U"]) else [0, 1]
            for w in ws:
                for ll in lls:
                    for b in bs:
                        for k in ks:
                            for z in zs:
                                for u in us:
                                    vvvv = 0xd if record["hasVEX_4V"] else 0xf
                                    if bits == 32:
                                        vvvv |= 8
                                    p0 = 0xf0 | mapping
                                    p1 = w << 7 | vvvv << 3 | u << 2 | pp
                                    p2 = z << 7 | ll << 5 | b << 4 | 8 | k
                                    yield bytes([0x62, p0, p1, p2, opcode] + rest + tail)
        elif enc in ("EncVEX", "EncXOP"):
            mapping = MAPS.get(record["OpMap"], 1)
            pp = PP.get(record["OpPrefix"], 0)
            first = 0xc4 if enc == "EncVEX" else 0x8f
            for w in ([record["hasREX_W"] or 0] if not wide else [0, 1]):
                for l in ([record["hasVEX_L"] or 0] if not wide else [0, 1]):
                    vvvv = 0xd if record["hasVEX_4V"] else 0xf
                    yield bytes([first, 0xe0 | mapping, w << 7 | vvvv << 3 | l << 2 | pp, opcode] + rest + tail)
        else:
            prefixes = x86_prefixes(record, bits)
            escape = ESCAPE.get(record["OpMap"], [])
            rex = [0x48] if record["hasREX_W"] else []
            variants = [prefixes + rex + escape + [opcode] + rest + tail]
            if record["OpMap"] == "ThreeDNow":
                # the opcode is the last byte, after the operands
                variants = [prefixes + [0x0f, 0x0f] + rest + [opcode] + tail]
            if record["hasLockPrefix"]:
                variants.append([0xf0] + variants[0])
            if record["hasREPPrefix"]:
                variants.append([0xf3] + variants[0])
            if record["Form"] == "PrefixByte":
                variants = [[opcode] + [0x90] * 12]
            for v in variants:
                yield bytes(v)
            if wide:
                for p in ([], [0x66], [0xf2], [0xf3], [0x67], [0x48], [0x66, 0x48], [0xf3, 0x48], [0xf2, 0x48], [0x40]):
                    yield bytes(p + escape + [opcode] + rest + tail)


def evex_fuzz(rng, count, bits):
    """Random EVEX encodings, for what isn't reached otherwise."""
    for _ in range(count):
        p0 = rng.randrange(256)
        if bits == 32:
            p0 |= 0xc0
        p1 = rng.randrange(256)
        p2 = rng.randrange(256)
        yield bytes([0x62, p0, p1, p2] + [rng.randrange(256) for _ in range(12)])


def write_corpus(path, encodings):
    with open(path, "w") as out:
        for encoding in encodings:
            out.write(encoding.hex() + "\n")


BATCH_LINES = 4000
BATCH_SECONDS = 10


def smoke_batch(limit, target, path, samples):
    """One batch: it takes seconds, so a timeout is something stuck, which is reported and not run again."""
    command = limit + ["timeout", str(BATCH_SECONDS), os.path.join(ROOT, ".lake/build/bin/bap-smoke"), target, path, str(samples)]
    output = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if output.returncode == 124:
        raise SystemExit(f"bap-smoke {target} {path} took over {BATCH_SECONDS} s: rerun it under gdb, it is stuck")
    if output.returncode != 0:
        sys.stderr.write(output.stderr[-2000:])
        raise SystemExit(f"bap-smoke {target} {path} exited {output.returncode}")
    tallies, totals = {}, (0, 0)
    for line in output.stdout.splitlines():
        if line.startswith("#"):
            fields = line.split()
            totals = (int(fields[2]), int(fields[4]))
            continue
        name, lifted, failed, encoding, error = line.split("\t", 4)
        tallies[name] = (int(lifted), int(failed), encoding, error)
    return tallies, totals


def smoke(target, path, samples, work):
    """Runs the harness on batches of the corpus under the limits of the machine. An opcode to (lifted, failed, encoding, error)."""
    limit = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
    try:
        subprocess.check_call(limit + ["true"], stderr=subprocess.DEVNULL)
    except (OSError, subprocess.CalledProcessError):
        limit = []
    with open(path) as corpus:
        lines = corpus.readlines()
    tallies, total, undecoded = {}, 0, 0
    part = path + ".batch"
    for first in range(0, len(lines), BATCH_LINES):
        with open(part, "w") as out:
            out.writelines(lines[first:first + BATCH_LINES])
        batch, (count, failures) = smoke_batch(limit, target, part, samples)
        merge(tallies, batch)
        total += count
        undecoded += failures
    print(f"  {target}: # lines {total} undecoded {undecoded} opcodes {len(tallies)}", flush=True)
    return tallies


def merge(into, more):
    for name, value in more.items():
        old = into.get(name)
        if old is None:
            into[name] = value
        else:
            first = old if old[1] else value
            into[name] = (old[0] + value[0], old[1] + value[1], first[2], first[3])


def family(name):
    """The family of an opcode: its name without what says its form or size."""
    name = re.sub(r"(Z128|Z256|Z)(?=[a-z_]|$)", "", name)
    name = re.sub(r"_(EVEX|ND|NF|NF_ND|REV|Int|alt|REX|PREFIX|ID)\b", "", name)
    name = re.sub(r"(rr|rm|mr|ri|mi|rrr|rrm|rmr|mrr|rri|rmi|mri|r|m|i)?(b|k|z|bk|bkz|kz|)?(i8|i|r|m|\d+)?$", "", name) or name
    return name


def x86_class(record):
    """What kind of an x86 instruction a record is."""
    if record["OpEnc"] == "EncEVEX":
        return "APX" if record["OpMap"] in ("T_MAP4",) else "EVEX"
    if record["OpEnc"] == "EncVEX":
        return "VEX"
    if record["OpEnc"] == "EncXOP":
        return "XOP"
    if record["OpMap"] == "ThreeDNow":
        return "3DNow"
    if record["OpMap"] == "OB" and 0xd8 <= record["Opcode"] <= 0xdf:
        return "x87"
    return "legacy"


# what stays an error on x86 on purpose, by what it is

PRIVILEGED = re.compile(r"^(VM[A-Z0-9]|INV|LGDT|LIDT|SGDT|SIDT|LLDT|LTR|LMSW|LKGS|MOV(32|64)(cr|dr|rc|rd)|RDMSR|WRMSR|RDPMC|WBINVD|WBNOINVD|IN[0-9SB]|OUT|IRET|ERET"
                        r"|SWAPGS|SYSRET|SYSEXIT|CLTS|STAC|CLAC|HRESET|PCONFIG|RSM|SEAM|ENCL|GETSEC|RMP|PSMASH|PVALIDATE|TDCALL|TLBSYNC|SKINIT|STGI|CLGI|MONITOR|MWAIT|XSETBV|LOADIWKEY|PBNDKB)")
OBSOLETE = re.compile(r"^(PAVGUSB|PF[0-9A-Z]|PI2F|PMULHRW|PSWAPD|VF[N]?M[A-Z]+[PS][SD]4|VFM[A-Z]+[PS][SD]4|VPERMIL2|BEXTRI|BLC|BLS(FILL|IC)|T1MSKC|TZMSK|L?LWP|SLWP|VFRCZ|VPCMOV|VPCOM|VPHADD|VPHSUB|VPMAC|VPMADC"
                      r"|VPPERM|VPROT|VPSHA|VPSHL|EXTRQ|INSERTQ|XCRYPT|XSHA|XSTORE|MONTMUL|BOUND|ARPL|INTO|AAA|AAD|AAM|AAS|DAA|DAS|SALC|BSWAP16r_BAD)")
SYSTEM = re.compile(r"^(LAR|LSL|VERR|VERW|SLDT|SMSW|STR|FAR(CALL|JMP)|LRET|AES(DEC|ENC)(WIDE)?(128|256)KL|ENCODEKEY|CLUI|STUI|TESTUI|UIRET|SENDUIPI)")


def why(name):
    return "privileged" if PRIVILEGED.match(name) else "obsolete" if OBSOLETE.match(name) else "system" if SYSTEM.match(name) else "OTHER"


def report(target, recs, tallies, out, klass=None):
    names = {name for name, record in recs.items() if decodable(record)}
    reached = set(tallies)
    lifted = {name for name, tally in tallies.items() if tally[1] == 0}
    failed = reached - lifted
    unreached = names - reached
    with open(os.path.join(out, target + ".failed.tsv"), "w") as file:
        for name in sorted(failed):
            tally = tallies[name]
            file.write(f"{name}\t{klass(recs[name]) if klass and name in recs else ''}\t{tally[2]}\t{tally[3]}\n")
    with open(os.path.join(out, target + ".unreached.txt"), "w") as file:
        for name in sorted(unreached):
            file.write(name + "\n")
    print(f"{target}: decodable {len(names)} reached {len(reached & names)} (+{len(reached - names)} others) "
          f"lift {len(lifted)} fail {len(failed)} unreached {len(unreached)}")
    if klass:
        for kind in sorted({klass(recs[name]) for name in names}):
            of = {name for name in names if klass(recs[name]) == kind}
            print(f"  {kind:8} decodable {len(of):6} reached {len(of & reached):6} lift {len(of & lifted):6} fail {len(of & failed):5} unreached {len(of - reached):5}")
        reasons = collections.Counter(why(name) for name in failed)
        print("  failing by reason: " + " ".join(f"{name}:{count}" for name, count in reasons.most_common()))
        others = sorted(name for name in failed if why(name) == "OTHER")
        if others:
            print("  failing and not expected: " + " ".join(others[:200]))
    families = collections.Counter(family(name) for name in failed)
    print("  failing families: " + " ".join(f"{name}:{count}" for name, count in families.most_common(80)))


def in_mode(record, bits):
    """Whether the predicates of a record allow a mode: the decoder has other tables for the others."""
    predicates = record.get("Predicates") or []
    if "In64BitMode" in predicates and bits != 64:
        return False
    if "Not64BitMode" in predicates and bits == 64:
        return False
    if "In16BitMode" in predicates:
        return False
    # there is no REX in the 32-bit mode, whose bytes are INC and DEC
    if record.get("hasREX_W") and bits != 64 and record.get("OpEnc") == "EncNormal":
        return False
    return True


def run_x86(target, recs, work, out, samples, seed):
    bits = 64 if target == "x86_64" else 32
    names = [name for name, record in recs.items() if decodable(record) and in_mode(record, bits)]
    corpus = os.path.join(work, target + ".corpus")
    harvested = harvest(TARGETS[target][2], False)
    encodings = set()
    for encoding in harvested:
        encodings.add(encoding + bytes(16 - min(len(encoding), 16)))
    for name in names:
        encodings.update(x86_encodings(recs[name], False, bits))
    write_corpus(corpus, sorted(encodings))
    tallies = smoke(target, corpus, samples, work)
    missing = [name for name in names if name not in tallies]
    print(f"  {target}: not reached after records and tests: {len(missing)}", flush=True)
    if missing:
        encodings = set()
        for name in missing:
            encodings.update(x86_encodings(recs[name], True, bits))
        write_corpus(corpus, sorted(encodings))
        merge(tallies, smoke(target, corpus, samples, work))
    missing = [name for name in names if name not in tallies]
    print(f"  {target}: not reached after the wider search: {len(missing)}", flush=True)
    if any(recs[name]["OpEnc"] == "EncEVEX" for name in missing):
        write_corpus(corpus, evex_fuzz(random.Random(seed), 2000000, bits))
        merge(tallies, smoke(target, corpus, samples, work))
    # the forms that the decoder only takes with one of several legacy prefixes, or none
    missing = [name for name in names if name not in tallies]
    if missing:
        print(f"  {target}: not reached: " + " ".join(sorted(missing)[:400]), flush=True)
    report(target, {name: recs[name] for name in set(names) | set(tallies) if name in recs}, tallies, out, x86_class)
    return tallies


def run_fixed(target, recs, work, out, samples, seed, count):
    word = FIXED_WORD.get(target, 0)
    corpus = os.path.join(work, target + ".corpus")
    encodings = {encoding + bytes(max(0, 8 - len(encoding))) for encoding in harvest(TARGETS[target][2], word != 0)}
    rng = random.Random(seed)
    for _ in range(count):
        encodings.add(rng.randbytes(word) + bytes(4))
    write_corpus(corpus, sorted(encodings))
    tallies = smoke(target, corpus, samples, work)
    report(target, recs, tallies, out)
    return tallies


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", default=["x86_64", "i386"])
    parser.add_argument("--work", default=os.path.join(ROOT, ".lake/smoke"))
    parser.add_argument("--samples", type=int, default=4, help="how many encodings of an opcode to lift")
    parser.add_argument("--random", type=int, default=1000000, help="random words of a target of fixed sizes")
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    os.makedirs(args.work, exist_ok=True)
    for target in args.targets:
        backend, top, _ = TARGETS[target]
        recs = records(backend, top, args.work)
        if backend == "X86":
            run_x86(target, recs, args.work, args.work, args.samples, args.seed)
        else:
            run_fixed(target, recs, args.work, args.work, args.samples, args.seed, args.random)


if __name__ == "__main__":
    main()
