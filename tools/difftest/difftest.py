#!/usr/bin/env python3
"""Runs instructions on real execution and through the lifter and `Bil.run`, from the same state, and compares what they end with.

    lake build bap-difftest
    python3 tools/difftest/difftest.py [--out DIR] [--scratch DIR] [--inputs N] [--per-opcode K] [--seed S] [--only REGEX] TARGET...

TARGET is x86_64, i686 (native on an x86-64 host with AVX2), aarch64, arm, thumb, riscv64, riscv32, mips, mipsel, mips64, mipsr6,
mips64r6, ppc, ppc64, ppc64le (under qemu-user, a second implementation, not silicon), or `all`. It takes a minute or so a target:
a batch of 1000 runs on the machine has 5 seconds and a session of the lifter 30, and it stops on the first that doesn't finish. Writes DIR/TARGET.json, with the disagreements and
what wasn't tested and why, and prints the table.

Each instruction goes through tools/difftest/stub.c, compiled for the target by clang, which loads the registers, the flags and
a window of memory, runs it and dumps them, and tools/difftest/DiffTest.lean, which does the same on the lifted program. What the
architecture leaves undefined is masked, see `undefined_x86`, and counted, so it can't hide anything else.
"""
import argparse
import concurrent.futures
import io
import json
import os
import random
import re
import resource
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field

import targets

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LEAN = os.path.join(ROOT, ".lake", "build", "bin", "bap-difftest")
SLOT = 32
WINDOW = 512


@dataclass
class Case:
    """An instruction under test: its bytes and how to choose its inputs."""

    code: bytes
    text: str
    pins: dict = field(default_factory=dict)  # register -> value, or "window+N", "taken"
    pinmem: dict = field(default_factory=dict)  # offset in the window -> (value, bytes)
    opcode: str = ""
    size: int = 0
    intrinsic: bool = False
    asm: str = ""
    control: bool = False
    always: bool = False  # run it however many of its opcode there are: it is of a condition, or of an implicit operand


def resolve(value, layout):
    if isinstance(value, str):
        if value == "taken":
            return layout["taken"]
        if value == "takenbit":
            return layout["taken"] | 1
        if value.startswith("taken-"):
            return layout["taken"] - int(value[6:])
        if value.startswith("window"):
            return layout["window"] + int(value[6:] or "0")
        raise ValueError(value)
    return value


def run_stub(cfg, stub, records, record_in, record_out, labels, timeout=5):
    """The outcomes of the records; a hung run loses its record and goes on from the next."""
    outputs = []
    start = 0
    header = None
    with tempfile.NamedTemporaryFile(dir=cfg.scratch, delete=False) as handle:
        path = handle.name
        handle.write(b"".join(records))
    batch = 1000
    try:
        while start < len(records):
            with open(path, "rb") as stdin:
                stdin.seek(start * record_in)
                stdin = io.BytesIO(stdin.read(batch * record_in))
                try:
                    out = subprocess.run(cfg.runner + [stub], input=stdin.getvalue(), capture_output=True, timeout=timeout)
                    data, code = out.stdout, out.returncode
                except subprocess.TimeoutExpired as expired:
                    data, code = expired.stdout or b"", -1
            header = data[:64]
            body = data[64:]
            count = len(body) // record_out
            for index in range(count):
                outputs.append(body[index * record_out : (index + 1) * record_out])
            start += count
            if start < len(records) and (code != 0 or count == 0):
                if code == 0:
                    raise RuntimeError(f"stub made no progress on {cfg.name}")
                # a stuck run is a bug of the harness, to diagnose and not to wait through again
                if code == -1:
                    raise RuntimeError(f"{cfg.name}: hung on {labels[start]}")
                print(f"{cfg.name}: exit {code} on {labels[start]}", flush=True)
                outputs.append(None)
                start += 1
    finally:
        os.unlink(path)
    return outputs


def layout_of(cfg, stub):
    out = subprocess.run(cfg.runner + [stub], input=b"", capture_output=True, timeout=30)
    fmt = cfg.endian + "8Q"
    magic, slot, taken, window, size, state, word, _ = struct.unpack(fmt, out.stdout[:64])
    assert magic == 0xD1FF7E57, f"bad header {out.stdout[:64].hex()}"
    assert size == WINDOW and word == cfg.word
    return {"slot": slot, "taken": taken, "window": window, "state": state}


def build_stub(cfg):
    path = os.path.join(cfg.scratch, f"stub-{cfg.name}")
    source = os.path.join(HERE, "stub.c")
    if os.path.exists(path) and os.path.getmtime(path) > os.path.getmtime(source):
        return path
    command = ["clang"] + cfg.cflags + ["-O1", "-fno-builtin", "-ffreestanding", "-fno-stack-protector", "-fno-pic", "-static",
        "-nostdlib", "-fuse-ld=lld", "-fomit-frame-pointer",
        "-Wl,-N,-T," + os.path.join(HERE, "link.ld") + ",-e,_start,--no-dynamic-linker,-z,noexecstack",
        "-o", path, source]
    subprocess.run(command, check=True, capture_output=True)
    return path


def lean_prefix():
    """What a session of the lifter runs under: a scope of 12 GiB, if there is a manager of the user's to make one, and a timeout."""
    scope = ["systemd-run", "--user", "--scope", "--quiet", "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0"]
    if shutil.which("systemd-run") and subprocess.run(scope + ["true"], capture_output=True).returncode == 0:
        return scope + ["timeout", "30"]
    # without a scope, a session is of a whole batch, which takes minutes, and only one that hangs is cut off
    return ["timeout", "1800"]


def lean_session(requests, scratch):
    """Runs the requests through the Lean side and gives its lines; in a file, not a pipe, as they are many."""
    with tempfile.NamedTemporaryFile("w", dir=scratch, delete=False) as handle:
        handle.write("\n".join(requests) + "\n")
        path = handle.name
    try:
        with open(path) as stdin:
            out = subprocess.run(lean_prefix() + [LEAN], stdin=stdin, capture_output=True, cwd=ROOT)
        if out.returncode != 0:
            raise RuntimeError(f"bap-difftest: {out.returncode} {out.stderr[-2000:].decode(errors='replace')}")
        return out.stdout.decode(errors="replace").splitlines()
    finally:
        os.unlink(path)


def lean_batches(requests, header, scratch, size=20000):
    """The answers to requests after a `header` of them, in sessions short enough to fail fast. They are cut before a `C`.
    A session that dies is split, down to the instruction it dies on, whose answers say so: the Lean side can panic."""
    head = requests[:header]
    answers = []

    def run(body):
        try:
            answers.extend(lean_session(head + body, scratch))
            return
        except RuntimeError as error:
            cuts = [index for index, line in enumerate(body) if line.startswith("C")]
            if len(cuts) > 1:
                middle = cuts[len(cuts) // 2]
                run(body[:middle])
                run(body[middle:])
                return
            message = str(error).replace("\n", " ")[:200]
            if " 124 " in message:
                raise
            print(f"lifter died on {body[0]}: {message}", flush=True)
            words = body[0].split(" ")
            if len(body) == 1:
                answers.append(f"E {words[1]} died: {message}")
            else:
                answers.append(f"D {words[1]} died 00 0")
                answers.extend(f"X {line.split(' ')[1]} died: {message}" for line in body[1:])

    start = header
    while start < len(requests):
        end = min(start + size, len(requests))
        while end < len(requests) and not requests[end].startswith("C"):
            end += 1
        run(requests[start:end])
        start = end
    return answers


def assemble(cfg, lines):
    """The encodings of the lines of assembly that the assembler takes, as `(line, bytes)`; a line that makes more than one
    instruction, or that needs a fixup, is not one. llvm-mc crashes on some lines, which are searched for and left out."""
    results = {}
    many = set()
    environment = dict(os.environ, LLVM_DISABLE_SYMBOLIZATION="1", LLVM_DISABLE_CRASH_REPORT="1")

    def no_core():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def run(low, high):
        if low >= high:
            return
        source = []
        for index in range(low, high):
            source.append(f".long {index + 1}")
            source.append(lines[index])
        source = cfg.asm_prelude + "\n".join(source) + "\n"
        out = subprocess.run(["llvm-mc", "--show-encoding", f"--triple={cfg.mc_triple}"] + cfg.mc_args, input=source.encode(),
            capture_output=True, env=environment, preexec_fn=no_core, timeout=15)
        if out.returncode < 0:
            if high - low > 1:
                middle = (low + high) // 2
                run(low, middle)
                run(middle, high)
            return
        current = None
        for line in out.stdout.decode(errors="replace").splitlines():
            marker = re.match(r"\s*\.(?:long|word|4byte|int)\s+(\d+)", line)
            if marker:
                current = int(marker.group(1)) - 1
                continue
            encoded = re.search(r"encoding: \[([^\]]*)\]", line)
            if encoded and current is not None:
                if "A" in encoded.group(1):
                    many.add(current)
                    continue
                if current in results:
                    many.add(current)
                atoms = [a for a in encoded.group(1).split(",") if a]
                results[current] = bytes(int(a, 16) for a in atoms)

    with concurrent.futures.ThreadPoolExecutor(max_workers=12) as pool:
        list(pool.map(lambda start: run(start, min(start + 2000, len(lines))), range(0, len(lines), 2000)))
    return [(index, code) for index, code in results.items() if index not in many]


def pad(cfg, code):
    assert len(code) <= SLOT, code.hex()
    code = code + cfg.pad_prefix(code)
    extra = SLOT - len(code)
    nop = cfg.nop
    return code + (nop * SLOT)[:extra]


EDGES = [0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF, 0x10000, 0x7FFFFFFF,
    0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFE,
    0xFFFFFFFFFFFFFF80, 0xFFFFFFFFFFFF8000, 0xFFFFFFFF80000000]


def pick(rng, width, others):
    roll = rng.random()
    if roll < 0.45:
        value = rng.choice(EDGES)
    elif roll < 0.6 and others:
        value = rng.choice(others)
    elif roll < 0.8:
        value = rng.getrandbits(rng.choice([8, 16, 32, 64]))
    else:
        value = rng.getrandbits(64)
    return value & ((1 << width) - 1)


def vector(rng, bits, others):
    """A vector whose lanes of one width are of the edges, or equal to those of another vector."""
    if others and rng.random() < 0.25:
        return rng.choice(others)
    lane = rng.choice([8, 16, 32, 64])
    edges = {8: [0, 1, 0x7F, 0x80, 0xFF], 16: [0, 1, 0x7F, 0x80, 0xFF, 0x7FFF, 0x8000, 0xFFFF],
        32: [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x7FFF, 0x8000, 0xFFFF],
        64: [0, 1, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFF, 0x80000000]}[lane]
    value = 0
    for index in range(bits // lane):
        chunk = rng.choice(edges) if rng.random() < 0.5 else rng.getrandbits(lane)
        value |= chunk << (index * lane)
    return value


def make_inputs(cfg, case, layout, rng, count):
    """The states of a case. The first few have the flags both ways on their own, whatever else is random."""
    states = []
    for index in range(count):
        values = {}
        taken = []
        for name, width in cfg.gprs:
            value = pick(rng, width, taken)
            values[name] = value
            taken.append(value)
        for name, *_ in cfg.flags:
            values[name] = rng.getrandbits(1) if index >= 4 else (index >> (hash_flag(name) % 2)) & 1
        vectors = []
        for name, bits in cfg.vectors:
            value = vector(rng, bits, vectors) & ((1 << bits) - 1)
            values[name] = value
            vectors.append(value)
        memory = bytearray()
        for _ in range(WINDOW // 8):
            memory += struct.pack("<Q", pick(rng, 64, taken))
        cfg.shape(case, values, index, rng)
        for name, value in {**cfg.default_pins, **case.pins}.items():
            if callable(value):
                value = value(index, rng)
            values[name] = resolve(value, layout)
        for offset, (value, size) in case.pinmem.items():
            value = value(index, rng) if callable(value) else resolve(value, layout)
            memory[offset : offset + size] = value.to_bytes(size, "big" if cfg.endian == ">" else "little")
        states.append((values, bytes(memory)))
    return states


def hash_flag(name):
    return sum(map(ord, name))


def hexvalue(value, width):
    return f"{value:0{(width + 3) // 4}x}"


def compare_case(cfg, case, layout, states, hw, lean, stats, report):
    """Compares what a case ended with on both sides."""
    known = report["disagreements"].setdefault(case.opcode, [])
    for index, (values, memory) in enumerate(states):
        outcome = hw[index]
        stats["inputs"] += 1
        if outcome is None:
            stats["hung"] += 1
            continue
        marker = int.from_bytes(outcome[:8], "big" if cfg.endian == ">" else "little")
        if marker & 0xFF == 2 and marker >> 8 < 64:
            stats["faulted"] += 1
            stats[f"signal{marker >> 8}"] += 1
            # a trap is what the instruction does: the lifter has to take it too, and on the runs that fall through not to
            if cfg.traps(case.opcode):
                words = lean[index].split(" ")
                if words[0] == "O" and words[2] == "s":
                    stats["agreements"] += 1
                else:
                    stats["disagreements"] += 1
                    if len(known) < 3:
                        known.append({"text": case.text, "bytes": case.code.hex(), "asm": case.asm, "kind": "trap", "signal": marker >> 8, "lifter": " ".join(words[:3]),
                            "inputs": {name: hexvalue(value, dict(cfg.all_widths)[name]) for name, value in values.items()}})
            continue
        if marker > 1:
            # what the instruction did to the state of the stub itself, e.g., a store through a wild register
            stats["corrupted"] += 1
            report.setdefault("corrupted", {})[case.opcode] = case.text
            continue
        line = lean[index]
        words = line.split(" ")
        if words[0] == "X":
            stats["lifter errors"] += 1
            if len(known) < 3:
                known.append({"text": case.text, "bytes": case.code.hex(), "asm": case.asm, "error": " ".join(words[2:]), "kind": "lifter error"})
            continue
        final = cfg.decode(outcome[8:8 + layout["state"]])
        memory_hw = outcome[8 + layout["state"] :]
        effect, shown, memory_lean = words[2], words[3:-1], words[-1]
        lean_values = dict(zip(cfg.lean_order, shown))
        masked = cfg.undefined(case, values, final) if cfg.undefined else set()
        differ = []
        expected_flow = 1 if marker == 1 else 0
        taken_lean = 0
        if effect.startswith("j"):
            target = int(effect[1:], 16)
            if target & ~cfg.pc_mask == layout["taken"]:
                taken_lean = 1
            elif layout["slot"] <= target < layout["slot"] + SLOT:
                # a branch into the no-ops of the slot, which falls through on the machine: only the hand-written cases aim
                taken_lean = 0
            else:
                taken_lean = 2
        elif effect != "n":
            stats["special effects"] += 1
            if not cfg.traps(case.opcode):
                continue
        if effect[0] in "sc" and cfg.traps(case.opcode):
            differ.append(("control", "fell through", effect))
        elif taken_lean != expected_flow:
            differ.append(("control", f"{expected_flow} (1 is taken)", f"{effect}"))
        for name, width in cfg.compared:
            theirs = lean_values.get(name, "?")
            ours = final[name]
            if theirs == "?":
                value = None
            else:
                value = int(theirs, 16)
                value &= (1 << width) - 1
            if value != ours:
                if name in masked:
                    stats["undefined, differ"] += 1
                    report["undefined_diffs"][case.opcode + " " + name] += 1
                else:
                    differ.append((name, hexvalue(ours, width), theirs if value is None else hexvalue(value, width)))
            elif name in masked:
                stats["undefined, same"] += 1
        if memory_lean != memory_hw.hex() and "memory" in masked:
            stats["undefined, differ"] += 1
        elif memory_lean != memory_hw.hex():
            differ.append(("memory", memory_hw.hex(), memory_lean))
        if differ and cfg.policy_of(differ):
            stats[cfg.policy_of(differ)] += 1
            stats["agreements"] += 1
        elif differ:
            stats["disagreements"] += 1
            if len(known) < 3:
                known.append({"text": case.text, "bytes": case.code.hex(), "asm": case.asm, "kind": "value",
                    "inputs": {name: hexvalue(value, dict(cfg.all_widths)[name]) for name, value in values.items()
                               if name in dict(cfg.all_widths)},
                    "window": memory.hex(), "diff": [list(d) for d in shorten(differ, memory)]})
        else:
            stats["agreements"] += 1


def shorten(differ, before):
    result = []
    for name, hw, lean in differ:
        if name == "memory" and len(hw) == len(lean):
            parts = []
            for offset in range(0, len(hw), 2):
                if hw[offset : offset + 2] != lean[offset : offset + 2]:
                    parts.append(f"+{offset // 2}:{before[offset // 2]:02x}->hw {hw[offset : offset + 2]} lean {lean[offset : offset + 2]}")
            result.append((name, "; ".join(parts[:16]), ""))
        else:
            result.append((name, hw, lean))
    return result


def lisp_opcodes(cfg):
    names = {}
    for path in cfg.semantics:
        with open(os.path.join(ROOT, "semantics", path)) as handle:
            for line in handle:
                found = re.match(r"\(defun ([A-Z][A-Za-z0-9_.$-]*)\s", line)
                if found:
                    names[found.group(1)] = path
    return names


def drive(name, options):
    cfg = targets.config(name, options.scratch)
    start = time.time()
    stub = build_stub(cfg)
    layout = layout_of(cfg, stub)
    cfg.layout = layout
    print(f"{name}: slot {layout['slot']:#x} window {layout['window']:#x}", flush=True)
    opcodes = lisp_opcodes(cfg)
    # the instructions: all the shapes that assemble, the hand-written ones, the corpus of upstream
    candidates = cfg.cases(opcodes, assemble, layout)
    print(f"{name}: {len(candidates)} candidates", flush=True)
    seen = {}
    for case in candidates:
        seen.setdefault(case.code, case)
    candidates = list(seen.values())
    window_spec = f"W {layout['window']:x} {WINDOW:x} {cfg.word * 8:x}"
    specs = " ".join(f"{name_}:{width:x}" for name_, width in cfg.lean_vars)
    requests = [f"T {cfg.lean}", f"V {specs}", window_spec]
    for index, case in enumerate(candidates):
        requests.append(f"C {index} {layout['slot']:x} {pad(cfg, case.code).hex()}")
    lines = lean_batches(requests, 3, cfg.scratch)
    by_opcode = defaultdict(list)
    decode_errors = Counter()
    decode_failed = {}
    untargeted = set()
    for line in lines:
        words = line.split(" ", 6)
        if words[0] == "D":
            case = candidates[int(words[1])]
            case.opcode, case.size, case.intrinsic = words[2], int(words[3], 16), words[4] == "1"
            case.control = words[5] == "1"
            case.asm = words[6] if len(words) > 6 else ""
            # only the hand-written control flow is aimed at an exit of the stub: an operand form of the assembler can
            # branch to itself, or anywhere
            if case.always or not case.control:
                by_opcode[case.opcode].append(case)
            else:
                untargeted.add(case.opcode)
        elif words[0] == "E":
            case = candidates[int(words[1])]
            decode_failed[case.code] = line
            decode_errors[" ".join(words[2:])[:60]] += 1
    only = re.compile(options.only) if options.only else None
    report = {"target": name, "disagreements": {}, "undefined_diffs": Counter(), "excluded": {}, "fp": [], "no_hw": {}}
    stats = Counter()
    rng = random.Random(options.seed)
    plan = []
    survey = []
    for opcode, cases in sorted(by_opcode.items()):
        if only and not only.search(opcode):
            continue
        reason = cfg.excluded(opcode, cases[0])
        if reason:
            report["excluded"][opcode] = reason
            continue
        if any(case.intrinsic for case in cases) and not cfg.traps(opcode):
            report["fp"].append(opcode)
            continue
        survey.append((opcode, [case for case in cases if case.always] + [case for case in cases if not case.always][:24]))
    # the forms that run: an operand form that the assembler takes can be of an address that doesn't, e.g., an absolute one
    records = []
    for _, cases in survey:
        for case in cases:
            for values, memory in make_inputs(cfg, case, layout, rng, 2):
                records.append(pad(cfg, case.code) + cfg.encode(values, layout["state"]) + memory)
    labels = [f"{case.opcode} {case.text}" for _, cases in survey for case in cases for _ in range(2)]
    outcomes = run_stub(cfg, stub, records, SLOT + layout["state"] + WINDOW, 8 + layout["state"] + WINDOW, labels)
    position = 0
    for opcode, cases in survey:
        good = []
        for case in cases:
            results = outcomes[position : position + 2]
            position += 2
            if any(r is not None and (int.from_bytes(r[:8], "big" if cfg.endian == ">" else "little") & 0xFF) != 2 for r in results):
                good.append(case)
        pool = good or cases
        plan.extend([case for case in pool if case.always] + [case for case in pool if not case.always][: options.per_opcode])
    print(f"{name}: {len(by_opcode)} opcodes decoded, {len(plan)} cases to run", flush=True)
    # run on the machine
    records = []
    all_states = []
    state_size = layout["state"]
    for case in plan:
        states = make_inputs(cfg, case, layout, rng, options.inputs)
        all_states.append(states)
        code = pad(cfg, case.code)
        for values, memory in states:
            records.append(code + cfg.encode(values, state_size) + memory)
    record_in = SLOT + state_size + WINDOW
    record_out = 8 + state_size + WINDOW
    labels = [f"{case.opcode} {case.text}" for case in plan for _ in range(options.inputs)]
    outcomes = run_stub(cfg, stub, records, record_in, record_out, labels)
    print(f"{name}: ran on the machine, {time.time() - start:.0f}s", flush=True)
    # run in the lifter
    requests = [f"T {cfg.lean}", f"V {specs}", window_spec]
    for case, states in zip(plan, all_states):
        requests.append(f"C 0 {layout['slot']:x} {pad(cfg, case.code).hex()}")
        for index, (values, memory) in enumerate(states):
            shown = " ".join(hexvalue(values[name_], width) if name_ in values else hexvalue(cfg.aux.get(name_, 0), width)
                for name_, width in cfg.lean_vars)
            requests.append(f"R {index} {memory.hex()} {shown}")
    lines = lean_batches(requests, 3, cfg.scratch)
    print(f"{name}: ran through the lifter, {time.time() - start:.0f}s", flush=True)
    cursor = 0
    position = 0
    opcode_results = defaultdict(Counter)
    for case, states in zip(plan, all_states):
        head = lines[cursor]
        cursor += 1
        answers = lines[cursor : cursor + len(states)]
        cursor += len(states)
        hw = outcomes[position : position + len(states)]
        position += len(states)
        local = Counter()
        compare_case(cfg, case, layout, states, hw, answers, local, report)
        stats.update(local)
        opcode_results[case.opcode].update(local)
    tested = {opcode for opcode, result in opcode_results.items() if result["agreements"] + result["disagreements"] > 0}
    agreed = {opcode for opcode in tested if opcode_results[opcode]["disagreements"] == 0 and opcode_results[opcode]["lifter errors"] == 0}
    no_hw = {opcode for opcode, result in opcode_results.items() if result["faulted"] == result["inputs"]}
    report["no_hw"] = sorted(no_hw)
    reached = set(by_opcode) | untargeted
    report["control_no_case"] = sorted(untargeted - set(by_opcode))
    report["untested_no_encoding"] = sorted(name for name in set(opcodes) - reached if cfg.relevant(name))
    report["reached_not_in_lisp"] = sorted(reached - set(opcodes))
    report["decode_errors"] = decode_errors.most_common(20)
    report["undefined_diffs"] = dict(report["undefined_diffs"])
    report["disagreements"] = {opcode: found for opcode, found in report["disagreements"].items() if found}
    report["stats"] = dict(stats)
    report["table"] = {
        "opcodes in the Lisp": len([name for name in opcodes if cfg.relevant(name)]),
        "decoded": len(reached),
        "tested": len(tested),
        "all agree": len(agreed),
        "disagree": len(report["disagreements"]),
        "inputs": stats["inputs"],
        "agreements": stats["agreements"],
        "disagreements": stats["disagreements"],
        "lifter errors": stats["lifter errors"],
        "faulted": stats["faulted"],
        "fp, no value": len(report["fp"]),
        "excluded": len(report["excluded"]),
        "no encoding": len(report["untested_no_encoding"]),
        "undefined, differ": stats["undefined, differ"],
    }
    path = os.path.join(options.out, f"{name}.json")
    with open(path, "w") as handle:
        json.dump(report, handle, indent=1)
    print(f"{name}: {report['table']} in {time.time() - start:.0f}s -> {path}", flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="+")
    parser.add_argument("--out", default=None)
    parser.add_argument("--scratch", default=None)
    parser.add_argument("--inputs", type=int, default=32)
    parser.add_argument("--per-opcode", type=int, default=2)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--only", default=None)
    options = parser.parse_args()
    if not options.scratch:
        options.scratch = tempfile.mkdtemp(prefix="difftest")
    os.makedirs(options.scratch, exist_ok=True)
    if not options.out:
        options.out = options.scratch
    os.makedirs(options.out, exist_ok=True)
    names = targets.ALL if options.targets == ["all"] else options.targets
    rows = {}
    for name in names:
        rows[name] = drive(name, options)["table"]
    columns = list(next(iter(rows.values())).keys())
    print("| target | " + " | ".join(columns) + " |")
    print("|---|" + "---|" * len(columns))
    for name, row in rows.items():
        print(f"| {name} | " + " | ".join(str(row[column]) for column in columns) + " |")


if __name__ == "__main__":
    main()
