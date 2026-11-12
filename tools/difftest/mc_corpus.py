#!/usr/bin/env python3
"""Makes a corpus of encodings for the differential test from the MC tests of LLVM: each instruction that a test assembles, and
copies of it with its registers and immediates changed, as far as they assemble, with what is written of them. What the tests
expect isn't used: only the forms of the operands, which the inputs of the test then vary.

    python3 tools/difftest/mc_corpus.py --mattr +sve2 --out tools/difftest/corpus/aarch64-sve2.insns \
        _deps/src/llvm-project-*/llvm/test/MC/AArch64/SVE2

TEST is a file of the MC tests or a directory of them, of which those of diagnostics are left out.
"""
import argparse
import os
import random
import re
import subprocess
import sys

COMMENT = re.compile(r"//.*|;.*")


def lines_of(paths):
    """The lines of the tests that are instructions: not directives, comments or what is empty."""
    for path in paths:
        files = sorted(os.path.join(path, name) for name in os.listdir(path)) if os.path.isdir(path) else [path]
        for name in files:
            if not name.endswith(".s") or "diagnostic" in name or "error" in name:
                continue
            with open(name) as source:
                for line in source:
                    line = COMMENT.sub("", line).strip()
                    if line and not line.startswith(".") and not line.endswith(":"):
                        yield line


def variant(line, rng):
    """The line with each register of a kind changed alike, so that a list of them stays one, and its immediates as they are."""
    mapping = {}

    def change(match):
        kind, number = match.group(1), int(match.group(2))
        limit = {"z": 32, "p": 16, "x": 31, "w": 31, "pn": 16, "v": 32}[kind.lower()]
        key = (kind.lower(), number)
        if key not in mapping:
            mapping[key] = (number + rng.randrange(limit)) % limit
        return f"{kind}{mapping[key]}"

    shift = rng.randrange(32)
    # the registers of a list, `{ z1.b - z4.b }` or `{ z1.b, z2.b }`, are moved together, as they have to be consecutive
    if "{" in line:
        return re.sub(r"\b([zZ])(\d+)\b", lambda m: f"{m.group(1)}{(int(m.group(2)) + shift) % 32}", line)
    return re.sub(r"\b(pn|[zpxwv])(\d+)\b", change, line)


def assemble(triple, mattr, lines):
    """The encoding of each line that assembles, in order."""
    result = subprocess.run(["llvm-mc", f"-triple={triple}", f"-mattr={mattr}", "-show-encoding"], input="\n".join(lines) + "\n",
                            capture_output=True, text=True)
    found = []
    for line in result.stdout.splitlines():
        match = re.match(r"\s*(.*?)\s*//\s*encoding:\s*\[(.*)\]", line)
        # an encoding of a fixup has bytes that aren't known, e.g. `0bAAAAAAAA`, which isn't run
        if match and all(re.fullmatch(r"0x[0-9a-fA-F]{1,2}", byte.strip()) for byte in match.group(2).split(",")):
            text = re.sub(r"\s+", " ", match.group(1).replace("\t", " ")).strip()
            found.append((bytes(int(byte, 16) for byte in match.group(2).split(",")), text))
    return found


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--triple", default="aarch64")
    parser.add_argument("--mattr", required=True)
    parser.add_argument("--variants", type=int, default=6)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--out", required=True)
    parser.add_argument("tests", nargs="+")
    arguments = parser.parse_args()
    rng = random.Random(arguments.seed)
    lines = sorted(set(lines_of(arguments.tests)))
    candidates = list(lines)
    for line in lines:
        candidates += [variant(line, rng) for _ in range(arguments.variants)]
    seen, out = set(), []
    # llvm-mc goes on past a line that doesn't assemble, and says nothing of it on standard output
    for code, text in assemble(arguments.triple, arguments.mattr, candidates):
        if code in seen:
            continue
        seen.add(code)
        out.append(f"{' '.join(f'{byte:02x}' for byte in code)}  # {text}")
    with open(arguments.out, "w") as output:
        output.write("# encodings of the MC tests of LLVM with their registers changed, for a differential test only: what they\n")
        output.write(f"# expect isn't used (tools/difftest/mc_corpus.py --mattr {arguments.mattr})\n\n")
        output.write("\n".join(out) + "\n")
    print(f"{len(out)} encodings of {len(lines)} lines", file=sys.stderr)


if __name__ == "__main__":
    main()
