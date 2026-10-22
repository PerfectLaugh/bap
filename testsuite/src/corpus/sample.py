#!/usr/bin/env python3
"""samples the instructions of the objects of corpus.sh, at most N of
each mnemonic, with their distinct encodings, as the input of check.ml:

  sample.py N OBJECT... > INSNS
"""
import collections, re, subprocess, sys

n = int(sys.argv[1])
seen = collections.defaultdict(set)
for obj in sys.argv[2:]:
    out = subprocess.run(["llvm-objdump", "-d", obj],
                         capture_output=True, text=True).stdout
    for line in out.splitlines():
        parts = line.split("\t")
        m = re.match(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} ?)+)\s*$", parts[0])
        if not m or len(parts) < 2:
            continue
        code, mnem = m.group(1).strip(), parts[1].strip()
        # the words of the little-endian targets, e.g., of AArch64, are
        # the bytes in the order of the memory
        code = " ".join(
            " ".join(reversed([t[i:i + 2] for i in range(0, len(t), 2)]))
            for t in code.split())
        rest = " ".join(p.strip() for p in parts[2:])
        if mnem and len(seen[mnem]) < n and code not in {c for c, _ in seen[mnem]}:
            seen[mnem].add((code, f"{mnem} {rest}"))
for mnem in sorted(seen):
    for code, text in sorted(seen[mnem]):
        print(f"{code}  # {text}")
