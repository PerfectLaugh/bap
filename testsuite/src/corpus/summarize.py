#!/usr/bin/env python3
"""summarizes the output of check.sh by the mnemonics: the ones, that
Unicorn doesn't have (unchecked), that have no semantics (missing), and
whose results differ (wrong), with an example of each:

  summarize.py CHECK
"""
import collections, re, sys

kinds = collections.defaultdict(dict)
for block in re.split(r"\n(?=DIFF)", open(sys.argv[1]).read()):
    m = re.match(r"DIFF (.*?)\s+# (\S+)(.*)", block)
    if not m:
        continue
    code, mnem = m.group(1), m.group(2)
    runs = [l for l in block.splitlines()[1:] if l.startswith("  run")]
    if all("unchecked" in r for r in runs):
        kind = "unchecked"
    elif any("no semantics" in r for r in runs):
        kind = "missing"
    else:
        kind = "wrong"
    kinds[kind].setdefault(mnem, f"{code} # {mnem}{m.group(3)}\n" + "\n".join(runs[:2]))
for kind in ["wrong", "missing", "unchecked"]:
    print(f"== {kind}: {len(kinds[kind])}")
    if kind == "wrong":
        for mnem, example in sorted(kinds[kind].items()):
            print(example[:400])
    else:
        print(" ".join(sorted(kinds[kind])))
