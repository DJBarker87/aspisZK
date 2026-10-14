#!/usr/bin/env python3
"""Generate the source-pinned retained exact tower/limb equivalence block."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs/research/100bit-spend-path-20261013/RETAINED-EXACT-LIMB-SOURCES.json"

def extract(m: dict) -> str:
    e = m["source"]
    path = ROOT / e["path"]
    raw = path.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != e["sha256"]:
        raise ValueError(f"source hash mismatch for {e['path']}: {actual}")
    src = raw.decode()
    if src.count(e["start"]) != 1 or src.count(e["end"]) != 1:
        raise ValueError("source extraction markers must be unique")
    i = src.index(e["start"])
    j = src.index(e["end"])
    if j <= i:
        raise ValueError("source extraction end precedes start")
    block = src[i:j].rstrip()
    repl = m["proof_replacement"]
    if block.count(repl["from"]) != repl["expected_count"]:
        raise ValueError("exact proof replacement count mismatch")
    block = block.replace(repl["from"], repl["to"])
    imports = "\n".join(f"import {x}" for x in m["imports"])
    opens = "\n".join(f"open {x}" for x in m["opens"])
    return (imports + "\n\n/-! Exact copied declaration block. The sole body replacement is its "+
            "namespace/open resolution; source bytes are pinned in the adjacent manifest. -/\n"+
            "set_option autoImplicit false\n\nnamespace " + m["namespace"] + "\n\n"+
            opens + "\n\n" + block + "\n\nend " + m["namespace"] + "\n")

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    m = json.loads(MANIFEST.read_text())
    out = ROOT / m["output"]
    expected = extract(m)
    if args.check:
        try:
            actual = out.read_text()
        except FileNotFoundError:
            print(f"missing generated file: {out}", file=sys.stderr)
            return 1
        if actual != expected:
            print(f"generated output differs: {out}", file=sys.stderr)
            return 1
        print(f"checked {out.relative_to(ROOT)}")
        return 0
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(expected)
    print(f"wrote {out.relative_to(ROOT)}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
