#!/usr/bin/env python3
"""Authenticate the unsigned slice against full pinned runtime source files.

This checks source text, not Lean elaboration or a complete caller refinement.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

PINS = {
    "Core.lean": "ceba1982545251f02d6e286abf23d01f4d2a691fe6934149f3a42d4a051af81e",
    "Ops/Add.lean": "8ef617fc0cd36e68a4c691a415ba94e79de99899ab1e93428739b95ebb0b658e",
    "Ops/Mul.lean": "da6635db5fb2721b5dc748e46cc8b5990dd9a8e4478b980ca3b9b941b23860b7",
}
PATTERN = re.compile(r"^-- SOURCE ([\w/.]+)\n(.*?)\n-- END SOURCE$", re.M | re.S)

def validate(sources, text):
    blocks = PATTERN.findall(text)
    if [name for name, _ in blocks] != ["Core.lean"] * 10 + ["Ops/Add.lean", "Ops/Mul.lean"]:
        raise ValueError("source block inventory mismatch")
    for name, body in blocks:
        if sources[name].count(body + "\n") != 1:
            raise ValueError("source block not uniquely authenticated: " + name)
    return len(blocks)

def check(runtime, sliced):
    sources = {}
    for name, digest in PINS.items():
        raw = (runtime / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("runtime pin mismatch: " + name)
        sources[name] = raw.decode()
    raw = sliced.read_bytes()
    text = raw.decode()
    count = validate(sources, text)
    mutations = [
        text.replace("x.val + y.val", "x.val * y.val", 1),
        text.replace("x < 2^ty.numBits", "x ≤ 2^ty.numBits", 1),
        text.replace("-- SOURCE Core.lean", "-- SOURCE Missing.lean", 1),
    ]
    for mutated in mutations:
        if mutated == text:
            raise ValueError("ineffective negative test")
        try:
            validate(sources, mutated)
        except ValueError:
            pass
        else:
            raise ValueError("negative mutation accepted")
    return {"source_blocks": count, "pins": PINS,
            "slice_sha256": hashlib.sha256(raw).hexdigest(),
            "negative_mutations_rejected": len(mutations),
            "full_caller_refinement": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--slice", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.runtime, args.slice), sort_keys=True))
