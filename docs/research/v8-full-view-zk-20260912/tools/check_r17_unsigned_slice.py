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
    "CoreConvertNum.lean": "d7bbeaa3cc7422dcad0a52ffc1904a2d11751717a7b5d820d645404e0bf81eaa",
    "Bitwise.lean": "63e4b1d0906c972fb4fef953d8d8a60410dcf5313261d2583b1170b4a1a5ce29",
    "Casts.lean": "fd709a15b1e66431b788bf2838b79ac662d4c2afd38acbcde078b775c8f1e668",
    "Ops/Sub.lean": "bd6716dad017ce0c0e9cf9084f9223eb5407ece920853ae7675cbe2362dd5e37",
}
PATTERN = re.compile(r"^-- SOURCE ([\w/.]+)\n(.*?)\n-- END SOURCE$", re.M | re.S)

def validate(sources, text, cross=False, reducer=False, signed=False):
    blocks = PATTERN.findall(text)
    expected = (["Core.lean"] * 2 + ["CoreConvertNum.lean", "Ops/Add.lean", "Ops/Mul.lean"] if cross else
                ["Core.lean"] * 10 + ["Ops/Add.lean", "Ops/Mul.lean"])
    if reducer:
        expected = ["Casts.lean"] + ["Bitwise.lean"] * 3 + ["Ops/Sub.lean"]
    if signed:
        expected = ["Core.lean"] * 5 + ["Bitwise.lean"] * 4
    if [name for name, _ in blocks] != expected:
        raise ValueError("source block inventory mismatch")
    for name, body in blocks:
        if sources[name].count(body + "\n") != 1:
            raise ValueError("source block not uniquely authenticated: " + name)
    return len(blocks)

def check(runtime, sliced, cross=False, reducer=False, signed=False):
    sources = {}
    for name, digest in PINS.items():
        raw = (runtime / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("runtime pin mismatch: " + name)
        sources[name] = raw.decode()
    raw = sliced.read_bytes()
    text = raw.decode()
    count = validate(sources, text, cross, reducer, signed)
    mutations = ([
        text.replace("U32   := UScalar .U32", "U32   := UScalar .U64", 1),
        text.replace("x.bv.setWidth _", "x.bv.setWidth 32", 1),
        text.replace("-- SOURCE Core.lean", "-- SOURCE Missing.lean", 1),
    ] if cross else [
        text.replace("x.val + y.val", "x.val * y.val", 1),
        text.replace("x < 2^ty.numBits", "x ≤ 2^ty.numBits", 1),
        text.replace("-- SOURCE Core.lean", "-- SOURCE Missing.lean", 1),
    ])
    if reducer:
        mutations = [
            text.replace("s < ty.numBits", "s ≤ ty.numBits", 1),
            text.replace("x.val - y.val", "x.val + y.val", 1),
            text.replace("-- SOURCE Casts.lean", "-- SOURCE Missing.lean", 1),
        ]
    if signed:
        mutations = [
            text.replace("s.val ≥ 0", "s.val > 0", 1),
            text.replace("s < ty.numBits", "s ≤ ty.numBits", 1),
            text.replace("x.bv ||| y.bv", "x.bv &&& y.bv", 1),
        ]
    for mutated in mutations:
        if mutated == text:
            raise ValueError("ineffective negative test")
        try:
            validate(sources, mutated, cross, reducer, signed)
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
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--cross", action="store_true")
    mode.add_argument("--reducer", action="store_true")
    mode.add_argument("--signed", action="store_true")
    args = parser.parse_args()
    print(json.dumps(check(args.runtime, args.slice, args.cross, args.reducer, args.signed), sort_keys=True))
