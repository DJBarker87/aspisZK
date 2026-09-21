#!/usr/bin/env python3
"""Read-only authentication of the focused current generated field slice."""
import argparse
import hashlib
import json
import re
from pathlib import Path

PINS = {
    "Types.lean": "02c93204cbcaa6f5389fed89b9e67074536c6375f990a4504bba297c7780138b",
    "FunsChunk04.lean": "e79e0726e1a58ebfe3701b83f4339ca52b042e46cae833d573df3190c4bd0c21",
}
NAMES = [
    "M31", "CM31", "P", "M31.add", "M31.double", "M31.sub",
    "reduce_u64", "M31.mul", "M31.reduce_u64", "CM31.square", "CM31.mul",
]

def declaration(text, name):
    match = re.search(r"^(?:def|structure) " + re.escape(name) + r"(?:\s|$)", text, re.M)
    if match is None:
        raise ValueError("missing declaration: " + name)
    start = text.rfind("\n@[", 0, match.start()) + 1
    ends = [i for i in (text.find("\n/--", match.start()), text.find("\n@[", match.start()),
                       text.find("\nend V7Tag73CurrentHelpersOpaque", match.start())) if i >= 0]
    if start < 1 or not ends:
        raise ValueError("unrecognized declaration boundary: " + name)
    return text[start:min(ends)].rstrip()

def validate_slice(sources, text):
    expected = ["aspis_core.field." + name for name in NAMES]
    found = re.findall(r"^(?:def|structure) ([\w.]+)", text, re.M)
    if found != expected:
        raise ValueError("slice declaration inventory mismatch")
    for index, name in enumerate(expected):
        source = sources["Types.lean" if index < 2 else "FunsChunk04.lean"]
        if declaration(source, name) != declaration(text, name):
            raise ValueError("changed generated declaration: " + name)

def check(stage, sliced, self_test=False):
    sources = {}
    for filename, digest in PINS.items():
        raw = (stage / filename).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("source pin mismatch: " + filename)
        sources[filename] = raw.decode()
    raw_slice = sliced.read_bytes()
    text = raw_slice.decode()
    validate_slice(sources, text)
    rejected = 0
    if self_test:
        mutations = [
            text.replace("2147483647#u32", "2147483646#u32", 1),
            text.replace("reducible, rust_type", "irreducible, rust_type", 1),
            text.replace("def aspis_core.field.M31 :=", "def aspis_core.field.Removed :=", 1),
            text + "\ndef injected : Nat := 0\n",
        ]
        for mutated in mutations:
            if mutated == text:
                raise ValueError("ineffective negative checker test")
            try:
                validate_slice(sources, mutated)
            except ValueError:
                rejected += 1
            else:
                raise ValueError("checker accepted a negative mutation")
    return {"declarations": len(NAMES), "pins": PINS,
            "slice_sha256": hashlib.sha256(raw_slice).hexdigest(),
            "declaration_bytes_match": True, "negative_mutations_rejected": rejected,
            "full_r17_source_refinement": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--slice", type=Path, required=True)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    print(json.dumps(check(args.stage, args.slice, args.self_test), sort_keys=True))
