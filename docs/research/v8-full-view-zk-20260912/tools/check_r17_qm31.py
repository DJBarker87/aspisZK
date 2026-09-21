#!/usr/bin/env python3
"""Check current QM31 scalar projection against pinned generated source."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from check_r17_generated_reducer import pinned, blocks_match
from check_r17_field_slice import PINS
from check_r17_half import CHUNK_PIN

def check(stage, scalar):
    sources = pinned(stage, {**PINS, "FunsChunk06.lean": CHUNK_PIN})
    pattern = re.compile(r"^-- GENERATED ([\w.]+)\n(.*?)\n-- END GENERATED$", re.M | re.S)
    def validate(text):
        blocks_match(pattern.findall(text),
                     ["Types.lean", "FunsChunk06.lean", "FunsChunk06.lean"], sources)
    text = scalar.read_text()
    validate(text)
    for before, after in [("c1 : aspis_core.field.CM31", "c1 : aspis_core.field.M31"),
                          ("M31.mul self.b rhs", "M31.mul self.a rhs"),
                          ("CM31.mul_m31 self.c1 rhs", "CM31.mul_m31 self.c0 rhs")]:
        changed = text.replace(before, after, 1)
        if changed == text:
            raise ValueError("ineffective negative mutation")
        try:
            validate(changed)
        except ValueError:
            pass
        else:
            raise ValueError("mutation accepted")
    return {"source_blocks": 3, "negative_mutations_rejected": 3,
            "sha256": hashlib.sha256(scalar.read_bytes()).hexdigest(),
            "full_caller_refinement": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--scalar", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.stage, args.scalar), sort_keys=True))
