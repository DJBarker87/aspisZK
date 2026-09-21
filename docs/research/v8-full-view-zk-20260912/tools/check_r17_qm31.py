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

def check(stage, scalar, mul_by_r=None, products=None):
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
    result = {"source_blocks": 3, "negative_mutations_rejected": 3,
            "sha256": hashlib.sha256(scalar.read_bytes()).hexdigest(),
            "full_caller_refinement": False}
    if mul_by_r is not None:
        value = mul_by_r.read_text()
        def validate_r(body):
            blocks_match(pattern.findall(body), ["FunsChunk04.lean"], sources)
        validate_r(value)
        for before, after in [("M31.sub m x.b", "M31.add m x.b"),
                              ("M31.add x.a m2", "M31.add x.b m2")]:
            changed = value.replace(before, after, 1)
            if changed == value:
                raise ValueError("ineffective mul_by_r mutation")
            try:
                validate_r(changed)
            except ValueError:
                pass
            else:
                raise ValueError("mul_by_r mutation accepted")
        result["mul_by_r"] = {"source_blocks": 1, "negative_mutations_rejected": 2,
                              "sha256": hashlib.sha256(mul_by_r.read_bytes()).hexdigest()}
    if products is not None:
        value = products.read_text()
        def validate_products(body):
            blocks_match(pattern.findall(body), ["FunsChunk04.lean"] * 2, sources)
        validate_products(value)
        for before, after in [("CM31.square self.c1", "CM31.square self.c0"),
                              ("CM31.sub c4 m1", "CM31.sub c4 m0")]:
            changed = value.replace(before, after, 1)
            if changed == value:
                raise ValueError("ineffective product mutation")
            try:
                validate_products(changed)
            except ValueError:
                pass
            else:
                raise ValueError("product mutation accepted")
        result["products"] = {"source_blocks": 2, "negative_mutations_rejected": 2,
                              "sha256": hashlib.sha256(products.read_bytes()).hexdigest()}
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--scalar", type=Path, required=True)
    parser.add_argument("--mul-by-r", type=Path)
    parser.add_argument("--products", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.stage, args.scalar, args.mul_by_r, args.products), sort_keys=True))
