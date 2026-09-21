#!/usr/bin/env python3
"""Authenticate generated ZERO/ONE and a direct word model of Rust M31_HALF."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from check_r17_generated_reducer import pinned, blocks_match, NOTATION_PIN, MACRO
from check_r17_field_slice import PINS
from check_r17_half import CHUNK_PIN, EXPANDED

def check(stage, runtime, field, constants):
    source = pinned(stage, {**PINS, "FunsChunk06.lean": CHUNK_PIN})
    notation = pinned(runtime, {"Notations.lean": NOTATION_PIN})
    if notation["Notations.lean"].count(MACRO + "\n") != 1:
        raise ValueError("literal macro mismatch")
    raw = field.read_bytes()
    if hashlib.sha256(raw).hexdigest() != "5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8":
        raise ValueError("field source pin mismatch")
    if raw.decode().count("pub const M31_HALF: M31 = M31(0x4000_0000);\n") != 1:
        raise ValueError("half constant mismatch")
    assert int("40000000", 16) == 1073741824
    normalized = {name: re.sub(r"\b([01])#u32", r"(U32.ofNat \1)", body)
                  for name, body in source.items()}
    def validate(text):
        blocks_match(EXPANDED.findall(text), ["FunsChunk04.lean", "FunsChunk06.lean"], normalized)
        if text.count("def halfWord : aspis_core.field.M31 := U32.ofNat 1073741824\n") != 1:
            raise ValueError("half word model mismatch")
    text = constants.read_text()
    validate(text)
    for changed in [text.replace("a := (U32.ofNat 1)", "a := (U32.ofNat 0)", 1),
                    text.replace("U32.ofNat 1073741824", "U32.ofNat 1073741823", 1)]:
        if changed == text:
            raise ValueError("ineffective mutation")
        try:
            validate(changed)
        except ValueError:
            pass
        else:
            raise ValueError("mutation accepted")
    return {"expanded_generated_blocks": 2, "rust_half_word_model": True,
            "negative_mutations_rejected": 2,
            "sha256": hashlib.sha256(constants.read_bytes()).hexdigest(),
            "full_caller_refinement": False}

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    for name in ("stage", "runtime", "field", "constants"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.stage, args.runtime, args.field, args.constants), sort_keys=True))
