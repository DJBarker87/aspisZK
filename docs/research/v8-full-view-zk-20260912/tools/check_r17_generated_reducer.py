#!/usr/bin/env python3
"""Authenticate literal support and the explicitly macro-expanded reducer.

The only permitted generated-text rewrite is a closed #u32 literal's expansion
to U32.ofNat. Lean checks constructor/proof irrelevance and operational equality.
This checker is not a claim about the complete R17 caller or extraction pipeline.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
from check_r17_unsigned_slice import PINS as RUNTIME_PINS, PATTERN
from check_r17_field_slice import PINS as GENERATED_PINS

NOTATION_PIN = "45c40bf90ae960c24e2a82200393ceb184046be22582b428d5026d7d9577b133"
MACRO = 'macro:max x:term:max noWs "#u32"   : term => `(U32.ofNat $x (by first | decide | scalar_tac))'

def pinned(root, pins):
    result = {}
    for name, digest in pins.items():
        raw = (root / name).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("source pin mismatch: " + name)
        result[name] = raw.decode()
    return result

def blocks_match(blocks, expected, sources):
    if [name for name, _ in blocks] != expected:
        raise ValueError("block inventory mismatch")
    for name, body in blocks:
        if sources[name].count(body + "\n") != 1:
            raise ValueError("source block mismatch: " + name)

def check(runtime, stage, literals, generated, m31_mul=None):
    sources = pinned(runtime, {**RUNTIME_PINS, "Notations.lean": NOTATION_PIN})
    if sources["Notations.lean"].count(MACRO + "\n") != 1:
        raise ValueError("unexpected #u32 macro")
    source_generated = pinned(stage, GENERATED_PINS)
    normalized = {name: re.sub(r"\b(2147483647|31)#u32", r"(U32.ofNat \1)", text)
                  for name, text in source_generated.items()}
    expanded = re.compile(r"^-- EXPANDED GENERATED ([\w.]+)\n(.*?)\n-- END EXPANDED GENERATED$", re.M | re.S)
    literal_text = literals.read_text()
    generated_text = generated.read_text()
    def validate(lit, gen):
        blocks_match(PATTERN.findall(lit), ["Core.lean"] * 6, sources)
        blocks_match(PATTERN.findall(gen), ["Bitwise.lean"] * 2 + ["Ops/Sub.lean"], sources)
        blocks_match(expanded.findall(gen), ["FunsChunk04.lean"] * 2, normalized)
    validate(literal_text, generated_text)
    mutations = [
        (literal_text.replace("LE.le a.val b.val", "LE.le b.val a.val", 1), generated_text),
        (literal_text, generated_text.replace("(U32.ofNat 31)", "(U32.ofNat 30)", 1)),
        (literal_text, generated_text.replace("if x3 >=", "if x3 <=", 1)),
    ]
    for lit, gen in mutations:
        if (lit, gen) == (literal_text, generated_text):
            raise ValueError("ineffective negative test")
        try:
            validate(lit, gen)
        except ValueError:
            pass
        else:
            raise ValueError("negative mutation accepted")
    result = {"literal_source_blocks": 6, "operator_source_blocks": 3,
            "expanded_generated_blocks": 2, "negative_mutations_rejected": 3,
            "notation_pin": NOTATION_PIN,
            "literal_sha256": hashlib.sha256(literals.read_bytes()).hexdigest(),
            "generated_sha256": hashlib.sha256(generated.read_bytes()).hexdigest(),
            "full_caller_refinement": False}
    if m31_mul is not None:
        text = m31_mul.read_text()
        pattern = re.compile(r"^-- GENERATED ([\w.]+)\n(.*?)\n-- END GENERATED$", re.M | re.S)
        def validate_mul(value):
            blocks_match(pattern.findall(value), ["FunsChunk04.lean"] * 2, source_generated)
        validate_mul(text)
        for mutated in [text.replace("let i2 ← i * i1", "let i2 ← i + i1", 1),
                        text.replace("reduce_u64 value", "reduce_u64 (U32.ofNat 0)", 1)]:
            if mutated == text:
                raise ValueError("ineffective multiplication negative test")
            try:
                validate_mul(mutated)
            except ValueError:
                pass
            else:
                raise ValueError("multiplication mutation accepted")
        result.update(m31_mul_blocks=2, m31_mul_negative_mutations_rejected=2,
                      m31_mul_sha256=hashlib.sha256(m31_mul.read_bytes()).hexdigest())
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    for key in ("runtime", "stage", "literals", "generated"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--m31-mul", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.runtime, args.stage, args.literals, args.generated, args.m31_mul), sort_keys=True))
