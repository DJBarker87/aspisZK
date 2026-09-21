#!/usr/bin/env python3
"""Authenticate signed literals and the macro-expanded current half graph.

One proof-only rewrite is allowed in ofIntCore. No executable expression or
premise is rewritten. This does not certify the whole extraction pipeline.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
from check_r17_generated_reducer import pinned, blocks_match, NOTATION_PIN
from check_r17_unsigned_slice import PINS, PATTERN

CHUNK_PIN = "f57cf84b503d6c0f03199a951872f3676bd7c9dcc644416372ab8289e6b52b9e"
OLD_PROOF = """    zify
    simp +zetaDelta only [Int.ofNat_toNat, sup_lt_iff, Nat.ofNat_pos, pow_pos, and_true]
    apply Int.emod_lt_of_pos; simp"""
NEW_PROOF = """    apply (Int.toNat_lt' (Nat.two_pow_pos ty.numBits)).mpr
    exact Int.emod_lt_of_pos x (Int.pow_pos (by decide))"""
ADAPTED = re.compile(r"^-- PROOF ADAPTED ([\w.]+)\n(.*?)\n-- END PROOF ADAPTED$", re.M | re.S)
EXPANDED = re.compile(r"^-- EXPANDED GENERATED ([\w.]+)\n(.*?)\n-- END EXPANDED GENERATED$", re.M | re.S)

def check(runtime, literals, stage=None, generated=None):
    sources = pinned(runtime, {**PINS, "Notations.lean": NOTATION_PIN})
    for suffix, constructor in [("i32", "I32.ofInt"), ("u32", "U32.ofNat")]:
        macro = f'macro:max x:term:max noWs "#{suffix}"   : term => `({constructor} $x (by first | decide | scalar_tac))'
        if sources["Notations.lean"].count(macro + "\n") != 1:
            raise ValueError("literal macro mismatch")
    def validate_literal(text):
        blocks_match(PATTERN.findall(text), ["Core.lean"] * 7, sources)
        adapted = ADAPTED.findall(text)
        if len(adapted) != 1 or adapted[0][1].count(NEW_PROOF) != 1:
            raise ValueError("unexpected proof adaptation")
        blocks_match([(name, body.replace(NEW_PROOF, OLD_PROOF)) for name, body in adapted],
                     ["Core.lean"], sources)
    text = literals.read_text()
    validate_literal(text)
    mutations = [text.replace("x % 2^ty.numBits", "x % 2^(ty.numBits-1)", 1),
                 text.replace("I32.rMax  : Int := 2147483647", "I32.rMax  : Int := 2147483646", 1)]
    for changed in mutations:
        if changed == text:
            raise ValueError("ineffective literal mutation")
        try:
            validate_literal(changed)
        except ValueError:
            pass
        else:
            raise ValueError("literal mutation accepted")
    result = {"literal_exact_blocks": 7, "proof_adapted_blocks": 1,
              "literal_mutations_rejected": 2,
              "literal_sha256": hashlib.sha256(literals.read_bytes()).hexdigest(),
              "full_caller_refinement": False}
    if generated is not None:
        source = pinned(stage, {"FunsChunk06.lean": CHUNK_PIN})
        normalized = {name: re.sub(r"\b(1|30)#i32", r"(I32.ofInt \1)",
                      re.sub(r"\b1#u32", "(U32.ofNat 1)", body)) for name, body in source.items()}
        def validate_generated(value):
            blocks_match(PATTERN.findall(value), ["Bitwise.lean"] * 3, sources)
            blocks_match(EXPANDED.findall(value), ["FunsChunk06.lean"] * 2, normalized)
        value = generated.read_text()
        validate_generated(value)
        for changed in [value.replace("(I32.ofInt 30)", "(I32.ofInt 29)", 1),
                        value.replace("M31.half self.b", "M31.half self.a", 1)]:
            if changed == value:
                raise ValueError("ineffective half mutation")
            try:
                validate_generated(changed)
            except ValueError:
                pass
            else:
                raise ValueError("half mutation accepted")
        result.update(generated_blocks=2, generated_mutations_rejected=2,
                      generated_sha256=hashlib.sha256(generated.read_bytes()).hexdigest(),
                      chunk_pin=CHUNK_PIN)
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--literals", type=Path, required=True)
    parser.add_argument("--stage", type=Path)
    parser.add_argument("--generated", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(args.runtime, args.literals, args.stage, args.generated), sort_keys=True))
