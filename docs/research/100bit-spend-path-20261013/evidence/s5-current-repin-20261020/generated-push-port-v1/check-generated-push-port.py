#!/usr/bin/env python3
"""Check the generated EbyEDot.push body against its explicit-callee Lean port.

This is a narrow source adapter check: it verifies the pinned emitted body and
the copied parameterized body differ only by the enumerated callee/constant
substitutions. It does not prove the Rust callees equal those parameters.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
PACKET = ROOT / "docs/research/100bit-spend-path-20261013/evidence/s5-current-repin-20261020/eby-e-four-dot-count-step-v1"
ADAPTER = Path(__file__).with_name("EbyEFourDotGeneratedPushPortV1.lean")
GEN = PACKET / "extraction/generated/AspisR1EbyEDotCutV1/Funs.lean"
EXPECTED_GENERATED = "ee6dab7728ae7cbace20a6ec655175c350405165d7c4441f7b0203072e9cefe5"

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def body_after(source: str, marker: str, end_marker: str) -> str:
    start = source.index(marker)
    end = source.index(end_marker, start)
    text = source[start:end]
    return text[text.index(":= do") + len(":= do"):]

generated = GEN.read_text()
adapter = ADAPTER.read_text()
if digest(GEN) != EXPECTED_GENERATED:
    raise SystemExit("generated Funs source pin mismatch")

g = body_after(generated, "def fast_pairing.EbyEDot.push\n", "/-- [eby_k_push_cut::fast_pairing::{eby_k_push_cut::fast_pairing::EbyEDot}::finish]")
a = body_after(adapter, "def emittedPushParameterized\n", "theorem emittedPushParameterized_eq_sourceSchedule")
g = g.replace("fast_pairing.MAX_TERMS", "maxTerm")
g = g.replace("fast_pairing.canonical.Q.from_wide", "fromWide")
g = g.replace("fast_pairing.canonical.Dot.push", "pushDot")
g = g.replace("self.count + 1#usize", "addUsize self.count 1#usize")
normalize = lambda s: re.sub(r"\s+", " ", s).strip()
if normalize(g) != normalize(a):
    raise SystemExit("generated push body differs beyond enumerated callee/constant substitutions")
print("PASS: generated EbyEDot.push body matches the parameterized Lean port modulo exactly: MAX_TERMS→maxTerm, Q.from_wide→fromWide, Dot.push→pushDot, checked count add→addUsize")
print(f"generated_sha256={digest(GEN)}")
print(f"adapter_sha256={digest(ADAPTER)}")
