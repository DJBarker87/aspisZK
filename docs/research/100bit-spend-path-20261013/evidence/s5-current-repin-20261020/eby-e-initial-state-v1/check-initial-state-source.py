#!/usr/bin/env python3
"""Check copied EbyEDot/Dot constructor bodies against pinned Aeneas Funs."""
import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
PACKET = ROOT / "docs/research/100bit-spend-path-20261013/evidence/s5-current-repin-20261020/eby-e-four-dot-count-step-v1"
GEN = PACKET / "extraction/generated/AspisR1EbyEDotCutV1/Funs.lean"
LEAN = Path(__file__).with_name("EbyEInitialStateV1.lean")
EXPECTED = "ee6dab7728ae7cbace20a6ec655175c350405165d7c4441f7b0203072e9cefe5"

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def body(src, marker, end):
    t = src[src.index(marker):src.index(end, src.index(marker))]
    return re.sub(r"\s+", "", t[t.index(":= do") + len(":= do"):])

g, a = GEN.read_text(), LEAN.read_text()
if sha(GEN) != EXPECTED: raise SystemExit("generated Funs pin mismatch")
gdot = body(g, "def fast_pairing.canonical.Dot.new", "/-- [eby_k_push_cut::fast_pairing::canonical::{eby_k_push_cut::fast_pairing::canonical::Dot}::finish]")
adot = body(a, "def sourceDotNew", "def sourceEbyENew")
if gdot != adot: raise SystemExit("Dot.new body mismatch")
geb = body(g, "def fast_pairing.EbyEDot.new", "/-- [eby_k_push_cut::fast_pairing::{eby_k_push_cut::fast_pairing::EbyEDot}::push]")
aeb = body(a, "def sourceEbyENew", "theorem sourceNew_success_initial_bound")
geb = geb.replace("fast_pairing.canonical.Dot.new", "sourceDotNew")
if geb != aeb: raise SystemExit("EbyEDot.new body mismatch beyond Dot.new callee")
print("PASS: constructor bodies match; only EbyEDot.new Dot.new call is renamed to sourceDotNew")
print(f"generated_sha256={sha(GEN)}")
print(f"adapter_sha256={sha(LEAN)}")
