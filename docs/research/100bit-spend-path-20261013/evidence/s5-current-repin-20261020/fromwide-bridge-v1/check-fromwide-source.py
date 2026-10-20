#!/usr/bin/env python3
"""Check the copied to_limbs/from_wide body against the pinned Aeneas output."""
import hashlib
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
PACKET = ROOT / "docs/research/100bit-spend-path-20261013/evidence/s5-current-repin-20261020/eby-e-four-dot-count-step-v1"
GEN = PACKET / "extraction/generated/AspisR1EbyEDotCutV1/Funs.lean"
LEAN = Path(__file__).with_name("EbyEFourDotFromWideBridgeV1.lean")
EXPECTED_FUNS = "ee6dab7728ae7cbace20a6ec655175c350405165d7c4441f7b0203072e9cefe5"

def norm(s):
    return re.sub(r"\s+", "", s)

def region(src, start, end):
    x = src[src.index(start):src.index(end, src.index(start))]
    return x[x.index(":= do") + len(":= do"):]

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

g, a = GEN.read_text(), LEAN.read_text()
if sha(GEN) != EXPECTED_FUNS:
    raise SystemExit("generated Funs source pin mismatch")
g_limb = region(g, "def field.wide_exact.WideExact.to_limbs\n", "/-- [eby_k_push_cut::field::reduce_u64]")
a_limb = region(a, "def sourceToLimbs ", "/-- Verbatim source-shaped body")
if norm(g_limb) != norm(a_limb):
    raise SystemExit("to_limbs body differs")
g_q = region(g, "def fast_pairing.canonical.Q.from_wide\n", "/-- [eby_k_push_cut::fast_pairing::canonical::{eby_k_push_cut::fast_pairing::canonical::Dot}::new]")
a_q = region(a, "def sourceFromWide ", "theorem toPushWide_fields")
g_q = g_q.replace("field.wide_exact.WideExact.to_limbs value", "sourceToLimbs value")
if norm(g_q) != norm(a_q):
    raise SystemExit("Q::from_wide body differs beyond to_limbs callee substitution")
print("PASS: copied to_limbs body matches exactly; copied Q::from_wide body differs only by WideExact.to_limbs → sourceToLimbs")
print(f"generated_sha256={sha(GEN)}")
print(f"adapter_sha256={sha(LEAN)}")
