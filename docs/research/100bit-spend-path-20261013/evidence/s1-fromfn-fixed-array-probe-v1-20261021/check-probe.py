#!/usr/bin/env python3
"""Validate the isolated, non-adopted fixed-array powers extraction probe."""
from pathlib import Path
import hashlib, json, re

D = Path(__file__).resolve().parent
C = D.parent.parent / "lean-candidates/s1-fromfn-fixed-array-probe-v1-20261021"
sha = lambda b: hashlib.sha256(b).hexdigest()

pins = json.loads((C / "input/source-pins.json").read_text())
for name, digest in pins["kit_files"].items():
    assert sha((C / "input" / name).read_bytes()) == digest, name

candidate = (C / "input/lib.rs").read_text()
proved = (D.parent.parent / "lean-candidates/s1-explicit-loop-powers-proved-candidate-20261020/extraction-input/lib.rs").read_text()
fn = re.compile(r"pub fn powers<const N:usize>.*?\n}", re.S)
cand_fn, proved_fn = fn.search(candidate).group(), fn.search(proved).group()
canon = lambda s: re.sub(r"\s+", "", s)
tail = lambda s: canon(s[s.index("while"):])
assert tail(cand_fn) == tail(proved_fn), "loop body differs from proved candidate body"
assert "core::array::from_fn" not in cand_fn
assert "letmutout=[E::ONE;N]" in canon(cand_fn)
assert "p=p.mul(x)" in canon(cand_fn)

funs = D / "generated/AspisR1CurrentPowers/Funs.lean"
text = funs.read_text()
assert "def weights.powers_loop.body" in text
assert "let out1 ← Array.update out i p" in text
assert "let p1 ← field.WideExact.mul p x" in text
assert "let i1 ← i + 1#usize" in text
assert "if i < 29#usize" in text
assert "from_fn" not in text and "try_from_fn" not in text

for phase in ("charon", "aeneas"):
    receipt = json.loads((D / f"receipts/{phase}/receipt.json").read_text())
    assert receipt["exit_status"] == 0
    assert receipt["limits"]["memory.swap.max"] == "0"
    assert receipt["process_swaps"] == 0

print(json.dumps({"status":"PASS", "candidate_only":True,
                  "loop_source_matches_proved_candidate_after_whitespace_normalization":True,
                  "generated_body":"weights.powers_loop.body", "N":29,
                  "std_from_fn_in_generated_Funs":False,
                  "formal_theorem_claimed_for_this_monomorphized_output":False}, indent=2))
