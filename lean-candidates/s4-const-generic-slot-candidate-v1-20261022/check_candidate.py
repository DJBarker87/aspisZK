#!/usr/bin/env python3
"""Check that this candidate is exactly one const-generic slot specialization."""

import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[1]
BASE_REV = "5b23a95e6"
REL = "crates/aspis-r1-cost-probe/src/fast_dots.rs"
EXPECTED_BASE = "53fa714e84ded64b844061f4d1b66ad20ee1ba48c3873a73970f80ede8a0b602"
EXPECTED_CANDIDATE = "f7174aa74b3b9608eec8cd63d1d891ec5591ebe3c7b799eb9520758cae5fa9c3"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


base = subprocess.run(
    ["git", "show", f"{BASE_REV}:{REL}"], cwd=REPO, check=True, capture_output=True
).stdout
assert sha(base) == EXPECTED_BASE
expected = base.decode()
old_sig = "fn four_dots_one(q: &[u8; 608], g: &[WideExact; 29], slot: usize) -> WideExact {"
new_sig = "fn four_dots_one<const SLOT: usize>(q: &[u8; 608], g: &[WideExact; 29]) -> WideExact {\n    let slot = SLOT;"
assert expected.count(old_sig) == 1
expected = expected.replace(old_sig, new_sig)
for slot in range(4):
    old_call = f"four_dots_one(q, g, {slot})"
    new_call = f"four_dots_one::<{slot}>(q, g)"
    assert expected.count(old_call) == 1
    expected = expected.replace(old_call, new_call)
candidate = (ROOT / "fast_dots.rs").read_bytes()
assert sha(candidate) == EXPECTED_CANDIDATE
assert candidate.decode() == expected
print("PASS: exactly one fast_dots.rs blob change; helper body preserved behind const local")
