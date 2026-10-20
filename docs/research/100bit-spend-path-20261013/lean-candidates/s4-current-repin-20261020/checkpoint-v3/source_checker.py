#!/usr/bin/env python3
"""Verify the exact current four_dots source pin and the range-critical shape."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[5]
SRC = ROOT / "crates/aspis-r1-cost-probe/src/fast_dots.rs"
SNAP = Path(__file__).with_name("four_dots.current.rs.txt")
PIN = Path(__file__).parents[2] / "evidence/s4-current-repin-20261020/source-pin.json"

def digest(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def extract_function(src: bytes) -> tuple[int, int, bytes]:
    start = src.index(b"pub fn four_dots(")
    brace = src.index(b"{", start)
    depth = 0
    for i in range(brace, len(src)):
        if src[i:i+1] == b"{":
            depth += 1
        elif src[i:i+1] == b"}":
            depth -= 1
            if depth == 0:
                return start, i + 1, src[start:i+1]
    raise AssertionError("four_dots closing brace not found")

raw = SRC.read_bytes()
start, end, body = extract_function(raw)
pin = json.loads(PIN.read_text())
assert digest(raw) == pin["source_sha256"]
assert [start, end] == pin["span_bytes"]
assert digest(body) == pin["span_sha256"]
assert SNAP.read_bytes().rstrip(b"\n") == body

# These are source-shape checks, not a proof of Rust/Aeneas operational semantics.
checks = {
    "fixed_608_prefix": r"let q\s*:\s*&\[u8;\s*608\]\s*=\s*q\[\.\.608\]\.try_into\(\)\.unwrap\(\)",
    "four_slots": r"core::array::from_fn\(\|slot\|",
    "seven_batch_loop": r"for start in \(0\.\.26\)\.step_by\(4\)",
    "batch_inner_range": r"for term in start\.\.core::cmp::min\(start \+ 4, 26\)",
    "base_offset": r"slot \* 120 \+ term \* 4",
    "eight_limb_loop": r"for limb in 0\.\.WideExact::LIMB_COUNT",
    "fold_expression": r"\(sums\[limb\] & 0x7fff_ffff\) \+ \(sums\[limb\] >> 31\)",
    "base_reduce": r"M31::reduce_u64\(limbs\[i\]\)",
    "slot_tail": r"slot\*120\+104\.\.slot\*120\+120",
    "two_tail_terms": r"for term in 0\.\.2",
    "tail_offset": r"480 \+ slot \* 32 \+ term \* 16",
    "tail_coefficients": r"g\[term\+26\]",
    "tail_finish_then_add": r"value\.add\(tail\.finish\(\)\)",
}
for name, pattern in checks.items():
    assert re.search(pattern, body.decode()), f"missing source shape {name}"

print(json.dumps({"source_sha256": digest(raw), "span_sha256": digest(body),
                  "span_bytes": [start, end], "checks": list(checks),
                  "status": "exact function snapshot and range-critical textual shapes verified; no semantic proof"},
                 indent=2))
