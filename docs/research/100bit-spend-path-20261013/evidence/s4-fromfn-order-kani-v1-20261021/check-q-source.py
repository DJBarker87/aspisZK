#!/usr/bin/env python3
"""Check the tiny Kani Q cut against the retained exact source snapshots."""
from pathlib import Path
import hashlib, json

root = Path(__file__).resolve().parents[2]
cut = Path(__file__).resolve().parent / "src-q-v2.rs"
pins_path = root / "lean-candidates/s4-checked-q-all-unrolled-candidate-v1-20261021/source-pins.json"
original_path = root / "lean-candidates/s4-checked-q-all-unrolled-candidate-v1-20261021/source-snapshot/fast_pairing.original.rs"
candidate_path = root / "lean-candidates/s4-checked-q-all-unrolled-candidate-v1-20261021/source-snapshot/fast_pairing.candidate.rs"
pins = json.loads(pins_path.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(original_path) == pins["original_source_sha256"]
assert sha(candidate_path) == pins["candidate_source_sha256"]
original = original_path.read_text()
candidate = candidate_path.read_text()
cut_text = cut.read_text()
assert "pub fn from_limbs(x:[u32;4])->Option<Self>{if x.iter().all(|&v|v<P){Some(Self(x))}else{None}}" in original
assert "let [a,b,c,d]=x;\n            if a<P && b<P && c<P && d<P {Some(Self([a,b,c,d]))}else{None}" in candidate
assert "if x.iter().all(|&v| v < Q_P) { Some(Q(x)) } else { None }" in cut_text
assert "if a < Q_P && b < Q_P && c < Q_P && d < Q_P" in cut_text
print(json.dumps({"status":"PASS", "original_snapshot_sha256":sha(original_path),
                  "candidate_snapshot_sha256":sha(candidate_path), "source_cut_sha256":sha(cut),
                  "provenance":"retained snapshots selected by s4-checked-q source pins; Kani harness uses exact predicate bodies with carrier renamed from private source module Q to local Q"}, indent=2))
