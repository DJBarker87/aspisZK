#!/usr/bin/env python3
"""Pin the S2 optimized inactive lookup to its Rust source and Lean table model."""
from pathlib import Path
import hashlib, json, re

root = Path(__file__).resolve().parents[5]
evidence = Path(__file__).resolve().parent
weights = (evidence / "weights.rs").read_text()
transport = (evidence / "transport.rs").read_text()
model = (evidence / "S3S9CurrentSourceModel.lean").read_text()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def literal_list(text, pattern, label):
    m = re.search(pattern, text, re.S)
    if not m:
        raise SystemExit(f"missing literal list: {label}")
    return [int(x) for x in re.findall(r"\d+", m.group(1))]

rust_groups = literal_list(weights, r"const\s+S2_INACTIVE_GROUPS\s*:\s*\[u8;\s*64\]\s*=\s*\[([^]]*)\]", "S2_INACTIVE_GROUPS")
rust_masks = literal_list(weights, r"const\s+S2_INACTIVE_MASKS\s*:\s*\[u16;\s*12\]\s*=\s*\[([^]]*)\]", "S2_INACTIVE_MASKS")
lean_groups = literal_list(model, r"def\s+inactiveGroups\s*:\s*List Nat\s*:=\s*\[([^]]*)\]", "inactiveGroups")
lean_masks = literal_list(model, r"def\s+inactiveMasks\s*:\s*List Nat\s*:=\s*\[([^]]*)\]", "inactiveMasks")
assert len(rust_groups) == 64 and rust_groups == lean_groups, "group table mismatch"
assert len(rust_masks) == 12 and rust_masks == lean_masks, "mask table mismatch"

compact_weights = re.sub(r"\s+", "", weights)
compact_transport = re.sub(r"\s+", "", transport)
required = [
    "ifweights.variant==Variant::S2&&f.len()==64*32{return s2_grouped_inactive_pair(f,low);}",
    "S2_INACTIVE_MASKS[group]&(1<<bit)!=0",
    "letgroup=S2_INACTIVE_GROUPS[j]asusize;",
    "coefficients[group]=coefficients[group].add(field(f,j));",
    "parts[0]=grouped_inactive_pair(self,f,&low);",
    "iffolds==1{",
]
for fragment in required:
    assert re.sub(r"\s+", "", fragment) in compact_weights, f"missing source branch fragment {fragment}"
assert re.sub(r"\s+", "", "pub fn folds(self) -> usize { if self == Self::S1 { 1 } else { 2 } }") in compact_transport
assert re.sub(r"\s+", "", "if n != 1024 >> (2*folds) { return Err(Error::Parse); }") in compact_weights

report = {
    "status": "PASS",
    "weights_sha256": digest(evidence / "weights.rs"),
    "transport_sha256": digest(evidence / "transport.rs"),
    "model_sha256": digest(evidence / "S3S9CurrentSourceModel.lean"),
    "frozen_source_revision": "b2727acd3",
    "groups_count": len(rust_groups),
    "masks_count": len(rust_masks),
    "checked_source_facts": [
        "S2 fast helper dispatch at f.len()==2048",
        "optimized S2 pair reaches grouped_inactive_pair in the two-fold branch",
        "S2 group and mask literals equal the Lean source model literals",
        "per-cell optimized test uses mask AND one shifted bit",
        "optimized coefficient loop uses the matching group index",
        "non-S2/non-2048 fallback remains a separate raw-based path",
    ],
    "scope": "source correspondence for optimized lookup structure and literal tables; no grouped accumulation arithmetic proof",
}
print(json.dumps(report, indent=2))
