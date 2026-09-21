#!/usr/bin/env python3
"""Stage allocation-free QM31 group-dot batching on retained R36 source."""
import argparse, hashlib, json, shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS

FIELD_SHA256 = "5795495e2fa9ad85e097c2ad96ffc826aaad3c16afc0e0bd00459f9f51068cd8"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def replace_fn(text, name, body):
    start = text.index(f"fn {name}")
    brace, depth, end = text.index("{", start), 0, start
    for end in range(brace, len(text)):
        if text[end] == "{": depth += 1
        elif text[end] == "}":
            depth -= 1
            if depth == 0:
                return text[:start] + body + text[end + 1:]
    raise AssertionError(name)

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--stage", type=Path, required=True)
ap.add_argument("--output", type=Path, required=True)
a = ap.parse_args()
assert not a.output.exists()
meta = json.loads((a.stage / "r17-compact-control.json").read_text())
for name, expected in meta["files"].items():
    assert sha(a.stage / EXPERIMENTS / name) == expected, name
for name, expected in meta.get("core_files", {}).items():
    assert sha(a.stage / name) == expected, name
assert sha(a.stage / "crates/aspis-core/src/field.rs") == FIELD_SHA256
shutil.copytree(a.stage, a.output)
root = a.output / EXPERIMENTS

wg = root / "r17_weighted_groups.rs"
old_wg = wg.read_text()
(root / "r17_weighted_groups_reference.rs").write_text(old_wg)
s = old_wg.replace(
    "use super::{corelib,K,M31};",
    "use super::{corelib,K,M31};\nuse corelib::field::{qm31_sum_products4,PreparedQm31Multiplier};", 1)
assert s != old_wg
s = s.replace("pub(super) struct Kernel { normal:[K;16],carry:[K;3],high:[K;16] }",
              "pub(super) struct Kernel { normal:[K;16],carry:[K;3],high:[K;16],prepared_carry:[PreparedQm31Multiplier;3] }", 1)
s = s.replace("Self{normal,carry,high}",
              "let prepared_carry=core::array::from_fn(|i|PreparedQm31Multiplier::new(carry[i])); Self{normal,carry,high,prepared_carry}", 1)
s = replace_fn(s, "contract", '''fn contract(&self,read:impl Fn(usize)->(K,K))->[K;4] {
        let mut out=[K::ZERO;4];
        for group in 0..4 {
            let mut left=[K::ZERO;4]; let mut right=[K::ZERO;4];
            for lane in 0..16 {
                let j=group*16+lane; let mut value=read(j).0;
                for (r,scale) in edges(j) { if r<64 { value=value.add(read(r).1.mul_m31(scale)); } }
                let slot=lane&3; left[slot]=self.high[lane]; right[slot]=value;
                if slot==3 { out[group]=out[group].add(qm31_sum_products4(left,right)); }
            }
        }
        for value in &mut out {for _ in 0..8 {*value=value.half();}}
        out
    }''')
wg.write_text(s)

wm = root / "r17_workspace_group_methods.rs"
old_wm = wm.read_text()
(root / "r17_workspace_group_methods_reference.rs").write_text(old_wm)
new_wm = old_wm.replace(
    "sums[2*g]=row.iter().enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.normal[j])));",
    "sums[2*g]=corelib::field::qm31_dot(&self.normal[..row.len()],row);", 1)
new_wm = new_wm.replace(
    "sums[2*g+1]=row.iter().take(3).enumerate().fold(K::ZERO,|s,(j,&v)|s.add(v.mul(self.carry[j])));",
    "sums[2*g+1]=match row.len(){0=>K::ZERO,1=>self.carry[0].mul(row[0]),2=>self.carry[0].mul(row[0]).add(self.carry[1].mul(row[1])),_=>corelib::field::qm31_sum_products3_prepared(&self.prepared_carry,&[row[0],row[1],row[2]])};", 1)
assert new_wm != old_wm
wm.write_text(new_wm)

for name in ["r17_weighted_groups.rs", "r17_workspace_group_methods.rs",
             "r17_weighted_groups_reference.rs", "r17_workspace_group_methods_reference.rs"]:
    meta["files"][name] = sha(root / name)
meta["group_dot"] = {
    "source_base": "r36b-retained-control",
    "field_helper_sha256": FIELD_SHA256,
    "before": {"r17_weighted_groups.rs": sha(a.stage / EXPERIMENTS / "r17_weighted_groups.rs"),
               "r17_workspace_group_methods.rs": sha(a.stage / EXPERIMENTS / "r17_workspace_group_methods.rs")},
    "after": {"r17_weighted_groups.rs": sha(root / "r17_weighted_groups.rs"),
              "r17_workspace_group_methods.rs": sha(root / "r17_workspace_group_methods.rs")},
    "reference": ["r17_weighted_groups_reference.rs", "r17_workspace_group_methods_reference.rs"],
    "route": "qm31_dot normal rows; prepared three-lane carry; qm31_sum_products4 high blocks; exact edges and eight halvings retained",
    "allocation": "caller-owned sums unchanged; no allocation in prefix_into or contract",
}
meta["scope"] = "R36 actual-source allocation-free group-dot candidate; source controls unchanged"
meta["bin"] = "r17-compact-workspace-check"
(a.output / "r17-compact-control.json").write_text(json.dumps(meta, indent=2) + "\n")

probe_path = a.output / "r17-sbf-probe.json"
probe = json.loads(probe_path.read_text())
probe["group_dot"] = {
    name: {"before_sha256": sha(a.stage / EXPERIMENTS / name),
           "after_sha256": sha(root / name)}
    for name in ("r17_weighted_groups.rs", "r17_workspace_group_methods.rs")
}
probe["group_dot_files"] = {
    name: sha(root / name)
    for name in ("r17_weighted_groups_reference.rs", "r17_workspace_group_methods_reference.rs")
}
probe_path.write_text(json.dumps(probe, indent=2) + "\n")
