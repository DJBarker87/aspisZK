#!/usr/bin/env python3
"""Stage the approved pure-read carry nesting and pivot shortcut on R38."""
import argparse, hashlib, json, shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def replace_fn(text, name, body):
    start = text.index(f"fn {name}")
    brace, depth = text.index("{", start), 0
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
control = json.loads((a.stage / "r17-compact-control.json").read_text())
for name, expected in control["files"].items():
    assert sha(a.stage / EXPERIMENTS / name) == expected, name
for name, expected in control.get("core_files", {}).items():
    assert sha(a.stage / name) == expected, name
probe = json.loads((a.stage / "r17-sbf-probe.json").read_text())
for section in ("group_dot", "opening_reuse"):
    assert section in probe, section
shutil.copytree(a.stage, a.output)
root = a.output / EXPERIMENTS

# Preserve exact pre-R41 source snapshots before replacing any implementation.
for name in ("r17_owned_weights.rs", "r17_weighted_groups.rs"):
    (root / (name[:-3] + "_r38_reference.rs")).write_bytes((a.stage / EXPERIMENTS / name).read_bytes())

owned = root / "r17_owned_weights.rs"
old_owned = owned.read_text()
old_xt = old_owned[old_owned.index("fn xt_at"):old_owned.index("\npub(super) fn chord", old_owned.index("fn xt_at"))]
new_xt = '''fn xt_at(read: impl Fn(usize) -> K, j: usize) -> K {
    assert!(j <= 1024);
    let mut bits = j.trailing_ones() as usize;
    let mut value = read(j + 1);
    while bits != 0 {
        bits -= 1;
        let row = j & !((1usize << (bits + 1)) - 1);
        value = value.add(read(row)).half();
    }
    value
}'''
owned.write_text(old_owned.replace(old_xt, new_xt, 1))
assert old_owned.count("fn xt_at") == 1

weighted = root / "r17_weighted_groups.rs"
old_weighted = weighted.read_text()
old_contract = old_weighted[old_weighted.index("fn contract"):old_weighted.index("\n    pub(super) fn prefix", old_weighted.index("fn contract"))]
new_contract = '''fn contract(&self,read:impl Fn(usize)->(K,K))->[K;4] {
        let mut out=[K::ZERO;4];
        for group in 0..4 {
            let mut left=[K::ZERO;4]; let mut right=[K::ZERO;4];
            for lane in 0..16 {
                let j=group*16+lane; let mut value=read(j).0;
                // Pure grouped-array read: index 64 and above are zero-extended.
                let carry=|r:usize|if r<64 {read(r).1}else{K::ZERO};
                let mut bits=j.trailing_ones() as usize; let mut nested=carry(j+1);
                while bits!=0 {bits-=1;let row=j&!((1usize<<(bits+1))-1);nested=nested.add(carry(row)).half();}
                value=value.add(nested);
                let slot=lane&3; left[slot]=self.high[lane]; right[slot]=value;
                if slot==3 {out[group]=out[group].add(qm31_sum_products4(left,right));}
            }
        }
        for value in &mut out {for _ in 0..8 {*value=value.half();}}
        out
    }'''
weighted.write_text(old_weighted.replace(old_contract, new_contract, 1))
assert old_weighted.count("fn contract") == 1

# Coordinate(1023) has only normal slot 15; all carry slots are absent.
text = weighted.read_text()
old_coord = '''pub(super) fn coordinate(&self,row:usize)->[K;4] {
        assert!(row<1024);
        self.contract(|j|if j==row/16 {
            (self.normal[row%16],if row%16<3 {self.carry[row%16]}else{K::ZERO})
        } else {(K::ZERO,K::ZERO)})
    }'''
new_coord = '''pub(super) fn coordinate(&self,row:usize)->[K;4] {
        assert!(row<1024);
        if row==1023 {
            let mut value=self.normal[15].mul(self.high[15]);
            for _ in 0..8 {value=value.half();}
            return [K::ZERO,K::ZERO,K::ZERO,value];
        }
        self.contract(|j|if j==row/16 {
            (self.normal[row%16],if row%16<3 {self.carry[row%16]}else{K::ZERO})
        } else {(K::ZERO,K::ZERO)})
    }'''
assert text.count(old_coord) == 1
weighted.write_text(text.replace(old_coord, new_coord, 1))

# Focused actual-source comparison binary: chord compares old/new xt_at on all
# 513/512/512 source reads; coordinate compares the old/new pivot result.
check = root / "r17_carry_shortcuts_check.rs"
check.write_text('''extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_owned_weights;
#[path="r17_owned_weights_r38_reference.rs"] mod r17_owned_weights_reference;
mod r17_weighted_groups;
#[path="r17_weighted_groups_r38_reference.rs"] mod r17_weighted_groups_reference;
use corelib::field::{CM31,M31,P,QM31 as K};
fn sample(n:u32)->K {K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}}
fn main(){
  for case in 0..80u32 { let w=(0..1024).map(|j|sample(case*1024+j)).collect::<Vec<_>>(); let abc=[sample(case+3),sample(case+7),sample(case+11)];
    assert_eq!(r17_owned_weights::chord(w.clone(),abc),r17_owned_weights_reference::chord(w,abc));
    let alpha=[sample(case+21),sample(case+27),sample(case+33),sample(case+39)];
    let a=r17_weighted_groups::Kernel::new(abc,alpha).coordinate(1023);
    let b=r17_weighted_groups_reference::Kernel::new(abc,alpha).coordinate(1023);
    assert_eq!(a,b);
  }
  println!("PASS: 80 actual-source chord carry/pivot controls; all 513/512/512 reads and coordinate(1023) match R38");
}
''')

# Append a focused host binary in the fresh output only.
manifest = root / "performance-host/Cargo.toml"
manifest.write_text(manifest.read_text() + '\n[[bin]]\nname="r17-carry-shortcuts-check"\npath="../r17_carry_shortcuts_check.rs"\n')

for name in ("r17_owned_weights.rs", "r17_weighted_groups.rs", "r17_carry_shortcuts_check.rs",
             "r17_owned_weights_r38_reference.rs", "r17_weighted_groups_r38_reference.rs"):
    control["files"][name] = sha(root / name)
control["carry_shortcuts"] = {
    "before": {"r17_owned_weights.rs": sha(a.stage / EXPERIMENTS / "r17_owned_weights.rs"),
               "r17_weighted_groups.rs": sha(a.stage / EXPERIMENTS / "r17_weighted_groups.rs")},
    "after": {"r17_owned_weights.rs": sha(root / "r17_owned_weights.rs"),
              "r17_weighted_groups.rs": sha(root / "r17_weighted_groups.rs")},
    "references": ["r17_owned_weights_r38_reference.rs", "r17_weighted_groups_r38_reference.rs"],
    "focused_binary": "r17-carry-shortcuts-check",
    "route": "pure-array nested carry reads, grouped index-64 zero extension, coordinate(1023) pivot normal[15]*high[15]/256",
    "source_boundary": "no protocol, mask, map, transcript, proof-premise, or non-pure callback change",
}
control["scope"] = "R41 approved pure-read carry nesting and pivot shortcut on R38 batched-dot source"
(a.output / "r17-compact-control.json").write_text(json.dumps(control, indent=2) + "\n")

probe_path = a.output / "r17-sbf-probe.json"
probe = json.loads(probe_path.read_text())
probe["carry_shortcuts"] = {
    name: {"before_sha256": sha(a.stage / EXPERIMENTS / name), "after_sha256": sha(root / name)}
    for name in ("r17_owned_weights.rs", "r17_weighted_groups.rs")
}
probe["carry_shortcuts_files"] = {
    name: sha(root / name)
    for name in ("r17_carry_shortcuts_check.rs", "r17_owned_weights_r38_reference.rs", "r17_weighted_groups_r38_reference.rs")
}
probe_path.write_text(json.dumps(probe, indent=2) + "\n")
