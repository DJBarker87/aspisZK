#!/usr/bin/env python3
"""Check the isolated S9 helper rewrite against its exact admitted base blob."""
from hashlib import sha256
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "source-pins/weights.original.rs"
CAND = ROOT / "candidate/src/weights.rs"
BASE_SHA = "28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137"
OLD = '''    for side in 0..2 {
        let q=kpowers::<4>(extra[side]);
        let q4=q[2].square();let q8=q4.square();let q12=q8.mul(q4);let q16=q8.square();
        let low=Weights::scalar_factor(&q,ap0);
        let high_powers=[K::ONE,q4,q8,q12];
        let terms:[E;4]=core::array::from_fn(|r|ap1[PERM[r]].mul_qm31(high_powers[r]).mul_m31(QUARTER));
'''
NEW = '''    for side in 0..2 {
        let q0=K::ONE;
        let q1=q0.mul(extra[side]);
        let q2=q1.mul(extra[side]);
        let q3=q2.mul(extra[side]);
        let _q4=q3.mul(extra[side]);
        let q=[q0,q1,q2,q3];
        let q4=q[2].square();let q8=q4.square();let q12=q8.mul(q4);let q16=q8.square();
        let low=Weights::scalar_factor(&q,ap0);
        let high_powers=[K::ONE,q4,q8,q12];
        let term0=ap1[PERM[0]].mul_qm31(high_powers[0]).mul_m31(QUARTER);
        let term1=ap1[PERM[1]].mul_qm31(high_powers[1]).mul_m31(QUARTER);
        let term2=ap1[PERM[2]].mul_qm31(high_powers[2]).mul_m31(QUARTER);
        let term3=ap1[PERM[3]].mul_qm31(high_powers[3]).mul_m31(QUARTER);
        let terms=[term0,term1,term2,term3];
'''

base = BASE.read_bytes()
cand = CAND.read_bytes()
if sha256(base).hexdigest() != BASE_SHA:
    sys.exit("FAIL: frozen weights.rs base hash mismatch")
text = base.decode()
if text.count(OLD) != 1:
    sys.exit("FAIL: expected original helper block exactly once")
expected = text.replace(OLD, NEW, 1).encode()
if cand != expected:
    sys.exit("FAIL: candidate differs outside the one approved helper block")
if b"core::array::from_fn" in NEW.encode() or b"kpowers::<4>" in NEW.encode():
    sys.exit("FAIL: candidate replacement still uses a targeted from_fn path")
# Keep the source target narrow: exact one helper, unchanged call inventory.
if text.count("factored_s2_libra_weights(") != 3:
    sys.exit("FAIL: unexpected base helper call inventory")
if text.count("factored_s2_libra_weights(") != text.replace(OLD, NEW, 1).count("factored_s2_libra_weights("):
    sys.exit("FAIL: helper call inventory changed")
print("PASS: candidate is exactly the approved local helper rewrite")
print(f"base_sha256={BASE_SHA}")
print(f"candidate_sha256={sha256(cand).hexdigest()}")
print("changed_function=factored_s2_libra_weights only")
print("targeted_from_fn_and_kpowers4_absent_in_replacement=true")
print("call_inventory_unchanged=true")
