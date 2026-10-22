from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent;p=json.loads((R/"source-identities.json").read_text());sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
for rel,v in p["cut_files"].items(): assert sha(R/rel)==v["sha256"],rel
for rel,v in [("source-snapshots/field.rs",p["actual_core_field"]),("source-snapshots/wide_exact.rs",p["actual_core_wide_exact"]),("source-snapshots/weights-candidate.rs",p["candidate_weights"]),("source-snapshots/weights-frozen.rs",p["frozen_weights"]),("source-snapshots/transport.rs",p["variant_source"])]: assert sha(R/rel)==v["sha256"],rel
assert (R/"input/src/field.rs").read_bytes()==(R/"source-snapshots/field.rs").read_bytes()
assert (R/"input/src/field/wide_exact.rs").read_bytes()==(R/"source-snapshots/wide_exact.rs").read_bytes()
assert "pub fn mul(self, rhs: Self) -> Self" in (R/"input/src/field/wide_exact.rs").read_text()
assert "pub fn focused_wide_exact_mul" in (R/"input/src/lib.rs").read_text()
assert p["transparent_target"]["body_sha256"]==p["opaque_arithmetic_bodies"]["WideExact.mul"]["method_body_sha256"]
print("WideExact.mul sourcecut and exact unchanged field-source pins: PASS")
