from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
p=json.loads((R/"source-identities.json").read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
for rel,v in p["cut_files"].items(): assert sha(R/rel)==v["sha256"],rel
for rel,v in [("source-snapshots/field.rs",p["actual_core_field"]),("source-snapshots/wide_exact.rs",p["actual_core_wide_exact"]),("source-snapshots/weights-candidate.rs",p["candidate_weights"]),("source-snapshots/weights-frozen.rs",p["frozen_weights"]),("source-snapshots/transport.rs",p["variant_source"])]: assert sha(R/rel)==v["sha256"],rel
wide=(R/"input/src/field/wide_exact.rs").read_text(); field=(R/"input/src/field.rs").read_text()
body=p["opaque_arithmetic_bodies"]["WideExact.mul_m31"]["method_text"]
assert body in wide and hashlib.sha256(body.encode()).hexdigest()==p["opaque_arithmetic_bodies"]["WideExact.mul_m31"]["method_body_sha256"]
assert "pub fn mul(self, rhs: M31) -> M31" in field
assert "pub fn mul_m31(self, rhs: M31) -> QM31" in field
assert (R/"input/Cargo.toml").read_text()==(R/"source-snapshots/../input/Cargo.toml").read_text()
print("sourcecut/preselector checks: PASS")
