from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
m=json.loads((r/"source-identities.json").read_text())
for rel,h in m["files"].items():assert hashlib.sha256((r/rel).read_bytes()).hexdigest()==h,rel
assert "circle::secure_ood_circle_point_from_parameter(parameter)" in (r/"input/src/lib.rs").read_text()
print("PASS frozen current circle kit hashes; actual callee, no opaque/source-body substitution")
