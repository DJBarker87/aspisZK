#!/usr/bin/env python3
"""Capture the exact read-only inputs supporting the focused stop."""
import hashlib
import json
import subprocess
from pathlib import Path

OUT = Path(__file__).resolve().parent
BASE = "61684cb2251381c897e112c85e48f092a82f5d31"
CANDIDATE = "d4ed1ba89f05a754d3982b9250f53acbd405ce7b"
manifest = []
(OUT / "inputs").mkdir(exist_ok=True)


def read(revision, path):
    return subprocess.check_output(["git", "show", f"{revision}:{path}"])


def save(name, revision, path, start=None, end=None):
    original = read(revision, path)
    content = original if start is None else b"".join(original.splitlines(keepends=True)[start-1:end])
    destination = OUT / "inputs" / name
    destination.write_bytes(content)
    manifest.append({"file": str(destination.relative_to(OUT)), "revision": revision,
                     "path": path, "lines_inclusive": None if start is None else [start, end],
                     "source_sha256": hashlib.sha256(original).hexdigest(),
                     "captured_sha256": hashlib.sha256(content).hexdigest()})


for name in ["host_sumcheck", "host_work"]:
    save(name + ".rs.txt", CANDIDATE, f"crates/aspis-r1-cost-probe/src/{name}.rs")
save("native_workers.rs.txt", CANDIDATE,
     "docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs")
save("op257.lean.txt", CANDIDATE,
     "docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean", 801, 803)
save("op257-abbrev.lean.txt", CANDIDATE,
     "docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean", 1070, 1070)
save("PV_Canon_Deployment.lean.txt", BASE,
     "docs/research/v8-r0-zk-20261009/lean/R1Z/PV_Canon_Deployment.lean")

report_path = "evidence/pv-rows10-20261029/REPORT.md"
report = read(CANDIDATE, report_path).decode()
lines = report.splitlines()
start = next(i for i, line in enumerate(lines, 1) if line.startswith("## V263"))
end = next(i for i, line in enumerate(lines, 1) if line.startswith("## V404")) - 1
save("V263-prior-report.md", CANDIDATE, report_path, start, end)
save("V220-prior-report.md", CANDIDATE, "evidence/pv-rdcd4-20261029/rows/V220.md")

basis = {}
for n in [11, 10, 9]:
    path = f"evidence/privacy-recount-20261026/recount{n}/rows{n}.json"
    rows = json.loads(read(BASE, path))
    basis[f"recount{n}/V403"] = next(row for row in rows if row["id"] == "V403")
    if n == 11:
        basis["recount11/V263"] = next(row for row in rows if row["id"] == "V263")
(OUT / "basis.json").write_text(json.dumps(basis, indent=2) + "\n")
(OUT / "input-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"captured_files": len(manifest), "basis_rows": len(basis)}))
