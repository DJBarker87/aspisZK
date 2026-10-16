#!/usr/bin/env python3
"""Reuse checked 4.32 backend; check only two candidate emissions and their audit."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
root = Path(sys.argv[1]).resolve()
work = root / "lean"
port = Path("/home/dombarker/project-offloads/aspis-r1-j17-port-20261015")
backend = json.loads((port / "backend-final-manifest.json").read_text())
for name, digest in backend["source_sha256"].items():
    assert sha(port / "backend" / name) == digest, name
pins = {}
for receipt in sorted((port / "successful-targets").glob("*.json")):
    d = json.loads(receipt.read_text())
    assert d["exit_status"] == 0
    source = port / "backend" / (d["target"].replace(".", "/") + ".lean")
    obj = port / "backend/.lake/build/lib/lean" / (d["target"].replace(".", "/") + ".olean")
    assert sha(source) == d["key"]["source"] and sha(obj) == d["olean_sha256"]
    pins[d["target"]] = {"source_path": str(source), "source_sha256": sha(source), "object_path": str(obj),
                         "object_sha256": sha(obj), "green_receipt_path": str(receipt), "green_receipt_sha256": sha(receipt)}
assert len(pins) == 237, len(pins)
(work / "backend-object-pins.json").write_text(json.dumps(pins, indent=2) + "\n")
for name in ["backend-final-manifest.json", "dependency-cache-pins.json"]:
    shutil.copy2(port / name, work / name)
sources = {str(p.relative_to(work / "sources")): sha(p) for p in sorted((work / "sources").rglob("*.lean"))}
for name in ["Types.lean", "Funs.lean"]:
    assert sources["AspisR1DigestInterfaceCandidate/" + name] == sha(root / "runs/candidate-b/generated/AspisR1DigestInterfaceCandidate" / name)
manifest = {"classification": "CANDIDATE only; no production adoption or source/effect preservation claim",
            "original_source_revision": "b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c",
            "candidate_source_sha256": sha(root / "runs/candidate-b/candidate-source/lib.rs"),
            "backend_source_manifest_sha256": sha(work / "backend-final-manifest.json"),
            "backend_object_pins_sha256": sha(work / "backend-object-pins.json"),
            "dependency_cache_pins_sha256": sha(work / "dependency-cache-pins.json"),
            "new_sources": sources, "new_import_objects": {}, "dependency_rebuild": False}
targets = [("types-a", "AspisR1DigestInterfaceCandidate.Types"),
           ("funs-a", "AspisR1DigestInterfaceCandidate.Funs"), ("axioms-a", "DigestCandidateAxioms")]
for attempt, module in targets:
    for name, digest in sources.items():
        assert sha(work / "sources" / name) == digest
    manifest["new_import_objects"] = {str(p.relative_to(work / "objects")): sha(p) for p in sorted((work / "objects").rglob("*.olean"))}
    data = json.dumps(manifest, indent=2) + "\n"
    (work / "input-manifest.json").write_text(data)
    (work / ("input-manifest-" + attempt + ".json")).write_text(data)
    result = subprocess.run(["python3", str(root / "kit/run-lean-host.py"), str(work), module,
                             "--attempt", attempt, "--revision", "candidate-only:" + manifest["candidate_source_sha256"],
                             "--lean-memory-mib", "0"])
    assert result.returncode == 0, (attempt, result.returncode)
    receipt = json.loads((work / "runs" / attempt / "receipt.json").read_text())
    assert receipt["exit_status"] == 0 and receipt["process_swaps"] == 0 and receipt["cgroup_swap_current"] == "0"
    if attempt == "axioms-a":
        log = (work / "runs" / attempt / "lean.log").read_text()
        reports = re.findall(r"depends on axioms: \[(.*?)\]", log, re.S)
        clean = re.findall(r"does not depend on any axioms", log)
        assert len(reports) + len(clean) == 2, log
        for report in reports:
            assert set(filter(None, (x.strip() for x in report.split(",")))) <= {"propext", "Classical.choice", "Quot.sound"}, report
print("PASS: two candidate generated modules + two-export standard-axiom audit; no proof of production correspondence")
