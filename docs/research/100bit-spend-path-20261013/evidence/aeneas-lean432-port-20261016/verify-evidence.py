#!/usr/bin/env python3
"""Check archived pins and patch reconstruction; never invoke Lean."""
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


manifest = json.loads((ROOT / "backend-final-manifest.json").read_text())
pins = json.loads((ROOT / "sha256.json").read_text())
for name, digest in pins.items():
    assert sha((ROOT / name).read_bytes()) == digest, name
with tempfile.TemporaryDirectory(prefix="j1-r17-evidence-") as tmp:
    with tarfile.open(ROOT / "original-source.tar.gz", "r:gz") as archive:
        archive.extractall(tmp, filter="data")
    backend = Path(tmp) / "backends/lean"
    for name, digest in manifest["original_source_sha256"].items():
        assert sha((backend / name).read_bytes()) == digest, name
    subprocess.run(["git", "apply", "--check", str(ROOT / "aeneas-lean432.patch")],
                   cwd=backend, check=True)
    subprocess.run(["git", "apply", str(ROOT / "aeneas-lean432.patch")],
                   cwd=backend, check=True)
    for name, digest in manifest["source_sha256"].items():
        assert sha((backend / name).read_bytes()) == digest, name

with tarfile.open(ROOT / "runs-and-receipts.tar.gz", "r:gz") as archive:
    data = {m.name: archive.extractfile(m).read() for m in archive.getmembers() if m.isfile()}
receipts = {Path(name).stem: json.loads(blob) for name, blob in data.items()
            if name.startswith("backend-successful-targets/")}
assert len(receipts) == 237
for name, receipt in receipts.items():
    assert receipt["exit_status"] == 0, name
    assert receipt["key"]["source"] == manifest["source_sha256"][name.replace(".", "/") + ".lean"], name
    for dep, digest in receipt["key"]["imports"].items():
        assert receipts[dep]["olean_sha256"] == digest, (name, dep)
    assert receipt["process_swaps"] == 0 and receipt["cgroup_swap_current"] == "0", name
    assert all(line.endswith(" 0") for line in receipt["memory_events_after"].splitlines()), name
final = json.loads(data["backend-runs/roots-port-f/preflight.json"])
assert set(final["ordered_modules"]) == set(receipts)
assert json.loads(data["backend-runs/roots-port-f/complete.json"])["exit_status"] == 0
failed = [json.loads(blob) for name, blob in data.items()
          if name.startswith("backend-runs/") and name.endswith("/receipt.json")
          and json.loads(blob)["exit_status"] != 0]
assert len(failed) == 10
print("PASS: 241 original/patched input pins, 237 green source/import receipt pins, 10 retained failures; no Lean run")
