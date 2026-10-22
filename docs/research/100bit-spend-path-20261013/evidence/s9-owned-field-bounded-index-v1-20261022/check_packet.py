#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((root / "manifest.json").read_text())
assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["compiled_objects_included"] is False
assert len(manifest["entries"]) == 1

def check_compile(entry, base, expected_target=None):
    receipt = json.loads((base / entry["receipt"]).read_text())
    preflight = json.loads((base / entry["preflight"]).read_text()) if "preflight" in entry else None
    command = json.loads((base / entry["command"]).read_text())
    log = (base / entry["log"]).read_text()
    source = base / entry["source"]
    assert receipt["exit_status"] == 0 and receipt["process_swaps"] == 0
    assert receipt["watchdog_abort"] is None and receipt["foreign_lean_samples"] == []
    assert sha(source) == entry["source_sha256"] == receipt["source_sha256"]
    assert receipt["object_sha256"] == entry["object_sha256"]
    if expected_target:
        assert receipt["mutex_owner"]["target"] == expected_target
    if preflight:
        assert receipt == entry["launch_metrics"]
        assert preflight["source_revision"] == receipt["source_revision_at_launch"]
        assert preflight["source_sha256"] == receipt["source_sha256"]
        assert preflight["no_dependency_builds"] is True
        assert preflight["direct_imports"] == entry["direct_imports"]
        assert preflight["controller_sha256"] == receipt["controller_sha256"]
        assert "LEAN_PATH=" + (base / entry["profile"]).read_text().strip() in command["argv"]
        assert "-j1" in command["argv"] and command["argv"][command["argv"].index("-M") + 1] == "4400"
        for pin in entry["direct_imports"].values():
            p = Path(pin["path"])
            assert p.is_file() and sha(p) == pin["sha256"]
    uncommented = re.sub(r"/\-.*?\-/", "", source.read_text(), flags=re.S)
    uncommented = re.sub(r"--[^\n]*", "", uncommented)
    assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", uncommented)
    assert not re.search(r"set_option\s+(max|.*Heartbeats|.*RecDepth)", uncommented)
    for name, axioms in entry["theorems"].items():
        reports = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
        assert len(reports) == 1, (name, len(reports))
        got = set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", reports[0]))
        assert got == set(axioms) and got <= {"propext", "Classical.choice", "Quot.sound"}
    return receipt

main = manifest["entries"][0]
main_base = root
main_receipt = check_compile(main, main_base, "S9OwnedFieldBoundedIndexV2")
dep = manifest["reused_dependencies"][0]
dep_receipt = json.loads((root / dep["receipt"]).read_text())
dep_log = (root / dep["log"]).read_text()
dep_source = root / dep["source"]
assert dep_receipt["exit_status"] == 0 and dep_receipt["process_swaps"] == 0
assert dep_receipt["watchdog_abort"] is None and dep_receipt["foreign_lean_samples"] == []
assert dep_receipt["source_sha256"] == dep["source_sha256"] == sha(dep_source)
assert dep_receipt["object_sha256"] == dep["object_sha256"]
for name, axioms in dep["theorems"].items():
    reports = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", dep_log, re.S)
    assert len(reports) == 1
    got = set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", reports[0]))
    assert got == set(axioms) and got <= {"propext", "Classical.choice", "Quot.sound"}

reader = root.parent / "s9-owned-field-reader-readback-v1-20261022"
subprocess.run([sys.executable, "-B", str(reader / "check_packet.py")], check=True, capture_output=True, text=True)
reader_entry = json.loads((reader / "manifest.json").read_text())["entries"][0]
assert main["direct_imports"]["S9OwnedFieldReaderReadbackV1"]["sha256"] == reader_entry["object_sha256"]
assert main["direct_imports"]["AspisV8R19.R152WrappingBounds"]["sha256"] == dep["object_sha256"]

for ext in ("*.olean", "*.elf", "*.so", "*.pyc"):
    assert not list(root.rglob(ext))
for line in (root / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    assert sha(root / rel) == digest, rel
print("PASS: bounded offset bridge, R152 reuse, selected reader import, standard axioms, no compiled artifacts")
