#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, subprocess, sys

root = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m = json.loads((root / "manifest.json").read_text())
assert m["schema"] == "focused-extractor-proof-packet-v1"
assert m["compiled_objects_included"] is False and len(m["entries"]) == 1
e = m["entries"][0]
base = root
r = json.loads((base / e["receipt"]).read_text())
pre = json.loads((base / e["preflight"]).read_text())
cmd = json.loads((base / e["command"]).read_text())
log = (base / e["log"]).read_text()
src = base / e["source"]
assert r == e["launch_metrics"] and r["exit_status"] == 0 and r["process_swaps"] == 0
assert r["watchdog_abort"] is None and r["foreign_lean_samples"] == []
assert sha(src) == e["source_sha256"] == r["source_sha256"] == pre["source_sha256"]
assert r["object_sha256"] == e["object_sha256"]
assert pre["source_revision"] == r["source_revision_at_launch"]
assert pre["no_dependency_builds"] is True and pre["direct_imports"] == e["direct_imports"]
assert pre["controller_sha256"] == r["controller_sha256"]
assert "LEAN_PATH=" + (base / e["profile"]).read_text().strip() in cmd["argv"]
assert "-j1" in cmd["argv"] and cmd["argv"][cmd["argv"].index("-M") + 1] == "4400"
for pin in e["direct_imports"].values():
    p = Path(pin["path"])
    assert p.is_file() and sha(p) == pin["sha256"]
for name, axioms in e["theorems"].items():
    reports = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", log, re.S)
    assert len(reports) == 1
    got = set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", reports[0]))
    assert got == set(axioms) and got <= {"propext", "Classical.choice", "Quot.sound"}
uncommented = re.sub(r"/\-.*?\-/", "", src.read_text(), flags=re.S)
uncommented = re.sub(r"--[^\n]*", "", uncommented)
assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b", uncommented)
assert not re.search(r"set_option\s+(max|.*Heartbeats|.*RecDepth)", uncommented)

for dep in m["reused_dependencies"]:
    packet = (root / dep["packet"]).resolve().parent
    subprocess.run([sys.executable, "-B", str(packet / "check_packet.py")], check=True,
                   capture_output=True, text=True)
    dm = json.loads((packet / "manifest.json").read_text())
    entries = dm["entries"]
    if isinstance(entries, list):
        found = [x for x in entries if x.get("module") == dep["module"]]
        assert found and found[0]["object_sha256"] == dep["object_sha256"]
    else:
        assert any(x.get("object_sha256") == dep["object_sha256"] for x in entries.values())

owners_meta = m["selected_v8_owners"]
owners_path = root / owners_meta["file"]
assert sha(owners_path) == owners_meta["sha256"]
owners = json.loads(owners_path.read_text())
assert len(owners) == owners_meta["modules"] == 66
for item in owners.values():
    p = Path(item["path"])
    assert p.is_file() and sha(p) == item["sha256"]

failed = m["failed_attempts"][0]
fr = json.loads((root / failed["receipt"]).read_text())
assert fr["exit_status"] == 1 and fr["object_sha256"] is None
assert "R152WrappingBounds.olean" in (root / failed["log"]).read_text()

for ext in ("*.olean", "*.elf", "*.so", "*.pyc"):
    assert not list(root.rglob(ext))
for line in (root / "SHA256SUMS").read_text().splitlines():
    digest, rel = line.split("  ", 1)
    assert sha(root / rel) == digest, rel
print("PASS: projection body bound, actual owned-reader mapping, linked bounded bridge, closure pins, standard axioms, no compiled artifacts")
