#!/usr/bin/env python3
import hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
M = json.loads((ROOT / "manifest.json").read_text())
assert M["schema"] == "focused-extractor-proof-packet-v1"
assert M["packet"] == ROOT.name

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

for item in M["files"]:
    p = ROOT / item["path"]
    assert p.is_file(), f"missing packet file: {item['path']}"
    assert p.stat().st_size == item["size_bytes"], f"size mismatch: {item['path']}"
    assert sha(p) == item["sha256"], f"hash mismatch: {item['path']}"

mod = M["modules"][0]
src = ROOT / mod["source"]
obj = Path(mod["object_external_path"])
assert sha(src) == mod["source_sha256"]
assert obj.is_file() and sha(obj) == mod["object_sha256"]
assert mod["exit_status"] == 0
assert mod["source_revision_at_launch"] is None
assert mod["axioms"] == ["propext", "Classical.choice", "Quot.sound"]
assert M["launch"]["repository_head_at_launch"] == "NOT_CAPTURED"
assert M["selected_profile"]["sha256"] == sha(ROOT / M["selected_profile"]["path_file"])
pins = json.loads((ROOT / "evidence/direct-import-pins.json").read_text())
assert pins == M["direct_import_object_pins"]
for name, pin in pins.items():
    p = Path(pin["selected_object_path"])
    assert p.is_file(), f"missing selected direct import object: {name}"
    assert sha(p) == pin["selected_object_sha256"], f"selected direct object changed: {name}"
    if "retained_source" in pin:
        sp = ROOT / pin["retained_source"]
        assert sp.is_file() and sha(sp) == pin["source_sha256"], f"retained source mismatch: {name}"
assert not list(ROOT.rglob("*.olean")), "compiled Lean objects must remain external to packet"
log = (ROOT / "evidence/lean.log").read_text()
assert "sorryAx" not in log
assert "literal_field_result_concrete_width29' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
assert (ROOT / "diagnostics/rejected-head-proof.md").is_file()
assert (ROOT / "diagnostics/rejected-module-name-cycle.md").is_file()
print("PASS", M["packet"])
