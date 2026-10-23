import hashlib, json
from pathlib import Path
root = Path(__file__).resolve().parent
manifest = json.loads((root / "manifest.json").read_text())
assert manifest["schema"] == "focused-extractor-proof-packet-v1"
assert manifest["compiled_objects_included"] is False
for target in manifest["targets"]:
    assert target["exit_status"] == 0 and target["process_swaps"] == 0
for item in manifest["files"]:
    path = root / item["path"]
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == item["sha256"]
    assert len(data) == item["bytes"]
for path in root.rglob("*"):
    if path.is_file():
        assert path.suffix not in {".olean", ".ilean", ".ir", ".llbc", ".so", ".dylib", ".dll"}
log = (root / "proof/lean.log").read_text()
assert "sorryAx" not in log and "error:" not in log
for ax in ["propext", "Classical.choice", "Quot.sound"]:
    assert ax in log
print("PASS: source-only focused proof packet")
