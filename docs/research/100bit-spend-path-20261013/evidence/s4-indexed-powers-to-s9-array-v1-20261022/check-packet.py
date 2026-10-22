#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
receipt = json.loads((HERE / "receipts/receipt.json").read_text())
profile = json.loads((HERE / "receipts/profile-manifest.json").read_text())
source = HERE / "sources/S4IndexedPowersToS9ArrayV1.lean"
assert receipt["exit_status"] == 0
assert receipt["source_sha256"] == sha(source.read_bytes())
assert receipt["object_sha256"] == "fca727e2107d5bc41b131f54c04fe1e02c7dbab1329c0c826928ca0439353b27"
assert receipt["wall_seconds"] == 19.856
assert receipt["process_swaps"] == 0
assert receipt["peak_aggregate_rss_bytes"] == 3207970816
assert profile["source_sha256"] == receipt["source_sha256"]
assert profile["profile_sha256"] == sha((HERE / "receipts/full-LEAN_PATH.txt").read_bytes())
assert profile["profile_entries"] == 447
assert sha((HERE / "source-pins/weights.rs").read_bytes()) == "28b558ffa9f5b004188c7f50b1597fe681186f54fb4d52a3bd125df4f2481137"
assert json.loads((HERE / "receipts/source-binding-check.json").read_text())["status"] == "PASS"
assert "depends on axioms: [propext," in (HERE / "receipts/lean.log").read_text()
assert "Classical.choice" in (HERE / "receipts/lean.log").read_text()
subprocess.run(["python3", str(HERE / "check-source-binding.py")], check=True, capture_output=True)
for p in HERE.rglob("*"):
    if p.is_file():
        assert p.suffix.lower() not in {".olean", ".ilean", ".so", ".dylib", ".dll", ".a", ".o", ".elf"}, p
print(json.dumps({"status": "PASS", "source_sha256": receipt["source_sha256"],
                  "object_sha256_metadata_only": receipt["object_sha256"],
                  "profile_sha256": profile["profile_sha256"],
                  "compiled_objects_in_packet": 0}, indent=2))
