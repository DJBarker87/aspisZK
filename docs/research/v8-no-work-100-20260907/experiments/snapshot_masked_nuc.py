#!/usr/bin/env python3
"""Freeze each run's imports, including outputs newly checked in this overlay."""
import hashlib
import json
from pathlib import Path
import sys

task, mode, target, tag = Path(sys.argv[1]), *sys.argv[2:]
state_path = task / "green-outputs.json"
state = json.loads(state_path.read_text()) if state_path.exists() else {}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

if mode == "record":
    assert target not in state, "A green target is immutable in this run directory"
    state[target] = {"source": sha(task / "overlay" / (target + ".lean")),
                     "outputs": {}}
    for suffix in (".olean", ".olean.private", ".olean.server"):
        path = task / "overlay" / (target + suffix)
        if path.exists():
            state[target]["outputs"][suffix] = sha(path)
    assert ".olean" in state[target]["outputs"]
    state_path.write_text(json.dumps(state, indent=2) + "\n")
else:
    assert mode == "snapshot"
    manifest = json.loads((task / "manifest.json").read_text())
    for entry in manifest["files"]:
        module = entry["module"]
        if module in manifest["pending_no_olean"] and entry["kind"] == "source":
            path = task / "overlay" / entry["overlay"]
            digest = sha(path)
            if module in state:
                assert digest == state[module]["source"], ("green source changed", module)
            entry["sha256"] = digest
            entry["bytes"] = path.stat().st_size
    for module, checked in state.items():
        for suffix, digest in checked["outputs"].items():
            path = task / "overlay" / (module + suffix)
            assert sha(path) == digest, ("green output changed", module)
            manifest["files"].append({"module": module, "category": "new_checked",
                "kind": suffix[1:], "local": None, "overlay": module + suffix,
                "remote_cache": None, "sha256": digest, "bytes": path.stat().st_size})
    known_sources = {entry["module"] for entry in manifest["files"] if entry["kind"] == "source"}
    for module in sorted(set(state) | {target}):
        if module not in known_sources:
            path = task / "overlay" / (module + ".lean")
            digest = sha(path)
            if module in state:
                assert digest == state[module]["source"], ("new green source changed", module)
            manifest["files"].append({"module": module, "category": "new_checked",
                "kind": "source", "local": None, "overlay": module + ".lean",
                "remote_cache": None, "sha256": digest, "bytes": path.stat().st_size})
    output = task / (tag + "-manifest.json")
    assert not output.exists()
    output.write_text(json.dumps(manifest, indent=2) + "\n")
