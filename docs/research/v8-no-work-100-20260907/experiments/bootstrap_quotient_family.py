#!/usr/bin/env python3
"""Validate the preceding frozen import closure at the new research revision.

Metadata-only: no compiler, cache mutation, field enumeration or remote write.
The emitted manifest is then installed in a fresh isolated NUC directory.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

EX = Path(__file__).resolve().parent
REPO = Path(subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip())
PARENT = "bc23dfeb647320c4fbf09012cd92da1a6a5fa95a"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

oldpath, greenpath, output = map(Path, sys.argv[1:])
assert not output.exists()
old = json.loads(oldpath.read_text())
green = json.loads(greenpath.read_text())
entries = {entry["overlay"]: entry for entry in old["files"]}
for module, checked in green.items():
    assert entries[module + ".lean"]["sha256"] == checked["source"], module
    for suffix, expected in checked["outputs"].items():
        path = EX / (module + suffix)
        assert digest(path) == expected, ("green local output", module, suffix)
        name = module + suffix
        if name in entries:
            assert entries[name]["sha256"] == expected, ("green prior manifest", module, suffix)
        else:
            entries[name] = {"module": module, "category": "research", "kind": suffix[1:],
                "local": str(path), "overlay": name, "remote_cache": None,
                "sha256": expected, "bytes": path.stat().st_size}
for entry in entries.values():
    if entry["kind"] != "source":
        path = Path(entry["local"]) if entry.get("local") else EX / entry["overlay"]
        assert digest(path) == entry["sha256"], ("retained import bytes", entry["module"])
        continue
    borrowed = entry["module"].startswith("AspisFormal.")
    revision = BORROWED if borrowed else PARENT
    relative = ("AspisFormal/" + entry["overlay"] if borrowed else
                "docs/research/v8-no-work-100-20260907/experiments/" + entry["overlay"])
    pinned = subprocess.check_output(["git", "-C", str(REPO), "show", revision + ":" + relative])
    assert hashlib.sha256(pinned).hexdigest() == entry["sha256"], ("pinned source", entry["module"], revision)
manifest = dict(old)
manifest.update(research=PARENT, borrowed=BORROWED, pending_no_olean=[],
                files=list(entries.values()), targets=["QuotientFamilyCore", "QuotientFamilySelected"],
                origin={"research": old["research"], "manifest_sha256": digest(oldpath),
                        "green_outputs_sha256": digest(greenpath), "manifest_name": oldpath.name})
output.write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"status": "PINNED_CLOSURE_PASS", "entries": len(entries),
                  "manifest": str(output), "sha256": digest(output), "parent": PARENT}))
