#!/usr/bin/env python3
"""Verify exact overlay bytes and the declared native-package cache boundary."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

task, cache = map(Path, sys.argv[1:3])
manifest_path = task / (sys.argv[3] if len(sys.argv) > 3 else "manifest.json")
manifest = json.loads(manifest_path.read_text())
for name, pin in manifest["packages"].items():
    package = cache / ".lake/packages" / name
    actual = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
    assert actual == pin, ("native package revision", name, actual, pin)
for entry in manifest["files"]:
    path = task / "overlay" / entry["overlay"]
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    assert h.hexdigest() == entry["sha256"], ("overlay hash", path)
print("OVERLAY_PROVENANCE_PASS=" + str(len(manifest["files"])))
print("NATIVE_PACKAGE_CACHE_BOUNDARY=pinned revisions; not a replay of package compilation")
