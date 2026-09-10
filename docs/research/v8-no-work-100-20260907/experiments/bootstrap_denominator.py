#!/usr/bin/env python3
"""Emit a fresh 2f6d82fe import manifest after checking frozen sources and outputs.

Metadata-only: no compiler, network operation or filesystem mutation. The
coordinator installs stdout in a new isolated NUC scope via an explicit patch.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

EX = Path(__file__).resolve().parent
PARENT = "2f6d82fef294410367aa1781fb924af7c38deab9"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
ORIGIN = "6f1ebbe55fcc6fd008071329d5270aae0521cf9a"
REPO = Path(subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip())


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


oldpath, greenpath, receiptpath = map(Path, sys.argv[1:])
receipt = json.loads(receiptpath.read_text())
assert receipt["research"] == ORIGIN and not receipt["unmapped_artifacts"]
old, green = json.loads(oldpath.read_text()), json.loads(greenpath.read_text())
assert old["research"] == ORIGIN
entries = {entry["overlay"]: dict(entry) for entry in old["files"]}
assert len(entries) == len(old["files"])
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
# Carry exact retained source fallbacks, never read a drifted main pathname.
fallbacks = []
for entry in entries.values():
    candidates = [item for item in receipt["artifacts"]
        if item["remote_path"].endswith("/overlay/" + entry["overlay"])
        and item["sha256"] == entry["sha256"]
        and item["local_path"].endswith(".lean.pinned")]
    if candidates:
        assert entry["kind"] == "source" and len(candidates) == 1
        retained = (receiptpath.parent / candidates[0]["local_path"]).resolve()
        assert digest(retained) == entry["sha256"]
        fallbacks.append({"module": entry["module"], "previous_local": entry["local"],
                          "retained_local": str(retained), "sha256": entry["sha256"]})
        entry["local"] = str(retained)
    elif entry.get("local") and entry["local"].endswith(".lean.pinned"):
        retained = Path(entry["local"]).resolve()
        assert entry["kind"] == "source" and digest(retained) == entry["sha256"]
        fallbacks.append({"module": entry["module"], "previous_local": entry["local"],
                          "retained_local": str(retained), "sha256": entry["sha256"]})
sources, outputs = 0, 0
for entry in entries.values():
    if not entry.get("local"):
        entry["local"] = str(EX / entry["overlay"])
    if entry["category"] == "new_checked":
        entry["category"] = "research"
    if entry["kind"] != "source":
        assert digest(Path(entry["local"])) == entry["sha256"], ("compiled cache", entry["module"])
        outputs += 1
        continue
    borrowed = entry["module"].startswith("AspisFormal.")
    revision = BORROWED if borrowed else PARENT
    relative = ("AspisFormal/" + entry["overlay"] if borrowed else
                "docs/research/v8-no-work-100-20260907/experiments/" + entry["overlay"])
    pinned = subprocess.check_output(["git", "-C", str(REPO), "show", revision + ":" + relative])
    assert hashlib.sha256(pinned).hexdigest() == entry["sha256"], ("pinned source", entry["module"], revision)
    assert digest(Path(entry["local"])) == entry["sha256"], ("local pinned source", entry["module"])
    sources += 1
manifest = dict(old)
manifest.update(research=PARENT, borrowed=BORROWED, pending_no_olean=[], targets=[],
    files=list(entries.values()),
    counts={"pinned_source_blobs": sources, "compiled_artifacts": outputs},
    origin={"research": old["research"], "manifest_sha256": digest(oldpath),
            "green_outputs_sha256": digest(greenpath), "manifest_name": oldpath.name,
            "receipt_name": receiptpath.name, "receipt_sha256": digest(receiptpath),
            "retained_source_fallbacks": fallbacks,
            "prior_origin": old["origin"]},
    bootstrap={"source_sha256": digest(Path(__file__).resolve()),
        "scope": "Exact source/blob and compiled-byte validation; inherited source-to-olean evidence and pinned native package cache, not a compilation replay."})
print(json.dumps(manifest, indent=2))
