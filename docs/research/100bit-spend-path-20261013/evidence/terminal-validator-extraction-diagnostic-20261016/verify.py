#!/usr/bin/env python3
"""Check diagnostic integrity. Does not accept external axioms or prove refinement."""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import tarfile

here = Path(__file__).resolve().parent
root = next(p for p in here.parents if (p / ".git").exists())
summary = json.loads((here / "SUMMARY.json").read_text())
digest = lambda raw: hashlib.sha256(raw).hexdigest()
archive = here / "terminal-diagnostic.tar.gz"
assert digest(archive.read_bytes()) == summary["archive_sha256"]
with tarfile.open(archive) as t:
    entries = json.loads((here / "archive-members.json").read_text())
    assert {m.name for m in t.getmembers() if m.isfile()} == {x["path"] for x in entries}
    for entry in entries:
        raw = t.extractfile(entry["path"]).read()
        assert len(raw) == entry["bytes"] and digest(raw) == entry["sha256"]
    pins = json.load(t.extractfile("input/source-pins.json"))
    source = subprocess.run(["git", "archive", pins["source_revision"], "--",
                             *pins["kit_files"]], cwd=root, capture_output=True, check=True)
    with tarfile.open(fileobj=io.BytesIO(source.stdout)) as s:
        for path, sha in pins["kit_files"].items():
            assert digest(s.extractfile(path).read()) == sha
    original = json.load(t.extractfile("extraction-a/TerminalValidator.llbc"))
    updated = json.load(t.extractfile("extraction-a/TerminalValidatorNamed.llbc"))
    report = json.load(t.extractfile("extraction-a/rename-report.json"))
    assert report == summary["rename_report"] and len(report["changes"]) == 2
    assert digest((root / "tools/j1-rename-enum-constructors.py").read_bytes()) == report["adapter_sha256"]
    for change in report["changes"]:
        field = updated["translated"]["fun_decls"][change["function_index"]]["item_meta"]["attr_info"]
        assert field["rename"] == change["new_rename"]
        field["rename"] = change["old_rename"]
    assert updated == original
    translation = json.load(t.extractfile("extraction-a/generated-named/translation.json"))
    opaque = [x for x in translation["functions"] if x.get("is_opaque")]
    assert len(opaque) == 11 and opaque == summary["opaque_functions"]
    for label, expected in [("charon-a", 0), ("aeneas-a", 2), ("aeneas-b", 0)]:
        receipt = json.load(t.extractfile(f"runs/{label}/receipt.json"))
        assert receipt == summary["runs"][label]
        assert receipt["exit_status"] == expected and receipt["swaps"] == 0
        assert receipt["limits"] == {"memory.high": "6442450944", "memory.max": "8589934592", "memory.swap.max": "0"}
print("PASS: retained diagnostic and 503 source pins; external obligations OPEN, no Lean proof claimed")
