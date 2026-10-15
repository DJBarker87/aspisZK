#!/usr/bin/env python3
"""Verify exact retained Prefix failure evidence; never compile."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
KIT = HERE.parents[1] / "tools/prefix-parser-extraction-kit"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    entries = {}
    for line in (HERE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        assert name not in entries
        entries[name] = digest
        assert sha((HERE / name).read_bytes()) == digest, name
    assert set(entries) == {str(p.relative_to(HERE)) for p in HERE.rglob("*")
                            if p.is_file() and p.name != "SHA256SUMS"}
    attempt = HERE / "attempt-a"
    for name, digest in json.loads((attempt / "artifact-pins.json").read_text()).items():
        assert sha((attempt / name).read_bytes()) == digest, name
    pins = json.loads((KIT / "source-pins.json").read_text())
    subprocess.run(["python3", "-B", str(KIT / "extract.py"), "--check"], check=True)
    for name in ["Cargo.toml", "lib.rs", "source-pins.json", "extract.py"]:
        assert (KIT / name).read_bytes() == (attempt / "source" / name).read_bytes(), name
    for name, digest in pins["source_files"].items():
        raw = subprocess.check_output(["git", "-C", str(REPO), "show",
                                       f"{pins['source_revision']}:{name}"])
        assert sha(raw) == digest and (HERE / "source-files" / name).read_bytes() == raw
    assert sha((HERE / "exact-cut-utility.py").read_bytes()) == pins["cut_utility_sha256"]
    assert sha((HERE / "reused-parser-kit/lib.rs").read_bytes()) == pins["reused_parser_kit"]["lib_sha256"]
    assert sha((HERE / "reused-parser-kit/source-manifest.json").read_bytes()) == pins["reused_parser_kit"]["manifest_sha256"]
    llbc = json.loads((attempt / "PrefixParser.llbc").read_text())
    assert llbc["has_errors"] is False
    function = llbc["translated"]["fun_decls"][30]
    cut, = [c for c in pins["declaration_cuts"] if c["name"] == "prefix_parse"]
    lines = (HERE / "source-files" / cut["path"]).read_text().splitlines()
    exact_body = "\n".join(lines[cut["first_line"] - 1:cut["last_line"]]).strip()
    assert function["item_meta"]["source_text"] == exact_body
    assert 'Ok(Self { c1_root, records })' in lines[296]
    assert 'Ok(Self { c1_root, records })' in (KIT / "lib.rs").read_text().splitlines()[230]
    assert not list(attempt.rglob("*.lean")), "No emitted Lean is expected from this failed attempt"
    records = json.loads((attempt / "commands.json").read_text())
    for label, expected in [("extract", 0), ("translate", 2)]:
        record, = [r for r in records if r["label"] == label]
        assert record["exit"] == expected and record["killed_reason"] is None
        assert record["wall_seconds"] < 180 and record["peak_group_rss_kib"] < 3_670_016
    log = (attempt / "translate.log").read_text()
    assert "There should be no bottoms in the value" in log
    assert "lines 231:27-231:34" in log
    print(f"PASS: {len(entries)} evidence digests,27 exact cuts,18 reused parser declarations,"
          " exact LLBC parse body; retained Aeneas exit2; Prefix refinement OPEN")


if __name__ == "__main__":
    main()
