#!/usr/bin/env python3
"""Check immutable extraction evidence and source cuts; never compile."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
KIT = HERE.parents[1] / "tools/qm31-sampler-extraction-kit"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    listed = set()
    for line in (HERE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        assert name not in listed, ("duplicate digest entry", name)
        listed.add(name)
        assert sha((HERE / name).read_bytes()) == digest, ("digest mismatch", name)
    actual = {str(p.relative_to(HERE)) for p in HERE.rglob("*")
              if p.is_file() and p.name != "SHA256SUMS"}
    assert listed == actual, ("digest coverage mismatch", listed ^ actual)
    attempt = HERE / "attempt-a"
    for name, digest in json.loads((attempt / "artifact-pins.json").read_text()).items():
        assert sha((attempt / name).read_bytes()) == digest, name
    findings = json.loads((HERE / "findings.json").read_text())
    rev = findings["source_revision"]
    for name, digest in findings["source_files"].items():
        raw = subprocess.check_output(["git", "-C", str(REPO), "show", f"{rev}:{name}"])
        assert sha(raw) == digest, name
        assert (HERE / "source-files" / name).read_bytes() == raw, name
    subprocess.run(["python3", str(KIT / "extract.py"), "--check"], check=True)
    for name in ["Cargo.toml", "lib.rs", "extract.py", "source-pins.json"]:
        assert (KIT / name).read_bytes() == (attempt / "source" / name).read_bytes(), name
    llbc = json.loads((attempt / "Qm31Sampler.llbc").read_text())
    assert llbc["has_errors"] is False
    source = (HERE / "source-files/crates/aspis-r1-cost-probe/src/sampler.rs").read_text()
    actual_body = "\n".join(source.splitlines()[7:24])
    assert llbc["translated"]["fun_decls"][0]["item_meta"]["source_text"] == actual_body
    translated = json.loads((attempt / "generated/translation.json").read_text())
    assert len(translated["functions"]) == 10
    assert sum(f["is_opaque"] for f in translated["functions"]) == 2
    assert not (attempt / "generated/AspisR1Qm31Sampler/FunsExternal.lean").exists()
    records = json.loads((attempt / "commands.json").read_text())
    for label in ["extract", "translate"]:
        record, = [r for r in records if r["label"] == label]
        assert record["exit"] == 0 and record["killed_reason"] is None
        assert record["wall_seconds"] < 180
        assert record["peak_group_rss_kib"] < 3_670_016
    assert findings["lean_compilation"] == "NOT RUN"
    print(f"PASS: {len(listed)} SHA entries, exact source/cut/LLBC body pins; "
          "2 opaque functions retained; source refinement OPEN")


if __name__ == "__main__":
    main()
