#!/usr/bin/env python3
"""Package retained candidate-only attempts without any build or replay."""
from pathlib import Path
import difflib
import hashlib
import io
import json
import re
import sys
import tarfile

root, out = map(Path, sys.argv[1:])
out.mkdir(parents=True, exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
files = {str(p.relative_to(root)): p.read_bytes() for p in sorted(root.rglob("*")) if p.is_file()}
kit = Path(__file__).resolve().parent
for name in ["check-lean-host.py", "run-lean-host.py", "README.txt"]:
    files["final-kit/" + name] = (kit / name).read_bytes()
a = files["runs/candidate-a/candidate-source/lib.rs"].decode()
b = files["runs/candidate-b/candidate-source/lib.rs"].decode()
files["candidate-a-to-b.diff"] = "".join(difflib.unified_diff(a.splitlines(keepends=True), b.splitlines(keepends=True), fromfile="candidate-a/lib.rs", tofile="candidate-b/lib.rs")).encode()
summary = {"scope": "Candidate-only generic Digest32 feasibility, not production adoption or source/effect preservation",
           "original_source_revision": "b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c",
           "candidate_source_sha256": sha(b.encode()), "attempts": {}, "lean_targets": {}}
for attempt in ["candidate-a", "candidate-b"]:
    prefix = "runs/" + attempt + "/"
    trans = json.loads(files[prefix + "generated/translation.json"])
    commands = json.loads(files[prefix + "commands.json"])
    record = {"emitted_functions": trans["functions"], "emitted_trait_declarations": trans["trait_decls"],
              "emitted_files": [p[len(prefix + "generated/"):] for p in files if p.startswith(prefix + "generated/")], "tools": {}}
    for cmd in commands:
        if cmd["name"] in ["charon", "aeneas"]:
            timing = files[prefix + cmd["name"] + ".time.log"].decode()
            record["tools"][cmd["name"]] = dict(cmd, peak_process_rss_kib=int(re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", timing)[1]), process_swaps=int(re.search(r"Swaps:\s*(\d+)", timing)[1]))
    record["outcome"] = "Rejected: trait-only emission, actual method absent" if attempt == "candidate-a" else "Full candidate method and wrapper emitted; checked subsequently"
    summary["attempts"][attempt] = record
for attempt in ["types-a", "funs-a", "axioms-a"]:
    summary["lean_targets"][attempt] = json.loads(files["lean/runs/" + attempt + "/receipt.json"])
summary["generated_explicit_axioms"] = []
summary["axiom_report"] = files["lean/runs/axioms-a/lean.log"].decode()
summary["remaining"] = ["Concrete hash backend and real effect/trace relation", "Production interface review/adoption and differential checks", "Constructor/caller/all33 and Observer extraction", "hbytes/htyped/ha provenance", "Rust/LLBC preservation, panic/unwind/nonreturning effects", "Arbitrary release-profile row overflow behavior"]
members = {name: {"sha256": sha(data), "bytes": len(data)} for name, data in sorted(files.items())}
with tarfile.open(out / "evidence.tar.gz", "w:gz") as t:
    for name, data in sorted(files.items()):
        entry = tarfile.TarInfo(name)
        entry.size, entry.mtime, entry.mode = len(data), 0, 0o644
        t.addfile(entry, io.BytesIO(data))
(out / "archive-members.json").write_text(json.dumps(members, indent=2) + "\n")
summary["archive_sha256"] = sha((out / "evidence.tar.gz").read_bytes())
summary["archive_member_count"] = len(members)
summary["member_manifest_sha256"] = sha((out / "archive-members.json").read_bytes())
(out / "SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
print(f"Packaged {len(members)} regular candidate evidence members; no keys or dependency objects")
