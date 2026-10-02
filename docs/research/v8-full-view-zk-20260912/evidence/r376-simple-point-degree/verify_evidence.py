#!/usr/bin/env python3
"""Offline integrity checker for the saved R376 focused Lean evidence."""
import hashlib, json, re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def readj(p): return json.loads(p.read_text())
d = readj(HERE / "formal.json")
target = ROOT / d["target"]["repository_path"]
target_copy = HERE / d["target"]["evidence_copy"]
need(sha(target) == d["target"]["sha256"], "promoted target hash")
need(target.read_bytes() == target_copy.read_bytes(), "target differs from successful compiler input")
imp = d["direct_local_import"]
imp_target = ROOT / imp["repository_path"]
imp_copy = HERE / imp["evidence_copy"]
need(sha(imp_target) == imp["sha256"] == sha(imp_copy), "direct R374 import identity")
need(sha(HERE / d["runner"]["path"]) == d["runner"]["sha256"], "runner hash")
for run in d["runs"]:
    rec = readj(HERE / run["receipt"])
    src, log = HERE / run["source"], HERE / run["log"]
    need(sha(src) == run["source_sha256"] == rec["source_sha256"], f"source {run['id']}")
    need(sha(log), f"log exists {run['id']}")
    for k in ("exit_status", "wall_time", "peak_rss_kib", "swaps", "source_revision", "resources", "complete_print_axioms"):
        need(run[k] == rec[k], f"receipt {k}: {run['id']}")
    txt = log.read_text(errors="replace")
    need(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {run['wall_time']}" in txt, f"wall {run['id']}")
    need(f"Maximum resident set size (kbytes): {run['peak_rss_kib']}" in txt, f"RSS {run['id']}")
    need(f"Swaps: {run['swaps']}" in txt and f"Exit status: {run['exit_status']}" in txt, f"status/swap {run['id']}")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]", txt)
    norm = lambda x: " ".join(x.split())
    need([(n, norm(a)) for n,a in reports] == [(x.split(" depends on axioms: [",1)[0].strip("'"), norm(x.split(" depends on axioms: [",1)[1][:-1])) for x in run["complete_print_axioms"]], f"axioms {run['id']}")
    if run["exit_status"] == 0:
        need(len(reports) == 3, "green axiom report count")
        need([n.rsplit(".",1)[-1] for n,_ in reports] == d["expected_theorem_names"], "green theorem names")
        need(all(set(x.strip() for x in a.split(",")) == FOUNDATIONS for _,a in reports), "green standard axioms")
    else:
        need("sorryAx" in txt and "Command exited with non-zero status 1" in txt, "failed attempt history")
need(next(r for r in d["runs"] if r["id"] == d["successful_run_id"])["exit_status"] == 0, "successful run")
checks = HERE / "SHA256SUMS"
listed = set()
for line in checks.read_text().splitlines():
    if not line.strip(): continue
    expected, rel = line.split(None,1); rel = rel.lstrip("* ").removeprefix("./")
    p = HERE / rel
    need(p.is_file() and sha(p) == expected, f"checksum {rel}")
    listed.add(rel)
actual = {str(p.relative_to(HERE)) for p in HERE.rglob("*") if p.is_file() and p != checks}
need(listed == actual, "root checksum inventory (root index excluded only)")
print(f"PASS: R376 evidence ({len(actual)} files), target/import identity, 2 runs, metrics and complete axiom reports")
