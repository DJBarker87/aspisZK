#!/usr/bin/env python3
"""Offline checker for saved R386 focused Lean evidence."""
import hashlib, json, re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def readj(p): return json.loads(p.read_text())
def norm(s): return " ".join(s.split())

d = readj(HERE / "formal.json")
target = ROOT / d["target"]["repository_path"]
target_copy = HERE / d["target"]["evidence_copy"]
need(sha(target) == d["target"]["sha256"], "promoted target hash")
need(target.read_bytes() == target_copy.read_bytes(), "target differs from final compiler input")
need(sha(target_copy) == d["runs"][-1]["source_sha256"], "final source hash")
for imp in d["direct_local_imports"]:
    repo = ROOT / imp["repository_path"]
    saved = HERE / imp["evidence_copy"]
    need(sha(repo) == imp["sha256"] == sha(saved), f"import identity {imp['module']}")
runner = HERE / d["runner"]["path"]
need(sha(runner) == d["runner"]["sha256"], "runner hash")
need(len(d["runs"]) == 10 and sum(r["exit_status"] == 1 for r in d["runs"]) == 9,
     "all nine failed drafts plus final run retained")
need(d["runs"][-1]["classification"] == "final_green" and d["successful_run_id"] == d["runs"][-1]["id"], "final green classification")
allow = set(d["foundation_allowlist"])
for run in d["runs"]:
    rec = readj(HERE / run["receipt"])
    src, log = HERE / run["source"], HERE / run["log"]
    need(sha(src) == run["source_sha256"] == rec["source_sha256"], f"source {run['id']}")
    need(log.is_file() and rec["target"] == "AspisV8R19/R386CopyDegree.lean", f"log/target {run['id']}")
    for k in ("exit_status", "wall_time", "peak_rss_kib", "swaps", "source_revision", "resources", "complete_print_axioms"):
        need(run[k] == rec[k], f"receipt field {k} {run['id']}")
    need(rec["resources"] == {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":0, "TasksMax":128, "lean_flags":"-j1 -M4500"}, f"caps {run['id']}")
    txt = log.read_text(errors="replace")
    for key, pattern in (("wall_time",r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"),
                         ("peak_rss_kib",r"Maximum resident set size \(kbytes\): (\d+)"),
                         ("swaps",r"Swaps: (\d+)"), ("exit_status",r"Exit status: (\d+)")):
        m = re.search(pattern, txt)
        need(m and str(run[key]) == m.group(1), f"logged metric {key} {run['id']}")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]", txt)
    expected_reports = [(x.split(" depends on axioms: [",1)[0].strip("'"), norm(x.split(" depends on axioms: [",1)[1][:-1])) for x in run["complete_print_axioms"]]
    need([(n,norm(a)) for n,a in reports] == expected_reports, f"complete axioms/receipt {run['id']}")
    if run["classification"] == "final_green":
        need(run["exit_status"] == 0 and "sorryAx" not in txt, "final compile/no sorryAx")
        need([n.rsplit(".",1)[-1] for n,_ in reports] == d["expected_final_theorem_names"], "final theorem names")
        need(len(reports) == 15, "final full report count")
        for _, axioms in reports:
            need(set(x.strip() for x in axioms.split(",")) <= allow, "foundation allowlist")
    else:
        need(run["exit_status"] == 1 and "Command exited with non-zero status 1" in txt, f"failed attempt retained {run['id']}")

# Check stated model shape directly in the saved promoted source.
txt = target.read_text()
for needle in [
    "((r.val / 2 ^ (9 - i.val)) % 2 = 1)",
    "∑ r : Fin 1024, rowSelector z j r *",
    "C (tag s r) + ∑ c : Fin 16",
    "∑ r : Fin 1024, rowSelector z j r * C (weightCoeff s r)",
    "∑ r : Fin 1024, rowSelector z j r * C (activeCoeff r)",
    "genericPairDen v chi * (helper * genericOtherDen v chi + genericOtherNumerator v w chi) -",
    "active * genericCopyCore v w helper chi",
    "copyResidual_degree", "copyZerocheck_degree", "copyInactiveHelper_degree",
]: need(needle in txt, f"model source shape {needle}")

# Preserve and verify the imported R381 trailing space, not a normalized rewrite.
r381 = next(x for x in d["direct_local_imports"] if x["module"].endswith("R381ProjectedPoseidonDegree"))
raw = (HERE / r381["evidence_copy"]).read_bytes().splitlines()
need(raw[102].endswith(b" "), "R381 imported trailing space retained at line 103")
need(sha(HERE / r381["evidence_copy"]) == r381["sha256"], "R381 exact import bytes")

# Root checksum excludes itself only.
checks = HERE / "SHA256SUMS"
listed = set()
for line in checks.read_text().splitlines():
    if not line.strip(): continue
    expected, rel = line.split(None,1); rel = rel.lstrip("* ").removeprefix("./")
    p = HERE / rel
    need(p.is_file() and sha(p) == expected, f"checksum {rel}")
    listed.add(rel)
actual = {str(p.relative_to(HERE)) for p in HERE.rglob("*") if p.is_file() and p != checks}
need(listed == actual, "root checksum inventory")
print(f"PASS: R386 evidence ({len(actual)} files), target/import identity, ten attempts, full metrics/axioms and model shape")
