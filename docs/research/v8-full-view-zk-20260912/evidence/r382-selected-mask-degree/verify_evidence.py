#!/usr/bin/env python3
"""Offline integrity checker for saved R382 source/model degree evidence."""
import hashlib, json, re
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok, msg):
    if not ok: raise SystemExit("FAIL: " + msg)
def readj(p): return json.loads(p.read_text())
def norm(x): return " ".join(x.split())
def source_shape(p, point):
    txt = p.read_text()
    start = txt.index("def maskOnlyTerm ")
    end = txt.index("\ndef selectedShared ", start)
    body = txt[start:end]
    need(f"claimPolynomial (tables (maskOnlyTableIndex i)) z j ({point} : Fin 3)" in body,
         f"mask-only model point {point}: {p.name}")
    return txt

d = readj(HERE / "formal.json")
target = ROOT / d["target"]["repository_path"]
target_copy = HERE / d["target"]["evidence_copy"]
need(sha(target) == d["target"]["sha256"], "promoted target hash")
need(target.read_bytes() == target_copy.read_bytes(), "promoted target differs from final compiler input")
need(sha(target_copy) == d["runs"][-1]["source_sha256"], "final target/source hash")
imp = d["direct_local_import"]
imp_target = ROOT / imp["repository_path"]
imp_copy = HERE / imp["evidence_copy"]
need(sha(imp_target) == imp["sha256"] == sha(imp_copy), "direct R376 import identity")
runner = HERE / d["runner"]["path"]
need(sha(runner) == d["runner"]["sha256"], "runner hash")
need(d["runner"]["sha256"] == "d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea", "pinned runner identity")

runs = d["runs"]
need(len(runs) == 6, "all six matching R382 target runs retained")
need([r["classification"] for r in runs].count("failed_draft") == 4, "four failed drafts classified")
need([r["classification"] for r in runs].count("superseded_point2_model") == 1, "one superseded green model")
need([r["classification"] for r in runs].count("final_point0_model") == 1, "one final green model")
expected_names = d["expected_theorem_names"]
for run in runs:
    rec = readj(HERE / run["receipt"])
    src, log = HERE / run["source"], HERE / run["log"]
    need(sha(src) == run["source_sha256"] == rec["source_sha256"], f"source {run['id']}")
    need(src.stat().st_size > 0 and log.is_file(), f"source/log exists {run['id']}")
    for k in ("exit_status", "wall_time", "peak_rss_kib", "swaps", "source_revision", "resources", "complete_print_axioms"):
        need(run[k] == rec[k], f"receipt {k}: {run['id']}")
    need(rec["target"] == "AspisV8R19/R382SelectedMaskDegree.lean", f"target {run['id']}")
    need(rec["resources"] == {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":0, "TasksMax":128, "lean_flags":"-j1 -M4500"}, f"resource caps {run['id']}")
    txt = log.read_text(errors="replace")
    for key, pattern in (("wall_time",r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"),
                         ("peak_rss_kib",r"Maximum resident set size \(kbytes\): (\d+)"),
                         ("swaps",r"Swaps: (\d+)"),
                         ("exit_status",r"Exit status: (\d+)")):
        m = re.search(pattern, txt)
        need(m and str(run[key]) == m.group(1), f"log metric {key} {run['id']}")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]", txt)
    got = [(n, norm(a)) for n,a in reports]
    want = [(x.split(" depends on axioms: [",1)[0].strip("'"), norm(x.split(" depends on axioms: [",1)[1][:-1])) for x in run["complete_print_axioms"]]
    need(got == want, f"complete axioms match receipt {run['id']}")
    need(len(got) == 11 and [n.rsplit(".",1)[-1] for n,_ in got] == expected_names, f"all theorem reports {run['id']}")
    if run["classification"] == "failed_draft":
        need(run["exit_status"] == 1 and "Command exited with non-zero status 1" in txt, f"failed run preserved {run['id']}")
    else:
        need(run["exit_status"] == 0, f"green run status {run['id']}")
        need("sorryAx" not in txt, f"no sorryAx in green run {run['id']}")
        for _, ax in got:
            need(set(x.strip() for x in ax.split(",")) <= ALLOW, f"foundation allowlist {run['id']}")

final = next(r for r in runs if r["classification"] == "final_point0_model")
sup = next(r for r in runs if r["classification"] == "superseded_point2_model")
need(final["id"] == d["successful_run_id"], "final successful run id")
source_shape(HERE / final["source"], 0)
source_shape(target, 0)
source_shape(HERE / sup["source"], 2)
need(final["source_sha256"] != sup["source_sha256"], "superseded source distinct")

# Verify the preserved R379 inventory and archived source bytes without relying on scratch paths.
r379 = HERE / "source-inventory/r379-mask-copy-inventory"
for line in (r379 / "SHA256SUMS").read_text().splitlines():
    if not line.strip(): continue
    expected, rel = line.split(None,1); rel = rel.lstrip("* ").removeprefix("./")
    p = r379 / rel
    need(p.is_file() and sha(p) == expected, f"R379 inventory checksum {rel}")
archive = readj(HERE / "source-inventory/source-object-archive.json")
sources = readj(r379 / "sources.json")["sources"]
need(len(archive["objects"]) == len(sources), "all R379 source rows archived")
for row, srcrow in zip(archive["objects"], sources):
    p = HERE / row["archive_path"]
    need(row["label"] == srcrow["label"] and row["sha256"] == srcrow["sha256"] == sha(p), f"R379 source object {row['label']}")
    need(row["bytes"] == srcrow["bytes"] == p.stat().st_size, f"R379 source size {row['label']}")

# Root index excludes only itself; nested R379 SHA256SUMS is covered here and checked above.
checks = HERE / "SHA256SUMS"
listed = set()
for line in checks.read_text().splitlines():
    if not line.strip(): continue
    expected, rel = line.split(None,1); rel = rel.lstrip("* ").removeprefix("./")
    p = HERE / rel
    need(p.is_file() and sha(p) == expected, f"root checksum {rel}")
    listed.add(rel)
actual = {str(p.relative_to(HERE)) for p in HERE.rglob("*") if p.is_file() and p != checks}
need(listed == actual, "root inventory (only root SHA256SUMS excluded)")
print(f"PASS: R382 evidence ({len(actual)} files), target/import identity, 6 runs (4 failed, 1 superseded green, 1 final green), complete metrics/axioms, and archived R379 source inventory")
