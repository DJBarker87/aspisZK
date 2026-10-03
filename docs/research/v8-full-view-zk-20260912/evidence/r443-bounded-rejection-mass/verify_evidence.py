#!/usr/bin/env python3
"""Read-only integrity checks for the saved R442/R443 proof evidence."""
from pathlib import Path
import hashlib, json, re, sys

HERE = Path(__file__).resolve().parent
DOCROOT = HERE.parent.parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(cond, message):
    if not cond:
        raise SystemExit("FAIL: " + message)

# Check every saved artifact except the checksum index itself.
index = HERE / "SHA256SUMS"
expected = {}
for line in index.read_text().splitlines():
    if not line.strip():
        continue
    digest, rel = line.split("  ", 1)
    expected[rel] = digest
actual = {p.relative_to(HERE).as_posix(): sha(p) for p in HERE.rglob("*") if p.is_file() and p != index}
require(expected == actual, "SHA256SUMS does not match evidence bundle file set/content")

manifest = json.loads((HERE / "manifest.json").read_text())
for row in manifest["targets"]:
    rid = row["run_id"]
    run = HERE / "runs" / rid
    receipt = json.loads((run / "receipt.json").read_text())
    require(receipt["target"] == row["target"], rid + " target mismatch")
    require(receipt["source_revision"] == manifest["source_revision"], rid + " source revision mismatch")
    require(receipt["source_sha256"] == row["source_sha256"], rid + " source hash mismatch")
    require(sha(run / "source.lean") == row["source_sha256"], rid + " saved source mismatch")
    require(receipt["exit_status"] == row["exit_status"] == 0, rid + " was not successful")
    require(receipt["wall_time"] == row["wall_time"], rid + " wall time mismatch")
    require(receipt["peak_rss_kib"] == row["peak_rss_kib"], rid + " GNU RSS mismatch")
    require(receipt["swaps"] == row["swaps"] == 0, rid + " swap mismatch")
    require(receipt["resources"]["MemoryHigh"] == "5G" and receipt["resources"]["MemoryMax"] == "7G" and receipt["resources"]["MemorySwapMax"] == 0 and receipt["resources"]["TasksMax"] == 128 and receipt["resources"]["lean_flags"] == "-j1 -M4500", rid + " resource limits mismatch")
    require(receipt["runner_sha256"] == sha(HERE / "runner/run_focus.py"), rid + " runner hash mismatch")
    log = (run / "lean.log").read_text()
    require("Exit status: 0" in log, rid + " GNU time status mismatch")
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", log)
    rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", log)
    swaps = re.search(r"Swaps:\s*(\d+)", log)
    require(wall and wall.group(1) == row["wall_time"], rid + " raw GNU wall mismatch")
    require(rss and int(rss.group(1)) == row["peak_rss_kib"], rid + " raw GNU RSS mismatch")
    require(swaps and int(swaps.group(1)) == row["swaps"] == 0, rid + " raw GNU swap mismatch")
    reports = re.findall(r"'[^'\n]+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", log)
    require(reports == receipt["complete_print_axioms"], rid + " receipt/log axiom reports differ")
    got = {}
    for report in reports:
        m = re.fullmatch(r"'([^']+)' depends on axioms: \[([^\]]*)\]", report)
        require(m is not None, rid + " successful theorem unexpectedly has an axiom-free report")
        got[m.group(1)] = [x.strip() for x in m.group(2).split(",") if x.strip()]
    require(got == row["axioms"], rid + " axiom sets do not match manifest")
    require(all(set(names) <= set(manifest["axiom_whitelist"]) for names in got.values()), rid + " contains axioms outside whitelist")
    saved = HERE / "source" / row["target"]
    promoted = DOCROOT / "lean" / row["target"]
    require(sha(saved) == row["source_sha256"], rid + " evidence source copy mismatch")
    require(sha(promoted) == row["source_sha256"], rid + " promoted source mismatch")

# Check the direct-import chain captured in successful run receipts.
r421 = HERE / "source/AspisV8R19/R421UniformMasked31Block.lean"
r442_source = HERE / "source/AspisV8R19/R442RejectionAlphabet.lean"
r443_source = HERE / "source/AspisV8R19/R443BoundedRejectionMass.lean"
r442_receipt = json.loads((HERE / "runs/1791013663890906000/receipt.json").read_text())
r443_receipt = json.loads((HERE / "runs/1791014199928630000/receipt.json").read_text())
r445_receipt = json.loads((HERE / "runs/1791014817462002000/receipt.json").read_text())
require(sha(r421) == r442_receipt["direct_local_import_sha256"]["AspisV8R19.R421UniformMasked31Block"], "R421 direct import hash mismatch")
require(sha(r442_source) == r443_receipt["direct_local_import_sha256"]["AspisV8R19.R442RejectionAlphabet"], "R442 direct import hash mismatch")
require(sha(r443_source) == r445_receipt["direct_local_import_sha256"]["AspisV8R19.R443BoundedRejectionMass"], "R443 direct import hash mismatch")

# Failed drafts stay explicitly failed; sorryAx is allowed only in their logs.
for row in manifest["rejected_runs"]:
    run = HERE / "runs" / row["run_id"]
    receipt = json.loads((run / "receipt.json").read_text())
    log = (run / "lean.log").read_text()
    require(receipt["exit_status"] == row["exit_status"] == 1, row["run_id"] + " rejected exit status mismatch")
    require(sha(run / "source.lean") == receipt["source_sha256"], row["run_id"] + " rejected source snapshot mismatch")
    require("Exit status: 1" in log, row["run_id"] + " rejected GNU time status mismatch")
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(\S+)", log)
    rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", log)
    swaps = re.search(r"Swaps:\s*(\d+)", log)
    require(wall and wall.group(1) == receipt["wall_time"], row["run_id"] + " rejected raw GNU wall mismatch")
    require(rss and int(rss.group(1)) == receipt["peak_rss_kib"], row["run_id"] + " rejected raw GNU RSS mismatch")
    require(swaps and int(swaps.group(1)) == receipt["swaps"] == 0, row["run_id"] + " rejected raw GNU swap mismatch")
    if row["run_id"].startswith("17910138") or row["run_id"].startswith("17910139"):
        require("sorryAx" in log, row["run_id"] + " expected rejected sorryAx history not present")

print("PASS: bundle hashes, promoted source identities, receipts, raw GNU time, resource limits, axioms, direct imports, runner, and rejected history verified")
