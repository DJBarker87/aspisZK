#!/usr/bin/env python3
"""Offline verification of R377 source copies and saved focused-run evidence."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[4]
MODULE = ROOT / "promoted-source/R377SelectorCoordinateDegree.lean"
TRACKED_MODULE = PROJECT / "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R377SelectorCoordinateDegree.lean"
NOTE = PROJECT / "docs/research/v8-full-view-zk-20260912/R377_CURRENT_SELECTOR_COORDINATE_DEGREE.md"
EXPECTED_IDS = ["1790951344531605000", "1790951374239780000", "1790951403732264000", "1790951426811815000"]
EXPECTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
EXPECTED_NAMES = ["selectorPolynomial_degree", "selectorPolynomial_eval", "weightedSelectorPolynomial_degree", "weightedSelectorPolynomial_eval"]
EXPECTED_FULL_NAMES = [f"AspisV8R19.R377SelectorCoordinateDegree.{n}" for n in EXPECTED_NAMES]
EXPECTED_RESOURCES = {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":0, "TasksMax":128, "lean_flags":"-j1 -M4500"}
FOUNDATIONS = set(EXPECTED_AXIOMS)

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok: bool, message: str) -> None:
    if not ok:
        raise SystemExit("FAIL: " + message)

def normalize(s: str) -> str:
    return " ".join(s.split())

def parse_axioms(log: str):
    pat = re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]", re.M | re.S)
    return [(name, [x.strip() for x in body.split(",") if x.strip()]) for name, body in pat.findall(log)]

inventory = json.loads((ROOT / "inventory.json").read_text())
require(inventory["module_sha256"] == sha(MODULE), "inventory module hash")
require(MODULE.read_bytes() == TRACKED_MODULE.read_bytes(), "promoted source differs from tracked module")
require(NOTE.is_file(), "current scope note missing")
require(inventory.get("publication_note_sha256") == sha(NOTE), "current scope note hash")
require(inventory.get("publication_note_sha256") == sha(NOTE), "current scope note hash")
source = MODULE.read_text()
for name in EXPECTED_NAMES:
    require(f"#print axioms {name}" in source, f"missing requested #print axioms: {name}")
require("else 1 - AspisR19.R374SingleCoordinateDegree.line" in source, "selector complement factor drift")
require("bits : Fin n → Coord → Bool" in source, "weighted selector model signature drift")
require("import AspisV8R19.R374SingleCoordinateDegree" in source, "direct import drift")

runner = ROOT / "runner/run_focus.py"
runner_hash = sha(runner)
require(runner_hash == "d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea", "runner hash")

for dep, digest in [
    ("R374SingleCoordinateDegree.lean", "cf9c64577d06c8cb96df204fa34f8832b3b604d3ca6867de2299022eea1fa518"),
    ("SourceStatementPoints.lean", "418236a0c336733d73f41d151b5d010a241649eaa4fb9f06d43e842dcf0ca447"),
]:
    copied = ROOT / "source-route/promoted-imports/AspisV8R19" / dep
    current = PROJECT / "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19" / dep
    require(sha(copied) == digest, f"archived dependency hash: {dep}")
    require(current.is_file() and sha(current) == digest, f"promoted dependency hash: {dep}")

runs = inventory["runs"]
require(len(runs) == 4, "inventory run count")
statuses = []
for index, run_id in enumerate(EXPECTED_IDS):
    stem = ROOT / "runs" / f"aspis-focus-{run_id}"
    receipt_path = stem.with_suffix(".receipt.json")
    log_path = stem.with_suffix(".log")
    source_path = stem.with_suffix(".source.lean")
    receipt = json.loads(receipt_path.read_text())
    log = log_path.read_text(errors="replace")
    expected_status = 0 if index == len(EXPECTED_IDS) - 1 else 1
    require(receipt["exit_status"] == expected_status, f"saved status {run_id}")
    require(receipt["resources"] == EXPECTED_RESOURCES, f"saved caps/flags {run_id}")
    require(receipt["swaps"] == 0, f"saved swap count {run_id}")
    require(receipt["runner_sha256"] == runner_hash, f"receipt runner hash {run_id}")
    require(receipt["source_revision"] == "bb93bebdd1f943b91bd283e85a3ab1a08dc881c7", f"source revision {run_id}")
    require(receipt["source_sha256"] == sha(source_path), f"source snapshot hash {run_id}")
    require(receipt["direct_local_import_sha256"].get("AspisV8R19.R374SingleCoordinateDegree") == "cf9c64577d06c8cb96df204fa34f8832b3b604d3ca6867de2299022eea1fa518", f"direct import receipt {run_id}")
    for name in EXPECTED_NAMES:
        require(f"#print axioms {name}" in source_path.read_text(), f"source lacks #print request {run_id}:{name}")

    # Compare exact report order/names and normalized complete axiom lists from raw log to receipt.
    parsed = parse_axioms(log)
    got_names = [name for name, _ in parsed]
    require(got_names == EXPECTED_FULL_NAMES, f"raw-log theorem names/order {run_id}: {got_names}")
    receipt_parsed=[]
    for line in receipt["complete_print_axioms"]:
        m=re.fullmatch(r"'([^']+)' depends on axioms: \[(.*?)\]", normalize(line))
        require(m is not None, f"malformed receipt axiom line {run_id}")
        receipt_parsed.append((m.group(1), [x.strip() for x in m.group(2).split(",") if x.strip()]))
    require(parsed == receipt_parsed, f"raw log/receipt complete axiom reports differ {run_id}")
    if expected_status == 0:
        require(all(set(axs) == FOUNDATIONS for _, axs in parsed), "successful report contains non-foundational axiom")
        require("sorryAx" not in log, "successful log contains sorryAx")
    else:
        require(any("sorryAx" in axs for _, axs in parsed), f"failed draft lost recorded sorryAx {run_id}")

    # Raw GNU-time evidence must agree with the saved receipt; systemd wrapper is reported separately.
    summary = next(x for x in runs if x["source_sha256"] == receipt["source_sha256"])
    for field in ("wall_time", "peak_rss_kib", "exit_status", "swaps"):
        require(summary.get(field) == receipt[field], f"inventory/receipt {field} mismatch {run_id}")
    require(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {receipt['wall_time']}" in log, f"raw wall time {run_id}")
    require(f"Maximum resident set size (kbytes): {receipt['peak_rss_kib']}" in log, f"raw peak RSS {run_id}")
    require(f"Swaps: {receipt['swaps']}" in log and f"Exit status: {receipt['exit_status']}" in log, f"raw status/swap {run_id}")
    statuses.append((run_id, receipt["exit_status"], receipt["wall_time"], receipt["peak_rss_kib"], receipt["swaps"]))

require((ROOT / "source-route/selector-split-census.md").is_file(), "selector source census missing")
require((ROOT / "source-route/selector-split-manifest.json").is_file(), "selector source manifest missing")
require(inventory["source_correspondence_claim"] is False, "source correspondence boundary changed")

# Separately recorded qualified-path cache population. This is a fifth focused run
# for the missing module-path artifact; the original four run records above remain intact.
q=inventory["qualified_path_cache_population"]
qstem=ROOT/q["source"]
qsource=qstem
qlog=ROOT/q["log"]
qreceipt_path=ROOT/q["receipt"]
qreceipt=json.loads(qreceipt_path.read_text())
require(sha(qsource)==q["source_sha256"]==qreceipt["source_sha256"]==sha(MODULE), "qualified-run source identity")
require(sha(qlog)==q["log_sha256"] and sha(qreceipt_path)==q["receipt_sha256"], "qualified-run log/receipt hashes")
require(qreceipt["target"]=="AspisV8R19/R377SelectorCoordinateDegree.lean", "qualified target path")
require(qreceipt["source_revision"]==q["source_revision"] and qreceipt["exit_status"]==0==q["exit_status"], "qualified-run revision/status")
require(qreceipt["resources"]==EXPECTED_RESOURCES==q["resources"] and qreceipt["swaps"]==0==q["swaps"], "qualified-run resource limits")
require(qreceipt["runner_sha256"]==runner_hash, "qualified-run runner identity")
qtxt=qlog.read_text(errors="replace")
qparsed=parse_axioms(qtxt)
require([x for x,_ in qparsed]==EXPECTED_FULL_NAMES, "qualified raw-log theorem names")
qreceipt_parsed=[]
for item in qreceipt["complete_print_axioms"]:
    m=re.fullmatch(r"'([^']+)' depends on axioms: \[(.*?)\]", normalize(item))
    require(m is not None, "qualified receipt axiom record format")
    qreceipt_parsed.append((m.group(1),[x.strip() for x in m.group(2).split(",") if x.strip()]))
require(qparsed==qreceipt_parsed and all(set(axs)==FOUNDATIONS for _,axs in qparsed), "qualified full axiom reports")
require(f"Elapsed (wall clock) time (h:mm:ss or m:ss): {qreceipt['wall_time']}" in qtxt, "qualified raw wall time")
require(f"Maximum resident set size (kbytes): {qreceipt['peak_rss_kib']}" in qtxt, "qualified raw RSS")
require(f"Swaps: 0" in qtxt and "Exit status: 0" in qtxt, "qualified raw status/swap")
pre=json.loads((ROOT/q["preflight_copy"]).read_text())
post=json.loads((ROOT/q["postflight_copy"]).read_text())
require(sha(ROOT/q["preflight_copy"])==q["preflight_sha256"] and "qualified_olean_before=1" in pre["observed_output"], "qualified object absence preflight")
require(sha(ROOT/q["postflight_copy"])==q["postflight_sha256"], "qualified object postflight record hash")
require(post["qualified_olean_path"]==q["qualified_olean_path"] and post["qualified_olean_sha256"]==q["qualified_olean_sha256"] and post["qualified_olean_size_bytes"]==q["qualified_olean_size_bytes"], "qualified object postflight metadata")
require(q["qualified_olean_path"].endswith("/AspisV8R19/R377SelectorCoordinateDegree.olean") and re.fullmatch(r"[0-9a-f]{64}",q["qualified_olean_sha256"]), "qualified object path/hash shape")
require(NOTE.is_file() and sha(NOTE)==inventory["publication_note_sha256"], "publication note hash")

# The bundle checksum must cover every file except itself, and no other file.
checksum = ROOT / "SHA256SUMS"
listed = set()
for line in checksum.read_text().splitlines():
    if not line.strip(): continue
    digest, rel = line.split("  ", 1)
    rel=rel.removeprefix("./")
    path=ROOT/rel
    require(path.is_file() and sha(path)==digest, f"bundle hash mismatch: {rel}")
    listed.add(rel)
actual={str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file() and p!=checksum}
require(listed==actual, "bundle inventory mismatch")
print(json.dumps({"status":"PASS","module_sha256":sha(MODULE),"runs":statuses,"axioms":EXPECTED_AXIOMS,"theorems":EXPECTED_NAMES,"files":len(actual)},indent=2))
