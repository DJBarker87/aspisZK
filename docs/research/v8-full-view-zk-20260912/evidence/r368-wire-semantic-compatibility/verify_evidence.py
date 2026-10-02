#!/usr/bin/env python3
"""Portable, read-only integrity and saved-run checker for R368."""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DOC_ROOT = ROOT.parent.parent
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(rel: str):
    return json.loads((ROOT / rel).read_text())


def normalized(text: str) -> str:
    return " ".join(text.split())


def main() -> None:
    failures: list[str] = []
    sums = ROOT / "SHA256SUMS"
    expected = {}
    for line in sums.read_text().splitlines():
        digest, rel = line.split("  ", 1)
        expected[rel] = digest
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file() and p != sums}
    if actual != set(expected):
        failures.append("outer checksum path set differs")
    for rel, digest in expected.items():
        p = ROOT / rel
        if not p.is_file() or sha(p.read_bytes()) != digest:
            failures.append(f"outer checksum mismatch: {rel}")

    inv = load("inventory.json")
    target = ROOT / inv["target"]["evidence_copy"]
    promoted = DOC_ROOT / inv["target"]["repository_path"].split("docs/research/v8-full-view-zk-20260912/", 1)[1]
    if not target.is_file() or not promoted.is_file() or target.read_bytes() != promoted.read_bytes():
        failures.append("promoted target differs from archived successful source")
    if sha(target.read_bytes()) != inv["target"]["sha256"]:
        failures.append("target SHA differs from inventory")

    dep = ROOT / inv["dependency"]["evidence_copy"]
    dep_target = DOC_ROOT / inv["dependency"]["repository_path"].split("docs/research/v8-full-view-zk-20260912/", 1)[1]
    if not dep.is_file() or not dep_target.is_file() or dep.read_bytes() != dep_target.read_bytes():
        failures.append("R366 dependency archive and direct local import differ")
    if sha(dep.read_bytes()) != inv["dependency"]["sha256"]:
        failures.append("R366 dependency SHA differs")

    runner = ROOT / inv["runner"]["path"]
    if sha(runner.read_bytes()) != inv["runner"]["sha256"]:
        failures.append("runner SHA differs")

    prov = load("source-provenance/source-provenance.json")
    census_root = ROOT / "source-provenance/r368-selected-semantic-degree-source-census"
    for rel in ("inventory.json", "excerpts.md", "README.md", "frozen-file-copies.json"):
        if not (census_root / rel).is_file():
            failures.append(f"saved source census file missing: {rel}")
    for key in ("selected_performance_verifier", "selected_terminal_source"):
        row = prov[key]
        path = ROOT / row["path"]
        if not path.is_file() or sha(path.read_bytes()) != row["sha256"]:
            failures.append(f"selected source census copy SHA mismatch: {key}")
    perf = (ROOT / prov["selected_performance_verifier"]["path"]).read_text()
    compact_perf = "".join(perf.split())
    for needle in ("poly[0]=sent[0]", "poly[2..].copy_from_slice(&sent[1..])", "poly[1]=s.claim.sub", "ifactual!=s.claim{returnErr(Error::Terminal);}"):
        if needle not in compact_perf:
            failures.append(f"frozen selected source does not contain recorded expression: {needle}")

    source_copies = []
    all_reports = []
    expected_ids = ["1790947788822766000", "1790947873301256000", "1790948002142284000"]
    if [r["id"] for r in inv["runs"]] != expected_ids:
        failures.append("run ID order/set differs")
    for run in inv["runs"]:
        src = ROOT / run["source"]
        log = ROOT / run["log"]
        recpath = ROOT / run["receipt"]
        receipt = json.loads(recpath.read_text())
        srcbytes = src.read_bytes()
        logtext = log.read_text()
        if sha(srcbytes) != run["source_sha256"] or sha(srcbytes) != receipt["source_sha256"]:
            failures.append(f"source checksum/receipt mismatch: {run['id']}")
        if sha(log.read_bytes()) != run["log_sha256"]:
            failures.append(f"log checksum mismatch: {run['id']}")
        if receipt["source_revision"] != run["source_revision"]:
            failures.append(f"source revision mismatch: {run['id']}")
        if receipt["direct_local_import_sha256"].get("AspisV8R19.R366SemanticNormalization") != inv["dependency"]["sha256"]:
            failures.append(f"R366 direct import SHA mismatch in run: {run['id']}")
        for key in ("exit_status", "wall_time", "peak_rss_kib", "swaps", "resources", "measurement_boundary"):
            if receipt.get(key) != run.get(key):
                failures.append(f"receipt/inventory {key} mismatch: {run['id']}")
        patterns = {
            "wall_time": r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)",
            "peak_rss_kib": r"Maximum resident set size \(kbytes\): (\d+)",
            "swaps": r"Swaps: (\d+)",
            "exit_status": r"Exit status: (\d+)",
        }
        for key, pat in patterns.items():
            m = re.search(pat, logtext)
            value = m[1] if key == "wall_time" and m else (int(m[1]) if m else None)
            if value != receipt.get(key):
                failures.append(f"raw-log/receipt {key} mismatch: {run['id']}")
        resources = run["resources"]
        if resources != {"MemoryHigh":"5G", "MemoryMax":"7G", "MemorySwapMax":0, "TasksMax":128, "lean_flags":"-j1 -M4500"}:
            failures.append(f"resource limits mismatch: {run['id']}")
        source_text = srcbytes.decode()
        requests = re.findall(r"^#print axioms\s+(.+?)\s*$", source_text, re.M)
        reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)", logtext)
        if len(requests) != 10 or len(reports) != len(requests):
            failures.append(f"complete print-request count mismatch: {run['id']}")
        for (actual_name, axiom_text), requested in zip(reports, requests):
            if not (actual_name == requested or actual_name.endswith("." + requested)):
                failures.append(f"axiom report name differs from source request: {run['id']} {requested}")
            axioms = {a.strip() for a in axiom_text.replace("\n", " ").split(",") if a.strip()}
            allowed_for_run = FOUNDATIONS if run["exit_status"] == 0 else FOUNDATIONS | {"sorryAx"}
            if not axioms <= allowed_for_run:
                failures.append(f"non-foundational axiom output: {run['id']} {actual_name}: {sorted(axioms-FOUNDATIONS)}")
        receipt_reports = [normalized(x) for x in receipt["complete_print_axioms"]]
        log_reports = [normalized(m.group(0)) for m in re.finditer(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", logtext)]
        if receipt_reports != log_reports:
            failures.append(f"complete receipt axiom output differs from log: {run['id']}")
        if run["exit_status"] == 0:
            if run["id"] != inv["successful_run_id"]:
                failures.append(f"unexpected successful run ID: {run['id']}")
            all_reports.extend(receipt["complete_print_axioms"])
            if "sorryAx" in "\n".join(receipt["complete_print_axioms"]):
                failures.append("sorryAx in successful axiom reports")
        elif "sorryAx" not in "\n".join(receipt["complete_print_axioms"]):
            failures.append(f"rejected draft lacks expected sorryAx trail: {run['id']}")
        source_copies.append(sha(srcbytes))

    if len(all_reports) != 10 or len(inv["axiom_output"]) != 10:
        failures.append("expected exactly ten successful axiom reports")
    release_note = DOC_ROOT / "R368_CURRENT_WIRE_SEMANTIC_COMPATIBILITY.md"
    if not release_note.is_file() or sha(release_note.read_bytes()) != inv["release_note"]["sha256"]:
        failures.append("release note missing")

    print(json.dumps({
        "status":"PASS" if not failures else "FAIL",
        "evidence_root":str(ROOT),
        "checksummed_files":len(expected),
        "target_byte_identity":target.is_file() and promoted.is_file() and target.read_bytes()==promoted.read_bytes(),
        "runs":len(inv["runs"]),"successful_axiom_reports":len(all_reports),
        "source_census_copies_checked":2,"failures":failures
    },indent=2))
    if failures:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
