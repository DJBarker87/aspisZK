#!/usr/bin/env python3
"""Portable, read-only verifier for the saved R367 evidence bundle."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DOC_ROOT = ROOT.parent.parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load(rel: str):
    return json.loads((ROOT / rel).read_text())


def main() -> None:
    failures: list[str] = []
    sums_path = ROOT / "SHA256SUMS"
    expected: dict[str, str] = {}
    for line in sums_path.read_text().splitlines():
        digest, rel = line.split("  ", 1)
        expected[rel] = digest
    actual = {
        p.relative_to(ROOT).as_posix()
        for p in ROOT.rglob("*") if p.is_file() and p != sums_path
    }
    if actual != set(expected):
        failures.append("root checksum manifest path set differs")
    for rel, digest in expected.items():
        path = ROOT / rel
        if not path.is_file() or sha(path.read_bytes()) != digest:
            failures.append(f"checksum mismatch or missing: {rel}")

    inventory = load("inventory.json")
    stage = load("staging-history/staging-receipt.json")
    normalization = load("staging-history/normalization-receipt.json")
    qualification = load("staging-history/qualification-patch-receipt.json")
    source_audit = load("final-sources/source-audit.json")
    result = load("source-inputs/r364-translation-result.json")
    translation = load("source-inputs/r364-translation.json")
    note = DOC_ROOT / "R367_CURRENT_CONTROLFLOW_EXECUTION.md"
    if not note.is_file() or sha(note.read_bytes()) != inventory["release_note"]["sha256"]:
        failures.append("release note missing or differs from recorded SHA")

    imports = ["import Aeneas.Std", "import Aeneas.Extract.Extract", "import Aeneas.Data.Discriminant"]
    source_reconstruction: dict[str, bool] = {}
    for name in ("Types.lean", "Funs.lean"):
        original = (ROOT / "generated-original" / name).read_bytes()
        print_axioms = stage["files"][name]["appended_print_axioms"]
        normalized = original.replace(
            b"import Aeneas\n", ("\n".join(imports) + "\n").encode(), 1
        )
        normalized += ("\n\n" + "\n".join(print_axioms) + "\n").encode()
        if name == "Funs.lean":
            if qualification["occurrences_replaced"] != 1 or qualification["all_other_bytes_identical"] is not True:
                failures.append("qualification receipt does not describe the permitted one-expression change")
            normalized = normalized.replace(
                b"let residual1 := read_discriminant residual",
                b"let residual1 := Aeneas.Std.read_discriminant residual", 1
            )
        final = (ROOT / "final-sources" / name).read_bytes()
        source_reconstruction[name] = normalized == final
        if not source_reconstruction[name]:
            failures.append(f"source reconstruction mismatch: {name}")
        if sha(final) != source_audit["generated_sources"][name]["actual_final_sha256"]:
            failures.append(f"source audit hash mismatch: {name}")

    target_checks = []
    for row in inventory["target_files"]:
        final = ROOT / row["evidence_copy"]
        target = DOC_ROOT / row["repository_path"].split("docs/research/v8-full-view-zk-20260912/", 1)[1]
        ok = final.is_file() and target.is_file() and final.read_bytes() == target.read_bytes()
        ok = ok and sha(final.read_bytes()) == row["sha256"]
        target_checks.append(ok)
        if not ok:
            failures.append(f"promoted target does not match evidence copy: {row['repository_path']}")

    if sha((ROOT / "source-inputs/R334ControlFlowSourceProjection.llbc").read_bytes()) != result["source_sha256"]:
        failures.append("R334 source LLBC hash differs from translation receipt")
    if result["exit_status"] != 0 or result["Lean_compiled"] is not False:
        failures.append("R364 translation receipt status mismatch")
    for rel, expected_hash in result["generated_files"].items():
        path = ROOT / "source-inputs" / rel.removeprefix("generated/")
        # Generated Lean files and generated/translation.json are saved in the census tree / original copies.
        if rel.endswith("Types.lean"):
            path = ROOT / "generated-original/Types.lean"
        elif rel.endswith("Funs.lean"):
            path = ROOT / "generated-original/Funs.lean"
        elif rel == "generated/translation.json":
            path = ROOT / "source-inputs/r364-translation.json"
        if not path.is_file() or sha(path.read_bytes()) != expected_hash:
            failures.append(f"R364 generated output hash mismatch: {rel}")

    for source in inventory["source_provenance"]["pinned_aeneas_sources"]:
        path = ROOT / source["path"]
        if not path.is_file() or sha(path.read_bytes()) != source["sha256"] or path.stat().st_size != source["bytes"]:
            failures.append(f"pinned Aeneas source copy mismatch: {source['path']}")

    census = load("static-census/census.json")
    if census["llbc"]["sha256"] != result["source_sha256"] or not census["llbc"]["expected_root_funs_present"]:
        failures.append("saved static census does not identify the R364 input/root functions")

    good_runs = inventory["successful_focus_runs"]
    bad_runs = inventory["failed_focus_runs"]
    successful_reports: list[str] = []
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for rec in good_runs + bad_runs:
        source = ROOT / rec["source_snapshot"]
        log = ROOT / rec["log"]
        receipt = ROOT / rec["receipt"]
        raw_receipt = json.loads(receipt.read_text())
        if not source.is_file() or sha(source.read_bytes()) != rec["source_sha256"]:
            failures.append(f"run source snapshot mismatch: {rec['id']}")
        if not log.is_file() or sha(log.read_bytes()) != rec["log_sha256"]:
            failures.append(f"run log mismatch: {rec['id']}")
        if raw_receipt["source_sha256"] != rec["source_sha256"] or raw_receipt["exit_status"] != rec["exit_status"]:
            failures.append(f"run receipt mismatch: {rec['id']}")
        if raw_receipt.get("source_revision") != rec["source_revision"]:
            failures.append(f"run source revision mismatch: {rec['id']}")
        for key in ("wall_time", "peak_rss_kib", "swaps", "resources", "measurement_boundary"):
            if raw_receipt.get(key) != rec.get(key):
                failures.append(f"receipt/inventory {key} mismatch: {rec['id']}")
        run_text = log.read_text() if log.is_file() else ""
        for key, pattern in (
            ("wall_time", r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)"),
            ("peak_rss_kib", r"Maximum resident set size \(kbytes\): (\d+)"),
            ("swaps", r"Swaps: (\d+)"),
            ("exit_status", r"Exit status: (\d+)"),
        ):
            match = re.search(pattern, run_text)
            value = (match[1] if key == "wall_time" else int(match[1])) if match else None
            if value != raw_receipt.get(key):
                failures.append(f"raw log/receipt {key} mismatch: {rec['id']}")
        res = rec["resources"]
        if res.get("MemoryHigh") != "5G" or res.get("MemoryMax") != "7G" or res.get("MemorySwapMax") != 0 or res.get("TasksMax") != 128 or res.get("lean_flags") != "-j1 -M4500":
            failures.append(f"resource cap or Lean flag mismatch: {rec['id']}")
        if rec["exit_status"] == 0:
            reports = re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", run_text)
            successful_reports.extend(reports)
            if "sorryAx" in "\n".join(reports):
                failures.append(f"sorryAx in successful run: {rec['id']}")
            printed = re.findall(r"'([^']+)' (?:depends on axioms: \[([\s\S]*?)\]|does not depend on any axioms)", run_text)
            requests = re.findall(r"^#print axioms\s+(.+?)\s*$", source.read_text(), re.M)
            if len(printed) != len(requests) or any(
                not (actual == requested or actual.endswith("." + requested))
                for (actual, _), requested in zip(printed, requests)
            ):
                failures.append(f"print request/report names differ: {rec['id']}")
            for name, axiom_text in printed:
                found = {x.strip() for x in axiom_text.replace("\n", " ").split(",") if x.strip()}
                if not found <= allowed_axioms:
                    failures.append(f"non-foundational axiom in {rec['id']} report {name}: {sorted(found - allowed_axioms)}")
            if len(printed) != len(requests):
                failures.append(f"print request/report count differs: {rec['id']}")

    if len(good_runs) != 3 or len(bad_runs) != 4:
        failures.append("expected three green and four preserved failed compile runs")
    expected_run_metrics = {
        "1790947119067298000": (1, "0:00.10", 185148, 0),
        "1790947438169868000": (0, "0:01.07", 2539084, 0),
        "1790947446157516000": (1, "0:00.97", 2520192, 0),
        "1790947675392238000": (0, "0:01.01", 2528224, 0),
        "1790947712215689000": (1, "0:00.98", 2519256, 0),
        "1790947737342504000": (1, "0:00.99", 2517192, 0),
        "1790947761471380000": (0, "0:01.02", 2530812, 0),
    }
    seen = {r["id"]: r for r in good_runs + bad_runs}
    for run_id, expected_metric in expected_run_metrics.items():
        r = seen.get(run_id)
        if r is None or (r["exit_status"], r["wall_time"], r["peak_rss_kib"], r["swaps"]) != expected_metric:
            failures.append(f"status/resource metrics mismatch: {run_id}")
        elif json.loads((ROOT / r["receipt"]).read_text()).get("runner_sha256") != inventory["runner"]["sha256"]:
            failures.append(f"runner SHA mismatch: {run_id}")
        elif json.loads((ROOT / r["receipt"]).read_text()).get("source_revision") != r["source_revision"]:
            failures.append(f"source revision receipt mismatch: {run_id}")
    if len(successful_reports) != 10:
        failures.append(f"expected 10 successful axiom reports; found {len(successful_reports)}")
    if successful_reports != source_audit["complete_good_axiom_reports"]:
        failures.append("complete successful axiom report set differs from source audit")
    if len(target_checks) != 3 or not all(target_checks):
        failures.append("one or more target copies differ")

    summary = {
        "status": "PASS" if not failures else "FAIL",
        "evidence_root": str(ROOT),
        "checksum_files": len(expected),
        "target_byte_identity": all(target_checks),
        "generated_source_reconstruction": source_reconstruction,
        "green_runs": len(good_runs),
        "failed_runs_preserved": len(bad_runs),
        "successful_axiom_reports": len(successful_reports),
        "failures": failures,
    }
    print(json.dumps(summary, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
