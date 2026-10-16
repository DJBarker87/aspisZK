#!/usr/bin/env python3
"""Read-only preflight / archive-only collector for the 15-target mask batch.

Run on the pinned NUC workspace. Default action is --preflight; --collect is
explicit and should only be used after the batch is green and authorized.
"""
from pathlib import Path
import argparse
import hashlib
import json
import tarfile

WORKSPACE = Path("/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015")
BUNDLE_NAME = "full-mask-coefficients"
MODULES = [
    "ExtractedMaskCoefficientArray",
    "ExtractedMaskCoefficientSchedule",
    "ExtractedMaskCoefficientStep",
    "ExtractedMaskForwardRange",
    "ExtractedMaskCoefficientLoop0",
    "ExtractedMaskCoefficientLoop1",
    "ExtractedMaskLinearsExact",
    "ExtractedMaskConstants",
    "ExtractedMaskCallerModel",
    "ExtractedMaskCoefficientDecode",
    "ExtractedMaskCoefficientScheduledSum",
    "ExtractedMaskCoefficientWriteMeaning",
    "ExtractedMaskCoefficientLoopMeaning",
    "ExtractedMaskPopulatedMeaning",
    "ExtractedMaskLinearMap",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_CGROUP = {
    "MemoryHigh": "4G", "MemoryMax": "6G", "MemorySwapMax": "0", "TasksMax": 128
}
# Preserve the historical receipt as written. It sampled an uncompiled draft's
# source next to the unchanged, successful h object. Reconcile only this exact
# case by the h receipt and snapshot; do not silently relabel the old receipt.
CALLER_RECONCILIATION = {
    "consumer": "ExtractedMaskPopulatedMeaning",
    "dependency": "ExtractedMaskCallerModel",
    "recorded_source_sha256": "876ed33b687f67d37772e44d507d58a09f2edfed9e4759e33a5bb59cd70af021",
    "compiled_source_sha256": "4e675d196e7d3c281674d440aa8d92c554cc9d29249cb2ad0e85d27121d12e1c",
    "object_sha256": "5c9fdf5d1634d3731c3b6344b2947990c0fee51ec677f33374b881f79678c631",
}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def attempt_inventory(workspace: Path):
    rows = []
    selected = {}
    all_files = set()
    for module in MODULES:
        dirs = sorted(p for p in (workspace / "attempts").glob(f"*-{module}") if p.is_dir())
        if not dirs:
            rows.append({"module": module, "state": "no_attempts"})
            continue
        receipts = []
        attempt_summaries = []
        for directory in dirs:
            # Keep the complete attempt tree even if the runner failed before
            # writing its receipt; missing receipts remain explicitly classified.
            all_files.update(q for q in directory.rglob("*") if q.is_file())
            receipt_path = directory / "receipt.json"
            if not receipt_path.is_file():
                attempt_summaries.append({
                    "attempt_dir": directory.name,
                    "state": "missing_receipt",
                    "receipt_path": str(receipt_path),
                })
                rows.append({"module": module, "attempt": directory.name, "state": "missing_receipt"})
                continue
            receipt = json.loads(receipt_path.read_text())
            receipts.append((directory, receipt))
            attempt_summaries.append({
                "attempt_dir": directory.name,
                "state": "receipt_present",
                "exit_status": receipt.get("exit_status"),
                "source_sha256": receipt.get("source_sha256"),
                "wall_seconds": receipt.get("controller_elapsed_wall_seconds"),
                "peak_rss_kib": receipt.get("max_rss_kib"),
                "swaps": receipt.get("process_swaps"),
                "axiom_report_count": receipt.get("axiom_report_count"),
            })
        source_path = workspace / "sources" / f"{module}.lean"
        current_sha = sha(source_path) if source_path.is_file() else None
        green_matches = []
        for directory, receipt in receipts:
            if receipt.get("exit_status") == 0 and current_sha and receipt.get("source_sha256") == current_sha:
                green_matches.append((directory, receipt))
        row = {
            "module": module,
            "attempt_count": len(dirs),
            "attempts": attempt_summaries,
            "current_source_path": str(source_path),
            "current_source_sha256": current_sha,
            "current_source_exists": source_path.is_file(),
            "successful_receipts_matching_current_source": len(green_matches),
            "state": "ready" if len(green_matches) == 1 else "pending_or_ambiguous",
        }
        rows.append(row)
        if len(green_matches) == 1:
            selected[module] = green_matches[0]
    return rows, selected, all_files


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workspace", type=Path, default=WORKSPACE)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--preflight", action="store_true", help="read manifests and receipts only (default)")
    mode.add_argument("--collect", action="store_true", help="create summary and archive; run only when authorized")
    parser.add_argument("--collector-path", type=Path, help="copy of this script already retained in workspace")
    args = parser.parse_args()
    workspace = args.workspace
    rows, selected, attempts_files = attempt_inventory(workspace)
    ready = len(selected) == len(MODULES)
    if not args.collect:
        print(json.dumps({
            "mode": "preflight_read_only", "workspace": str(workspace),
            "target_count": len(MODULES), "ready_target_count": len(selected),
            "targets": rows,
            "source_kit_manifest_exists": (workspace / "source-kit/manifest.json").is_file(),
            "environment_files": [p.name for p in workspace.glob("environment*.json") if p.is_file()],
            "runner_files": [p.name for p in workspace.glob("*.py") if p.is_file()],
        }, indent=2))
        return 0 if ready else 2

    if not ready:
        raise SystemExit(f"refusing collection: only {len(selected)}/{len(MODULES)} targets have one current-source-matching green")
    source_manifest_path = workspace / "source-kit/manifest.json"
    environment_path = workspace / "environment.json"
    if not source_manifest_path.is_file() or not environment_path.is_file():
        raise SystemExit("refusing collection: source-kit/manifest.json or environment.json is missing")

    files = set(attempts_files)
    manifest = json.loads(source_manifest_path.read_text())
    environment = json.loads(environment_path.read_text())
    for relroot in ("source-kit", "evidence"):
        root = workspace / relroot
        if root.is_dir():
            files.update(p for p in root.rglob("*") if p.is_file())
    files.update(p for p in workspace.glob("environment*.json") if p.is_file())
    files.update(p for p in workspace.glob("*.py") if p.is_file())
    files.update(p for p in workspace.glob("*.sh") if p.is_file())
    if args.collector_path and args.collector_path.is_file():
        files.add(args.collector_path)

    target_rows = []
    green_axioms = 0
    reconciliations = []
    for module, (attempt_dir, receipt) in selected.items():
        source = Path(receipt["source_path"])
        snapshot = Path(receipt["snapshot_path"])
        output = Path(receipt["output_path"])
        assert source.is_file() and snapshot.is_file() and output.is_file(), module
        assert sha(source) == sha(snapshot) == receipt["source_sha256"], module
        assert sha(output) == receipt["output_sha256"], module
        assert receipt.get("source_unchanged_after") is True, module
        assert receipt.get("process_swaps") == 0, module
        assert receipt.get("cgroup") == EXPECTED_CGROUP, module
        reports = receipt.get("axiom_reports", [])
        assert len(reports) == receipt.get("axiom_report_count"), module
        assert all(set(a.get("axioms", [])) <= ALLOWED_AXIOMS for a in reports), module
        green_axioms += len(reports)
        files.add(source)
        files.add(output)
        for companion in (Path(str(output)+".private"), Path(str(output)+".server"), output.with_suffix(".ir")):
            if companion.is_file():
                files.add(companion)
        imports = []
        for dep in receipt.get("direct_imports", []):
            obj = Path(dep["object_path"])
            assert obj.is_file() and sha(obj) == dep["object_sha256"], (module, dep.get("module"))
            files.add(obj)
            imp = {"module": dep.get("module"), "object_sha256": dep["object_sha256"]}
            if dep.get("source_path"):
                imp_source = Path(dep["source_path"])
                assert imp_source.is_file(), (module, dep.get("module"))
                actual_source_sha = sha(imp_source)
                if actual_source_sha != dep["source_sha256"]:
                    fix = CALLER_RECONCILIATION
                    assert module == fix["consumer"] and dep["module"] == fix["dependency"]
                    assert receipt["attempt"] == "populated-meaning-i"
                    assert dep["source_sha256"] == fix["recorded_source_sha256"]
                    assert actual_source_sha == fix["compiled_source_sha256"]
                    assert dep["object_sha256"] == fix["object_sha256"]
                    dep_dir, dep_receipt = selected[dep["module"]]
                    assert dep_receipt["attempt"] == "caller-model-h"
                    assert dep_receipt["source_sha256"] == actual_source_sha
                    assert dep_receipt["output_sha256"] == dep["object_sha256"]
                    assert sha(Path(dep_receipt["snapshot_path"])) == actual_source_sha
                    variant = workspace / "attempts/caller-model-i-ExtractedMaskCallerModel/uncompiled-variant-preserved.lean"
                    assert variant.is_file() and sha(variant) == dep["source_sha256"]
                    files.add(variant)
                    reconciliation = dict(fix, consumer_receipt=str(attempt_dir / "receipt.json"),
                        dependency_receipt=str(dep_dir / "receipt.json"),
                        preserved_uncompiled_source=str(variant),
                        disposition="Imported object matches exact successful h source and snapshot; historical receipt source pin was an uncompiled draft. Original receipts unchanged; no replay.")
                    reconciliations.append(reconciliation)
                    imp["recorded_source_sha256"] = dep["source_sha256"]
                    imp["source_pin_reconciled_by_dependency_receipt"] = True
                files.add(imp_source)
                imp["source_sha256"] = actual_source_sha
            imports.append(imp)
        target_rows.append({
            "module": module, "attempt": receipt["attempt"], "attempt_dir": attempt_dir.name,
            "exit_status": receipt["exit_status"], "source_sha256": receipt["source_sha256"],
            "object_sha256": receipt["output_sha256"],
            "wall_seconds": receipt["controller_elapsed_wall_seconds"],
            "peak_rss_kib": receipt["max_rss_kib"], "swaps": receipt["process_swaps"],
            "axiom_report_count": len(reports), "axiom_reports": reports,
            "direct_imports": imports, "runner_hashes": receipt.get("runner_hashes"),
            "cgroup": receipt.get("cgroup"),
        })

    # Preserve every failed/superseded attempt in the archive, but only current-source
    # matching green receipts appear as final target rows above.
    archive_names = {}
    for path in files:
        try:
            archive_names[path] = str(path.relative_to(workspace))
        except ValueError:
            # Preserve path identity for external cache pins without collisions
            # between equal basenames in different toolchain directories.
            path_key = hashlib.sha256(str(path).encode()).hexdigest()[:16]
            archive_names[path] = f"external-pins/{path_key}/{path.name}"
    summary = {
        "bundle": "lean-full-mask-coefficients-20261016",
        "scope": "Fifteen focused Lean 4.32 extracted-mask coefficient and full-mask composition targets; no full protocol or Rust source-refinement claim.",
        "source_revision": manifest.get("source_revision"),
        "environment_revision": environment.get("source_revision"),
        "target_count": len(target_rows), "attempt_count": sum(r.get("attempt_count", 0) for r in rows),
        "axiom_report_count_green_only": green_axioms,
        "green_axioms_standard_only": True,
        "green_controller_wall_seconds_sum": round(sum(r["wall_seconds"] for r in target_rows), 3),
        "green_max_target_peak_rss_kib": max(r["peak_rss_kib"] for r in target_rows),
        "green_process_swaps_total": sum(r["swaps"] for r in target_rows),
        "import_source_pin_reconciliations": reconciliations,
        "targets": target_rows,
        "attempts": rows,
        "archived_files": [{"path": archive_names[p], "sha256": sha(p), "bytes": p.stat().st_size} for p in sorted(files)],
    }
    summary_path = workspace / f"{BUNDLE_NAME}-summary.json"
    archive_path = workspace / f"{BUNDLE_NAME}-evidence-20261016.tar.gz"
    if summary_path.exists() or archive_path.exists():
        raise SystemExit("refusing overwrite of existing summary/archive")
    summary_path.write_text(json.dumps(summary, indent=2) + "\n")
    files.add(summary_path)
    archive_names[summary_path] = str(summary_path.relative_to(workspace))
    with tarfile.open(archive_path, "w:gz", compresslevel=6) as archive:
        for path in sorted(files):
            archive.add(path, arcname=archive_names[path], recursive=False)
    print(json.dumps({"summary": str(summary_path), "summary_sha256": sha(summary_path),
                      "archive": str(archive_path), "archive_sha256": sha(archive_path),
                      "archive_bytes": archive_path.stat().st_size, "targets": len(target_rows),
                      "green_axiom_reports": green_axioms}, indent=2))


if __name__ == "__main__":
    main()
