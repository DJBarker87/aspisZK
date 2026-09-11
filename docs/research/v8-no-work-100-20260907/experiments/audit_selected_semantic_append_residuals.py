#!/usr/bin/env python3
"""Read-only clone-portable receipt for the failed and green append leaves."""
import argparse
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import audit_selected_semantic_output_transition as predecessor

util = predecessor.prior
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RECORD = HERE / "selected-semantic-append-residuals-evidence.json"
PARENT = "d879105131a34a4bd087409bced83778d3ea8a96"
ATTEMPTS = [
    ("selected-semantic-append-residuals-nuc-v1", "SelectedSemanticAppendResiduals", 1,
     "finite-sum guard simplification and off-diagonal equality normalization"),
    ("selected-semantic-append-residuals-v2-nuc-v1", "SelectedSemanticAppendResidualsV2", 0,
     "green symbolic sum rewrite and exact row-inequality simplification"),
]


def static_source_check():
    path = ROOT / "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs"
    text = path.read_text()
    pattern = (r"CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), "
               r"producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, "
               r"consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}")
    links = [tuple(map(int, values)) for values in re.findall(pattern, text)]
    assert len(links) == 136
    for level in range(20):
        assert links[24 + 2 * level] == (1124073496 + 2 * level, 3, level,
                                       539 + 16 * level, 0, 1, 556 + 16 * level, 0, 1)
        assert links[25 + 2 * level] == (1124073497 + 2 * level, 4, level,
                                       539 + 16 * level, 1, 1, 544 + 16 * level, 0, 10)
    # Tiny metadata arithmetic, not a field/probability/runtime release gate.
    empty = {16 * (34 + level) for level in range(20)}
    live = {16 * (34 + level) + 12 for level in range(20)}
    other = {907, 427, 475, 523, 859} | {16 * (33 + carry) + 11 for carry in range(20)}
    assert len(empty) == len(live) == 20
    assert not empty & live and not (empty | live) & other
    return {"literal_registry_entries": 136, "checked_append_links": 40,
            "sibling_rows": 40, "disjoint_public_and_carry_selectors": True,
            "scope": "source metadata only; kernel proofs establish symbolic row isolation"}


def collect():
    previous = predecessor.collect()
    assert previous == json.loads(predecessor.RECORD.read_text()), "predecessor receipt changed"
    boundary = dict(previous["imported_green_boundary"])
    boundary[previous["target"]] = {
        "source_sha256": previous["source_sha256"], "olean_sha256": previous["olean_sha256"]}
    results = []
    for tag, target, expected_exit, classification in ATTEMPTS:
        source = HERE / (target + ".lean")
        snapshot = HERE / (tag + "-source.txt")
        log = HERE / (tag + ".log")
        manifest_path = HERE / (tag + "-manifest.json")
        source_hash = util.sha(source)
        assert util.sha(snapshot) == source_hash
        text = log.read_text()
        manifest = json.loads(manifest_path.read_text())
        assert util.one(r"^TARGET=(\w+)$", text) == target
        assert int(util.one(r"^LEAN_EXIT=(\d+)$", text)) == expected_exit
        assert manifest["research"] == util.BOOTSTRAP and manifest["borrowed"] == util.BORROWED
        assert f"RESEARCH_PIN={util.BOOTSTRAP}" in text
        assert f"BORROWED_SOURCE_PIN={util.BORROWED}" in text
        for value in [source_hash, util.sha(manifest_path), util.RUNNER]:
            assert value + "  " in text
        for setting in ["memory.high=8589934592", "memory.max=10737418240",
                        "memory.swap.max=0", "cpu.max=200000 100000"]:
            assert setting in text
        checks = re.findall(r"^OVERLAY_PROVENANCE_PASS=(\d+)$", text, re.MULTILINE)
        assert len(manifest["files"]) == 1055
        assert checks == (["1055", "1055"] if expected_exit == 0 else ["1055"])
        target_sources = [entry for entry in manifest["files"]
                          if entry["module"] == target and entry["kind"] == "source"]
        assert len(target_sources) == 1 and target_sources[0]["sha256"] == source_hash
        assert re.findall(r"^import (\w+)$", source.read_text(), re.MULTILINE) == [previous["target"]]
        for module, hashes in boundary.items():
            for suffix, expected in [(".lean", hashes["source_sha256"]), (".olean", hashes["olean_sha256"])]:
                matches = [entry for entry in manifest["files"]
                           if entry["module"] == module and entry["overlay"].endswith(suffix)]
                assert len(matches) == 1 and matches[0]["sha256"] == expected, (module, suffix)
        audits = [{"declaration": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
                  for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)]
        requested = re.findall(r"^#print axioms (\w+)$", source.read_text(), re.MULTILINE)
        assert len(audits) == len(requested) == 10
        assert [entry["declaration"].split(".")[-1] for entry in audits] == requested
        command = util.one(r"^COMMAND=(.+)$", text)
        assert " -j1 -M9500 " in command and command.endswith(f"/overlay/{target}.lean")
        output_hash = None
        if expected_exit == 0:
            assert "error:" not in text and "sorryAx" not in text
            assert "PROVENANCE_UNCHANGED=true" in text
            assert all(set(entry["axioms"]) <= util.STANDARD for entry in audits)
            output_hash = util.one(rf"^([0-9a-f]{{64}})  .*/overlay/{target}\.olean$", text)
            output = HERE / (target + ".olean")
            if output.exists():
                assert util.sha(output) == output_hash
        else:
            assert "error: unsolved goals" in text and "sorryAx" in text
            assert "PROVENANCE_UNCHANGED=true" not in text
        swaps = int(util.one(r"^\s*Swaps: (\d+)$", text))
        assert swaps == 0
        results.append({"tag": tag, "target": target, "exit": expected_exit,
                        "classification": classification, "source_sha256": source_hash,
                        "snapshot_sha256": util.sha(snapshot), "log_sha256": util.sha(log),
                        "manifest_sha256": util.sha(manifest_path), "olean_sha256": output_hash,
                        "wall": util.one(r"^\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)$", text),
                        "peak_rss_kib": int(util.one(r"^\s*Maximum resident set size \(kbytes\): (\d+)$", text)),
                        "swaps": swaps, "command": command, "manifest_entries": 1055,
                        "postflight_unchanged": expected_exit == 0, "audits": audits})
    assert results[0]["source_sha256"] != results[1]["source_sha256"]
    return {
        "schema": 1, "source_parent": PARENT, "runner_bootstrap_parent": util.BOOTSTRAP,
        "borrowed_source_pin": util.BORROWED, "runner_sha256": util.RUNNER,
        "audit_sha256": util.sha(Path(__file__)),
        "report_sha256": util.sha(HERE.parent / "selected-semantic-append-residuals-review.md"),
        "prior_audit_sha256": util.sha(Path(predecessor.__file__)),
        "prior_evidence_sha256": util.sha(predecessor.RECORD),
        "green_audits": 10, "attempts": results, "imported_green_boundary": boundary,
        "rust_source_hashes": previous["rust_source_hashes"],
        "static_source_metadata": static_source_check(),
        "scope": "Same-table AppendResiduals derived from complete semantic rows, actual selected copy aliases and PoseidonChecks; direct AfterstateChecks/authentication/acceptance remain explicit",
        "cache_boundary": "Pinned imported source/olean artifacts and native package revisions; not a cold replay",
        "clone_policy": "Retained sources/snapshots/logs/manifests/JSON mandatory; ignored local oleans checked only when present",
    }


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-recorded", action="store_true")
    mode.add_argument("--emit-record", action="store_true")
    args = parser.parse_args()
    value = collect()
    if args.emit_record:
        print(json.dumps(value, indent=2, sort_keys=True))
    else:
        assert value == json.loads(RECORD.read_text()), "record differs from retained evidence"
        print("PASS: two attempts retained; 10 green standard-only audits; five imported green pairs matched; 40 source links checked; optional oleans checked when present")


if __name__ == "__main__":
    main()
