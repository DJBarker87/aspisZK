#!/usr/bin/env python3
"""Read-only clone-portable receipt for the failed and green afterstate leaves."""
import argparse
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import audit_selected_semantic_append_residuals as predecessor

util = predecessor.util
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
RECORD = HERE / "selected-semantic-afterstate-checks-evidence.json"
PARENT = "8761cd89ab7ccea779ef4a9f86fa415d670bd16d"
ATTEMPTS = [
    ("selected-semantic-afterstate-checks-nuc-v1", "SelectedSemanticAfterstateChecks", 1, 1059,
     "named carry row if-branch and Fin proof-witness conversion"),
    ("selected-semantic-afterstate-checks-v2-nuc-v1", "SelectedSemanticAfterstateChecksV2", 0, 1061,
     "green explicit row equality and Fin.ext frontier transport"),
]
SOURCE_HASHES = {
    "docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs": "bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc",
    "docs/research/v8-no-work-100-20260907/experiments/complete_callback.rs": "aaf776171df5bbab9e3f18339990acb857092b59be9d84d7f5fd948254394419",
    "docs/research/v8-no-work-100-20260907/experiments/complete_binding.rs": "d35d46ac4b0128de04a333377e1d6dc801de313dce6111e3e820d3384cd9a360",
    "docs/research/v8-no-work-100-20260907/experiments/complete-integration.patch": "677e9ff8ae0c09e2ecc9b09a04702323726fb632f7eaa6156e76e5eccf39301b",
    "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs": "4577c435a5c41a147331ca7d42b65053e181d58dca1b4322ef96b48c85babf77",
    "programs/aspis-pool/src/pair_forest.rs": "d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30",
    "programs/aspis-pool/src/pair_forest_dispatch.rs": "7e45910a3d64e328dc234ede290119770e898bcb48f277d978219740ec891514",
    "AspisFormal/AspisFormal/Pool/V7EightLaneCompactDispatch.lean": "41bbb65b7eb6344801cea6659dc5eb5ec221c2141e07f85bffb1fbb0962b52ee",
    "AspisFormal/AspisFormal/Pool/V7PairCallerLiveSnapshotGate.lean": "9fc74c036b4f692114288585a8d3daff3e53f6c8282280133375d8c82c5abb3d",
}


def collect():
    previous = predecessor.collect()
    assert previous == json.loads(predecessor.RECORD.read_text()), "predecessor receipt changed"
    boundary = dict(previous["imported_green_boundary"])
    green = [attempt for attempt in previous["attempts"] if attempt["exit"] == 0]
    assert len(green) == 1
    prior_green = green[0]
    boundary[prior_green["target"]] = {
        "source_sha256": prior_green["source_sha256"], "olean_sha256": prior_green["olean_sha256"]}
    for path, digest in SOURCE_HASHES.items():
        assert util.sha(ROOT / path) == digest, path
    results = []
    for tag, target, expected_exit, expected_entries, classification in ATTEMPTS:
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
        assert len(manifest["files"]) == expected_entries
        assert checks == ([str(expected_entries)] * (2 if expected_exit == 0 else 1))
        target_sources = [entry for entry in manifest["files"]
                          if entry["module"] == target and entry["kind"] == "source"]
        assert len(target_sources) == 1 and target_sources[0]["sha256"] == source_hash
        assert re.findall(r"^import (\w+)$", source.read_text(), re.MULTILINE) == [prior_green["target"]]
        for module, hashes in boundary.items():
            for suffix, expected in [(".lean", hashes["source_sha256"]), (".olean", hashes["olean_sha256"])]:
                matches = [entry for entry in manifest["files"]
                           if entry["module"] == module and entry["overlay"].endswith(suffix)]
                assert len(matches) == 1 and matches[0]["sha256"] == expected, (module, suffix)
        audits = [{"declaration": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
                  for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)]
        requested = re.findall(r"^#print axioms (\w+)$", source.read_text(), re.MULTILINE)
        assert len(audits) == len(requested) == 8
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
                        "swaps": swaps, "command": command, "manifest_entries": expected_entries,
                        "postflight_unchanged": expected_exit == 0, "audits": audits})
    assert results[0]["source_sha256"] != results[1]["source_sha256"]
    return {
        "schema": 1, "source_parent": PARENT, "runner_bootstrap_parent": util.BOOTSTRAP,
        "borrowed_source_pin": util.BORROWED, "runner_sha256": util.RUNNER,
        "audit_sha256": util.sha(Path(__file__)),
        "report_sha256": util.sha(HERE.parent / "selected-semantic-afterstate-checks-review.md"),
        "prior_audit_sha256": util.sha(Path(predecessor.__file__)),
        "prior_evidence_sha256": util.sha(predecessor.RECORD),
        "green_audits": 8, "attempts": results, "imported_green_boundary": boundary,
        "rust_source_hashes": previous["rust_source_hashes"],
        "inspected_source_hashes": SOURCE_HASHES,
        "scope": "Same-table dynamic root/carry equations and constructed AfterstateChecks from literal source comparisons; native carry/account/runtime/accepted-to-rows correspondence remains explicit",
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
        print("PASS: two attempts retained; 8 green standard-only audits; six imported green pairs matched; optional oleans checked when present")


if __name__ == "__main__":
    main()
