#!/usr/bin/env python3
"""Read-only, clone-portable audit of the nine retained focused attempts."""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECORD = HERE / "selected-semantic-transfer-evidence.json"
PARENT = "2f92bdd5f08fa89060c85262a55c19545a002064"
BOOTSTRAP = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
RUNNER = "5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# tag, target, exit, green audit count, classification
ATTEMPTS = [
    ("selected-semantic-rows-nuc-v1", "SelectedSemanticRows", 1, 0, "missing SelectedAppendAfterstate artifact"),
    ("selected-append-afterstate-nuc-v1", "SelectedAppendAfterstate", 1, 0, "missing SelectedOutputPair artifact"),
    ("selected-output-pair-nuc-v1", "SelectedOutputPair", 0, 12, "unchanged missing dependency focused check"),
    ("selected-append-afterstate-nuc-v2", "SelectedAppendAfterstate", 0, 11, "unchanged missing dependency focused check"),
    ("selected-semantic-rows-nuc-v2", "SelectedSemanticRows", 1, 0, "reserved binder and concrete cardinality reduction"),
    ("selected-semantic-rows-v2-nuc-v1", "SelectedSemanticRowsV2", 1, 0, "deep concrete row projection"),
    ("selected-semantic-rows-v3-nuc-v1", "SelectedSemanticRowsV3", 0, 11, "green new oracle"),
    ("selected-semantic-transfer-nuc-v1", "SelectedSemanticTransfer", 1, 0, "ambiguous residual and branch/index glue"),
    ("selected-semantic-transfer-v2-nuc-v1", "SelectedSemanticTransferV2", 0, 14, "green new consumer"),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def one(pattern, value):
    matches = re.findall(pattern, value, re.MULTILINE)
    assert len(matches) == 1, (pattern, matches)
    return matches[0]


def collect():
    results = []
    for tag, target, expected_exit, expected_audits, classification in ATTEMPTS:
        log_path = HERE / (tag + ".log")
        snapshot = HERE / (tag + "-source.txt")
        manifest_path = HERE / (tag + "-manifest.json")
        text = log_path.read_text()
        manifest = json.loads(manifest_path.read_text())
        source = HERE / (target + ".lean")
        source_hash = sha(source)
        assert sha(snapshot) == source_hash, tag
        assert one(r"^TARGET=(\w+)$", text) == target
        assert int(one(r"^LEAN_EXIT=(\d+)$", text)) == expected_exit
        assert f"RESEARCH_PIN={BOOTSTRAP}" in text
        assert f"BORROWED_SOURCE_PIN={BORROWED}" in text
        assert manifest["research"] == BOOTSTRAP and manifest["borrowed"] == BORROWED
        assert f"{sha(manifest_path)}  " in text
        assert f"{source_hash}  " in text and f"{RUNNER}  " in text
        for setting in ["memory.high=8589934592", "memory.max=10737418240",
                        "memory.swap.max=0", "cpu.max=200000 100000"]:
            assert setting in text, (tag, setting)
        command = one(r"^COMMAND=(.+)$", text)
        assert " -j1 -M9500 " in command
        assert command.endswith(f"/overlay/{target}.lean")
        target_sources = [entry for entry in manifest["files"]
                          if entry["module"] == target and entry["kind"] == "source"]
        assert target_sources and all(entry["sha256"] == source_hash for entry in target_sources)
        audits = [{"declaration": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
                  for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)]
        output_hash = None
        optional_output = None
        if expected_exit == 0:
            assert len(audits) == expected_audits, (tag, len(audits))
            requested = re.findall(r"^#print axioms (\w+)$", source.read_text(), re.MULTILINE)
            assert [a["declaration"].split(".")[-1] for a in audits] == requested
            assert "sorryAx" not in text and "error:" not in text
            assert all(set(audit["axioms"]) <= STANDARD for audit in audits)
            assert "PROVENANCE_UNCHANGED=true" in text
            checks = re.findall(r"^OVERLAY_PROVENANCE_PASS=(\d+)$", text, re.MULTILINE)
            assert len(checks) == 2 and checks[0] == checks[1] == str(len(manifest["files"]))
            output_hash = one(rf"^([0-9a-f]{{64}})  .*/overlay/{target}\.olean$", text)
            optional_output = (target + ".olean" if target in
                               {"SelectedSemanticRowsV3", "SelectedSemanticTransferV2"}
                               else tag + "-output.olean")
            path = HERE / optional_output
            if path.exists():
                assert sha(path) == output_hash, path
        swaps = int(one(r"^\s*Swaps: (\d+)$", text))
        assert swaps == 0
        results.append({
            "tag": tag, "target": target, "classification": classification,
            "exit": expected_exit, "source_sha256": source_hash,
            "log_sha256": sha(log_path), "manifest_sha256": sha(manifest_path),
            "snapshot_sha256": sha(snapshot), "output_sha256": output_hash,
            "optional_local_output": optional_output,
            "wall": one(r"^\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)$", text),
            "peak_rss_kib": int(one(r"^\s*Maximum resident set size \(kbytes\): (\d+)$", text)),
            "swaps": swaps, "audits": audits,
            "manifest_entries": len(manifest["files"]), "command": command,
        })
    return {
        "schema": 1, "source_parent": PARENT, "runner_bootstrap_parent": BOOTSTRAP,
        "borrowed_source_pin": BORROWED, "runner_sha256": RUNNER,
        "audit_sha256": sha(Path(__file__)),
        "report_sha256": sha(HERE.parent / "selected-semantic-transfer-review.md"),
        "new_green_audits": 25, "recovered_dependency_audits": 23,
        "scope": "Boolean semantic oracle and same-table TransferFacts; not acceptance or a complete checked witness",
        "cache_boundary": "Pinned imported artifacts/native package revisions, not a replay of their compilation; old variants are not overwritten",
        "clone_policy": "Logs, source snapshots, live sources, manifests and JSON are mandatory; ignored local oleans are hash-checked only when present",
        "attempts": results,
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
        print("PASS: nine attempts; 25 new + 23 dependency standard-only green audits; optional oleans checked when present")


if __name__ == "__main__":
    main()
