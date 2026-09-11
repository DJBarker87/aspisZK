#!/usr/bin/env python3
"""Read-only, clone-portable focused output-transition evidence check."""
import argparse
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import audit_selected_semantic_transfer as prior

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TARGET = "SelectedSemanticOutputTransition"
TAG = "selected-semantic-output-transition-nuc-v1"
PARENT = "d879105131a34a4bd087409bced83778d3ea8a96"
RECORD = HERE / "selected-semantic-output-transition-evidence.json"
SOURCE_HASHES = {
    "pair_forest_copy_terminal_constants.rs": "cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50",
    "pair_tree_profile.rs": "8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2",
    "pair_trace.rs": "80290c5af3e8102da8e43efbadccfde745af272c2bfb046a919d5ce4da9f9371",
    "pair_forest_trace.rs": "0a97cbba7740acf44e3b85082ff917e6fb60b81a26662a2d7f96acaf0e72309d",
    "pair_forest_semantic_terminal.rs": "efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58",
}


def collect():
    previous = prior.collect()
    assert previous == json.loads(prior.RECORD.read_text()), "prior evidence changed"
    source = HERE / (TARGET + ".lean")
    snapshot = HERE / (TAG + "-source.txt")
    log_path = HERE / (TAG + ".log")
    manifest_path = HERE / (TAG + "-manifest.json")
    text = log_path.read_text()
    manifest = json.loads(manifest_path.read_text())
    digest = prior.sha(source)
    assert prior.sha(snapshot) == digest
    assert prior.one(r"^TARGET=(\w+)$", text) == TARGET
    assert prior.one(r"^LEAN_EXIT=(\d+)$", text) == "0"
    assert manifest["research"] == prior.BOOTSTRAP and manifest["borrowed"] == prior.BORROWED
    for value in [digest, prior.sha(manifest_path), prior.RUNNER]:
        assert value + "  " in text
    for setting in ["memory.high=8589934592", "memory.max=10737418240",
                    "memory.swap.max=0", "cpu.max=200000 100000",
                    "PROVENANCE_UNCHANGED=true"]:
        assert setting in text
    checks = re.findall(r"^OVERLAY_PROVENANCE_PASS=(\d+)$", text, re.MULTILINE)
    assert checks == ["1049", "1049"] and len(manifest["files"]) == 1049
    assert "sorryAx" not in text and "error:" not in text
    audits = [{"declaration": name, "axioms": [a.strip() for a in axioms.split(",") if a.strip()]}
              for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text)]
    requested = re.findall(r"^#print axioms (\w+)$", source.read_text(), re.MULTILINE)
    assert len(audits) == len(requested) == 10
    assert [a["declaration"].split(".")[-1] for a in audits] == requested
    assert all(set(a["axioms"]) <= prior.STANDARD for a in audits)
    command = prior.one(r"^COMMAND=(.+)$", text)
    assert " -j1 -M9500 " in command and command.endswith(f"/overlay/{TARGET}.lean")
    target_sources = [f for f in manifest["files"] if f["module"] == TARGET and f["kind"] == "source"]
    assert len(target_sources) == 1 and target_sources[0]["sha256"] == digest
    imports = re.findall(r"^import (\w+)$", source.read_text(), re.MULTILINE)
    assert imports == ["SelectedSemanticTransferV2"]
    # Match the imported retained four-leaf boundary, not just an unverified
    # file with the right module name. This is still not a cold closure replay.
    imported = {}
    for entry in previous["attempts"]:
        if entry["exit"] != 0:
            continue
        module = entry["target"]
        for suffix, expected in [(".lean", entry["source_sha256"]), (".olean", entry["output_sha256"])]:
            matches = [f for f in manifest["files"] if f["module"] == module and f["overlay"].endswith(suffix)]
            assert len(matches) == 1 and matches[0]["sha256"] == expected, (module, suffix)
        imported[module] = {"source_sha256": entry["source_sha256"], "olean_sha256": entry["output_sha256"]}
    output_hash = prior.one(rf"^([0-9a-f]{{64}})  .*/overlay/{TARGET}\.olean$", text)
    output = HERE / (TARGET + ".olean")
    if output.exists():
        assert prior.sha(output) == output_hash
    for filename, expected in SOURCE_HASHES.items():
        assert prior.sha(ROOT / "crates/aspis-statement/src/pool_v1" / filename) == expected
    swaps = int(prior.one(r"^\s*Swaps: (\d+)$", text))
    assert swaps == 0
    return {
        "schema": 1, "target": TARGET, "tag": TAG, "source_parent": PARENT,
        "runner_bootstrap_parent": prior.BOOTSTRAP, "borrowed_source_pin": prior.BORROWED,
        "runner_sha256": prior.RUNNER, "source_sha256": digest,
        "snapshot_sha256": prior.sha(snapshot), "log_sha256": prior.sha(log_path),
        "manifest_sha256": prior.sha(manifest_path), "olean_sha256": output_hash,
        "audit_sha256": prior.sha(Path(__file__)), "prior_audit_sha256": prior.sha(Path(prior.__file__)),
        "prior_evidence_sha256": prior.sha(prior.RECORD),
        "report_sha256": prior.sha(HERE.parent / "selected-semantic-output-transition-review.md"),
        "exit": 0, "wall": prior.one(r"^\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)$", text),
        "peak_rss_kib": int(prior.one(r"^\s*Maximum resident set size \(kbytes\): (\d+)$", text)),
        "swaps": swaps, "command": command, "audits": audits,
        "manifest_entries": 1049, "imported_green_boundary": imported,
        "rust_source_hashes": SOURCE_HASHES,
        "scope": "Same-table checked field-stage output pair and explicit-premise append transition; not acceptance, authenticated membership or complete settlement",
        "clone_policy": "Retained sources/logs/manifests/JSON are mandatory; ignored local oleans are checked only when present",
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
        print("PASS: output transition, 10 standard-only audits; prior four green artifacts matched; optional oleans checked when present")


if __name__ == "__main__":
    main()
