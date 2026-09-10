#!/usr/bin/env python3
"""Clone-portable, read-only audit of retained output-leaf evidence.

Logs, source snapshots, manifests and the published receipts are mandatory.
Ignored local compiler/cache payloads are additional hash checks when present;
their absence neither erases their recorded hashes nor claims a new replay.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

EX = Path(__file__).resolve().parent
OUTPUT_SHA = "29caa06c61159b1b1507f987811abe68ae9cca807e2a38cddbffe31bd1025ad5"


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def json_sha(value):
    return hashlib.sha256((json.dumps(value, indent=2) + "\n").encode()).hexdigest()


def check_if_present(path, expected):
    if path.exists():
        assert sha(path) == expected, str(path)


def content():
    source = EX / "SelectedEarlyC1Outputs.lean"
    assert sha(source) == "6da1be45f88967fa924d2fbd523193b6791610407b0c4b2149c6ce0b724f36ae"
    assert source.read_text().count("#print axioms ") == 9
    output = EX / "SelectedEarlyC1Outputs.olean"
    check_if_present(output, OUTPUT_SHA)
    attempts = []
    manifests = []
    for version, status, wall, rss, audits_expected in [(1, 1, "0:00.96", 2106668, 0), (2, 0, "0:03.67", 6715072, 9)]:
        tag = "selected-early-c1-outputs-nuc-v" + str(version)
        log = (EX / (tag + ".log")).read_text()
        assert "LEAN_EXIT=" + str(status) in log
        assert "Elapsed (wall clock) time (h:mm:ss or m:ss): " + wall in log
        assert "Maximum resident set size (kbytes): " + str(rss) in log
        assert re.search(r"Swaps:\s*0\b", log)
        snapshot = EX / (tag + "-source.txt")
        assert sha(snapshot) == sha(source)
        manifest = EX / (tag + "-manifest.json")
        assert sha(manifest) in log
        manifests.append(json.loads(manifest.read_text()))
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
        assert len(audits) == audits_expected
        assert all(set(a.strip() for a in axioms.split(",") if a.strip()) <=
                   {"propext", "Classical.choice", "Quot.sound"} for _, axioms in audits)
        if status == 0:
            assert "PROVENANCE_UNCHANGED=true" in log and "OVERLAY_PROVENANCE_PASS=943" in log
            assert not re.search(r"error:|sorryAx", log)
            assert OUTPUT_SHA in log
        attempts.append({"tag": tag, "exit": status, "wall": wall, "rss_kib": rss, "swaps": 0,
                         "audits": [{"theorem": name, "axioms": [a.strip() for a in used.split(",")]} for name, used in audits],
                         "files": {suffix: sha(EX / (tag + suffix)) for suffix in [".log", "-source.txt", "-manifest.json"]}})
    cache = EX / ".early-c1-output-cache-evidence"
    cache_path = EX / "early-c1-output-cache-evidence.json"
    cache_evidence = json.loads(cache_path.read_text())
    receipt, retained = cache_evidence["receipt"], cache_evidence["retained_files"]
    # Exact original metadata bytes are committed as JSON, independently of
    # the optional local copies. Reconstruct both base manifests from the
    # mandatory per-run manifests and compare their historical hashes.
    assert json_sha(receipt) == retained["receipt.json"]
    assert json_sha(receipt["plan"]) == retained["plan.json"]
    assert receipt["status"] == "verified_copy_only_cache_append"
    assert receipt["existing_artifact_replacements"] == 0 and not receipt["compiler_launched"]
    assert len(receipt["copied"]) == 16 and len(receipt["registered"]) == 18
    assert sha(EX / "append_early_c1_output_cache.py") == receipt["helper_sha256"]
    before = dict(manifests[0], files=manifests[0]["files"][:800])
    after = dict(manifests[1], files=manifests[1]["files"][:818])
    assert json_sha(before) == receipt["base_before"] == retained["before-manifest.json"]
    assert json_sha(after) == receipt["base_after"] == retained["after-manifest.json"]
    assert receipt["green_state_unchanged"] == retained["before-green-outputs.json"]
    assert attempts[0]["files"]["-manifest.json"] == receipt["failed_run_unchanged"] == \
        retained["before-selected-early-c1-outputs-nuc-v1-manifest.json"]
    assert after["files"][:len(before["files"])] == before["files"]
    assert after["files"][800:] == receipt["registered"] == receipt["plan"]["artifacts"]
    assert receipt["after_entries"] == len(after["files"]) == 818
    indexed = {entry["overlay"]: entry for entry in manifests[1]["files"]}
    for entry in receipt["plan"]["boundary"] + receipt["registered"]:
        assert indexed[entry["overlay"]]["sha256"] == entry["sha256"]
    # Old green dependency logs are tracked and remain mandatory, unlike
    # native .trace files and compiler outputs in the ignored local cache.
    for name in ["selected-pair-cache-v1.log", "selected-forest-cache-v2.log"]:
        assert sha(EX / name) == retained[name]
        assert "LEAN_EXIT=0" in (EX / name).read_text()
    for name, digest in retained.items():
        check_if_present(cache / name, digest)
    for entry in receipt["plan"]["artifacts"]:
        check_if_present(cache / entry["overlay"], entry["sha256"])
    for entry in receipt["plan"]["provenance"]:
        assert retained[entry["staged"]] == entry["sha256"]
        check_if_present(cache / entry["staged"], entry["sha256"])
    result = {"status": "focused_green", "source_parent": "96046bac27e443a67cd4a3820d1c0801f94816fa",
              "source_sha256": sha(source), "olean_sha256": OUTPUT_SHA, "attempts": attempts,
              "audit_sha256": sha(Path(__file__)), "cache_helper_sha256": receipt["helper_sha256"],
              "cache_evidence_sha256": sha(cache_path),
              "artifact_policy": "Tracked source/logs/manifests/receipts are mandatory; ignored local olean/cache copies are verified only when present, with recorded hashes unchanged.",
              "review_sha256": sha(EX.parent / "selected-early-c1-outputs-review.md"),
              "scope": "Same-table output openings, strict amounts and unchanged collision alternative; no acceptance or own-support recovery theorem"}
    return {"early-c1-output-cache-evidence.json": cache_evidence,
            "selected-early-c1-outputs-evidence.json": result}


def main():
    values = content()
    if sys.argv[1:] == ["--check-recorded"]:
        for name, value in values.items():
            assert json.loads((EX / name).read_text()) == value, name
    else:
        raise SystemExit("Use --check-recorded; publication changes use apply_patch")
    print("SELECTED_EARLY_C1_OUTPUTS_FOCUSED_EVIDENCE_PASS: 2 attempts; 9 green standard-only audits")


if __name__ == "__main__":
    main()
