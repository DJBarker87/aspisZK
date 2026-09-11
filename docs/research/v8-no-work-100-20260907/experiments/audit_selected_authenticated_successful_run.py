#!/usr/bin/env python3
"""Read-only, clone-portable audit of the six retained focused attempts."""
import argparse
import hashlib
import json
import pathlib
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true", required=True)
    parser.parse_args()
    base = pathlib.Path(__file__).resolve().parent.parent
    data = json.loads((base / "selected-authenticated-successful-run-evidence.json").read_text())
    target = data["target"]
    source = base / data["source"]["path"]
    assert sha(source) == data["source"]["sha256"]
    text = source.read_text()
    assert "set_option maxRecDepth 200" in text
    assert "set_option maxHeartbeats 250000" in text
    assert not re.search(r"\b(sorry|admit|axiom)\b", text)
    names = re.findall(r"^#print axioms (\S+)$", text, re.M)
    expected = data["axiom_audits"]
    assert {f"AspisV8.{target}.{name}" for name in names} == set(expected)
    assert len(expected) == 7
    assert len(data["attempts"]) == 6
    assert len({a["source_sha256"] for a in data["attempts"]}) == 6
    previous = None
    for attempt in data["attempts"]:
        tag = attempt["tag"]
        artifacts = {
            "source": base / "experiments" / (tag + "-source.txt"),
            "log": base / "experiments" / (tag + ".log"),
            "manifest": base / "experiments" / (tag + "-manifest.json"),
        }
        for kind, path in artifacts.items():
            assert sha(path) == attempt[kind + "_sha256"], path
        log = artifacts["log"].read_text()
        manifest = json.loads(artifacts["manifest"].read_text())
        assert manifest["research"] == data["runner_bootstrap_revision"]
        assert manifest["borrowed"] == data["borrowed_source_revision"]
        assert manifest["lean_commit"] == data["lean_commit"]
        assert len(manifest["files"]) == attempt["provenance_entries"]
        selected = [entry for entry in manifest["files"]
                    if entry["module"] == target and entry["kind"] == "source"]
        assert len(selected) == 1
        assert selected[0]["sha256"] == attempt["source_sha256"]
        assert selected[0]["bytes"] == artifacts["source"].stat().st_size
        assert len({e["overlay"] for e in manifest["files"]}) == len(manifest["files"])
        for module in ("SelectedWireOpeningTerminal", "SuccessfulSelectedVerifierRun"):
            assert {e["kind"] for e in manifest["files"] if e["module"] == module} >= {"source", "olean"}
        for key, pattern in (
            ("exit_status", r"LEAN_EXIT=(\d+)"),
            ("peak_rss_kib", r"Maximum resident set size \(kbytes\): (\d+)"),
            ("swaps", r"Swaps: (\d+)"),
            ("provenance_entries", r"OVERLAY_PROVENANCE_PASS=(\d+)"),
        ):
            assert int(re.search(pattern, log).group(1)) == attempt[key]
        assert re.search(r"Elapsed .*: ([0-9:.]+)", log).group(1) == attempt["wall_elapsed"]
        assert data["runner_sha256"] in log
        assert attempt["manifest_sha256"] in log and attempt["source_sha256"] in log
        for setting in ("memory.high=8589934592", "memory.max=10737418240",
                        "memory.swap.max=0", "cpu.max=200000 100000", " -j1 -M9500 "):
            assert setting in log
        assert f"TARGET={target}\n" in log
        assert "Lean (version 4.32.0," in log and data["lean_commit"] in log
        assert attempt["swaps"] == 0
        assert previous != attempt["source_sha256"]
        previous = attempt["source_sha256"]
        if attempt["exit_status"] == 0:
            assert attempt is data["attempts"][-1]
            assert attempt["source_sha256"] == data["source"]["sha256"]
            assert "PROVENANCE_UNCHANGED=true" in log
            assert log.count("OVERLAY_PROVENANCE_PASS=") == 2
            assert data["output"]["sha256"] in log
            audits = dict((name, re.findall(r"[\w.]+", axioms)) for name, axioms in
                          re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log))
            assert audits == expected
            assert "sorryAx" not in log and not re.search(r": error(?:\(|:)", log)
        else:
            assert attempt["exit_status"] == 1
            assert ": error" in log
    output = base / data["output"]["path"]
    if output.exists():
        assert sha(output) == data["output"]["sha256"]
    report = (base / "selected-authenticated-successful-run-review.md").read_text()
    assert data["source"]["sha256"] in report and data["output"]["sha256"] in report
    print("PASS: six exact source/log/manifest triplets; seven standard-only green audits;")
    print("same caps, no unchanged retry; optional local olean " +
          ("matched." if output.exists() else "absent (recorded output hash retained)."))


if __name__ == "__main__":
    main()
