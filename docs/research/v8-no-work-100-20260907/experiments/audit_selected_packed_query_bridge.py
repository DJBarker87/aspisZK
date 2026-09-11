#!/usr/bin/env python3
"""Read-only audit of retained query bridge receipts; never runs Lean or SSH."""
import argparse
import hashlib
import json
from pathlib import Path
import re

BASE = Path(__file__).resolve().parent
PARENT = "8761cd89ab7ccea779ef4a9f86fa415d670bd16d"
RUN_PARENT = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
LEAN = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
RUNNER = "5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52"
NAMES = ["extendRows_at", "observedWord_at", "matching_slots", "matching_fold",
         "observed_quotient_slots", "observed_fold", "observed_residual",
         "q22_received_sum", "source_pole_reject"]
ATTEMPTS = [
    ("selected-packed-query-bridge-nuc-v1", "SelectedPackedQueryBridge", 1, "missing PackedQueryRecord"),
    ("selected-packed-query-bridge-nuc-v2", "SelectedPackedQueryBridge", 1, "slotIndex dimension and reserved matches token"),
    ("selected-packed-query-bridge-v2-nuc-v1", "SelectedPackedQueryBridgeV2", 1, "concrete matching_fold congruence recursion"),
    ("selected-packed-query-bridge-v3-nuc-v1", "SelectedPackedQueryBridgeV3", 0, "generic expanded_congr; kernel checked")]


def need(test, message):
    if not test:
        raise SystemExit("FAIL: " + message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def match(pattern, text):
    found = re.search(pattern, text, re.M)
    need(found is not None, "missing pattern " + pattern)
    return found[1]


def collect():
    files = {}

    def retain(path):
        key = str(path.relative_to(BASE.parent))
        files[key] = sha(path)
        return files[key]

    prefile = BASE / "selected-packed-query-dependency-preflight.json"
    retain(prefile)
    preflight = json.loads(prefile.read_text())
    observation = BASE / "selected-packed-query-restored-dependencies.txt"
    retain(observation)
    observed = observation.read_text()
    need("Tailscale dombarker@100.108.41.90" in observed, "actual endpoint")
    need("not an execution-time checksum" in observed, "observation timing scope")
    restored = preflight["manifest_omitted_research_pairs"]
    need(len(restored) == 14, "exact restored pair census")
    for entry in restored:
        module = entry["module"]
        for kind, ext in [("source", ".lean"), ("olean", ".olean")]:
            digest = entry[kind]["sha256"]
            local = BASE / (module + ext)
            if kind == "source":
                need(retain(local) == digest, module + " pinned source")
            elif local.exists():
                need(sha(local) == digest, module + " optional output bytes")
            need(re.search(r"^" + digest + r"  .*/overlay/" + module + re.escape(ext) + r"$", observed, re.M),
                 module + " exact post-run pair")
            need(entry[kind]["old_green_receipts"], module + " prior receipt required")
            for path in entry[kind]["old_green_receipts"]:
                oldlog = BASE / Path(path).name
                retain(oldlog)
                oldtext = oldlog.read_text()
                need("LEAN_EXIT=0" in oldtext and LEAN in oldtext, module + " retained green toolchain")
                need(re.search(r"^" + digest + r"  .*/" + module + re.escape(ext) + r"$", oldtext, re.M),
                     module + " exact old pair")
    for record in preflight["old_green_logs"]:
        need(retain(BASE / Path(record["path"]).name) == record["sha256"], "old full log pin")
    comparison = BASE / Path(preflight["comparison_manifest"]).name
    need(retain(comparison) == preflight["comparison_manifest_sha256"], "historical manifest pin")
    need(len(preflight["registered_boundary_pairs"]) == 8, "four boundary pair census")

    records = []
    for tag, target, code, reason in ATTEMPTS:
        source = BASE / (target + ".lean")
        snapshot = BASE / (tag + "-source.txt")
        logfile = BASE / (tag + ".log")
        manifestfile = BASE / (tag + "-manifest.json")
        source_hash, snapshot_hash, log_hash, manifest_hash = map(retain, (source, snapshot, logfile, manifestfile))
        need(source_hash == snapshot_hash, tag + " immutable source snapshot")
        text, log = source.read_text(), logfile.read_text()
        need(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", text), target + " placeholders")
        need(re.findall(r"^import (.+)$", text, re.M) == ["PackedQueryRecord", "SelectedQueryBuffer"], target + " imports")
        names = (["expanded_congr"] if target.endswith("V3") else []) + NAMES
        need(re.findall(r"^#print axioms ([\w.]+)$", text, re.M) == names, target + " source audit names")
        for option, value in [("maxRecDepth", "200"), ("maxHeartbeats", "200000")]:
            need(re.findall(r"^set_option " + option + r" (\d+)$", text, re.M) == [value], target + " unchanged limits")
        for token in [source_hash, manifest_hash, RUNNER, LEAN, "TARGET=" + target,
                      "RESEARCH_PIN=" + RUN_PARENT, "BORROWED_SOURCE_PIN=" + BORROWED,
                      " -j1 -M9500 -R ", "memory.high=8589934592", "memory.max=10737418240",
                      "memory.swap.max=0", "cpu.max=200000 100000"]:
            need(token in log, tag + " missing " + token)
        need(int(match(r"^LEAN_EXIT=(\d+)$", log)) == code, tag + " exit")
        need(int(match(r"Swaps: (\d+)", log)) == 0, tag + " swaps")
        manifest = json.loads(manifestfile.read_text())
        need((manifest["research"], manifest["borrowed"], manifest["lean_commit"]) ==
             (RUN_PARENT, BORROWED, LEAN), tag + " manifest pins")
        need(len(manifest["files"]) == 1059, tag + " registered entry count")
        need(log.count("OVERLAY_PROVENANCE_PASS=1059") == (2 if code == 0 else 1), tag + " registered checks")
        for entry in restored:
            need(not any(f["module"] == entry["module"] for f in manifest["files"]),
                 tag + " preserve actual import omission " + entry["module"])
        for boundary in preflight["registered_boundary_pairs"]:
            [actual] = [f for f in manifest["files"] if (f["module"], f["kind"]) ==
                        (boundary["module"], boundary["kind"])]
            need(actual["sha256"] == boundary["manifest_sha256"] and
                 boundary["old_receipt_sha256"] == [actual["sha256"]], tag + " boundary exact pair")
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
        output_hash = None
        if code == 0:
            need("PROVENANCE_UNCHANGED=true" in log, tag + " postflight")
            need(not re.search(r": error(?:\(|:)|\bsorryAx\b|: warning:", log), tag + " no successful errors/warnings")
            need([n for n, _ in audits] == ["AspisV8.SelectedPackedQueryBridge." + n for n in names], tag + " exact audits")
            for name, ax in audits:
                expected = {"propext", "Quot.sound"}
                if not name.endswith(".expanded_congr"):
                    expected.add("Classical.choice")
                need(set(map(str.strip, ax.split(","))) == expected, name + " exact standard axioms")
            output_hash = match(r"^([0-9a-f]{64})  .*/" + target + r"\.olean$", log)
            output = BASE / (target + ".olean")
            if output.exists():
                need(sha(output) == output_hash, target + " optional output")
        elif reason.startswith("missing"):
            need("unknown module prefix 'PackedQueryRecord'" in log and not audits, tag + " dependency-only failure")
        else:
            need("sorryAx" in log and ": error:" in log, tag + " retained failed proof diagnostics")
        records.append({"tag": tag, "target": target, "exit": code, "reason": reason,
                        "source_sha256": source_hash, "snapshot_sha256": snapshot_hash,
                        "log_sha256": log_hash, "manifest_sha256": manifest_hash,
                        "olean_sha256": output_hash,
                        "wall_time": match(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", log),
                        "peak_rss_kib": int(match(r"Maximum resident set size \(kbytes\): (\d+)", log)),
                        "swaps": 0, "registered_entries": 1059,
                        "warning_lines": re.findall(r"^.*: warning:.*$", log, re.M),
                        "audits": [{"name": n, "axioms": list(map(str.strip, ax.split(",")))} for n, ax in audits]})
    controlfile = BASE / "selected-query-record-control.json"
    retain(controlfile)
    control = json.loads(controlfile.read_text())
    need(retain(BASE / "check_selected_query_record.py") == control["source_sha256"], "control source pin")
    need((control["status"], control["single_bit_cases"], control["noncanonical_cases"]) ==
         ("PASS", 4712, 152), "retained tiny control result")
    retain(BASE.parent / "selected-packed-query-bridge-review.md")
    retain(Path(__file__).resolve())
    return {"schema": "aspis-v8-selected-packed-query-bridge/v1",
            "status": "kernel-checked observed query algebra; fixed-word authentication and machine/source refinement remain open",
            "source_parent": PARENT, "runner_parent": RUN_PARENT, "borrowed_pin": BORROWED,
            "lean_commit": LEAN, "runner_sha256": RUNNER,
            "census": {"green_targets": 1, "standard_axiom_audits": 10, "attempts": 4, "failures": 3},
            "attempts": records, "restored_dependencies": restored,
            "registered_boundary_pairs": preflight["registered_boundary_pairs"],
            "restored_observation_utc": match(r"^(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ)$", observed),
            "provenance_boundary": "All 14 exact restored pairs omitted from all four run manifests; old green receipts plus separate post-run hash observation, not execution-time checksums or complete closure certification.",
            "olean_policy": "Optional in clone; exact bytes required whenever present. Output digests retained in green logs.",
            "control": control, "file_sha256": dict(sorted(files.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--emit-record", action="store_true")
    modes.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = collect()
    if args.emit_record:
        print(json.dumps(result, indent=2))
    else:
        need(result == json.loads((BASE / "selected-packed-query-bridge-evidence.json").read_text()), "record differs")
        print("PASS: 1 green / 10 standard audits / 4 exact attempts / 3 failures; 14 restored omissions explicit; no compiler replay")


if __name__ == "__main__":
    main()
