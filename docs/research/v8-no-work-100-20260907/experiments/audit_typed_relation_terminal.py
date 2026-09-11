#!/usr/bin/env python3
"""Audit retained typed-recurrence receipts. No compiler, SSH or file writes."""
import argparse
import hashlib
import json
from pathlib import Path
import re

BASE = Path(__file__).resolve().parent
RESEARCH = "289d7356c78a4cd493fe61a54f9548f2a0c11298"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
LEAN = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
RUNNER = "5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52"
PREFIX = "AspisV8.TypedRelationTerminal."
NAMES = ["last_fold", "image_first_fold", "post_terminal", "first_claim_horner",
         "tail_accepts_iff", "source_accepts_iff", "Decoded.response_fields", "Decoded.compact_boundary"]
ATTEMPTS = [
    ("typed-relation-terminal-nuc-v1", "TypedRelationTerminal", 1, "missing CanonicalRelationInput"),
    ("typed-relation-terminal-nuc-v2", "TypedRelationTerminal", 1, "missing CanonicalCollect"),
    ("typed-relation-terminal-nuc-v3", "TypedRelationTerminal", 1, "finite index / rewrite / wrapper"),
    ("typed-relation-terminal-v2-nuc-v1", "TypedRelationTerminalV2", 1, "one opaque finite index equality"),
    ("typed-relation-terminal-v3-nuc-v1", "TypedRelationTerminalV3", 0, "kernel-checked")]
RESTORED = ["CanonicalCollect", "CanonicalRelationInput"]


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

    records = []
    for tag, target, code, reason in ATTEMPTS:
        source = BASE / (target + ".lean")
        snapshot = BASE / (tag + "-source.txt")
        logfile = BASE / (tag + ".log")
        manifestfile = BASE / (tag + "-manifest.json")
        source_hash, snapshot_hash, log_hash, manifest_hash = map(retain, (source, snapshot, logfile, manifestfile))
        need(source_hash == snapshot_hash, tag + " exact snapshot")
        text, log = source.read_text(), logfile.read_text()
        need(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", text), target + " source placeholders")
        need(re.findall(r"^import (.+)$", text, re.M) == ["CausalOrderedRelation", "CanonicalRelationInput"], target + " imports")
        need(re.findall(r"^#print axioms ([\w.]+)$", text, re.M) == NAMES, target + " source audits")
        for option, value in [("maxRecDepth", "200"), ("maxHeartbeats", "200000")]:
            need(re.findall(r"^set_option " + option + r" (\d+)$", text, re.M) == [value], target + " limits")
        for token in [source_hash, manifest_hash, RUNNER, LEAN, "TARGET=" + target,
                      "RESEARCH_PIN=" + RESEARCH, "BORROWED_SOURCE_PIN=" + BORROWED,
                      " -j1 -M9500 -R ", "memory.high=8589934592", "memory.max=10737418240",
                      "memory.swap.max=0", "cpu.max=200000 100000"]:
            need(token in log, tag + " missing " + token)
        need(int(match(r"^LEAN_EXIT=(\d+)$", log)) == code, tag + " exit")
        need(int(match(r"Swaps: (\d+)", log)) == 0, tag + " swaps")
        manifest = json.loads(manifestfile.read_text())
        need((manifest["research"], manifest["borrowed"], manifest["lean_commit"]) == (RESEARCH, BORROWED, LEAN), tag + " manifest pins")
        count = len(manifest["files"])
        need(count in (1051, 1053), tag + " entry count")
        need(log.count("OVERLAY_PROVENANCE_PASS=" + str(count)) == (2 if code == 0 else 1), tag + " provenance checks")
        for module in RESTORED:
            need(not any(f["module"] == module for f in manifest["files"]), tag + " preserve documented omission " + module)
        direct = [f for f in manifest["files"] if f["module"] == "CausalOrderedRelation"]
        need({f["kind"] for f in direct} == {"source", "olean"}, tag + " registered direct import")
        for f in direct:
            path = BASE / (f["module"] + (".lean" if f["kind"] == "source" else ".olean"))
            if f["kind"] == "source":
                need(retain(path) == f["sha256"], "direct source bytes")
            elif path.exists():
                need(sha(path) == f["sha256"], "direct optional output bytes")
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
        output_hash = None
        if code == 0:
            need("PROVENANCE_UNCHANGED=true" in log, tag + " postflight")
            need(not re.search(r": error(?:\(|:)|\bsorryAx\b", log), tag + " no successful errors")
            need([n for n, _ in audits] == [PREFIX + n for n in NAMES], tag + " audit names")
            need(all(set(map(str.strip, a.split(","))) == {"propext", "Classical.choice", "Quot.sound"} for _, a in audits), tag + " standard axioms")
            output_hash = match(r"^([0-9a-f]{64})  .*/" + target + r"\.olean$", log)
            output = BASE / (target + ".olean")
            if output.exists():
                need(sha(output) == output_hash, target + " optional local output")
        elif "missing " in reason:
            need("unknown module prefix '" + reason.removeprefix("missing ") + "'" in log, tag + " import failure")
            need(not audits, tag + " no import-failure theorem credit")
        else:
            need("sorryAx" in log and "omega could not prove" in log, tag + " preserved proof diagnostics")
        records.append({"tag": tag, "target": target, "exit": code, "reason": reason,
                        "source_sha256": source_hash, "log_sha256": log_hash,
                        "manifest_sha256": manifest_hash, "olean_sha256": output_hash,
                        "wall_time": match(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", log),
                        "peak_rss_kib": int(match(r"Maximum resident set size \(kbytes\): (\d+)", log)),
                        "swaps": 0, "registered_entries": count,
                        "warning_lines": re.findall(r"^.*: warning:.*$", log, re.M),
                        "audits": [{"name": n, "axioms": list(map(str.strip, a.split(",")))} for n, a in audits]})
    oldfile = BASE.parent / "canonical-relation-input-evidence.json"
    retain(oldfile)
    old = json.loads(oldfile.read_text())
    need(old["environment"]["lean_commit"] == LEAN, "restored toolchain")
    observation = BASE / "typed-relation-terminal-restored-dependencies.txt"
    retain(observation)
    observed = observation.read_text()
    restored = []
    for module in RESTORED:
        [entry] = [r for r in old["runs"] if r["target"] == module and r["exit"] == 0]
        source = BASE / (module + ".lean")
        oldlog = BASE.parent / entry["log"]
        need(retain(source) == entry["source_sha256"], module + " old source pin")
        need(retain(oldlog) == entry["log_sha256"], module + " original log pin")
        oldtext = oldlog.read_text()
        for digest in [entry["source_sha256"], entry["olean_sha256"]]:
            need(digest in oldtext and digest in observed, module + " original and post-run pair")
        need("LEAN_EXIT=0" in oldtext and LEAN in oldtext, module + " reused green receipt")
        output = BASE / (module + ".olean")
        if output.exists():
            need(sha(output) == entry["olean_sha256"], module + " restored optional output")
        restored.append({"module": module, "source_sha256": entry["source_sha256"],
                         "olean_sha256": entry["olean_sha256"], "original_log": entry["log"],
                         "original_log_sha256": entry["log_sha256"], "omitted_from_run_manifests": True})
    retain(BASE.parent / "typed-relation-terminal-review.md")
    retain(Path(__file__).resolve())
    return {"schema": "aspis-v8-typed-relation-terminal/v1",
            "status": "kernel-checked typed recurrence; whole Rust/input/FS refinement remains open",
            "source_parent": "d879105131a34a4bd087409bced83778d3ea8a96",
            "runner_parent": RESEARCH, "borrowed_pin": BORROWED, "lean_commit": LEAN,
            "runner_sha256": RUNNER,
            "census": {"green_targets": 1, "standard_axiom_audits": 8, "attempts": 5, "failures": 4},
            "attempts": records, "restored_dependencies": restored,
            "provenance_boundary": "Registered-entry checks plus separate post-run parser-pair observation and old green receipts; no complete transitive-cache equivalence claim.",
            "olean_policy": "Optional in clone; exact bytes required whenever present. Output digests retained in green logs.",
            "file_sha256": dict(sorted(files.items()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--emit-record", action="store_true")
    modes.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    result = collect()
    if args.emit_record:
        print(json.dumps(result, indent=2) + "\n", end="")
    else:
        need(result == json.loads((BASE / "typed-relation-terminal-evidence.json").read_text()), "record differs")
        print("PASS: 1 green / 8 standard audits / 5 exact attempts / 4 failures; restored parser omission explicit; no compiler replay")


if __name__ == "__main__":
    main()
