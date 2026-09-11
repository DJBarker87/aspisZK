#!/usr/bin/env python3
"""Read-only audit of two retained attempts; never invokes Lean or SSH."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def require(ok, why):
    if not ok:
        raise SystemExit("FAIL: " + why)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-recorded", action="store_true", required=True)
    parser.parse_args()
    base = Path(__file__).resolve().parent
    record = json.loads((base / "selected-accepted-prefix-partition-evidence.json").read_text())
    green = []
    for attempt in record["attempts"]:
        target, tag = attempt["target"], attempt["tag"]
        source = base / (target + ".lean")
        snapshot = base / (tag + "-source.txt")
        logfile = base / (tag + ".log")
        manifestfile = base / (tag + "-manifest.json")
        for path, key in [(source, "source_sha256"), (snapshot, "source_sha256"),
                          (logfile, "log_sha256"), (manifestfile, "manifest_sha256")]:
            require(path.is_file() and digest(path) == attempt[key], path.name + " digest")
        text = source.read_text()
        require(not re.search(r"\b(sorry|admit|axiom|native_decide)\b", text), target + " no placeholders")
        require(re.findall(r"^import (.+)$", text, re.M) == [record["direct_import"]["module"]], target + " imports")
        for name in ("maxRecDepth", "maxHeartbeats"):
            require(re.findall(r"^set_option " + name + r" (\d+)$", text, re.M) == [str(record["caps"][name])], target + " " + name)
        log = logfile.read_text()
        for token in ["TARGET=" + target, "RESEARCH_PIN=" + record["runner_parent"],
                      "BORROWED_SOURCE_PIN=" + record["borrowed_source_pin"],
                      record["lean_commit"], record["runner_sha256"],
                      attempt["source_sha256"], attempt["manifest_sha256"],
                      "LEAN_EXIT=" + str(attempt["exit"]), " -j1 -M9500 -R ",
                      "memory.high=8589934592", "memory.max=10737418240",
                      "memory.swap.max=0", "cpu.max=200000 100000"]:
            require(token in log, tag + " missing " + token)
        for pattern, expected in [
            (r"Maximum resident set size \(kbytes\): (\d+)", str(attempt["peak_rss_kib"])),
            (r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): 0:(\d+\.\d+)", "0" + attempt["wall_seconds"]),
            (r"Swaps: (\d+)", str(attempt["swaps"])),
            (r"Exit status: (\d+)", str(attempt["exit"]))]:
            match = re.search(pattern, log)
            require(match is not None and match[1] == expected, tag + " resource " + pattern)
        manifest = json.loads(manifestfile.read_text())
        require(manifest["research"] == record["runner_parent"] and
                manifest["borrowed"] == record["borrowed_source_pin"] and
                manifest["lean_commit"] == record["lean_commit"], tag + " manifest pins")
        require(len(manifest["files"]) == 1035, tag + " registered entries")
        dependency = record["direct_import"]
        for kind, key, extension in [("source", "source_sha256", ".lean"), ("olean", "olean_sha256", ".olean")]:
            entries = [f for f in manifest["files"] if f["module"] == dependency["module"] and f["kind"] == kind]
            require(len(entries) == 1 and entries[0]["sha256"] == dependency[key], tag + " direct import " + kind)
            path = base / (dependency["module"] + extension)
            if kind == "source" or path.exists():
                require(path.is_file() and digest(path) == dependency[key], path.name + " bytes")
        if attempt["exit"] == 0:
            require(log.count("OVERLAY_PROVENANCE_PASS=1035") == 2 and
                    "PROVENANCE_UNCHANGED=true" in log, tag + " pre/post provenance")
            require(not re.search(r"\bsorryAx\b|: error(?:\(|:)|: warning:", log), tag + " successful diagnostics")
            audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
            require([name for name, _ in audits] == [record["audit_namespace"] + "." + name for name in record["audit_declarations"]], tag + " audit names/order")
            require(all(set(map(str.strip, axioms.split(","))) == {"propext", "Classical.choice", "Quot.sound"} for _, axioms in audits), tag + " standard axioms")
            require(re.findall(r"^#print axioms (\w+)$", text, re.M) == record["audit_declarations"], tag + " source audits")
            require(attempt["olean_sha256"] in log, tag + " recorded output digest")
            output = base / (target + ".olean")
            if output.exists():
                require(digest(output) == attempt["olean_sha256"], target + " optional local output")
            green.append(target)
        else:
            require("sorryAx" in log and "maximum recursion depth" in log and
                    "Invalid field notation" in log, tag + " preserved failed diagnostics")
    for filename, expected in record["rust_source_hashes"].items():
        require(digest(base / filename) == expected, filename + " reviewed Rust bytes")
    require(record["census"] == {"green_targets": len(green), "standard_axiom_audits": 5,
                                "attempts": len(record["attempts"]), "failed_attempts": 1}, "census")
    print("PASS: 1 green target; 5 standard-only audits; 2 exact attempts / 1 failure; source/output/import hashes checked; no compiler replay")


if __name__ == "__main__":
    main()
