#!/usr/bin/env python3
"""Read-only bc23 continuation audit: three focused leaves and one Rust control.

No compiler, remote job, field enumeration, old manifest replay or file write.
Reuses frozen evidence-parsing helpers, not the preceding ten-leaf audit main.
Missing/stale endpoints remain pending and return exit 1.
"""
import argparse
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import re
import subprocess
import sys

import audit_off_family_tail_evidence as prior

EX, RD = prior.EX, prior.RD
BASE = "bc23dfeb647320c4fbf09012cd92da1a6a5fa95a"
ORIGIN = "b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9"
INITIAL = EX / "quotient-family-initial-manifest.json"
INITIAL_SHA = "c7c0792100c4b9f0c98d060f9c91fec1b12ea9d836c35bb309201cf0cfefb0aa"
LEAVES = {"QuotientFamilyCore": ("quotient-family-core", 4),
          "QuotientFamilySelected": ("quotient-family-selected", 5),
          "EarlyC1Family": ("early-c1-family", 7)}
prior.BASE = BASE
require, sha, relative = prior.require, prior.sha, prior.relative


def log_paths():
    result = set(EX.glob("mixed-c1-control-nuc-*.log"))
    for stem, _ in LEAVES.values():
        result.update(EX.glob(stem + "-nuc-*.log"))
    return sorted(result)


def inventory():
    manifest = json.loads(INITIAL.read_text())
    artifacts, runs, missing = {}, [], []
    for path in log_paths():
        log = path.read_text()
        target = re.search(r"^TARGET=(.+)$", log, re.M)
        for digest, raw in re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M):
            choices = [EX / Path(raw).name, EX / (path.stem + "-source.txt"),
                       EX / (path.stem + "-runner.txt")]
            if Path(raw).name.startswith("mixed-c1-mixed-c1-control-"):
                choices.append(EX / "target/MixedC1Control")
            local = next((p for p in choices if p.exists() and sha(p) == digest), None)
            if local is None:
                missing.append({"log": relative(path), "remote_path": raw, "sha256": digest})
            else:
                artifacts[(raw, digest)] = {"remote_path": raw, "local_path": relative(local),
                                            "sha256": digest}
        command = re.search(r"^COMMAND=(.+)$", log, re.M)
        def prop(name):
            match = re.search(r"^" + re.escape(name) + r"=(\d+)\s*$", log, re.M)
            return int(match.group(1)) if match else None
        runs.append({"target": target.group(1) if target else "MixedC1Control",
                     "log": relative(path), "command": command.group(1) if command else None,
                     "memory_high_bytes": prop("memory.high"),
                     "memory_max_bytes": prop("memory.max"), "memory_swap_max": prop("memory.swap.max")})
    # Every newly generated imported artifact is pinned before downstream use.
    for record in list(artifacts.values()):
        if not record["remote_path"].endswith("-manifest.json"):
            continue
        run_manifest = json.loads((RD / record["local_path"]).read_text())
        task = record["remote_path"].rsplit("/", 1)[0]
        for item in run_manifest["files"]:
            if item["category"] != "new_checked":
                continue
            raw = task + "/overlay/" + item["overlay"]
            key = (raw, item["sha256"])
            if key in artifacts:
                continue
            local = EX / Path(item["overlay"]).name
            if local.exists() and sha(local) == item["sha256"]:
                artifacts[key] = {"remote_path": raw, "local_path": relative(local), "sha256": item["sha256"]}
            else:
                missing.append({"manifest": record["local_path"], "remote_path": raw, "sha256": item["sha256"]})
    return {**{key: manifest[key] for key in ("research", "borrowed", "mathlib", "lean_commit")},
            "status": "retained_artifact_inventory_not_global_evidence",
            "manifest": {"path": relative(INITIAL), "sha256": sha(INITIAL)},
            "origin": manifest["origin"], "artifacts": list(artifacts.values()),
            "runs": runs, "unmapped_artifacts": missing}


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "new-turn initial manifest changed")
    manifest = json.loads(INITIAL.read_text())
    require(manifest["research"] == BASE and manifest["pending_no_olean"] == [], "incorrect new-turn baseline")
    origin = manifest["origin"]
    require(origin["research"] == ORIGIN, "old origin confused with new parent")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"], "prior import snapshot changed")
    require(sha(EX / "quotient-family-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "prior green output receipt changed")
    repo = Path(subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip())
    checked_sources = checked_artifacts = 0
    for entry in manifest["files"]:
        if entry["kind"] == "source":
            borrowed = entry["module"].startswith("AspisFormal.")
            revision = prior.BORROWED if borrowed else BASE
            path = ("AspisFormal/" if borrowed else
                    "docs/research/v8-no-work-100-20260907/experiments/") + entry["overlay"]
            blob = subprocess.check_output(["git", "-C", str(repo), "show", revision + ":" + path])
            require(prior.hashlib.sha256(blob).hexdigest() == entry["sha256"], "pinned imported source mismatch: " + entry["module"])
            checked_sources += 1
        else:
            local = Path(entry["local"]) if entry.get("local") else EX / entry["overlay"]
            require(sha(local) == entry["sha256"], "retained compiled cache mismatch: " + entry["module"])
            checked_artifacts += 1
    return {"status": "green", "manifest_sha256": INITIAL_SHA, "entries": len(manifest["files"]),
            "pinned_source_blobs_checked": checked_sources, "retained_compiled_artifacts_checked": checked_artifacts,
            "origin": origin, "bootstrap_script_sha256": sha(EX / "bootstrap_quotient_family.py"),
            "boundary": "Exact research/borrowed source and retained compiled bytes; inherited source-to-olean evidence, not a compiler reproduction. Native packages are pinned revisions, not replayed."}


def check_leaf(name, path, transfer):
    source = (EX / (name + ".lean")).read_text()
    log = path.read_text()
    require(not re.search(prior.BAD_LOG, log, re.M), "error/guard marker in log")
    require(re.findall(r"^LEAN_EXIT=(\d+)\s*$", log, re.M) == ["0"], "missing successful terminal")
    require(all(pin in log for pin in (BASE, prior.BORROWED, prior.LEAN)), "source/toolchain pin missing")
    require(not re.search(r"^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b", source, re.M), "admitted source")
    hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M)
    target = [value for value, raw in hashes if Path(raw).name == name + ".lean"]
    output = [value for value, raw in hashes if Path(raw).name == name + ".olean"]
    require(target and set(target) == {sha(EX / (name + ".lean"))}, "stale/missing current-source hash")
    require(len(set(output)) == 1, "missing/ambiguous output hash")
    resources = prior.measurements(log)
    require(len(resources) == 1 and resources[0]["format"] == "GNU_time_v", "focused GNU resource block missing")
    require(resources[0]["peak_rss_bytes"] <= 10 * 1024**3, "RSS exceeded authorized selected cache profile")
    require("-j1 -M9500" in log and "cpu.max=200000 100000" in log, "thread/heap/CPU cap mismatch")
    for prop, value in (("memory.high", 8 * 1024**3), ("memory.max", 10 * 1024**3), ("memory.swap.max", 0)):
        require(re.findall(r"^" + re.escape(prop) + r"=(\d+)\s*$", log, re.M) == [str(value)], "actual cgroup mismatch: " + prop)
    runs = [row for row in transfer.runs(name) if transfer.resolve(row["log"]) == path]
    require(len(runs) == 1 and runs[0]["command"] and runs[0]["command"] in log, "missing unique command receipt")
    closure = prior.remote_closure(name, log, hashes, transfer)
    for digest, raw in hashes:
        transfer.file(raw, digest)
    audits = prior.axiom_audits(source, log)
    require(len(audits) == LEAVES[name][1], "unexpected selected audit count")
    return {"log": relative(path), "log_sha256": sha(path), "exit": 0,
            "source_sha256": target[0], "olean_sha256": output[0], "measurement": resources[0],
            "axiom_audits": audits, "import_closure": closure, "command": runs[0]["command"],
            "resource_profile": "Previously established native selected-cache scope: High8GiB/Max10GiB/Swap0/-j1/-M9500; no cold build."}


def leaves(transfer):
    result = []
    for name, (stem, _) in LEAVES.items():
        good, diagnostic = [], []
        for path in sorted(EX.glob(stem + "-nuc-*.log")):
            try:
                good.append(check_leaf(name, path, transfer))
            except (OSError, ValueError, KeyError) as error:
                diagnostic.append({"log": relative(path), "log_sha256": sha(path),
                                   "status": "retained_diagnostic_not_release_evidence", "reason": str(error),
                                   "recorded_exits": re.findall(r"^LEAN_EXIT=(\d+)\s*$", path.read_text(), re.M)})
        result.append({"target": name + ".lean", "status": "green" if good else "pending",
                       "runs": good, "retained_diagnostics": diagnostic})
    return result


def rust(transfer):
    results, diagnostics = [], []
    for path in sorted(EX.glob("mixed-c1-control-nuc-*.log")):
        log = path.read_text()
        try:
            require(BASE in log and "SOURCE_UNCHANGED=true" in log, "missing source pin/postflight")
            require(re.findall(r"^COMPILE_EXIT=(\d+)\s*$", log, re.M) == ["0"] and
                    re.findall(r"^CONTROL_EXIT=(\d+)\s*$", log, re.M) == ["0"], "compile/control not green")
            require("-O -C overflow-checks=yes" in log, "not optimized checked arithmetic")
            compile_commands = re.findall(r"^COMPILE_COMMAND=(.+)$", log, re.M)
            control_commands = re.findall(r"^CONTROL_COMMAND=(.+)$", log, re.M)
            require(len(compile_commands) == len(control_commands) == 1,
                    "literal compile/control command missing")
            require("memory.high=1073741824" in log and "memory.max=2147483648" in log and
                    "memory.swap.max=0" in log and "cpu.max=200000 100000" in log, "Rust cgroup mismatch")
            hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M)
            require(any(Path(raw).name == "MixedC1Control.rs" and digest == sha(EX / "MixedC1Control.rs")
                        for digest, raw in hashes), "current Rust source not executed")
            for digest, raw in hashes:
                transfer.file(raw, digest)
            measurements = prior.measurements(log)
            require(len(measurements) == 2 and all(row["peak_rss_bytes"] < 2 * 1024**3 for row in measurements), "Rust resources missing")
            rows = [json.loads(line) for line in log.splitlines() if line.startswith("{")]
            require(len(rows) == 1, "missing unique control result")
            row = rows[0]
            require(row["fixed_strategy"] and (row["field"], row["fibres"], row["minority"], row["early_support"]) == (31, 7, 2, 5), "unexpected model")
            require(row["exhaustive_five_fibre_systems"] == 21 and row["unique_early_lane"] == "zero" and row["reference_checks"] == 58977, "control census changed")
            require([r["chord"] for r in row["chord_results"]] == ["2x", "2y"], "missing chord control")
            for r in row["chord_results"]:
                require((r["far_alphas"], r["all_suffix_accept_numerator"], r["far_suffix_accept_numerator"],
                         r["denominator"], r["far_minority_query_prefixes"]) ==
                        (30, 207836460, 170299800, 1163636460, 1800), "fixed control exact counts changed")
            k = (2**31 - 1)**4
            exact = Fraction(k - 3, k) * Fraction(comb(16535, 22), comb(262144, 22))
            bound = row["full_profile_no_pole_conditional_lower_bound"]
            require(Fraction(int(bound["numerator"]), int(bound["denominator"])) == exact, "conditional rational mismatch")
            ledger_path = RD / "mixed-c1-control-ledger.json"
            ledger = json.loads(ledger_path.read_text())
            require(ledger["revision"] == BASE and ledger["proof_body_bytes"] == 40282 and
                    ledger["work_security_credit"] == 0, "mixed-C1 ledger contract changed")
            recorded = ledger["conditional_lower_bound"]
            require(Fraction(int(recorded["numerator"]), int(recorded["denominator"])) == exact and
                    recorded["direction"] == "lower", "ledger conditional direction/rational changed")
            require(ledger["reduced_control"]["rate_extrapolation_to_QM31"] is False and
                    ledger["reduced_control"]["valid_payment_witness_asserted"] is False,
                    "reduced control promoted beyond its scope")
            results.append({"log": relative(path), "log_sha256": sha(path), "measurements": measurements,
                            "compile_command": compile_commands[0], "control_command": control_commands[0],
                            "ledger_sha256": sha(ledger_path), "result": row,
                            "scope": "Reduced geometric/scalar suffix; exact full-profile rational is conditional, not a payment execution or security bound."})
        except (OSError, ValueError, KeyError) as error:
            diagnostics.append({"log": relative(path), "log_sha256": sha(path), "reason": str(error),
                                "status": "retained_diagnostic_not_release_evidence"})
    return {"status": "green" if results else "pending", "runs": results, "retained_diagnostics": diagnostics}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt is not evidence")
        receipt = inventory()
        print(json.dumps(receipt, indent=2))
        return 1 if receipt["unmapped_artifacts"] else 0
    transfer = prior.Transfer(RD / "quotient-family-transfer.json")
    require(transfer.data is not None, "missing new-turn transfer receipt")
    output = {"schema": "aspis-v8-quotient-family-evidence-v1", "parent_revision": BASE,
              "auditor_sha256": sha(Path(__file__).resolve()),
              "reused_read_only_audit_helpers_sha256": sha(EX / "audit_off_family_tail_evidence.py"),
              "borrowed_formal_revision": prior.BORROWED, "mathlib_revision": prior.MATHLIB,
              "lean_commit": prior.LEAN, "transfer_receipt_sha256": sha(transfer.path),
              "bootstrap": bootstrap(), "leaves": leaves(transfer), "mixed_c1_control": rust(transfer),
              "proof_body_bytes": 40282, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Literal finite-family mathematics and one reduced causal control; no executable list recovery, payment-witness extraction, actual replay, full-view ZK or resource-bounded Fiat–Shamir theorem."}
    require(9558**2 - 262144 * 255 == 24508644 and
            100 * 24508644 - 262144 * (9558 - 255) == 12138768 and
            262144 <= 2 * 100 * 9558, "Johnson arithmetic certificate changed")
    output["quotient_johnson_arithmetic"] = {"coordinate_count": 262144, "support_floor": 9558,
        "distinct_support_overlap": 255, "family_cardinality_cap": 99,
        "positive_quadratic_margin": 24508644, "positive_list_margin": 12138768,
        "scope": "Independently checked exact integers; selected hypotheses separately proved in Lean."}
    complete = all(row["status"] == "green" for row in output["leaves"]) and output["mixed_c1_control"]["status"] == "green"
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "pending endpoint: refusing recorded-evidence success")
        require(json.loads((RD / "quotient-family-evidence.json").read_text()) == output, "recorded evidence changed")
        print("Quotient-family focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("QUOTIENT_FAMILY_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
