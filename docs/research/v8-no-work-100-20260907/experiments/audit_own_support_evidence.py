#!/usr/bin/env python3
"""Read-only ed41b253 focused evidence; no compiler or prior-suite replay."""
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import re
import subprocess
import sys

import audit_symbolic_ood_evidence as prior

old = prior.old
EX, RD = old.EX, old.RD
BASE = "ed41b2537e7dad15ce8055d9e5524e337ee8b9a4"
ORIGIN = "2f6d82fef294410367aa1781fb924af7c38deab9"
INITIAL = EX / "own-support-initial-manifest.json"
INITIAL_SHA = "a3cbc9272d897797f1b832c5d1372226c9992f3877d0a504c1e024b55adbaf9e"
CENSUS_FINAL = True
TARGETS = {
    "FixedTargetQuerySupport": ("fixed-target-query-support-nuc-export", 17),
    "OwnSymbolCollision": ("own-symbol-collision", 7),
    "OwnFibreGeometry": ("own-fibre-geometry", 4),
    "TupleQueryTransportCore": ("tuple-query-transport-core", 4),
    "TupleQuerySymbols": ("tuple-query-symbols", 8),
    "TupleQueryTransport": ("tuple-query-transport", 5),
    "InsufficientOwnSupport": ("insufficient-own-support", 7),
    "InsufficientOwnSupportFamily": ("insufficient-own-support-family", 4),
    "SelectedOwnSymbol": ("selected-own-symbol", 11),
    "SelectedOwnSupportGame": ("selected-own-support-game", 7),
}  # Frozen: 57 new named audits and 17 reused export audits, not 74 new results.
ATTEMPTS = {"FixedTargetQuerySupport": 1, "OwnSymbolCollision": 3,
    "OwnFibreGeometry": 1, "TupleQueryTransportCore": 1, "TupleQuerySymbols": 1,
    "TupleQueryTransport": 12, "InsufficientOwnSupport": 2,
    "InsufficientOwnSupportFamily": 2, "SelectedOwnSymbol": 14,
    "SelectedOwnSupportGame": 5}
old.BASE = old.helpers.BASE = old.helpers.prior.BASE = BASE
old.INITIAL, old.INITIAL_SHA, old.TARGETS = INITIAL, INITIAL_SHA, TARGETS
require, sha, relative = old.require, old.sha, old.relative


def target_logs(name):
    stem = TARGETS[name][0]
    # Preserve literal actual run tags, with or without -nuc-.
    # Prefixes can overlap (EarlyC1CopyCollision and its Core); the actual
    # recorded TARGET, not a filename prefix, owns each run.
    result = []
    for path in sorted(EX.glob(stem + "-*.log")):
        target = re.search(r"^TARGET=(.+)$", path.read_text(), re.M)
        require(target and target.group(1) in TARGETS, "unexpected target log: " + path.name)
        if target.group(1) == name:
            result.append(path)
    return result


def all_logs():
    return sorted({path for name in TARGETS for path in target_logs(name)})


old.logs = all_logs


def inventory():
    data = old.inventory()
    module = "AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction"
    entries = [entry for entry in json.loads(INITIAL.read_text())["files"]
               if entry["module"] == module and entry["kind"] == "source"]
    require(len(entries) == 1, "missing frozen restoration trace source")
    entry = entries[0]
    local = EX / "own-support-import-snapshots/V7Tag73ConcreteRestorationTraceInduction.lean.pinned"
    require(sha(local) == entry["sha256"] ==
            "6a21a2a463ca4ed109e09ab7e629828e083cb5be13e3657ab185ee649784c9d2",
            "restoration trace fallback differs from pinned source")
    artifacts = {(row["remote_path"], row["sha256"]): row for row in data["artifacts"]}
    for run in data["runs"]:
        log = (RD / run["log"]).read_text()
        task = re.search(r"^REMOTE_TASK=(.+)$", log, re.M).group(1)
        raw = task + "/overlay/" + entry["overlay"]
        artifacts[(raw, entry["sha256"])] = {"remote_path": raw,
            "local_path": relative(local), "sha256": entry["sha256"],
            "retention": "Exact borrowed26a9 blob after concurrent main-source drift; unchanged frozen remote source/olean and manifests. No main overwrite or proof replay."}
    data["artifacts"] = list(artifacts.values())
    return data


def leaves(transfer):
    result = []
    for name in TARGETS:
        green, diagnostics = [], []
        for path in target_logs(name):
            try:
                green.append(old.helpers.check_leaf(name, path, transfer))
            except (OSError, ValueError, KeyError) as error:
                diagnostics.append({"log": relative(path), "log_sha256": sha(path),
                    "status": "retained_diagnostic_not_release_evidence", "reason": str(error),
                    "recorded_exits": re.findall(r"^LEAN_EXIT=(\d+)\s*$", path.read_text(), re.M)})
        role = ("existing_proof_missing_output_export_new_native_environment" if
                name == "FixedTargetQuerySupport" else "new_current_turn_proof")
        result.append({"target": name + ".lean", "evidence_role": role,
                       "status": "green" if green else "pending",
                       "runs": green, "retained_diagnostics": diagnostics})
    return result


def elaboration_history():
    source = EX / "tuple-query-transport-nuc-v10-source.txt"
    text = source.read_text()
    declared = re.findall(r"^set_option maxRecDepth (\d+)( in)?\s*$", text, re.M)
    names = re.findall(r"^set_option maxRecDepth 400 in\s*\ntheorem (\w+)", text, re.M)
    require(declared == [("200", ""), ("400", " in"), ("400", " in")] and
            names == ["selected_residual_fold", "source_query_residual"],
            "retained v10 declaration-local recursion allowance changed")
    require(re.findall(r"^set_option maxHeartbeats (\d+)\s*$", text, re.M) == ["150000"],
            "retained v10 heartbeat allowance changed")
    log = EX / "tuple-query-transport-nuc-v10.log"
    require(re.findall(r"^LEAN_EXIT=(\d+)\s*$", log.read_text(), re.M) == ["1"],
            "v10 must remain failed diagnostic evidence")
    current = {}
    for name in ("TupleQuerySymbols", "TupleQueryTransport", "SelectedOwnSymbol"):
        path = EX / (name + ".lean")
        raw = path.read_text()
        require(re.findall(r"^set_option maxRecDepth (\d+)( in)?\s*$", raw, re.M)
                == [("200", "")], "current recursion budget changed: " + name)
        require(re.findall(r"^set_option maxHeartbeats (\d+)\s*$", raw, re.M)
                == ["150000"], "current heartbeat budget changed: " + name)
        current[name] = {"source_sha256": sha(path), "max_rec_depth": 200,
                         "max_heartbeats": 150000}
    return {"current_source_settings": current,
            "failed_v10": {"snapshot": relative(source), "source_sha256": sha(source),
                "log_sha256": sha(log), "exit": 1, "module_max_rec_depth": 200,
                "declaration_local_max_rec_depth": 400, "declarations": names,
                "max_heartbeats": 150000,
                "authorization": "Root authorized only these two static adapters; no memory, CPU or heartbeat limit change.",
                "status": "Failed doc-comment and bounded definitional-equality diagnostics; no successful depth-400 proof is claimed."},
            "replacement": "Settled symbolic declarations are a separate TupleQuerySymbols leaf; the remaining zero-check adapters use depth 200. Source settings alone do not establish a proof."}


def reused_dependency():
    source = EX / "FixedTargetQuerySupport.lean"
    expected = "61e265e65c15bcee5f21d3aea671a734bf55657d9ca736866348396ac2b25dad"
    require(sha(source) == expected, "reused dependency source changed")
    old_record = RD / "lean-repair-evidence.json"
    record = json.loads(old_record.read_text())
    require(record["lean"]["source_sha256"] == expected and
            record["lean"]["exit_code"] == 0 and record["lean"]["audited_declarations"] == 17,
            "prior dependency proof record changed")
    return {"source_sha256": expected, "prior_proof_commit": "1803896acf5d8c4ebe769b3927010031faf40e0e",
            "prior_record_sha256": sha(old_record), "prior_log_sha256": sha(RD / record["lean"]["log"]),
            "recorded_prior_lean_version": record["environment"]["lean"],
            "reason": "Old successful command did not export an olean; targeted retained-cache searches found no output. Root authorized only this missing-artifact export in the pinned native NUC environment.",
            "new_mathematics": False, "reused_named_audits": 17}


def restricted_ledger():
    path = RD / "own-support-ledger.json"
    data = json.loads(path.read_text())
    event = data["new_restricted_event"]
    k, domain, q = (2**31-1)**4, 262144, 22
    schedules, common = comb(domain, q), comb(9556, q)
    gamma, alpha, size, degree, exceptional = k-1, k, 111, 28, 28*1048576
    integer_count = size*(common*exceptional*alpha +
                         schedules*(degree*alpha+(gamma-degree)*3))
    normalized = Fraction(integer_count, schedules*gamma*alpha)
    beta = Fraction(common, schedules)
    common_term = beta*Fraction(exceptional, gamma)
    outside_term = Fraction(degree, gamma)+(1-Fraction(degree, gamma))*Fraction(3, alpha)
    require(normalized == size*(common_term+outside_term), "independent count normalization differs")
    def value(record):
        return Fraction(int(record["numerator"]), int(record["denominator"]))
    for name, expected in (("coarse_probability", normalized),
            ("one_member_common_term", common_term), ("one_member_outside_term", outside_term),
            ("common_schedule_probability", beta)):
        require(value(event[name]) == expected, "restricted ledger arithmetic differs: " + name)
    require(Fraction(1, 2**113) < normalized < Fraction(1, 2**112), "restricted display interval differs")
    require(data["parent_revision"] == BASE and int(data["field_size"]) == k,
            "restricted ledger source/field pin changed")
    require((event["family_cardinality_cap"], event["gamma_degree"],
             event["own_support_symbols_threshold"], event["common_fibres_cap"],
             event["exception_gamma_cap"]) == (111, 28, 38228, 9556, 29360128),
            "restricted event constants changed")
    require(data["global_extraction_bound"] is None and data["global_remaining_allowance"] is None
            and event["global_charge"] is None, "restricted arithmetic promoted to global charge")
    require(data["proof_body_bytes"] == 697*16+52+24+22*621+2*296*26 == 40282
            and data["new_proof_bytes"] == data["new_verifier_operations"] ==
                data["grinding_security_credit"] == 0, "wire/work boundary changed")
    require(data["new_complete_transaction_CU"] is None and data["new_prover_measurements"] is None
            and data["quantum_claim"] is None, "unmeasured performance/quantum claim introduced")
    return {"status": "independent_exact_integer_and_rational_check", "ledger_sha256": sha(path),
            "generator_sha256": sha(EX / "own_support_ledger.py"),
            "integer_count_numerator": str(integer_count),
            "original_product_denominator": str(schedules*gamma*alpha),
            "bits_interval": [112, 113],
            "scope": "Restricted represented true-final, insufficient-own-support pointwise event under the stated conditional product law. The coarse outside term intentionally uses all schedules, not a conditioned pole-free domain. No global acceptance/extraction composition."}


def retained_tiny_control():
    path = EX / "insufficient-own-support-control.json"
    data = json.loads(path.read_text())
    expected = {"outcomes_per_tuple": 3*6*7, "charged_count": 3*7,
        "common_count": 2*7, "wrong_count": 7,
        "proved_shape_upper_bound": 2*7+(7+5*3),
        "without_gamma_charge_count": 2*6*7+7,
        "after_gamma_singleton_common_count": 2*6*7,
        "unchecked_zero_denominator_wrong_count": 6*7,
        "pole_rejecting_count": 2*7, "adaptive_two_member_union_count": 2*3*7,
        "quantum_or_QM31_probability_claim": None}
    require(all(data[key] == value for key, value in expected.items()), "retained F7 control counts differ")
    require("not all strategies" in data["scope"], "tiny control scope broadened")
    return {"source_sha256": sha(EX / "insufficient_own_support_control.py"),
            "output_sha256": sha(path), "reported_counts_checked": expected,
            "scope": "Retained fixed F7 fixture only, simple count arithmetic checked read-only; no control rerun, field search or QM31 extrapolation."}


def final_census(checked, retained):
    require(CENSUS_FINAL and set(ATTEMPTS) == set(TARGETS), "census not frozen")
    for name, count in ATTEMPTS.items():
        paths = target_logs(name)
        versions = [int(re.search(r"-v(\d+)\.log$", path.name).group(1)) for path in paths]
        require(sorted(versions) == list(range(1, count+1)), "missing/extra retained attempt: " + name)
    require(all(row["status"] == "green" and len(row["runs"]) == 1 for row in checked),
            "final target missing unique current-source green evidence")
    new = sum(len(row["runs"][0]["axiom_audits"]) for row in checked
              if row["evidence_role"] == "new_current_turn_proof")
    reused = sum(len(row["runs"][0]["axiom_audits"]) for row in checked
                 if row["evidence_role"] != "new_current_turn_proof")
    require((len(checked), new, reused) == (10, 57, 17), "final leaf/axiom census changed")
    require(len(retained) == 42 and sum(row["exit"] == 0 for row in retained) == 10
            and sum(row["exit"] == 1 for row in retained) == 32,
            "final retained success/failure census changed")
    for row in retained:
        log = (RD / row["log"]).read_text()
        require(len(row["measurements"]) == 1, "ambiguous attempt resource record")
        measurement = row["measurements"][0]
        require(measurement["format"] == "GNU_time_v" and measurement["swaps"] == 0
                and measurement["peak_rss_bytes"] <= 10*1024**3, "attempt resources changed")
        for setting in ("memory.high=8589934592", "memory.max=10737418240",
                        "memory.swap.max=0", "cpu.max=200000 100000", "-j1 -M9500"):
            require(setting in log, "missing capped attempt setting: " + row["log"])
    return {"new_leaves": 9, "new_named_standard_axiom_audits": new,
            "reused_dependency_exports": 1, "reused_named_standard_axiom_audits": reused,
            "retained_attempts": 42, "successful_attempts": 10, "failed_attempts": 32,
            "versions_by_target": ATTEMPTS,
            "all_recorded_attempt_swaps_zero": True,
            "maximum_single_attempt_peak_rss_bytes": max(
                row["measurements"][0]["peak_rss_bytes"] for row in retained),
            "scope": "Per-process GNU measurements only; no host-wide or aggregate concurrent RSS claim. Failed axiom output is not counted."}


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "new initial manifest changed")
    data = json.loads(INITIAL.read_text())
    require(data["research"] == BASE and data["pending_no_olean"] == [], "new source parent changed")
    origin = data["origin"]
    require(sha(RD / origin["receipt_name"]) == origin["receipt_sha256"], "prior final receipt changed")
    for fallback in origin["retained_source_fallbacks"]:
        require(sha(Path(fallback["retained_local"])) == fallback["sha256"], "retained source fallback changed")
    require(origin["research"] == ORIGIN, "inherited cache origin confused with source parent")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"], "prior final snapshot changed")
    require(sha(EX / "own-support-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "prior green output receipt changed")
    require(sha(EX / "bootstrap_own_support.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    sources = outputs = 0
    for item in data["files"]:
        if item["kind"] == "source":
            borrowed = item["module"].startswith("AspisFormal.")
            revision = old.helpers.prior.BORROWED if borrowed else BASE
            path = ("AspisFormal/" if borrowed else "docs/research/v8-no-work-100-20260907/experiments/") + item["overlay"]
            raw = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + path])
            require(hashlib.sha256(raw).hexdigest() == item["sha256"], "pinned imported source changed: " + item["module"])
            sources += 1
        else:
            require(sha(Path(item["local"])) == item["sha256"], "retained compiled artifact changed: " + item["module"])
            outputs += 1
    log = EX / "own-support-bootstrap-preflight.log"
    text = log.read_text()
    require("METADATA_EXIT=0" in text and "OVERLAY_PROVENANCE_PASS=" + str(len(data["files"])) in text and
            INITIAL_SHA in text, "missing successful remote metadata preflight")
    require((sources, outputs) == (387, 387), "frozen import census changed")
    drift_source = EX / "own-support-import-snapshots/V7Tag73ConcreteRestorationTraceInduction.lean.pinned"
    drift_log = EX / "own-support-import-drift-check.log"
    module = "AspisFormal.K1.V7Tag73ConcreteRestorationTraceInduction"
    remote_hashes = dict((raw.rsplit("/", 1)[-1], digest) for digest, raw in
        re.findall(r"^([a-f0-9]{64})  (.+)$", drift_log.read_text(), re.M))
    for entry in data["files"]:
        if entry["module"] == module:
            require(remote_hashes.get(Path(entry["overlay"]).name) == entry["sha256"],
                    "remote restoration trace drift check differs from frozen manifest")
            if entry["kind"] == "source":
                require(sha(drift_source) == entry["sha256"], "new source fallback changed")
    return {"status": "green", "initial_manifest_sha256": INITIAL_SHA, "origin": origin,
            "pinned_source_blobs_checked": sources, "retained_compiled_artifacts_checked": outputs,
            "metadata_log_sha256": sha(log), "host_preflight_sha256": sha(EX / "own-support-host-preflight.log"),
            "native_package_revisions": data["packages"],
            "new_source_fallback": {"module": module, "source": relative(drift_source),
                "source_sha256": sha(drift_source), "remote_check_sha256": sha(drift_log),
                "reason": "Concurrent main source changed; exact pinned git and unchanged remote source/olean were verified. No cache edit or proof replay."},
            "boundary": "Inherited source-to-olean evidence and exact artifact bytes; pinned native package revisions are not a compiler reproduction or package replay. The inherited Types diagnostic is not counted as a proof."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt generation is not an evidence pass")
        data = inventory()
        print(json.dumps(data, indent=2))
        return int(bool(data["unmapped_artifacts"]))
    old.helpers.LEAVES = {name: (stem, old.target_count(name, count)) for name, (stem, count) in TARGETS.items()}
    transfer = old.helpers.prior.Transfer(RD / "own-support-transfer.json")
    require(transfer.data is not None, "missing new-turn receipt")
    output = {"schema": "aspis-v8-own-support-evidence-v1", "parent_revision": BASE,
              "borrowed_formal_revision": old.helpers.prior.BORROWED,
              "mathlib_revision": old.helpers.prior.MATHLIB, "lean_commit": old.helpers.prior.LEAN,
              "auditor_sha256": sha(Path(__file__).resolve()), "target_census_final": CENSUS_FINAL,
              "read_only_helper_sha256": {name: sha(EX / name) for name in
                  ("audit_symbolic_ood_evidence.py", "audit_component_cover_evidence.py",
                   "audit_covered_family_evidence.py", "audit_quotient_family_evidence.py",
                   "audit_off_family_tail_evidence.py")},
              "transfer_receipt_sha256": sha(transfer.path), "bootstrap": bootstrap(),
              "leaves": leaves(transfer),
              "retained_runs": prior.inherited.retained_runs(transfer),
              "attempt_source_snapshots": prior.source_snapshots(transfer),
              "reused_dependency_export": reused_dependency(),
              "elaboration_history": elaboration_history(),
              "restricted_event_arithmetic": restricted_ledger(),
              "retained_tiny_control": retained_tiny_control(),
              "proof_body_bytes": 40282, "new_verifier_operations": 0, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Only the listed focused implications with their exact premises. No full verifier/extractor, payment witness, full-view privacy, actual Fiat-Shamir or CU-parity claim."}
    output["final_census"] = final_census(output["leaves"], output["retained_runs"])
    complete = CENSUS_FINAL and bool(TARGETS) and all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "target census or endpoint remains pending")
        require(json.loads((RD / "own-support-evidence.json").read_text()) == output, "recorded evidence differs")
        print("Own-support focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("OWN_SUPPORT_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
