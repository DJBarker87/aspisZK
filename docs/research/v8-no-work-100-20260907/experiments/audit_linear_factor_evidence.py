#!/usr/bin/env python3
"""Read-only6f1ebbe5 focused evidence; no compiler or prior-suite replay."""
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
BASE = "6f1ebbe55fcc6fd008071329d5270aae0521cf9a"
ORIGIN = "f0f46ffede8812252ac7cee9edf5547f228533d5"
INITIAL = EX / "linear-factor-initial-manifest.json"
INITIAL_SHA = "a6c1ea8c94462ebe64d082c81a464d33141dc2c8ae79ecc44fcd7d512d082b17"
CENSUS_FINAL = True
TARGETS = {
    "MonicFactorOOD": ("monic-factor", 8),
    "SelectedMonicCover": ("selected-monic", 3),
    "PrimeFactorRegularity": ("prime-regular", 4),
    "RationalHelperSpecialization": ("rational-specialization", 2),
    "PolynomialValueInterpolation": ("polynomial-value-interpolation", 6),
    "LinearFactorInterpolation": ("linear-factor-interpolation", 4),
    "CircleGRSLinearity": ("circle-grs-linearity", 5),
    "SelectedGRSSubmodule": ("selected-grs-submodule", 5),
    "SelectedLinearFactorRecovery": ("selected-linear-factor-recovery", 3),
    "SelectedCopyAliasCore": ("selected-copy-alias-core", 12),
    "SelectedCopyAliases": ("selected-copy-aliases", 11),
    "SelectedCopyAliasQM31": ("selected-copy-alias-qm31", 9),
}
old.BASE = old.helpers.BASE = old.helpers.prior.BASE = BASE
old.INITIAL, old.INITIAL_SHA, old.TARGETS = INITIAL, INITIAL_SHA, TARGETS
require, sha, relative = old.require, old.sha, old.relative


def target_logs(name):
    stem = TARGETS[name][0]
    # Preserve actual run tags, including root's monic-factor-v1 rather
    # than fabricating a -nuc- pathname absent from the logged manifest.
    return sorted(EX.glob(stem + "-*.log"))


def all_logs():
    return sorted({path for name in TARGETS for path in target_logs(name)})


old.logs = all_logs


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
        result.append({"target": name + ".lean", "status": "green" if green else "pending",
                       "runs": green, "retained_diagnostics": diagnostics})
    return result


def native_copy_imports():
    path = EX / "linear-factor-native-copy-imports.log"
    text = path.read_text()
    require(old.helpers.prior.MATHLIB in text and "MISSING=" not in text,
            "native copy import availability/pin check failed")
    hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", text, re.M)
    require(len(hashes) == 4 and sorted(Path(raw).name for _, raw in hashes) ==
            ["FieldDivision.lean", "FieldDivision.olean", "Wronskian.lean", "Wronskian.olean"],
            "native copy import observation census changed")
    return {"status": "read_only_cache_availability_record", "log": relative(path),
            "log_sha256": sha(path), "native_mathlib_revision": old.helpers.prior.MATHLIB,
            "observed_artifacts": [{"remote_path": raw, "sha256": digest} for digest, raw in hashes],
            "scope": "Presence and exact-byte observation for two existing native imports; not a package compilation replay or independent source-to-olean reproduction."}


def arithmetic():
    path, script = RD / "linear-factor-ledger.json", EX / "linear_factor_ledger.py"
    data = json.loads(path.read_text())
    p, T, q = 2**31 - 1, 262144, 22
    k = p**4
    n = k - p**2
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    previous = beta(9557) + Fraction(9396508281246, k) * beta(117964) + Fraction(117396, k - 1) + Fraction(739, k)
    pair, sparse = Fraction(114687**2, n * (n - 1)), Fraction(28, k - 1)
    rational = lambda row: Fraction(int(row["numerator"]), int(row["denominator"]))
    require(data["parent_revision"] == BASE and rational(data["previous_local_reduction_ceiling"]) == previous and
            data["local_reduction_unchanged"] is True, "previous local accounting changed")
    classes = data["new_class_information"]
    require(len(classes) == 4, "class ledger census changed")
    model = classes[0]["conditional_uniform_distinct_K_minus_CM31_model"]
    require(classes[0]["finite_pair_numerator_upper_bound"] == 114687**2 and
            int(model["domain_cardinality"]) == n and rational(model["bound"]) == pair and
            pair < Fraction(1, 2**214) and classes[0]["factor_count_multiplier"] is False and
            classes[0]["global_charge"] is None and "NOT instantiated" in model["status"],
            "conditional two-OOD counting model changed or promoted")
    require(rational(classes[1]["bound_under_fresh_uniform_nonzero_gamma"]) == sparse and
            sparse < Fraction(1, 2**119) and classes[1]["global_charge"] is None,
            "per-factor specialization arithmetic changed or promoted")
    require(classes[2]["extra_exception_term"] is False and
            classes[3]["nonzero_good_cardinality_upper_bound"] == 1 and classes[3]["global_charge"] is None,
            "derived pole/regularity classifications charged as unproved probabilities")
    copy = data["selected_copy_partition"]
    require(copy["actual_active_link_count_at_most"] == 136 and
            copy["lambda_error_degree_at_most"] == "16 * actual_active_link_count" and
            copy["chi_error_degree_strictly_below"] == "2 * actual_active_link_count" and
            copy["global_probability_charge"] is None, "selected copy scope or degree bounds changed")
    require(data["global_extraction_bound"] is None and data["global_remaining_allowance"] is None and
            all(value is None for value in data["remaining_mass"].values()), "unsupported global extraction charge")
    require((data["body_bytes"], data["new_proof_bytes"], data["new_verifier_operations"],
             data["new_complete_transaction_CU"], data["new_prover_measurements"], data["grinding_security_credit"])
            == (40282, 0, 0, None, None, 0), "body/operation/work contract changed")
    require(697 * 16 + 52 + 24 + q * 621 + 2 * 296 * 26 == 40282, "body census mismatch")
    return {"status": "green", "ledger_sha256": sha(path), "generator_sha256": sha(script),
            "unchanged_local_reduction_ceiling": data["previous_local_reduction_ceiling"],
            "conditional_pair_model": model["bound"], "per_factor_sparse_model": classes[1]["bound_under_fresh_uniform_nonzero_gamma"],
            "scope": "Independent exact rational/class accounting only. The actual two-OOD sampler law and full factor/early-C1/extractor composition remain uninstantiated; new class bounds are not added to a global allowance."}

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
    require(sha(EX / "linear-factor-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "prior green output receipt changed")
    require(sha(EX / "bootstrap_linear_factor.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
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
    log = EX / "linear-factor-bootstrap-preflight.log"
    text = log.read_text()
    require("METADATA_EXIT=0" in text and "OVERLAY_PROVENANCE_PASS=" + str(len(data["files"])) in text and
            INITIAL_SHA in text, "missing successful remote metadata preflight")
    require((sources, outputs) == (365, 365), "frozen import census changed")
    return {"status": "green", "initial_manifest_sha256": INITIAL_SHA, "origin": origin,
            "pinned_source_blobs_checked": sources, "retained_compiled_artifacts_checked": outputs,
            "metadata_log_sha256": sha(log), "host_preflight_sha256": sha(EX / "linear-factor-host-preflight.log"),
            "native_package_revisions": data["packages"],
            "boundary": "Inherited source-to-olean evidence and exact artifact bytes; pinned native package revisions are not a compiler reproduction or package replay. The inherited Types diagnostic is not counted as a proof."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt generation is not an evidence pass")
        data = old.inventory()
        print(json.dumps(data, indent=2))
        return int(bool(data["unmapped_artifacts"]))
    old.helpers.LEAVES = {name: (stem, old.target_count(name, count)) for name, (stem, count) in TARGETS.items()}
    transfer = old.helpers.prior.Transfer(RD / "linear-factor-transfer.json")
    require(transfer.data is not None, "missing new-turn receipt")
    output = {"schema": "aspis-v8-linear-factor-evidence-v1", "parent_revision": BASE,
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
              "native_copy_imports": native_copy_imports(),
              "exact_arithmetic": arithmetic(),
              "proof_body_bytes": 40282, "new_verifier_operations": 0, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Only the listed focused implications with their exact premises. No full verifier/extractor, payment witness, full-view privacy, actual Fiat-Shamir or CU-parity claim."}
    complete = CENSUS_FINAL and bool(TARGETS) and all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "target census or endpoint remains pending")
        require(json.loads((RD / "linear-factor-evidence.json").read_text()) == output, "recorded evidence differs")
        print("Linear-factor focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("LINEAR_FACTOR_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
