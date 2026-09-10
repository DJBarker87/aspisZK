#!/usr/bin/env python3
"""Read-only 2f6d82fe focused evidence; no compiler or prior-suite replay."""
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
BASE = "2f6d82fef294410367aa1781fb924af7c38deab9"
ORIGIN = "6f1ebbe55fcc6fd008071329d5270aae0521cf9a"
INITIAL = EX / "denominator-initial-manifest.json"
INITIAL_SHA = "5ab9cfe6a223e1a956e55a56cda678f72f2b758ea9e89aa94b4db3eb1472550d"
CENSUS_FINAL = True
TARGETS = {
    "LinearDenominatorPrimitive": ("linear-denominator-primitive", 3),
    "GammaConstantLinear": ("gamma-constant-linear", 7),
    "SelectedGammaConstantRecovery": ("selected-gamma-constant-recovery", 1),
    "LinearMessageFamily": ("linear-message-family", 3),
    "LinearDenominatorOOD": ("linear-denominator-ood", 4),
    "LinearDenominatorFactors": ("linear-denominator-factors", 5),
    "LinearDenominatorRegression": ("linear-denominator-regression", 6),
    "SelectedLinearCover": ("selected-linear-cover", 8),
    "EarlyC1CopyCollisionCore": ("early-c1-copy-collision-core", 7),
    "EarlyC1CopyCollision": ("early-c1-copy-collision", 12),
}  # Final ten-target, 56 named-audit census.
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


def arithmetic():
    path, script = RD / "denominator-ledger.json", EX / "denominator_ledger.py"
    data = json.loads(path.read_text())
    p, T, q = 2**31 - 1, 262144, 22
    k, n = p**4, p**4 - p**2
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    previous = beta(9557) + Fraction(9396508281246, k) * beta(117964) + Fraction(117396, k - 1) + Fraction(739, k)
    degree, sparse = (2 * 117077 + 1) * 114687, 111 * 28
    first, second = 100 * 16 * 136, 100 * (2 * 136 - 1)
    pair, one, sparse_bound, copy_bound = (Fraction(degree**2, n * (n - 1)),
        Fraction(degree, n), Fraction(sparse, k - 1), Fraction(first + second, k - 1))
    rational = lambda row: Fraction(int(row["numerator"]), int(row["denominator"]))
    require(data["parent_revision"] == BASE and int(data["field_size"]) == k and
            rational(data["unchanged_local_reduction_ceiling"]) == previous,
            "parent, field or previous local accounting changed")
    events = data["new_events"]
    require(len(events) == 3 and all(row["global_charge"] is None for row in events),
            "class census changed or unsupported global charge")
    ood, gamma, copy = events
    model = ood["uniform_distinct_K_minus_CM31_model"]
    require(ood["degree_cap"] == degree == 26854534485 and
            int(ood["pair_count_upper_bound"]) == degree**2 and
            int(model["domain_cardinality"]) == n and rational(model["bound"]) == pair and
            pair < Fraction(1, 2**178) and "not instantiated" in model["status"] and
            "do not add" in ood["overlap"], "OOD model changed or double charged")
    diagnostic = ood["one_point_only_diagnostic"]
    require(rational(diagnostic["bound"]) == one and diagnostic["passes100"] is False and
            Fraction(1, 2**90) < one < Fraction(1, 2**89), "one-point diagnostic changed")
    require(gamma["set_cardinality_cap"] == sparse == 3108 and
            rational(gamma["uniform_nonzero_gamma_model"]["bound"]) == sparse_bound and
            sparse_bound < Fraction(1, 2**112) and "actual gamma hits" in gamma["event"] and
            "sparse property itself is not rare" in gamma["fixing_prefix"] and
            "NOT111 times a query tail" in gamma["scope"], "sparse event or family/query accounting changed")
    require((copy["lambda_root_union_cap"], copy["chi_root_union_cap_each_lambda"]) ==
            (first, second) == (217600, 27100) and
            copy["finite_pair_cap"] == "217600*card(Chi)+27100*card(Lambda)" and
            rational(copy["uniform_nonzero_pair_model"]["bound"]) == copy_bound and
            copy_bound < Fraction(1, 2**106) and "slot-pole" in copy["source_premises"],
            "copy root arithmetic or retained source prerequisites changed")
    require(data["global_extraction_bound"] is None and data["global_remaining_allowance"] is None and
            all(value is None for value in data["remaining_mass"].values()), "global extraction mass promoted")
    require((data["body_bytes"], data["new_proof_bytes"], data["new_verifier_operations"],
             data["new_complete_transaction_CU"], data["new_prover_measurements"],
             data["grinding_security_credit"], data["quantum_claim"]) ==
            (40282, 0, 0, None, None, 0, None), "body/operation/work contract changed")
    require(697 * 16 + 52 + 24 + q * 621 + 2 * 296 * 26 == 40282, "body census mismatch")
    return {"status": "green", "ledger_sha256": sha(path), "generator_sha256": sha(script),
            "unchanged_local_reduction_ceiling": data["unchanged_local_reduction_ceiling"],
            "conditional_ood_pair_model": model["bound"], "one_point_diagnostic": diagnostic["bound"],
            "conditional_sparse_gamma_model": gamma["uniform_nonzero_gamma_model"]["bound"],
            "conditional_copy_pair_model": copy["uniform_nonzero_pair_model"]["bound"],
            "scope": "Independent exact class arithmetic; no new term is added to a global bound. Actual sampler/FS, own-support, source acceptance and checked-payment extraction composition remain uninstantiated."}


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
    require(sha(EX / "denominator-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "prior green output receipt changed")
    require(sha(EX / "bootstrap_denominator.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
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
    log = EX / "denominator-bootstrap-preflight.log"
    text = log.read_text()
    require("METADATA_EXIT=0" in text and "OVERLAY_PROVENANCE_PASS=" + str(len(data["files"])) in text and
            INITIAL_SHA in text, "missing successful remote metadata preflight")
    require((sources, outputs) == (377, 377), "frozen import census changed")
    return {"status": "green", "initial_manifest_sha256": INITIAL_SHA, "origin": origin,
            "pinned_source_blobs_checked": sources, "retained_compiled_artifacts_checked": outputs,
            "metadata_log_sha256": sha(log), "host_preflight_sha256": sha(EX / "denominator-host-preflight.log"),
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
    transfer = old.helpers.prior.Transfer(RD / "denominator-transfer.json")
    require(transfer.data is not None, "missing new-turn receipt")
    output = {"schema": "aspis-v8-denominator-evidence-v1", "parent_revision": BASE,
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
              "exact_arithmetic": arithmetic(),
              "proof_body_bytes": 40282, "new_verifier_operations": 0, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Only the listed focused implications with their exact premises. No full verifier/extractor, payment witness, full-view privacy, actual Fiat-Shamir or CU-parity claim."}
    complete = CENSUS_FINAL and bool(TARGETS) and all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "target census or endpoint remains pending")
        require(json.loads((RD / "denominator-evidence.json").read_text()) == output, "recorded evidence differs")
        print("Denominator focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("DENOMINATOR_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
