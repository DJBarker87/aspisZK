#!/usr/bin/env python3
"""Read-only f0f46ffe focused artifact audit; never invokes a compiler.

The coordinator must freeze the target census before this can report complete.
No unchanged proof suite, native package cache or field computation is replayed.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import re
import subprocess
import sys

import audit_component_cover_evidence as inherited

old = inherited.old
EX, RD = old.EX, old.RD
BASE = "f0f46ffede8812252ac7cee9edf5547f228533d5"
ORIGIN = "9254b2416c3f8c3c488d0475a00d812fee836e00"
INITIAL = EX / "symbolic-ood-initial-manifest.json"
INITIAL_SHA = "5deb683b63262b20ffe0502f5ffbc29b711772e0f4f6a09c997c98dc196073d2"
CENSUS_FINAL = True
TARGETS = {
    "SelectedCopyLinkBalance": ("selected-copy-link-balance", 12),
    "CurveOODDerivative": ("curve-ood-derivative", 6),
    "FactorCoherence": ("factor-coherence", 7),
    "SelectedFactorCoherence": ("selected-factor-coherence", 5),
    "RationalHelperIdentity": ("rational-helper-identity", 7),
    "FactorIdentityCover": ("factor-identity-cover", 7),
    "SelectedIdentityCover": ("selected-identity-cover", 2),
    "CausalFactorReduction": ("causal-factor-reduction", 7),
}
old.BASE = old.helpers.BASE = old.helpers.prior.BASE = BASE
old.INITIAL, old.INITIAL_SHA, old.TARGETS = INITIAL, INITIAL_SHA, TARGETS
inherited.DIAGNOSTICS = {}
require, sha, relative = old.require, old.sha, old.relative


def inventory():
    data = old.inventory()
    module = "AspisFormal.K1.V7Tag73CheckedRefinementFullFutureFreePath"
    initial = json.loads(INITIAL.read_text())
    entries = [item for item in initial["files"] if item["module"] == module and item["kind"] == "source"]
    require(len(entries) == 1, "missing frozen full-future source entry")
    entry = entries[0]
    local = EX / "symbolic-ood-import-snapshots/V7Tag73CheckedRefinementFullFutureFreePath.lean.pinned"
    require(sha(local) == entry["sha256"] == "b6b196e9a78811ddc9c6b31a85ce57ed53dcfa08a10e569b3ec3a43099e9cd66",
            "pinned source fallback differs from borrowed initial bytes")
    artifacts = {(row["remote_path"], row["sha256"]): row for row in data["artifacts"]}
    for run in data["runs"]:
        text = (RD / run["log"]).read_text()
        task = re.search(r"^REMOTE_TASK=(.+)$", text, re.M).group(1)
        raw = task + "/overlay/" + entry["overlay"]
        artifacts[(raw, entry["sha256"])] = {"remote_path": raw, "local_path": relative(local),
            "sha256": entry["sha256"],
            "retention": "Exact borrowed26a9 git blob retained after concurrent main source advanced; unchanged remote overlay and old manifests, no cache overwrite or proof replay."}
    data["artifacts"] = list(artifacts.values())
    return data


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "new initial manifest changed")
    data = json.loads(INITIAL.read_text())
    require(data["research"] == BASE and data["pending_no_olean"] == [], "new source parent changed")
    origin = data["origin"]
    require(origin["research"] == ORIGIN, "inherited cache origin confused with source parent")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"], "prior final snapshot changed")
    require(sha(EX / "symbolic-ood-prior-green-outputs.json") == origin["green_outputs_sha256"],
            "prior green output receipt changed")
    require(sha(EX / "bootstrap_symbolic_ood.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
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
    log = EX / "symbolic-ood-bootstrap-preflight.log"
    text = log.read_text()
    require("METADATA_EXIT=0" in text and "OVERLAY_PROVENANCE_PASS=" + str(len(data["files"])) in text and
            INITIAL_SHA in text, "missing successful remote metadata preflight")
    require((sources, outputs) == (357, 357), "frozen import census changed")
    return {"status": "green", "initial_manifest_sha256": INITIAL_SHA, "origin": origin,
            "pinned_source_blobs_checked": sources, "retained_compiled_artifacts_checked": outputs,
            "metadata_log_sha256": sha(log), "host_preflight_sha256": sha(EX / "symbolic-ood-host-preflight.log"),
            "native_package_revisions": data["packages"],
            "boundary": "Inherited source-to-olean evidence and exact artifact bytes; pinned native package revisions are not a compiler reproduction or package replay. The inherited Types diagnostic is not counted as a proof."}


def separability_cache():
    path = EX / "symbolic-ood-separability-cache.json"
    rows = json.loads(path.read_text())
    items = {(item["module"], item["kind"]): item for item in json.loads(INITIAL.read_text())["files"]}
    require(len(rows) == 7, "borrowed separability import census changed")
    for row in rows:
        source, output = items[(row["module"], "source")], items[(row["module"], "olean")]
        require(row["source_hash"] == source["sha256"] and row["olean_hash"] == output["sha256"],
                "borrowed separability source/output pin changed")
        require(all(row[key] is True for key in ("pinned_source_match", "inspected_worktree_match",
                "retained_olean_match")), "separability inspection had a mismatch")
    return {"status": "pinned_import_map_checked", "map_sha256": sha(path), "modules": len(rows),
            "scope": "Existing prime-factor separability chain only; no square-free parent claim or actual second-OOD smoothness inference. Exact inherited source/output bytes are checked by bootstrap."}


def scope_timing():
    path = EX / "selected-copy-link-balance-scope-timing.log"
    require(sha(path) == "31848c42b2e629d4adbe114df09ad693efc6fba1c51f47c04ff65537ea590c11",
            "retained journal excerpt changed")
    text = path.read_text()
    for timestamp, message in (
        ("23:48:39", "Started aspis-symbolic-curve-ood-derivative-nuc-v1.scope"),
        ("23:48:40", "Started aspis-symbolic-selected-copy-link-balance-nuc-v2.scope"),
        ("23:48:42", "aspis-symbolic-curve-ood-derivative-nuc-v1.scope: Consumed"),
        ("23:48:46", "aspis-symbolic-selected-copy-link-balance-nuc-v2.scope: Consumed")):
        require(any("2026-09-09T" + timestamp + "+00:00" in line and message in line
                    for line in text.splitlines()), "missing observed scope timestamp")
    return {"status": "reported_coordination_deviation", "fully_serialized": False,
            "journal_excerpt": relative(path), "journal_excerpt_sha256": sha(path),
            "overlapping_runs": ["curve-ood-derivative-nuc-v1", "selected-copy-link-balance-nuc-v2"],
            "approximate_overlap_seconds": 2, "timestamp_resolution_seconds": 1,
            "simultaneous_declared_memory_max_bytes": 20 * 1024**3,
            "aggregate_peak_rss_bytes": None,
            "scope": "A grant/hold message race caused brief overlap of two individually capped scopes. Source/output provenance remains checked; no serialized performance or measured aggregate RSS is claimed."}


def source_snapshots(transfer):
    result = []
    for path in old.logs():
        log = path.read_text()
        name = re.search(r"^TARGET=(.+)$", log, re.M).group(1)
        hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M)
        targets = {digest for digest, raw in hashes if Path(raw).name == name + ".lean"}
        snapshots = [(digest, raw) for digest, raw in hashes if Path(raw).name == path.stem + "-source.txt"]
        require(len(targets) == len(snapshots) == 1 and targets == {snapshots[0][0]},
                "attempted source snapshot differs from logged target: " + path.name)
        digest, raw = snapshots[0]
        retained = transfer.file(raw, digest)
        result.append({"log": relative(path), "source_snapshot": relative(retained), "sha256": digest})
    return {"status": "every_retained_attempt_snapshot_matches_target_hash", "attempts": result,
            "scope": "Runner-created exact source snapshots, including failed attempts; no inverse-edit reconstruction is used for this batch."}


def arithmetic():
    path, script = RD / "symbolic-factor-ledger.json", EX / "symbolic_factor_ledger.py"
    data = json.loads(path.read_text())
    k, T, q = (2**31 - 1)**4, 262144, 22
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    # Reconstruct directly, independently of both ledger generators. The
    # existing one-shot rho and four-repair charges are already collected.
    old = beta(9557) + Fraction(9396508281246, k) * beta(117964) + Fraction(319, k - 1) + Fraction(739, k)
    term, local = Fraction(117077, k - 1), old + Fraction(117077, k - 1)
    rational = lambda row: Fraction(int(row["numerator"]), int(row["denominator"]))
    require(data["parent_revision"] == BASE and data["theorem"] == "AspisV8.CausalFactorReduction.total_reduction",
            "incorrect factor reduction parent/event")
    p = data["parameters"]
    require((int(p["field_size"]), p["queries"], p["fibres"], p["interpolant_x_bound"],
             p["interpolant_y_rows"], p["interpolant_gamma_bound"], p["component_answer_degree"],
             p["helper_curve_degree_unchanged"]) == (k, q, T, 114688, 112, 117078, 28, 2),
            "sampling or helper/claim degree changed")
    require([row["name"] for row in data["terms"]] == ["missing_good_quotient",
            "good_quotient_outside_identity_factor_family"] and
            [rational(row["value"]) for row in data["terms"]] == [old, term],
            "factor-event partition or rational charges changed")
    require(data["terms"][1]["replaces_previous_OOD_nonidentity_charge"] is True and
            data["terms"][1]["extra_derivative_content_zero_specialization_factor_union_charges"] is False,
            "duplicated derivative/content/family charge")
    require(rational(data["local_reduction_ceiling"]) == local and local < Fraction(1, 2**100) and
            rational(data["local_difference_not_global_allowance"]) == Fraction(1, 2**100) - local,
            "incorrect exact local arithmetic")
    previous = json.loads((RD / "component-ood-ledger.json").read_text())
    require(rational(previous["local_reduction_ceiling"]) == local and data["arithmetic_ceiling_unchanged"] is True,
            "unchanged arithmetic claim is false")
    retained = data["retained_factor_branch"]
    require(retained["remaining_mass"] is None and retained["honest_singular_parent_allowed"] is True and
            retained["factor_cardinality_upper_bound"] == p["interpolant_y_rows"] - 1,
            "retained factor class or scope changed")
    require(data["secondary_regular_branch"]["included_in_primary_ledger"] is False and
            data["secondary_regular_branch"]["conditional_degree_bound"] == 117077 - 28,
            "secondary regularity charge promoted or miscounted")
    require(data["global_extraction_bound"] is None and data["global_remaining_allowance"] is None,
            "unsupported global extraction budget promoted")
    require((data["body_bytes"], data["new_proof_bytes"], data["new_verifier_operations"],
             data["new_complete_transaction_CU"], data["new_prover_measurements"], data["grinding_security_credit"])
            == (40282, 0, 0, None, None, 0), "body/operation/work contract changed")
    require(697 * 16 + 52 + 24 + q * 621 + 2 * 296 * 26 == 40282, "body byte census mismatch")
    return {"status": "green", "ledger_sha256": sha(path), "generator_sha256": sha(script),
            "theorem": data["theorem"], "local_reduction_ceiling": data["local_reduction_ceiling"],
            "arithmetic_unchanged_stronger_retained_event": True,
            "scope": "Independent exact rational accounting, not an extraction bound. The same-Q both-identity-factor accepted mass stays symbolic; neither111 factors nor a polynomial identity is a checked component tuple/payment witness."}


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
    transfer = old.helpers.prior.Transfer(RD / "symbolic-ood-transfer.json")
    require(transfer.data is not None, "missing new-turn artifact receipt")
    output = {"schema": "aspis-v8-symbolic-ood-evidence-v1", "parent_revision": BASE,
              "borrowed_formal_revision": old.helpers.prior.BORROWED,
              "mathlib_revision": old.helpers.prior.MATHLIB, "lean_commit": old.helpers.prior.LEAN,
              "auditor_sha256": sha(Path(__file__).resolve()), "target_census_final": CENSUS_FINAL,
              "read_only_helper_sha256": {name: sha(EX / name) for name in
                  ("audit_component_cover_evidence.py", "audit_covered_family_evidence.py",
                   "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
              "transfer_receipt_sha256": sha(transfer.path), "bootstrap": bootstrap(),
              "leaves": old.helpers.leaves(transfer), "retained_runs": inherited.retained_runs(transfer),
              "borrowed_separability_cache": separability_cache(),
              "scope_timing": scope_timing(),
              "attempt_source_snapshots": source_snapshots(transfer),
              "exact_arithmetic": arithmetic(),
              "proof_body_bytes": 40282, "new_verifier_operations": 0, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "Only the listed new focused implications with their exact hypotheses. No bounded authenticated extractor, checked payment witness, full-view privacy, actual source/Fiat-Shamir or CU-parity theorem is inferred."}
    complete = CENSUS_FINAL and bool(TARGETS) and all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "target census or endpoint remains pending")
        require(json.loads((RD / "symbolic-ood-evidence.json").read_text()) == output, "recorded evidence differs")
        print("Symbolic OOD focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("SYMBOLIC_OOD_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
