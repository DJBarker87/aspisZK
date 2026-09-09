#!/usr/bin/env python3
"""Read-only 9254 component-cover evidence: no builds or old-leaf replay.

The explicit new target census must be complete. Missing/stale success logs,
imported artifacts or requested standard-axiom reports remain pending.
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

import audit_covered_family_evidence as old

EX, RD = old.EX, old.RD
BASE = "9254b2416c3f8c3c488d0475a00d812fee836e00"
ORIGIN = "f19673b4fe72cf74ae687a926eeae9d1e5a6a52e"
INITIAL = EX / "component-cover-initial-manifest.json"
INITIAL_SHA = "5ada1fd379886e25c6845054a825aecf82145f9f9f896c3433b1036407396f45"
TARGETS = {
    "CoveredOriginalSymbols": ("covered-original-symbols", 7),
    "CoveredOODGRS": ("covered-ood-grs", 7),
    "CurveOODGate": ("curve-ood-gate", 6),
    "SelectedOODGate": ("selected-ood-gate", 8),
    "CausalOODReduction": ("causal-ood-reduction", 5),
    "SelectedCopyLayout": ("selected-copy-layout", 2),
    "SelectedCopyLayoutRows": ("selected-copy-layout-rows", 6),
}
DIAGNOSTICS = {"CoveredOODGRSTypes": ("covered-ood-grs-types", 0)}
old.BASE = old.helpers.BASE = old.helpers.prior.BASE = BASE
old.INITIAL, old.INITIAL_SHA, old.TARGETS = INITIAL, INITIAL_SHA, {**TARGETS, **DIAGNOSTICS}
require, sha, relative = old.require, old.sha, old.relative


def inventory():
    data = old.inventory()
    # Two failed sources were reconstructed by reversing the documented edit
    # and hash-checked against the immutable preflight. They were NOT cache
    # snapshots. Preserve that provenance rather than inventing a snapshot.
    retained = {sha(path): path for path in sorted((EX / "component-cover-failed-sources").glob("*.lean.failed"))}
    missing = []
    artifacts = {(row["remote_path"], row["sha256"]): row for row in data["artifacts"]}
    for row in data["unmapped_artifacts"]:
        local = retained.get(row["sha256"])
        if local is None:
            missing.append(row)
        else:
            key = (row["remote_path"], row["sha256"])
            artifacts[key] = {"remote_path": row["remote_path"], "local_path": relative(local),
                              "sha256": row["sha256"],
                              "retention": "inverse-edit reconstruction matching recorded preflight hash, not an earlier cached source snapshot"}
    data["artifacts"] = list(artifacts.values())
    data["unmapped_artifacts"] = missing
    return data


def retained_runs(transfer):
    require(not transfer.data.get("unmapped_artifacts"), "unmapped retained run artifact")
    result = []
    for path in old.logs():
        log = path.read_text()
        name = re.search(r"^TARGET=(.+)$", log, re.M).group(1)
        hashes = re.findall(r"^([a-f0-9]{64})  (.+)$", log, re.M)
        verified = [{"remote_path": raw, "local_path": relative(transfer.file(raw, digest)),
                     "sha256": digest} for digest, raw in hashes]
        exits = re.findall(r"^LEAN_EXIT=(\d+)\s*$", log, re.M)
        require(len(exits) == 1, "missing retained terminal: " + path.name)
        status = "diagnostic_only_not_a_proof_result" if name in DIAGNOSTICS else (
            "successful_target_checked_separately" if exits == ["0"] else "failed_target_not_release_evidence")
        row = {"target": name, "log": relative(path), "log_sha256": sha(path), "status": status,
               "exit": int(exits[0]), "artifacts": verified,
               "measurements": old.helpers.prior.measurements(log)}
        if name in DIAGNOSTICS:
            require(exits == ["0"] and not re.search(r"^#print axioms", (EX / (name + ".lean")).read_text(), re.M),
                    "type diagnostic changed into a theorem release")
            require("-j1 -M9500" in log and "memory.high=8589934592" in log and
                    "memory.max=10737418240" in log and "memory.swap.max=0" in log and
                    "cpu.max=200000 100000" in log, "diagnostic resource scope mismatch")
            row["import_closure"] = old.helpers.prior.remote_closure(name, log, hashes, transfer)
            row["scope"] = "Type/instance inspection only; zero theorem audits, excluded from the seven-proof and 41-audit census."
        result.append(row)
    return result


def arithmetic():
    path, script = RD / "component-ood-ledger.json", EX / "component_ood_ledger.py"
    data = json.loads(path.read_text())
    k, T, q = (2**31 - 1)**4, 262144, 22
    beta = lambda m: Fraction(comb(m, q), comb(T, q))
    # Independent direct collection of the already-charged row/image/query
    # budgets, not a call to either ledger generator.
    previous = beta(9557) + Fraction(9396508281246, k) * beta(117964) + Fraction(319, k - 1) + Fraction(739, k)
    extra = Fraction(117077, k - 1)
    total = previous + extra
    rational = lambda row: Fraction(int(row["numerator"]), int(row["denominator"]))
    require(data["parent_revision"] == BASE, "wrong OOD arithmetic parent")
    p = data["parameters"]
    require((int(p["field_size"]), p["queries"], p["fibres"], p["interpolant_x_bound"],
             p["interpolant_y_rows"], p["interpolant_gamma_bound"], p["component_answer_degree"],
             p["helper_curve_degree_unchanged"]) == (k, q, T, 114688, 112, 117078, 28, 2),
            "OOD/helper degree or sampling parameters changed")
    require([term["name"] for term in data["terms"]] == ["previous_missing_good_quotient_ceiling",
            "good_quotient_nonidentity_OOD_gamma"], "OOD event partition changed")
    require([rational(term["value"]) for term in data["terms"]] == [previous, extra] and
            data["terms"][1]["no_family_union"] is True, "extra repair or family charge in OOD ledger")
    require(rational(data["local_reduction_ceiling"]) == total and total < Fraction(1, 2**100),
            "OOD local rational ceiling mismatch")
    require(rational(data["unused_local_difference_not_a_global_allowance"]) == Fraction(1, 2**100) - total,
            "incorrect unused local difference")
    require(data["support"] == {"quotient_complete_fibres": 9558, "quotient_symbols": 38232,
            "maximum_lost_pole_symbols": 2, "original_symbols": 38230,
            "original_V7_strict_threshold": 38229} and 4 * 9558 - 2 > 38229,
            "symbol-vs-fibre pole deduction changed")
    require(data["retained_identity_branch"]["remaining_mass"] is None and
            data["global_accepted_extraction_failure_bound"] is None and
            data["global_remaining_numerical_allowance"] is None, "unsupported global bound promoted")
    require((p["body_bytes"], data["new_proof_bytes"], data["new_verifier_operations"],
             data["new_complete_transaction_CU"], data["new_prover_time"], data["grinding_security_credit"])
            == (40282, 0, 0, None, None, 0), "operation/byte/work census changed")
    require(697 * 16 + 52 + 24 + q * 621 + 2 * 296 * 26 == 40282, "body census mismatch")
    return {"status": "green", "ledger_sha256": sha(path), "generator_sha256": sha(script),
            "event": data["event"], "local_reduction_ceiling": data["local_reduction_ceiling"],
            "new_term": {"numerator": str(extra.numerator), "denominator": str(extra.denominator)},
            "scope": "Independent exact rational arithmetic only. The retained pair-of-symbolic-OOD-identities branch remains unbounded; this is not accepted-extraction security."}


def bootstrap():
    require(sha(INITIAL) == INITIAL_SHA, "initial component-cover manifest changed")
    data = json.loads(INITIAL.read_text())
    require(data["research"] == BASE and data["pending_no_olean"] == [], "parent or initial state mismatch")
    origin = data["origin"]
    require(origin["research"] == ORIGIN, "prior cache origin confused with current source parent")
    require(sha(EX / origin["manifest_name"]) == origin["manifest_sha256"], "prior snapshot changed")
    require(sha(EX / "component-cover-prior-green-outputs.json") == origin["green_outputs_sha256"], "prior outputs changed")
    require(sha(EX / "bootstrap_component_cover.py") == data["bootstrap"]["source_sha256"], "bootstrap source changed")
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    sources = outputs = 0
    for entry in data["files"]:
        if entry["kind"] == "source":
            borrowed = entry["module"].startswith("AspisFormal.")
            revision = old.helpers.prior.BORROWED if borrowed else BASE
            path = ("AspisFormal/" if borrowed else "docs/research/v8-no-work-100-20260907/experiments/") + entry["overlay"]
            blob = subprocess.check_output(["git", "-C", repo, "show", revision + ":" + path])
            require(hashlib.sha256(blob).hexdigest() == entry["sha256"], "pinned source mismatch: " + entry["module"])
            sources += 1
        else:
            require(sha(Path(entry["local"])) == entry["sha256"], "compiled artifact mismatch: " + entry["module"])
            outputs += 1
    log = EX / "component-cover-bootstrap-preflight.log"
    text = log.read_text()
    require("METADATA_EXIT=0" in text and "OVERLAY_PROVENANCE_PASS=" + str(len(data["files"])) in text and
            INITIAL_SHA in text, "remote bootstrap preflight missing")
    return {"status": "green", "manifest_sha256": INITIAL_SHA, "pinned_source_blobs_checked": sources,
            "retained_compiled_artifacts_checked": outputs, "origin": origin,
            "metadata_log_sha256": sha(log), "host_preflight_sha256": sha(EX / "component-cover-host-preflight.log"),
            "native_package_revisions": data["packages"],
            "boundary": "Exact source/blob and compiled-byte checks inherit prior source-to-olean evidence. Native package caches are pinned revisions, not a compiler reproduction or package replay."}


def layout_metadata():
    """Compare 272 endpoint triples and 224 pattern cells; no field work."""
    repo = subprocess.check_output(["git", "-C", str(EX), "rev-parse", "--show-toplevel"], text=True).strip()
    source_path = "crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs"
    raw = subprocess.check_output(["git", "-C", repo, "show", BASE + ":" + source_path])
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == "cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50", "selected constants changed")
    source = raw.decode()
    leaf = EX / "SelectedCopyLayout.lean"
    lean = leaf.read_text()
    rust_links = re.findall(r"CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), "
        r"producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, "
        r"consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}", source)
    rust_links = [tuple(map(int, row)) for row in rust_links]
    section = lean.split("def sourceLinks : Fin 136 → Link := ![", 1)[1].split("]", 1)[0]
    lean_links = [tuple(map(int, row)) for row in re.findall(r"\blink\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)", section)]
    require(len(rust_links) == len(lean_links) == 136, "136-link census mismatch")
    require([row[3:] for row in rust_links] == lean_links, "literal producer/consumer endpoint mapping mismatch")
    require([row[0] for row in rust_links] == list(range(1124073472, 1124073472 + 136)), "tag/index order mismatch")
    pattern_rows = re.findall(r"CompiledPoolV1PairForestPattern \{ kinds: \[([^]]+)\], columns: \[([^]]+)\], offsets: \[([^]]+)\] \}", source)
    rust_patterns = [[list(map(int, re.findall(r"\d+", cells))) for cells in row] for row in pattern_rows]
    section = lean.split("def sourcePatterns : Fin 14 → Pattern := ![", 1)[1].split("]", 1)[0]
    descriptors = [tuple(map(int, values)) for values in re.findall(r"⟨(\d+),\s*(\d+),\s*(\d+)⟩", section)]
    require(len(rust_patterns) == len(descriptors) == 14, "14-pattern census mismatch")
    for index, ((width, start, offset), actual) in enumerate(zip(descriptors, rust_patterns)):
        require(0 < width <= 16 and start + width <= 16 and all(len(row) == 16 for row in actual), "pattern ranges changed")
        expected = [[int(j < width) for j in range(16)],
                    [start + j if j < width else 0 for j in range(16)],
                    [offset if j + 1 == width else 0 for j in range(16)]]
        require(actual == expected, "pattern cell mismatch at " + str(index))
    masks = [int(n) for n in re.findall(r"\d+", re.search(r"ACTIVE_ROW_MASKS: \[u16; 64\] = \[([^]]+)\]", source).group(1))]
    require(len(masks) == 64, "mask census mismatch")
    for pr, ps, pp, cr, cs, cp in lean_links:
        require(0 <= pr < 1024 and 0 <= cr < 1024 and 0 <= ps < 2 and 0 <= cs < 2 and 0 <= pp < 14 and 0 <= cp < 14,
                "endpoint range mismatch")
        require((masks[pr // 16] >> (pr % 16)) & 1 and (masks[cr // 16] >> (cr % 16)) & 1,
                "literal endpoint lies outside the active mask")
    return {"status": "green", "source": source_path, "source_revision": BASE, "source_sha256": digest,
            "lean_source_sha256": sha(leaf), "links": 136, "endpoint_occurrences": 272, "patterns": 14,
            "pattern_cells": 224, "pattern_integer_entries": 672,
            "scope": "Static selected registry order/endpoint/pattern/mask comparison; no Rust execution, slot-to-link rational identity, collision bound, alias extraction or payment acceptance is inferred."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-receipt", action="store_true")
    parser.add_argument("--check-recorded", action="store_true")
    args = parser.parse_args()
    if args.prepare_receipt:
        require(not args.check_recorded, "receipt is not an evidence pass")
        data = inventory()
        print(json.dumps(data, indent=2))
        return 1 if data["unmapped_artifacts"] else 0
    old.helpers.LEAVES = {name: (stem, old.target_count(name, count)) for name, (stem, count) in TARGETS.items()}
    transfer = old.helpers.prior.Transfer(RD / "component-cover-transfer.json")
    require(transfer.data is not None, "missing new-turn receipt")
    output = {"schema": "aspis-v8-component-cover-evidence-v1", "parent_revision": BASE,
              "borrowed_formal_revision": old.helpers.prior.BORROWED,
              "mathlib_revision": old.helpers.prior.MATHLIB, "lean_commit": old.helpers.prior.LEAN,
              "auditor_sha256": sha(Path(__file__).resolve()),
              "read_only_helper_sha256": {name: sha(EX / name) for name in
                  ("audit_covered_family_evidence.py", "audit_quotient_family_evidence.py", "audit_off_family_tail_evidence.py")},
              "transfer_receipt_sha256": sha(transfer.path), "bootstrap": bootstrap(),
              "leaves": old.helpers.leaves(transfer), "retained_runs": retained_runs(transfer),
              "exact_arithmetic": arithmetic(), "selected_layout_metadata": layout_metadata(),
              "proof_body_bytes": 40282, "positive_work_credit": 0,
              "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
              "scope": "New focused algebra/ideal-game implications with their exact premises. No completed original-component recovery, checked payment extractor, authenticated replay, full-view privacy, resource-bounded Fiat–Shamir or CU-parity certificate."}
    complete = all(row["status"] == "green" for row in output["leaves"])
    output["status"] = "focused_evidence_complete_not_global_security" if complete else "pending"
    if args.check_recorded:
        require(complete, "pending endpoint: refusing recorded-evidence success")
        require(json.loads((RD / "component-cover-evidence.json").read_text()) == output, "recorded evidence changed")
        print("Component-cover focused evidence matches; global security remains unproved.")
    else:
        print(json.dumps(output, indent=2))
    return 0 if complete else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, IndexError, AttributeError) as error:
        print("COMPONENT_COVER_EVIDENCE_REJECTED: " + str(error), file=sys.stderr)
        sys.exit(1)
