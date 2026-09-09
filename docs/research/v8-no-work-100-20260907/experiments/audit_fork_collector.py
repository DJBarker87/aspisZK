#!/usr/bin/env python3
"""Read-only current-source/evidence audit; no Lean or Rust replay."""
import json
from pathlib import Path
import re
import sys
from fractions import Fraction
from math import comb

import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf

BASE = "532ade2064e533602902fc9ae5b4dd90f9207131"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"


def hashes(log):
    return dict((path, digest) for digest, path in re.findall(
        r"^([a-f0-9]{64})  (/[^\n]+)$", log, re.M))


def proofs():
    evidence.BASE = BASE
    out = []
    for name, pattern in [("FourKappaRecovery", "four-kappa-recovery-v*.log"),
                          ("CensoredCollectorGrowth", "censored-collector-growth-v*.log")]:
        leaf = checked_leaf(name, pattern)
        source = (evidence.EX / leaf["target"]).read_text()
        assert not re.search(r"^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b", source, re.M)
        log = (evidence.ROOT / leaf["log"]).read_text()
        assert "LEAN_EXIT=0" in log
        current = hashes(log)
        for path, digest in current.items():
            assert evidence.sha(Path(path)) == digest, path
        if name == "FourKappaRecovery":
            assert f"BORROWED_SOURCE_PIN={BORROWED}" in log
            # Cross-check the borrowed imported olean/source closure against
            # the earlier successful ThreeTau replay, not just today's files.
            previous = hashes((evidence.EX / "three-tau-recovery-v1.log").read_text())
            imported = {p: h for p, h in current.items()
                        if p.endswith((".lean", ".olean")) and Path(p).stem != name}
            assert imported
            for path, digest in imported.items():
                assert previous.get(path) == digest, ("import provenance", path)
            leaf["imported_hashes_matching_previous_three_tau_evidence"] = len(imported)
        leaf["logged_current_hashes_checked"] = len(current)
        out.append(leaf)
    return out


def measurements(log):
    times = re.findall(r"^\s*([0-9.]+) real", log, re.M)
    rss = re.findall(r"^\s*(\d+)\s+maximum resident set size", log, re.M)
    swaps = re.findall(r"^\s*(\d+)\s+swaps$", log, re.M)
    assert len(times) == len(rss) == len(swaps)
    assert all(int(s) == 0 for s in swaps)
    return [{"wall_seconds": float(t), "peak_rss_bytes": int(r), "swaps": int(s)}
            for t, r, s in zip(times, rss, swaps)]


def collector():
    path = evidence.EX / "fork-collector-control-v1.log"
    log = path.read_text()
    assert BASE in log and "BUILD_EXIT=0" in log and "SEARCH_EXIT=0" in log
    for raw, digest in hashes(log).items():
        assert evidence.sha(Path(raw)) == digest
    rows = [json.loads(line) for line in log.splitlines() if line.startswith("{")]
    cases = [r for r in rows if "case" in r]
    policies = [r for r in rows if "policy_case" in r]
    positive = [r for r in rows if "positive_control_mode" in r]
    summary = [r for r in rows if r.get("scope") == "exact_predeclared_prefix_collector_control"]
    assert len(cases) == len(policies) == 8 and len(positive) == 2 and len(summary) == 1
    for case, policy in zip(cases, policies):
        assert case["case"] == policy["policy_case"]
        assert 10 <= case["best_qualifying_alphas"] <= 13
        assert case["chosen_policy_best_coherence"] == 5
        assert case["all_optimal_ties_best_common_two"] in (4, 5)
        assert case["all_optimal_ties_seven_pair_groups"] == 0
        assert case["all_optimal_ties_imagevalid_common_two"] == 0
        assert case["four_disclosure_subsets"] == comb(case["best_qualifying_alphas"], 4)
        assert all(value == 0 for value in policy["chosen_priors"])
    for row in positive:
        assert all(row[key] for key in ("all19_coherent", "all4_fibres", "image_valid", "actual_combined_relation"))
        assert row["collector_attempts"] == 4 and row["collector_reads"] == 16
    assert summary[0]["final_candidates"] == 54872
    assert summary[0]["four_disclosure_subsets"] == 2665
    assert summary[0]["negative_controls"] == 14
    times = measurements(log)
    assert len(times) == 2
    return {"log": str(path.relative_to(evidence.ROOT)), "log_sha256": evidence.sha(path),
            "compilation": times[0], "optimized_control": times[1],
            "result": summary[0], "cases": cases, "positive_controls": positive,
            "scope": "restricted F19 full-oracle candidate interpolation/audit; no actual Merkle, FS or payment extractor"}


def growth():
    path = evidence.EX / "censored-collector-v1.log"
    log = path.read_text()
    assert "SCRIPT_EXIT=0" in log and BASE in log
    expected = re.search(r"^SOURCE_SHA256=([a-f0-9]{64})$", log, re.M).group(1)
    assert evidence.sha(evidence.EX / "censored_collector.py") == expected
    data = json.loads((evidence.ROOT / "censored-collector.json").read_text())
    assert json.JSONDecoder().raw_decode(log[log.index("{\n"):])[0] == data
    rows = data["small_games"]
    assert len(rows) == 108
    for row in rows:
        get = lambda x: Fraction(int(x["numerator"]), int(x["denominator"]))
        assert get(row["optimum"]) <= min(Fraction(1), get(row["bound"]))
    term = data["selected_profile"]["one_draw_stagnation_bound"]
    assert Fraction(int(term["numerator"]), int(term["denominator"])) == Fraction(comb(255,22), comb(262144,22))
    return {"log": str(path.relative_to(evidence.ROOT)), "log_sha256": evidence.sha(path),
            "measurements": measurements(log), "games": len(rows),
            "dp_states": sum(r["states"] for r in rows),
            "selected_profile": data["selected_profile"],
            "probability_proof_status": "symbolic finite-history derivation, not Lean probability theorem"}


def result():
    body = 697*16 + 52 + 24 + 22*621 + 2*296*26
    assert body == 40282
    failed_path = evidence.EX / "censored-collector-growth-v1.log"
    failed_log = failed_path.read_text()
    assert "LEAN_EXIT=1" in failed_log and "Tactic `subst` failed" in failed_log
    return {"parent_revision": BASE, "borrowed_v7_revision": BORROWED,
            "environment": "macOS26.5 arm64 laptop; serialized focused jobs; NUC idle",
            "lean": proofs(), "collector": collector(), "support_growth": growth(),
            "failed_focused_predecessor": {
                "log": str(failed_path.relative_to(evidence.ROOT)),
                "log_sha256": evidence.sha(failed_path), "exit": 1,
                "measurements": measurements(failed_log),
                "cause": "explicit-prefix witness needed head-equality projection before subst",
                "resolution": "local proof repair; unchanged memory cap; green v2",
                "proof_credit": False},
            "events": [
                {"event": "actual suffix acceptance with nonzero prior or nonzero pointwise residual",
                 "theorem": "RelationCompatibleMoment.suffix_bound (reused)",
                 "bound": "q/(k-1) + 18/k plus the retained compatible moment",
                 "prefix": "actual final and query nonce before fresh queries; schedule before rho; sequential later responses",
                 "status": "formal source-shaped ideal theorem; actual-source/authentication/FS coupling separate",
                 "overlap": "do not re-add repairs from near/image/row ceilings"},
                {"event": "qualifying common-support four-kappa/three-tau/seven-alpha fork grid",
                 "theorem": "FourKappaRecovery.four_kappa_common_support",
                 "conclusion": "constructed Q, same represented finals, both image constraints, all four original claims",
                 "event_probability": None, "status": "deterministic formal proof complete"},
                {"event": "at least235 qualifying retained continuations but one-final union at most255 within N draws",
                 "bound": "min(1, N*choose(255,22)/choose(262144,22))",
                 "prefix": "one fixed final and fixed authenticated oracle; each union before next fresh schedule",
                 "status": "symbolic censoring-safe probability derivation; deterministic growth Lean checked; tiny exact causal controls",
                 "overlap": "collector event, not independent additional protocol soundness credit"},
                {"event": "accepted failure to obtain enough coherent authenticated forks or another checked witness",
                 "bound": None, "status": "quantitative recovery obligation unresolved"},
                {"event": "recovered component/semantic/context/witness failure",
                 "bound": None, "status": "source and causal extraction obligations retained"}],
            "global_accepted_extraction_bound": None, "remaining_global_allowance": None,
            "full_view_ZK": "unresolved", "resource_bounded_FS": "unresolved",
            "positive_work_credit": 0, "proof_body_bytes": body,
            "new_public_messages": 0, "new_verifier_operations": 0,
            "new_full_transaction_CU": None, "new_actual_extractor_timing": None}


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "fork-collector-evidence.json").read_text()) == out
        print("Fork collector source/cache provenance, focused axioms, exact controls and symbolic ledger match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
