#!/usr/bin/env python3
"""Audit the focused rational-fold, packed-query and payment-tail continuation.

This consumes existing logs and exact arithmetic only.  It deliberately does
not replay Lean, enumerate QM31, or turn conditional screens into ledger credit.
"""
import json
from pathlib import Path
import re
import subprocess
import sys
from fractions import Fraction

import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf


BASE = "edb199c12fcc41f00330298b95b4736f60ac6f3a"
BORROWED = "26a9cd4718aae9f9de7ef1c3394fb74a229085d5"
LEAVES = [
    ("ChordRationalAlgebra", "chord-rational-algebra-v*.log"),
    ("ChordRationalDegree", "chord-rational-degree-v*.log"),
    ("FourPointSubmodule", "four-point-submodule-v*.log"),
    ("ChordRationalDivisibility", "chord-rational-divisibility-v*.log"),
    ("ChordRationalQuotientDegree", "chord-rational-quotient-degree-v*.log"),
    ("ChordRationalOOD", "chord-rational-ood-v*.log"),
    ("ChordRationalBadOOD", "chord-rational-bad-ood-v*.log"),
    ("RationalCoordinates", "rational-coordinates-v*.log"),
    ("PackedLimbCollect", "packed-limb-collect-v*.log"),
    ("PackedQueryRecord", "packed-query-record-v*.log"),
    ("SelectedAppendAfterstate", "selected-append-afterstate-v*.log"),
    ("RelationCompatibleMoment", "relation-compatible-moment-v*.log"),
    ("AdaptiveFinalPrior", "adaptive-final-prior-v*.log"),
    ("FixedC1FarMoment", "fixed-c1-far-moment-v*.log"),
    ("SevenAlphaRecovery", "seven-alpha-recovery-v*.log"),
    ("ThreeTauRecovery", "three-tau-recovery-v*.log"),
]


def proofs():
    evidence.BASE = BASE
    out = []
    for name, pattern in LEAVES:
        leaf = checked_leaf(name, pattern)
        source = (evidence.EX / leaf["target"]).read_text()
        assert not re.search(
            r"^\s*(axiom|sorry|admit)\b|\bby\s+(sorry|admit)\b", source, re.M
        )
        log = (evidence.ROOT / leaf["log"]).read_text()
        if "BORROWED_SOURCE_PIN=" in log:
            assert f"BORROWED_SOURCE_PIN={BORROWED}" in log
        else:
            # The afterstate leaf uses only the research worktree's pinned
            # formal closure, rather than the separately borrowed main cache.
            assert name == "SelectedAppendAfterstate"
        assert "LEAN_EXIT=0" in log
        verified = 0
        for expected, raw in re.findall(r"^([a-f0-9]{64})  (/[^\n]+)$", log, re.M):
            path = Path(raw)
            if path.suffix == ".sh":
                continue
            assert path.exists(), raw
            assert evidence.sha(path) == expected, (raw, expected)
            verified += 1
        leaf["current_logged_source_cache_hashes_verified"] = verified
        out.append(leaf)
    return out


def arithmetic():
    script = evidence.EX / "chord_rational_bounds.py"
    recorded_path = evidence.ROOT / "chord-rational-bounds.json"
    current = subprocess.run(
        [sys.executable, "-B", str(script)], check=True, capture_output=True, text=True
    ).stdout
    recorded = recorded_path.read_text()
    assert current == recorded
    value = json.loads(current)
    assert value["possible_match_cap"] == 259
    assert value["conditional_screen"]["applicability"] is False
    assert value["status"] == "arithmetic_verified_theorem_applicability_unresolved"
    return value


def strategy_preflight():
    log_path = evidence.EX / "helper-ood-strategy-preflight-v2.log"
    log = log_path.read_text()
    assert "BUILD_EXIT=0" in log and "PREFLIGHT_EXIT=0" in log
    assert re.search(r"^\s*0\s+swaps$", log, re.M)
    payloads = [json.loads(line) for line in log.splitlines() if line.startswith("{")]
    assert len(payloads) == 1
    out = payloads[0]
    assert out["reference_checks"] == 9104
    assert out["direct_scalar_checks"] == 6840
    assert out["states_where_unrestricted_far_beats_zero_prior_far"] == 456
    assert all(row[3] == 3 for row in out["distance_records_profile_chord_gamma"])
    for name in ("helper_ood_strategy.rs", "run_helper_ood_strategy.sh"):
        path = evidence.EX / name
        expected = re.search(
            rf"^([a-f0-9]{{64}})  {re.escape(str(path))}$", log, re.M
        )
        assert expected and evidence.sha(path) == expected.group(1)
    return {
        "log": str(log_path.relative_to(evidence.ROOT)),
        "log_sha256": evidence.sha(log_path),
        "result": out,
        "interpretation": (
            "restricted exact F19 causal search falsifies forcing the pre-query "
            "carried discrepancy to zero; not an attack, payment trace or QM31 bound"
        ),
    }


def far_strategy():
    """Validate the completed restricted search, without executing it again."""
    log_path = evidence.EX / "helper-far-moment-v1.log"
    log = log_path.read_text()
    assert "BUILD_EXIT=0" in log and "SEARCH_EXIT=0" in log
    for name in ("helper_far_moment.rs", "run_helper_far_moment.sh"):
        path = evidence.EX / name
        match = re.search(rf"^([a-f0-9]{{64}})  {re.escape(str(path))}$", log, re.M)
        assert match and evidence.sha(path) == match.group(1), name
    payloads = [json.loads(line) for line in log.splitlines() if line.startswith("{")]
    rows = [row for row in payloads if "result_profile" in row]
    results = [row for row in payloads if row.get("mode") == "restricted_full_causal_exact"]
    assert len(rows) == 2 and len(results) == 1
    out = results[0]
    assert out["field"] == 19 and out["query_count"] == 2
    assert out["formal_claim_polynomial"] == "1+X^28"
    assert out["raw_helper_degree"] == 2
    assert out["prefix_count"] == 23328
    assert out["response_alpha_lookups"] == 3040128288
    assert out["final_candidate_count"] == 160006752
    expected_moments = [Fraction(7219, 73872), Fraction(21365, 221616)]
    derived = []
    for index, row in enumerate(rows):
        assert row["result_profile"] == index
        values = [Fraction(n, row["common_denominator"]) for n in row["numerators"]]
        assert values == [Fraction(*pair) for pair in row["reduced_fractions"]]
        assert values[2] == expected_moments[index]
        assert values[1] > values[4] and values[3] > values[2]
        # Every positive far pointwise score is choose(2,2)/choose(4,2)=1/6.
        # These are incidence counts under an optimizing response policy;
        # they do not assert coherence of finals across alpha branches.
        prefixes = out["prefix_count"] // 2
        incidences = values[2] * 6 * prefixes * out["field"]
        assert incidences.denominator == 1
        excess = incidences.numerator - 6 * prefixes
        at_least_seven = max(0, (excess + 12) // 13)
        derived.append({"profile": index,
                        "qualifying_prefix_alpha_incidences": incidences.numerator,
                        "prefixes_with_at_least_seven_qualifying_alphas_lower_bound": at_least_seven,
                        "coherent_quotient_count": None})
    assert [row["qualifying_prefix_alpha_incidences"] for row in derived] == [129942, 128190]
    assert [row["prefixes_with_at_least_seven_qualifying_alphas_lower_bound"] for row in derived] == [4613, 4478]
    times = re.findall(r"^\s*([0-9.]+) real", log, re.M)
    rss = re.findall(r"^\s*(\d+)\s+maximum resident set size", log, re.M)
    swaps = re.findall(r"^\s*(\d+)\s+swaps$", log, re.M)
    assert len(times) == len(rss) == len(swaps) == 2
    assert all(int(value) == 0 for value in swaps)
    return {
        "log": str(log_path.relative_to(evidence.ROOT)),
        "log_sha256": evidence.sha(log_path),
        "measurements": [{"stage": stage, "exit": 0, "wall_seconds": float(times[i]),
                          "peak_rss_bytes": int(rss[i]), "swaps": int(swaps[i])}
                         for i, stage in enumerate(("optimized_rust_compilation", "restricted_exact_search"))],
        "profiles": rows,
        "result": out,
        "derived_incidence_counts": derived,
        "coherence_status": "argmax final choices not recorded; no shared quotient or shared support inferred",
        "scope": "exhaustive within the declared F19 family and abstract tail game; no QM31 probability or payment-extraction conclusion",
    }


def far_budget():
    script = evidence.EX / "far_moment_budget.py"
    output = subprocess.run([sys.executable, "-B", str(script)], check=True,
                            capture_output=True, text=True).stdout
    value = json.loads(output)
    bound = value["proved_suffix_and_root_terms"]
    k = (2**31 - 1)**4
    assert Fraction(int(bound["numerator"]), int(bound["denominator"])) == Fraction(50, k-1) + Fraction(18, k)
    assert value["status"] == "arithmetic_only_theorem_applicability_unresolved"
    return value


def result():
    body = 697 * 16 + 52 + 24 + 22 * 621 + 2 * 296 * 26
    assert body == 40282
    return {
        "base_revision": BASE,
        "borrowed_formal_revision": BORROWED,
        "environment": (
            "Lean4.32.0 / Mathlib81a5d257; serialized cached focused leaves; "
            "-M7000 and 7GiB aggregate child RSS guard"
        ),
        "leaves": proofs(),
        "exact_arithmetic": arithmetic(),
        "causal_falsification": strategy_preflight(),
        "far_causal_search": far_strategy(),
        "far_local_budget_screen": far_budget(),
        "proved_scope": {
            "rational_algebra": (
                "actual low-bit natural basis, explicit chord adjugate/norm and "
                "equality with the imported normalized four-point fold"
            ),
            "rational_degree": (
                "for four polynomial raw coefficient lines of degree<=255 and a "
                "nonzero cleared discrepancy, any false degree<=255 final has at "
                "most 257 nonpole plus two pole matches"
            ),
            "four_point_submodule": (
                "four distinct cubic evaluations in an arbitrary fixed submodule "
                "force all four coefficients into that submodule"
            ),
            "rational_divisibility": (
                "four exact cleared discrepancies force all four adjugate-product "
                "components to be norm-divisible; nonzero norm constructs one global "
                "polynomial quotient q with the exact identity u=chord*q"
            ),
            "rational_ood": (
                "the exact product identity for the actual radial natural-basis lanes "
                "forces both gamma-batched OOD answers for the same original message, "
                "without image, degree, norm-at-point or nonpole premises"
            ),
            "quotient_degree": (
                "the quotient constructed from four exact degree-bounded adaptive "
                "finals is the same quotient reconstructed globally, every component "
                "inherits degree<=255, and all four folds equal their supplied finals"
            ),
            "bad_ood_alpha_cap": (
                "for a fixed polynomial raw message with either batched OOD answer "
                "wrong, arbitrary alpha-dependent finals can have zero full cleared "
                "discrepancy on at most three alpha values in any finite domain"
            ),
            "rational_coordinates": (
                "actual final coordinate z=2s-1 and radial coordinate s=(z+1)/2 "
                "are linked injectively; transformed final/raw lane polynomials retain "
                "degree<=255 and injective index matching counts transfer exactly"
            ),
            "packed_record": (
                "successful canonical 621-byte parsing fixes all C1/C2 limbs, salt, "
                "tower ordering and 29-lane gamma recombination"
            ),
            "payment_afterstate": (
                "same recovered table and selected modeled residuals determine the "
                "20-level append hashes, candidate frontier/root and cursor increment"
            ),
            "relation_compatible_suffix": (
                "arbitrary received oracle and post-alpha adaptive final: causal suffix "
                "acceptance <= E[1_(actual prior=0) choose(M,q)/choose(T,q)] + q/|G| + 18/|A|"
            ),
            "adaptive_prior_correction": (
                "one nonzero folded weight permits a legal post-alpha coefficient correction "
                "that zeros the actual prior; its exact query residual change is derived"
            ),
            "fixed_c1_far_reduction": (
                "early identified C1, degree-two helper curve and degree-28 wrong-claim "
                "polynomial retained in the causal far-final reduction; arbitrary fixed "
                "helper targets give root bookkeeping, without a helper-coverage or moment bound"
            ),
            "seven_alpha_recovery": (
                "construct a quotient from four adaptive finals matching one fixed received "
                "word on >255 common fibres; selected encoder overlap identifies all finals; "
                "seven actual prior zeros for one compact response force the single-tau mixed equation"
            ),
            "three_tau_recovery": (
                "retain the quotient constructed from the first tau across all common-support "
                "branches; three tau values separate the ordinary scalar and both image "
                "constraints, with tau-dependent responses and tau/alpha-dependent finals"
            ),
        },
        "event_accounting": [
            {
                "class": "exact-polynomial raw coefficient lines; cleared discrepancy nonzero",
                "query_match_bound": "choose(259,22)/choose(262144,22)",
                "status": "theorem applicable after selected-domain/source identification",
            },
            {
                "class": "four distinct folds with cleared discrepancy zero",
                "bound": "at most 3 alpha values unless exact polynomial reconstruction",
                "status": (
                    "principal-ideal interpolation and norm cancellation proved; "
                    "actual batched OOD bridge and wrong-OOD finite-alpha cap proved; "
                    "uniform challenge/source experiment composition pending"
                ),
            },
            {
                "class": "arbitrary non-polynomial received oracle/provider-outside branch",
                "bound": None,
                "status": (
                    "fixed early-C1 wrong-claim/far subclass now has a proved relation-compatible "
                    "moment reduction; the moment, early-C1-none and valid-witness extraction remain unresolved"
                ),
            },
            {
                "class": "authentication, replay/fuel and actual source/transcript mismatch",
                "bound": None,
                "status": "real verifier/extractor coupling pending",
            },
        ],
        "conditional_118_bit_screen_is_global_credit": False,
        "global_accepted_extraction_bound": None,
        "global_remaining_allowance": None,
        "far_event_is_extraction_failure": False,
        "next_fork_certificate": {
            "status": "seven-alpha and three-tau selected-code constructions kernel checked; authenticated fork collection and probability pending",
            "requirements": "three distinct tau values, each with seven distinct alpha branches and one response0, actual prior zero, and >255 common matching fibres across the whole grid",
            "conclusion": "construct one coherent quotient and derive its ordinary scalar equality and both zero-image constraints separately",
            "missing_input": "bounded replay/authentication access and a quantitative accepted-mass bound on failure to collect a useful coherent certificate",
            "same_quotient_required_across_tau_and_kappa": True,
            "four_kappa_composition": "not completed in this continuation",
        },
        "resource_bounded_fiat_shamir": "open; no grinding credit",
        "full_view_zero_knowledge": "open",
        "body_bytes": body,
        "new_proof_body_values": 0,
        "production_or_verifier_changes": False,
        "new_complete_transaction_CU_measurement": False,
    }


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        recorded = evidence.ROOT / "rational-continuation-evidence.json"
        assert json.loads(recorded.read_text()) == out
        print("Rational-fold, packed-query and payment-tail evidence matches current source.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
