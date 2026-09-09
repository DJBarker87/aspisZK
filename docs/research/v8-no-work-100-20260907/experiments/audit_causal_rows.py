#!/usr/bin/env python3
"""Audit current-source causal/endpoint leaves and exact conditional ledgers.
No field enumeration, Monte Carlo security estimate, or unchanged Lean replay.
"""
import json
import math
import re
import sys
from fractions import Fraction

import audit_soundness_proofs as evidence
from audit_ordered_post_query import rational

BASE = "15e73e9fdf529a0d0ab46353b98bccaf029bf4f5"
LEAVES = [
    ("FirstImageDiscrepancy", "first-image-lean-v*.log"),
    ("CausalOrderedRelation", "causal-ordered-lean-v*.log"),
    ("ShiftedRowPrefix", "shifted-row-lean-v*.log"),
    ("CausalShiftedRows", "causal-shifted-lean-v*.log"),
    ("SelectedForestPath", "selected-forest-leaf-v*.log"),
    ("EarlyC1InstanceTransport", "early-c1-specialization-v*-generic.log"),
    ("EarlyC1Specialization", "early-c1-specialization-v*-identify.log"),
    ("EarlyC1LateProjection", "early-c1-late-projection-v*.log"),
]


def checked_leaf(name, pattern):
    out = evidence.final_leaf(name, pattern)
    log = (evidence.ROOT / out["log"]).read_text()
    out["axiom_audits"].extend(
        {"declaration": declaration, "axioms": []}
        for declaration in re.findall(r"'([^']+)' does not depend on any axioms", log))
    source = (evidence.EX / (name+".lean")).read_text()
    assert len(out["axiom_audits"]) == len(re.findall(r"^#print axioms ", source, re.M))
    return out


def result():
    evidence.BASE = BASE
    k, q, T, B, d = (2**31-1)**4, 22, 262144, 9301, 255
    miss = Fraction(math.comb(B+d, q), math.comb(T, q))
    exact_miss = Fraction(math.comb(d, q), math.comb(T, q))
    post = miss + Fraction(q, k-1) + Fraction(18, k)
    row = miss + Fraction(q+3, k-1) + Fraction(24, k)
    image = miss + Fraction(q+2, k-1) + Fraction(24, k)
    exact_image = exact_miss + Fraction(q+2, k-1) + Fraction(24, k)
    previous_near = miss + Fraction(53, k-1) + Fraction(24, k)
    assert row-post == Fraction(3, k-1)+Fraction(6, k)
    assert previous_near-row == Fraction(28, k-1)
    assert exact_image < Fraction(1, 2**118)
    body = 697*16 + 52 + 24 + q*621 + 2*296*26
    assert body == 40282
    return {
        "base_revision": BASE,
        "environment": "Lean4.32.0; Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serialized cached focused leaves",
        "leaves": [checked_leaf(name, pattern) for name, pattern in LEAVES],
        "scope": "kernel-checked constructed field games and modeled deterministic extraction bridges, not complete Rust verifier or global knowledge theorem",
        "regime": "ideal classical fresh finite challenges, zero positive grinding credit; no quantum or unlimited-offline-search claim",
        "profile": {"k": str(k), "q": q, "T": T, "illustrative_B": B, "d": d, "body_bytes": body},
        "constructed_shifted_game": {
            "theorem": "CausalShiftedRows.wrong_rows_bound",
            "prefix": "Q, B, actual four-slot received oracle, L/I, four original covectors and four claims fixed before kappa",
            "law": "uniform nonzero kappa, uniform nonzero tau, uniform alpha0; ordered uniform distinct q queries; uniform nonzero rho; three sequential uniform field alpha challenges",
            "responses": "firstResponse may depend on kappa/tau but not alpha0; final follows alpha0; raw tail follows ordered schedule/rho and each prior tail challenge",
            "required_event": "at least one actual original row error is nonzero",
            "required_geometry": "reference image-valid and reconstructed batched word matches received outside B complete fibres; all used chord denominators and fold coordinates nonzero",
            "bound": rational(row),
            "terms": [
                {"event": "nonzero shifted four-row discrepancy cancels", "fixing_prefix": "pre-kappa", "challenge": "kappa", "bound": rational(Fraction(3, k-1))},
                {"event": "first compact discrepancy repairs", "fixing_prefix": "response0 precedes alpha0", "challenge": "alpha0", "bound": rational(Fraction(6, k))},
                {"event": "different adaptive final agrees at all sampled fibres", "fixing_prefix": "post-alpha0/pre-query", "challenge": "ordered distinct schedule", "bound": rational(miss)},
                {"event": "nonzero shifted prior/query discrepancy cancels", "fixing_prefix": "queries before rho", "challenge": "rho", "bound": rational(Fraction(q, k-1))},
                {"event": "remaining discrepancy repairs in three compact tail rounds", "fixing_prefix": "each response before its fresh challenge", "challenge": "alpha1..3", "bound": rational(Fraction(18, k))}],
            "tau_handling": "Image-valid reference makes its discrepancy constant in tau; no conditioning on passing the image check and no extra tau error term.",
            "applicability": "formal proof complete for constructed field game; concrete selected source/anchor production unresolved"},
        "other_restricted_bounds": {
            "supported_bad_image_or_wrong_ordinary": rational(image),
            "exact_polynomial_invalid_image_B0": rational(exact_image),
            "different_final_accepted_mass": rational(post),
            "overlap": "These overlap the shifted game and each other. Do not add them. All four relation repairs are counted once within each all-stage theorem."},
        "previous_near_ceiling_arithmetic_only": rational(previous_near),
        "near_composition_status": "The 28/(k-1) arithmetic difference is not a completed near-gamma/source constructor or global bound.",
        "deterministic_progress": {
            "C1": "Original earlyC1 optional object identified on >=245609 own-support fibres via exact V7 encoder; no replacement decoder or populated-option premise.",
            "late_projection": "A qualifying width29 tuple restricts to the same fixed-C1 optional object despite arbitrary late C2; tuple existence and fixed authenticated-word coupling remain separate.",
            "path": "Modeled selected path/copy/two-round residuals construct 24 parent steps from trace59 to trace907; no assumed RoundChain/root. gateStep-to-Rust/constants and authoritative root binding remain open."},
        "global_accepted_extraction_bound": None,
        "remaining_global_allowance": None,
        "open_obligations": [
            "accepted uncovered/far recovery, including all provider-none executions",
            "fixed authenticated C1 word and bounded oracle/replay/private-coin extraction coupling",
            "near-gamma cover instantiated in the concrete reconstructed source game",
            "coefficient reconstruction L versus slotwise chord/interpolant encoder identity and original-code image membership",
            "acceptance enforcing exact individual early semantic/copy constraints",
            "literal gateStep/constant/source and remaining owner/note/nullifier/payment/context/settlement endpoint",
            "complete parser/transcript/optimized-field verifier refinement",
            "resource-bounded FS with actual nonce/retry/prequery/fork/restoration costs",
            "adaptive full-view zero knowledge"],
        "verifier_source_or_production_changes": False,
        "new_proof_body_bytes": 0,
        "new_verifier_operations": 0,
        "new_CU_prover_extractor_or_Rust_measurements": False}


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "causal-row-evidence.json").read_text()) == out
        print("Causal/endpoint current-source evidence, axioms, exact conditional ledger and body census match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
