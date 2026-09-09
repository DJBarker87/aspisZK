#!/usr/bin/env python3
"""Current-source proof audit and explicit, non-numeric unresolved ledger."""
import json
import sys

import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf

BASE = "3a0b144dee108041320a23850ab4478444a74745"
LEAVES = [
    ("AuthenticatedEarlyC1Prefix", "authenticated-early-c1-prefix-v*.log"),
    ("AuthenticatedEarlyC1Projection", "authenticated-early-c1-projection-v*.log"),
    ("AuthenticatedEarlyC1Targets", "authenticated-early-c1-targets-v*.log"),
    ("ChordPolynomialImage", "chord-polynomial-v*.log"),
    ("NaturalLineBoundary", "natural-line-boundary-v*.log"),
    ("NaturalChordImage", "natural-chord-image-v*.log"),
    ("NaturalProjectionCore", "natural-projection-core-v*.log"),
    ("NaturalChordProjection", "natural-chord-projection-v*.log"),
    ("SelectedNoteRecovery", "selected-note-leaf-v*.log"),
]


def result():
    evidence.BASE = BASE
    body_sections = {"canonical_field_values": 697*16, "roots": 52,
                     "nonces": 24, "query_records": 22*621,
                     "two_maximum_frontiers": 2*296*26}
    assert sum(body_sections.values()) == 40282
    return {
        "base_revision": BASE,
        "environment": "Lean4.32.0 / Mathlib81a5d257c8e410db227a6665ed08f64fea08e997; serialized cached leaves with independent7GiB descendant RSS guard",
        "leaves": [checked_leaf(name, pattern) for name, pattern in LEAVES],
        "scope": "kernel-checked deterministic, source-shaped mathematical bridges; not a translated full Rust verifier or global extraction theorem",
        "body_sections_bytes": body_sections,
        "maximum_body_bytes": sum(body_sections.values()),
        "hash_events": [
            {"event": "accepted C1 opening not a projection of the early completed word",
             "fixing_prefix": "finite early input/answer records and C1 root",
             "theorem": "AuthenticatedEarlyC1Targets.accepted_opening_prefix_or_shared_failure",
             "reduction": "shared WholeDomainLaterHit OR RawLogTruncatedDigestCollision",
             "required": "recorded-answer consistency; same-root bottom-up path acceptance; early and supplied-path raw inputs included in shared log",
             "status": "formal deterministic reduction complete; actual chronological V8 source injection unresolved",
             "probability_bound": None},
            {"event": "a later fresh raw input hits an early unresolved C1 target",
             "fixing_prefix": "same early records/root, before later position selection",
             "theorem": "AuthenticatedEarlyC1Targets.allTargets_card_le",
             "target_cardinality_upper_bound": 262144,
             "probability_bound": None,
             "uninstantiated_RO_formula": "Q * 262144 / 2^208, only after causal shared-oracle event injection, uniform fresh outputs and declared Q across replays",
             "overlap": "one shared whole-domain event, not an additional q22 union"},
            {"event": "shared log has two distinct raw inputs with equal208bit outputs",
             "probability_bound": None,
             "required": "count all distinct queries/branches in the actual resource-bounded experiment",
             "overlap": "shared with other authentication stages; no per-opening replication"}],
        "C1_identification": {
            "theorem": "AuthenticatedEarlyC1Projection.authenticated_support_identifies_or_bad",
            "sufficient_support_fibres": 245609,
            "support_kind": "actual root-authenticated canonical C1 values matching the tuple encoder",
            "conclusion": "original earlyC1 option identifies tuple C1 projection OR explicit late-target/collision event",
            "not_claimed": "acceptance supplies this support; one q22 proof exposes it; noncomputable choice is efficient decoding",
            "alternative": "apply existing EarlyC1LateProjection to near-gamma own support of the SAME prefix-totalized C1 word after proving the concrete query/source coupling; no claim that totalized support itself consists of authenticated openings"},
        "natural_image": {
            "theorem": "NaturalChordImage.selected_image_iff",
            "full_pair": "E=aA+bXA+c(1-X^2)B; O=cA+aB+bXB",
            "hypotheses": "A/B are natural line sums of even/odd q lanes; char not2; b or c nonzero",
            "equivalence": "degree(E),degree(O)<=511 IFF q1023=0 AND b*q1022-c*q1021=0",
            "projection_theorem": "NaturalChordProjection.selected_projected_circle_eval",
            "projection": "inverse natural coefficient conversion at514, then natural prefix512; not monomial truncation",
            "circle_hypothesis": "x^2+y^2=1",
            "remaining": "actual interleaved Rows.reconstruction and optimized carry/transpose source refinement; exact encoder domain/denominator/OOD interfaces; accepted coverage"},
        "payment_hash_slice": {
            "theorem": "SelectedNoteRecovery.decoded_note_reaches_recorded_forest",
            "prerequisites": "explicit individual selected note/path/copy/two-round residuals",
            "derived": "same recovered key/salt yields owner, input-note, nullifier and the note's24level path to trace907",
            "not_assumed": ["honest trace", "valid witness", "successful decoder", "supplied hash equality", "RoundChain"],
            "remaining": "literal Rust/constants; individual constraint enforcement; positivity, output/transition, authenticated context and validator"},
        "unchanged_conditional_ledger": {
            "artifact": "causal-row-evidence.json",
            "artifact_sha256": evidence.sha(evidence.ROOT / "causal-row-evidence.json"),
            "new_error_terms_added": False,
            "note": "near/row/image/query events overlap; no duplicate relation repairs or historical396430 inventory"},
        "global_accepted_extraction_bound": None,
        "remaining_global_allowance": None,
        "raw_to_FS_connection_complete": False,
        "full_view_zero_knowledge_complete": False,
        "positive_work_security_credit": 0,
        "new_protocol_messages_or_verifier_operations": 0,
        "production_or_verifier_source_changes": False,
        "new_Rust_SBF_proving_extractor_CU_measurements": False,
    }


if __name__ == "__main__":
    out = result()
    if sys.argv[1:] == ["--check-recorded"]:
        assert json.loads((evidence.ROOT / "authenticated-source-evidence.json").read_text()) == out
        print("Authenticated/source current-proof evidence, standard axioms and unchanged body census match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out, indent=2))
