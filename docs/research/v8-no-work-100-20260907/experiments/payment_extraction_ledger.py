#!/usr/bin/env python3
"""Summarise retained execution evidence and exact access/wire costs, not security."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent.parent

def results():
    log=(ROOT/"evidence/payment-extraction-host.log").read_text()
    cases=[]
    seed=None
    for line in log.splitlines():
        m=re.fullmatch(r"seed=(\d+)",line)
        if m: seed=int(m[1])
        m=re.match(r"RESULT corrupt=(true|false) accepted=(true|false) checked_witness=(true|false) touched=(\d+) body=(\d+) proof_id=\[([^]]+)\] c1_root=\[([^]]+)\]",line)
        if m:
            hx=lambda s: "".join(x.strip().zfill(2) for x in s.split(","))
            cases.append(dict(seed=seed,corrupt=m[1]=="true",accepted=m[2]=="true",
                checked_witness=m[3]=="true",touched_support=int(m[4]),body_bytes=int(m[5]),
                proof_id=hx(m[6]),c1_root=hx(m[7])))
    assert len(cases)==8 and {c["seed"] for c in cases}=={1,2,3,4}
    assert all(c["checked_witness"] for c in cases)
    assert all(c["accepted"] for c in cases if not c["corrupt"])
    assert all(not c["accepted"] and c["touched_support"]==1 for c in cases if c["corrupt"])
    for seed in range(1,5):
        pair=[c for c in cases if c["seed"]==seed]
        assert pair[0]["c1_root"]==pair[1]["c1_root"]
    old=json.loads((ROOT/"radius-results.json").read_text())
    body=697*16+52+24+22*621+2*296*26
    assert body==40282
    n=1024
    return dict(
        base_revision="1c1e55a7213732068a6064168628c244e40a7f32",
        status="same-execution honest payment proofs with authenticated-opening witness recovery; corrupted arms rejected in fixed cohort",
        cases=cases,
        authenticated_reconstruction=dict(
            access="one explicit extra-opening-oracle response for fixed C1 root; not supplied by the proof or a Merkle root",
            requested_fibres=256,indices="0..255",distinct_evaluations_per_column=1024,
            semantic_columns_recovered=16,authenticated_columns=26,
            exact_source_matrix_rank=1024,
            one_q22_proof_evaluations_per_column=88,
            one_proof_unconstrained_column_nullity_lower_bound=1024-88,
            frontier_hashes=10,response_without_predetermined_ids=256*(403+32)+10*26,
            response_with_explicit_u32_ids=256*(403+32)+10*26+256*4,
            matrix_storage_bytes=n*n*4,elimination_augmented_storage_bytes=n*(2*n)*4,
            gaussian_update_mult_sub_pair_upper_bound=2*n**3,
            solve16_mult_add_pairs=16*n*n,
            leaf_hash_calls_per_bundle=256,parent_hash_calls_per_bundle=2*(255+10),
            serialized_parent_hash_input_bytes=53,
            precomputation_seconds=float(re.search(r"public_matrix_seconds=([0-9.]+)",log)[1]),
            full_oracle_codeword_assumption="Intact C1 control; arbitrary received C1 is NOT error-corrected or proved low degree by 1024 openings.",
            actual_replay_calls=None,actual_replay_forks=None,actual_replay_failure_bound=None,
            minimum_q22_transcripts_by_count_only=(1024+87)//88,
            transcript_count_warning="12 is only an information lower bound, not access to the fixed contiguous set or a rank/extraction guarantee.",
            authenticated_single_C1_change="interpolation returns coefficients; payment validation rejects for the four tested changed roots; not a forgery or proof no witness exists"
        ),
        deterministic_proofs=dict(
            file="experiments/PaymentMaskRead.lean",
            scope="all listed decoder reads invariant under arbitrary allowed field-mask additions; selected-child equality from actual Boolean/path residual forms",
            source_layout_cells_checked=16384,mask_cells=3803,read_mask_intersection=0,
            source_translation=False,universal_validator_completeness=False
        ),
        ideal_boundary_query_diagnostic=old["boundary"]["query_miss"],
        diagnostic_scope="uniform distinct query-miss probability only; neither observed cohort frequency nor accepted-extraction failure bound",
        near_local_result_reference="near-gamma-results.json; unchanged and not replayed",
        global_target="Pr[A AND NOT X_replay_checked_within_resources]",
        event_partition=["access/replay unavailable or exhausted","authentication/source mismatch",
            "insufficient or wrong-basis/rank recovery","recovered coefficients but witness/context/transition validation fails"],
        missing_bounds=dict(access_replay=None,accepted_C1_recovery_failure=None,
            tuple_semantic_to_witness_coverage=None,authentication=None,FS_resource_lift=None),
        missing_deterministic_bridges=["complete source-to-ideal coupling",
            "universal selected-residuals imply literal decoder/validator success",
            "pre-lambda/chi C1 recovery from ROM query graph or causally valid replays"],
        global_100_bit_certificate=None,
        relation_repairs_rule="existing near/image games charge four degree-six repairs; do not add another 24/k",
        maximum_proof_body_bytes=body,maximum_observed_body_bytes=max(c["body_bytes"] for c in cases),
        new_proof_body_bytes=0,new_verifier_operations=0,
        cost_scope="new research harness/extractor only; inherited row/image/dense transpose and 16384-byte weight hash costs remain",
        full_view_ZK=None,complete_transaction_CU=None,full_production_prover_RSS=None,
        full_production_prover_time=None,grinding_security_credit_bits=0,
        unapproved_controls=dict(q23_bytes=41527,quintic_q22_bytes=42984),
        log_sha256=sha256(log.encode()).hexdigest()
    )

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--check",action="store_true")
    a=p.parse_args()
    r=results()
    if a.check:
        assert r==json.loads((ROOT/"payment-extraction-results.json").read_text())
        print("PASS eight same-execution records, exact access/wire census, symbolic global ledger")
    else:
        print(json.dumps(r,indent=2))
