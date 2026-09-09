#!/usr/bin/env python3
"""Current-source evidence audit. No unchanged Lean/prover/rank replay."""
import json
import math
import re
import sys
from fractions import Fraction
import audit_soundness_proofs as evidence
from audit_causal_rows import checked_leaf

BASE="33e13de4e4b8bfdef7f3f2fb2e472b34db44865e"
LEAVES=[
    ("SelectedTransferMaskAdapter","selected-transfer-mask-adapter-v*.log"),
    ("OODInterpolantCore","ood-interpolant-core-v*.log"),
    ("OODInterpolantRows","ood-interpolant-rows-v*.log"),
    ("OODInverseBoundary","ood-inverse-boundary-v*.log"),
    ("ExactFoldRecovery","exact-fold-recovery-v*.log"),
    ("ExactFoldSelected","exact-fold-selected-v*.log"),
    ("PositiveTerminalInsertion","positive-terminal-insertion-v*.log"),
]

def rust_log(name,markers):
    path=evidence.ROOT/"evidence"/name
    text=path.read_text()
    assert BASE in text and "EXIT=0" in text
    assert not re.search(r"panicked at|^error(?:\[|:)|^EXIT=[1-9]|AGGREGATE_RSS_STOP",text,re.M)
    for marker in markers: assert marker in text,marker
    wall=re.findall(r"^\s*([0-9.]+) real",text,re.M)
    rss=re.findall(r"^\s*(\d+)\s+maximum resident set size",text,re.M)
    swap=re.findall(r"^\s*(\d+)\s+swaps$",text,re.M)
    assert len(wall)==len(rss)==len(swap)==1 and int(swap[0])==0
    return {"log":str(path.relative_to(evidence.ROOT)),"sha256":evidence.sha(path),
            "exit":0,"wall_seconds":float(wall[0]),"peak_rss_bytes":int(rss[0]),"swaps":0}

def rational(v):return {"numerator":str(v.numerator),"denominator":str(v.denominator)}

def result():
    evidence.BASE=BASE
    manifest=evidence.ROOT/"evidence/positive-transfer-source-v1.sha256"
    sources={}
    for line in manifest.read_text().splitlines():
        digest,path=line.split(maxsplit=1)
        relative=path.split("/docs/research/v8-no-work-100-20260907/",1)[1]
        assert evidence.sha(evidence.ROOT/relative)==digest,relative
        sources[relative]=digest
    assert len(sources)==65
    layout="old_cells=3803 new_cells=3802 old_fp=f9daf3d54f4285d1 new_fp=6b661245a56c7189 active_reserved=true unchanged_dependents=16 descriptor_bytes=107 packing_controls=32"
    cases={"build":rust_log("positive-transfer-build-v1.log",["Finished `release` profile","f771bbb4b04a041c72d6d09e6c5c4c887bb5f6e31de37e8677dcd75cf3ef018f"]),
           "honest":rust_log("positive-transfer-honest-v1.log",[layout,'"accepted":true,"body_bytes":38982','"stress_nonce_attempts":0'])}
    for case in ("recipient_zero","change_zero"):
        cases[case]=rust_log("positive-transfer-"+case.replace("_","-")+"-v1.log",[layout,
            "POSITIVE_CASE case="+case,
            "verifier_error=4 verifier_reached_PCS=false nonce_search=false complete_bad_proof=false"])
    k=(2**31-1)**4
    exact=Fraction(3,k)
    assert Fraction(1,2**123)<exact<Fraction(1,2**122)
    sections={"canonical_fixed":697*16,"roots":52,"nonces":24,"queries":22*621,"maximum_frontiers":2*296*26}
    assert sum(sections.values())==40282
    return {
        "base_revision":BASE,"sources":sources,"source_manifest_sha256":evidence.sha(manifest),
        "leaves":[checked_leaf(*leaf) for leaf in LEAVES],"rust_evidence":cases,
        "new_design":{"opt_in_cfg":"v8_positive_transfer","selected_default_changed":False,
            "transfer_only":True,"complete_pool_wrapper_integrated":False,
            "new_equation":"C1[1][1014]*C1[1][1015]*C1[3][1014]-1=0",
            "packing":{"source_lane":94,"packed_group":23,"limb":2,"theta_power":27},
            "legacy_mask_draw_count":3803,"remaining_mask_inventory":3802,
            "discarded_draw":"active row1014 column3; legacy draw order/balancer retained",
            "new_mask_fingerprint":"6b661245a56c7189","canonical_descriptor_bytes":107,
            "descriptor_framed_hash_input_bytes":141,"descriptor_sha256_compression_blocks":3,
            "new_transmitted_bytes":0,"new_nonce_search":False},
        "host_reference_extra_terminal_arithmetic":{"QM31_multiplications":39,"QM31_squarings":4,"pack_base4":1,
            "scope":"additive wrapper duplicates selector/equality/theta work; not minimal integrated-lane cost or SBF CU"},
        "exact_global_fold_class":{"received_fixing":"actual virtual quotient fixed before alpha0",
            "event":"non-full-code received quotient AND adaptive final agrees at EVERY final-domain position",
            "fresh_law":"ideal uniform full QM31 alpha0 conditional on the prefix",
            "bound":rational(exact),"display_bits":math.log2(exact.denominator)-math.log2(exact.numerator),
            "evidence_scope":"kernel-checked cardinality <=3 for the selected mathematical encoder; rational corollary under the stated ideal law, not a Rust/FS probability theorem",
            "does_not_cover":["partial agreement","component-wise original code recovery","checked payment extraction","authentication/replay/Fiat-Shamir"],
            "composition":"not added to existing image/row/near/relation subtotals; source and event partition obligations remain"},
        "body_sections":sections,"maximum_body_bytes":sum(sections.values()),"honest_body_bytes":38982,
        "honest_public_artifacts_sha256":{
            "proof":"00699c67efeb22534cfde586d880544850e62b3cbebca4789d56d1c3251154ed",
            "public":"76f29db662d14513be3925975d57bd49663acd630666e89c9b16e2ec68caf9ea",
            "transition":"f9474caef25594cf4fffd608428c482485f2764c5cc4da3eafdd5231a5e39766",
            "binding":"1f46700845c22fb7e696f2db3f95a0ad06a2694e0deeebe27f35912887a243b7"},
        "measurements":{"host":"Apple aarch64 macOS; rustc1.93.0; release optimized overflow-checked",
            "honest_prover_seconds_excluding_setup":5.651607041,"setup_seconds":1.189731166,
            "new_full_transaction_CU":None,"new_SBF_stack_measurement":None,
            "new_rank_probe":False,"raw_witness_or_mask_logged":False},
        "open_accepted_failure_terms":{"partial_agreement_and_provider_none_recovery":None,
            "semantic_constraints_enforced_on_recovered_C1":None,"full_checked_payment_endpoint":None,
            "source_authentication_replay_fuel_mismatch":None,"actual_FS_resource_composition":None},
        "global_accepted_extraction_bound":None,"remaining_global_allowance":None,
        "full_view_zero_knowledge_complete":False,"positive_grinding_security_credit":0,
        "production_changes":False,
    }

if __name__=="__main__":
    out=result()
    if sys.argv[1:]==["--check-recorded"]:
        assert json.loads((evidence.ROOT/"positive-recovery-evidence.json").read_text())==out
        print("Positive-transfer/current-source proofs, exact local bound, body and unresolved ledger match.")
    else:
        assert not sys.argv[1:]
        print(json.dumps(out,indent=2))
