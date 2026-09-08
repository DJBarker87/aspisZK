#!/usr/bin/env python3
"""Replay retained noncanonical-C1 evidence and symbolic failure partition."""
from pathlib import Path
from hashlib import sha256
import json, re, argparse
ROOT=Path(__file__).resolve().parent.parent
def results():
    log=(ROOT/'evidence/noncanonical-c1-host.log').read_text()
    m=re.search(r'RESULT corrupt=false accepted=(true|false) checked_witness=(true|false).*?body=(\d+) proof_id=\[([^]]+)\] c1_root=\[([^]]+)\]',log)
    assert m and m[1]==m[2]=='true'
    hx=lambda s:''.join(x.strip().zfill(2) for x in s.split(','))
    assert 'invalid_limbs=8 totalized_zero=true' in log
    assert 'CANDIDATE window=0 decode_error=Canonical' in log
    assert 'CANDIDATE window=1 decode_error=Canonical' in log
    assert 'corrected_fibres=2' in log
    assert 'queried_invalid_fibre=false' in log
    audit=(ROOT/'evidence/circle-laurent-axioms.log').read_text()
    assert 'sorryAx' not in audit
    for theorem in ['natural_tensor_embedding','checked_image_global','totalized_bad_fibres_le']:
        assert f'AspisV8.CircleLaurentRecovery.{theorem}' in audit
    coordinate=(ROOT/'evidence/source-coordinates-host.log').read_text()
    assert 'distinct_points=1048576 single_bit_source_checks=10485760' in coordinate
    controls=(ROOT/'evidence/raw-c1-controls.log').read_text()
    assert 'selected_gamma_parser_still_rejects=true' in controls
    return dict(base_revision='7b9d3f457ea929b7d1efa9e6dbafa540f0fd4143',
      same_execution=dict(seed=1,corrupt_fibres=[0,256],column=0,slots=[0,1,2,3],invalid_limb=2**31-1,
        fixing_prefix='raw C1 leaf construction BEFORE root, lambda and chi',
        strict_extractor_rejects=True,raw_root_checked=True,coefficient_windows_reject=True,
        totalized_Gao_returns_checked_witness=True,proof_accepts=True,
        observed_proof_body_bytes=int(m[3]),proof_id=hx(m[4]),C1_root=hx(m[5]),
        no_seed_search=True,execution_scope='same synthetic transfer and repaired research grammar; not full pool/SBF'),
      decoder=dict(access='frozen instrumented raw C1 SHA query graph, not a public proof/root',
        sample_positions=1153,ambient_dimension=1025,symbol_error_capacity=64,observed_sample_errors=8,
        global_totalized_fibre_cap=16,raw_bytes_preserved=True,invalid_arithmetic_value=0,
        return_validation='literal payment/runtime/nullifier/transition validator'),
      formal=dict(natural_tensor_embedding='kernel checked: one message polynomial, all circle points, degree<=1024',
        finite_check_implies_global='kernel checked for >1024 distinct circle points and bounded candidate degree',
        totalization_preserves_support='kernel checked pointwise and common-fibre cardinal inequality',
        universal_source_FFT_refinement=False,Gao_algorithm_completeness_port=False),
      source_checks=dict(all_domain_points=1048576,single_bit_factors=10485760,
        degree_hypothesis='natural tensor polynomial theorem, not rate-only RS substitution',
        actual_point_and_twiddle_kernel_certificate=False),
      event_partition=['A and raw graph/access/resource failure',
        'A and raw graph returned but all bounded candidates fail checked witness validation'],
      diagnostic_refuted='A implies all unqueried C1 field encodings are canonical',
      sampling_ledger_reused='c1-sampling-results.json: same exact rational tail, now explicitly conditional on distance of TOTALIZED word to code tuple',
      sampling_bound_changed=False,additional_soundness_terms=0,
      unresolved=dict(accepted_raw_graph_failure=None,accepted_general_decoder_failure=None,
        semantic_to_checked_witness=None,FS_lift=None,full_view_ZK=None,full_transaction_CU=None),
      body_maximum=697*16+52+24+22*621+2*296*26,new_proof_bytes=0,new_verifier_operations=0,
      grinding_security_credit_bits=0,global_100_bit_certificate=None,
      evidence_sha256={n:sha256((ROOT/'evidence'/n).read_bytes()).hexdigest() for n in
        ['noncanonical-c1-host.log','raw-c1-controls.log','source-coordinates-host.log','circle-laurent-axioms.log']})
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args();r=results()
    if args.check:
        assert r==json.loads((ROOT/'raw-c1-results.json').read_text());print('PASS same-execution noncanonical recovery, exact source-domain census, clean Lean audit and symbolic residual ledger')
    else: print(json.dumps(r,indent=2))
