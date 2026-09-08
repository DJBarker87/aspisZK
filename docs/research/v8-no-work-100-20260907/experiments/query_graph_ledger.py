#!/usr/bin/env python3
"""Exact retained evidence/cost ledger. Missing acceptance bounds stay null."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse,json,re
ROOT=Path(__file__).resolve().parent.parent
def parse(name):
    text=(ROOT/'evidence'/name).read_text();cases=[];seed=None
    for line in text.splitlines():
        if re.fullmatch(r'seed=\d+',line):seed=int(line.split('=')[1])
        m=re.match(r'RESULT corrupt=(true|false) accepted=(true|false) checked_witness=(true|false) touched=(\d+) body=(\d+) proof_id=\[([^]]+)\] c1_root=\[([^]]+)\]',line)
        if m:
            hx=lambda s:''.join(x.strip().zfill(2) for x in s.split(','))
            cases.append(dict(seed=seed,corrupt=m[1]=='true',accepted=m[2]=='true',checked_witness=m[3]=='true',touched_support=int(m[4]),body_bytes=int(m[5]),proof_id=hx(m[6]),c1_root=hx(m[7])))
    return text,cases
def results():
    log,cases=parse('query-graph-final-host.log')
    old=json.loads((ROOT/'payment-extraction-results.json').read_text())['cases']
    assert cases==old
    outside,a=parse('c1-boundary-host.log');inside,b=parse('c1-first-window-host.log')
    assert len(a)==len(b)==1 and all(c['accepted'] and c['checked_witness'] for c in a+b)
    assert 'full_semantic_C1_codeword=false' in outside and 'full_semantic_C1_codeword=false' in inside
    assert 'CANDIDATE window=0 checked_witness=false' in inside
    assert 'CANDIDATE window=1 checked_witness=true' in inside
    assert 'c1_hit=false' in outside and 'c1_hit=false' in inside
    both,c=parse('c1-both-windows-host.log');gao,d=parse('c1-gao-host.log');near,e=parse('c1-near-gao-host.log')
    assert len(c)==len(d)==len(e)==1
    assert c[0]['accepted'] and not c[0]['checked_witness']
    assert d[0]['accepted'] and d[0]['checked_witness']
    assert c[0]['proof_id']==d[0]['proof_id'] and c[0]['c1_root']==d[0]['c1_root']
    assert not e[0]['accepted'] and e[0]['checked_witness']
    assert 'corrected_fibres=16535' in near
    stats=[]
    for m in re.finditer(r'GRAPH_PREFIX seed=(\d+).*?stats=Stats \{ ([^}]+) \} seconds=([0-9.]+)',log):
        row={k:int(v) for k,v in re.findall(r'(\w+): (\d+)',m[2])}
        row.update(seed=int(m[1]),seconds=float(m[3]));stats.append(row)
    assert len(stats)==4
    for s in stats:
        assert s['walk_nodes']==s['recompute_hashes']==2*(1<<18)-1
        assert s['index_hashes']==s['raw_queries']+38
        assert s['default_leaves']==0
    miss=Fraction((1<<18)-22,1<<18)
    return dict(base_revision='d96f56533bba7763fd907d931df40331f2497de7',
        scope='Frozen instrumented SHA-prefix graph to bounded checked coefficient candidates, not complete FS extraction',
        baseline_and_D_cases=cases,accepted_nonpolynomial_C1_cases=[dict(fibre=256,**a[0]),dict(fibre=0,**b[0])],
        both_window_failure=c[0],same_proof_gao_repair=d[0],large_corruption_control=e[0],
        gao=dict(access='same frozen C1 query graph; no witness or original coefficients',
            fixed_sample=dict(points=1153,ambient_k=1025,symbol_error_radius=64,global_fibre_cap=16),
            scattered_sample=dict(fibres=513,points=2052,ambient_k=1025,symbol_error_radius=513,global_fibre_cap=16535),
            arithmetic_controls=2688,source_basis_checks_large=2052*1024,
            source_Lean_port=False,conditional_sampling_ledger='c1-sampling-results.json',
            large_control_sampling='fixed SHA coins; no uniform-law claim',
            no_new_protocol_bytes=True),
        prefix_stats=stats,
        single_fibre_uniform_query_miss=dict(numerator=miss.numerator,denominator=miss.denominator,display=float(miss),event='fresh uniform distinct q22 queries avoid one fixed fibre; NOT an acceptance/extraction bound'),
        graph=dict(depth=18,full_leaves=1<<18,value_bytes=403,salt_bytes=32,raw_C1_leaf_input_bytes=437,parent_input_bytes=53,
            raw_payload_storage_bytes=(1<<18)*435,tree_digest_payload_bytes=((1<<19)-1)*26,
            default_collision_inputs_max=38,ordered_query_failure_classes=['missing root','missing preimage','forward reference','truncated collision','malformed typed preimage','noncanonical M31','fuel','root recomputation mismatch'],
            supplied_extra_openings=0,rewinds_executed=0,graph_walk_fuel=(1<<19)-1,
            access='all raw calls through the research SHA gateway from fixture public-binding hash through C1 root; private query-log instrumentation, not proof-account data'),
        decoder=dict(windows=[[0,255],[256,511]],window_units='complete four-point fibres',matrix_ranks=[1024,1024],
            retained_inverse_payload_bytes=2*1024*1024*4,augmented_matrix_payload_bytes=1024*2048*4,
            candidate_mul_add_pairs=16*1024*1024,maximum_candidate_mul_add_pairs=2*16*1024*1024,
            maximum_candidate_selection_validator_calls=2,validator_count_scope='candidate-selection loop only; harness also repeats validation for assertions and proof-root coupling',full_code_test='diagnostic only; not required for checked witness return',
            guarantee='one COMMON window recovers all 16 columns under at most one corrupted fibre relative to a code tuple and the two matrix-inverse hypotheses',
            source_matrix_kernel_certificate=False,translated_Rust_refinement=False,general_error_correction=False),
        lean='experiments/ExactC1Recovery.lean; exact recovery, code-test equivalence, uniqueness, off-sample rejection, joint one-fibre two-window theorem',
        remaining_failure_event='A AND NOT X_graph_checked_with_Gao, plus the unproved actual-source/ROM coupling',
        precedence=['query-log access or resource/fuel failure','graph authentication/grammar/canonicality failure','both coefficient candidates and bounded Gao fallback fail literal payment/context/transition validation'],
        classifier_warning='non-codeword received C1 alone is not extraction failure; whole-word canonicality is currently a conservative failure, not bounded by hash collision probability',
        missing_bounds=dict(accepted_graph_or_canonical_failure=None,accepted_two_candidate_failure=None,semantic_to_payment_coverage=None,FS_source_resource_lift=None),
        near_local_ceiling='reuse unchanged near-gamma-results.json, stated bad-binding event only; no global numerical allowance calculated',
        global_100_bit_certificate=None,full_view_ZK=None,complete_transaction_CU=None,
        maximum_proof_body_bytes=697*16+52+24+22*621+2*296*26,new_proof_bytes=0,new_protocol_verifier_operations=0,
        maximum_observed_body_bytes=max(c['body_bytes'] for c in cases+a+b),grinding_security_credit_bits=0,
        exhaustive_query_order_test=dict(permutations=5040,causal_successes=80,rejections=4960,scope='all orders of one fixed seven-vertex depth-two graph; NOT all adaptive strategies'),
        evidence_hashes={n:sha256((ROOT/'evidence'/n).read_bytes()).hexdigest() for n in ['query-graph-final-host.log','c1-boundary-host.log','c1-first-window-host.log','c1-both-windows-host.log','c1-gao-host.log','c1-near-gao-host.log','exact-c1-joint-window-axioms.log','query-graph-orders.log']})
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();r=results()
    if a.check:
        assert r==json.loads((ROOT/'query-graph-results.json').read_text());print('PASS eight proof IDs, accepted fixed-window failure, SAME-proof Gao repair, large-corruption recovery, exact costs and symbolic remaining ledger')
    else: print(json.dumps(r,indent=2))
