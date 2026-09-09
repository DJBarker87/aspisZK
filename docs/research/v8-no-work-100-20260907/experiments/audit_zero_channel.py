#!/usr/bin/env python3
"""Audit complete TxV1 observations, not extrapolated CU or security bounds."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
def read(p): return json.loads(p.read_text())
def check(x):
    e,a=x['execution'],x['atomicity']
    expected=x['scenario'] in ('success','replay-nullifier')
    assert (e['outcome']=='accepted')==expected
    assert e['simulation_equals_execution'] and not e['runtime_limit_is_diagnostic_override']
    assert e['compute_units']<=e['txv1_declared_compute_unit_limit']<=1400000
    assert x['grinding_security_credit_bits']==0
    for k in ('master_unchanged','checkpoint_unchanged','entry_unchanged','registry_unchanged','proof_unchanged'):
        assert a[k],k
    if expected:
        assert e['selected_verifier_cpi_observed_in_logs'] and e['return_data_bytes']==792
        assert all(a[k] for k in ('settled_history_equals_expected','settled_lane_equals_candidate','settled_marker_equals_expected'))
        if x['authenticated_path']['history_mode']=='rollover':
            assert a['settled_rollover_page_equals_expected']
        if a['withdrawal_vault_amount_before'] is not None:
            assert a['withdrawal_vault_amount_before']-a['withdrawal_vault_amount_after']==250
            assert a['withdrawal_destination_amount_after']-a['withdrawal_destination_amount_before']==250
    else:
        assert a['failure_all_accounts_byte_exact'] and e['error'] is not None
    if x['scenario']=='replay-nullifier':
        assert a['replay_preserved_settled_state_byte_exact'] and e['replay']['error'] is not None
    return x
def dataset(rel,count):
    rows={p.stem:check(read(p)) for p in sorted((ROOT/rel).glob('*.json'))}
    assert len(rows)==count,(rel,len(rows),count)
    return rows
def summary(rows):
    shapes={}
    for op in ('transfer','withdrawal'):
        for count in (13,255):
            entries=[x for key,x in rows.items() if key.startswith(f'{op}-{count}-') and x['scenario']=='success']
            if entries:
                shapes[f'{op}-{count}']=[{'cu':x['execution']['compute_units'],
                    'body':x['fixture']['proof_bytes'],'proof_sha256':x['fixture']['proof_sha256'],
                    'tx_bytes':x['execution']['serialized_transaction_bytes']} for x in entries]
    return {'cases':len(rows),'shapes':shapes,
        'artifact_hashes':{role:next(iter(rows.values()))['artifacts'][role]['sha256']
            for role in ('selected_verifier','pool','registry')}}
Z='evidence/zero-page/'
C='evidence/channel/'
sets={
    'old_max':dataset('evidence/complete/complete-matrix-partial-max',24),
    'zero_max':dataset(Z+'zero-page-cap1200-max-v1',12),
    'zero_ordinary':dataset(Z+'zero-page-matrix-v1',24),
    'zero_v7':dataset(Z+'zero-page-v7-v1',16),
    'channel_max':dataset(C+'channel-cap1200-max-v1',12),
    'channel_ordinary':dataset(C+'channel-matrix-v1',24),
    'channel_legacy35_max':dataset(C+'channel-legacy35-cap1200-max-v1',12),
    'channel_ptoken_max':dataset(C+'channel-ptoken-cap1200-max-v1',12),
    'legacy35_v7':dataset(C+'zero-page-legacy35-v7-v1',16),
    'group_legacy35_max':dataset(C+'group-legacy35-cap1200-max-v1',12),
}
summaries={k:summary(v) for k,v in sets.items()}
for key,rows in sets.items():
    if key!='old_max':
        assert all(x['execution']['txv1_declared_compute_unit_limit']==1200000 for x in rows.values())
    if key.endswith('_max'):
        assert all(x['fixture']['proof_bytes']==40282 for x in rows.values() if x['scenario']=='success')
def compare(a,b):
    out={}
    sa,sb=summaries[a]['shapes'],summaries[b]['shapes']
    for shape in sa:
        assert len(sa[shape])==len(sb[shape])
        assert [x['proof_sha256'] for x in sa[shape]]==[x['proof_sha256'] for x in sb[shape]],(a,b,shape)
        out[shape]=[x['cu']-y['cu'] for x,y in zip(sa[shape],sb[shape])]
    return out
zero_savings=compare('old_max','zero_max')
assert all(x==13 for s,v in zero_savings.items() if s.endswith('-13') for x in v)
assert all(x==60892 for s,v in zero_savings.items() if s.endswith('-255') for x in v)
channel_savings=compare('zero_max','channel_max')
ptoken_change=compare('channel_ptoken_max','channel_max')
assert all(x==0 for v in ptoken_change.values() for x in v)
legacy_extra=compare('channel_legacy35_max','channel_ptoken_max')
group_delta=compare('channel_legacy35_max','group_legacy35_max')
assert all(x==0 for v in group_delta.values() for x in v)
for key in ('channel_legacy35_max','channel_ptoken_max'):
    for x in sets[key].values():
        ctl=x['artifacts']['token_program']['explicit_pinned_sbf_control']
        assert ctl['variant']==('legacy35' if 'legacy35' in key else 'ptoken')
for k in ('zero_max','zero_v7','channel_max','channel_legacy35_max','legacy35_v7'):
    assert summaries[k]['artifact_hashes']['pool']==summaries['zero_max']['artifact_hashes']['pool']
    assert summaries[k]['artifact_hashes']['registry']==summaries['zero_max']['artifact_hashes']['registry']
bad_old=dataset(Z+'zero-page-reject-old-v1',48)
bad_fast=dataset(Z+'zero-page-reject-fast-v1',48)
for key,x in bad_fast.items():
    assert x['scenario']=='nonzero-fresh-page'
    assert not x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['fresh_page_mutation']==bad_old[key]['fresh_page_mutation']
    assert x['execution']['error']==bad_old[key]['execution']['error']
rollback=dataset(Z+'zero-page-rollback-v1',2)
rollback.update({f'channel-{k}':v for k,v in dataset(C+'channel-rollback-v1',2).items()})
for x in rollback.values():
    assert x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['scenario']=='withdrawal-cpi-failure'
profile={}
for mode in ('old','fast'):
    x=read(ROOT/Z/f'zero-page-profile-{mode}-v1/transfer-255-1.json')
    logs=x['execution']['logs']
    vals=[]
    for i,line in enumerate(logs):
        if 'v8-pool:zero-scan:' in line:
            vals.append(int(re.fullmatch(r'Program consumption: (\d+) units remaining',logs[i+1])[1]))
    assert len(vals)==2
    profile[mode]={'checkpoint_interval_cu':vals[0]-vals[1],'total_cu':x['execution']['compute_units']}
assert profile['old']['checkpoint_interval_cu']-profile['fast']['checkpoint_interval_cu']==60880
out={'schema':'aspis.research.v8.zero-channel-performance.v1',
    'base_revision':'b9630a7099cb533ff559770db81a7a8a55ee18ba',
    'variants':summaries,'zero_scan_profile_includes_logging':profile,
    'same_proof_zero_page_savings':zero_savings,'same_proof_channel_savings':channel_savings,
    'same_proof_legacy35_extra_cu':legacy_extra,
    'same_proof_group_rewrite_savings_cu':group_delta,
    'rejection_control_pairs':len(bad_fast),'post_verifier_atomic_rollback_cases':len(rollback),
    'maximum_body_bytes':697*16+52+24+22*621+2*296*26,
    'all_measured_shapes_pass_actual_1200000':True,
    'universal_maximum_cu':None,'full_transaction_no_regression':False,
    'security':{'grinding_credit_bits':0,'global_recovery_error':None,'full_view_zk':'unresolved',
        'resource_bounded_fs':'unresolved','translated_full_acceptance_equivalence':'unresolved'},
    'proof_and_transcript_change_from_b9630a7':False}
out['worst_observed_max_body_cu']={key:max(x['cu'] for v in summaries[key]['shapes'].values() for x in v)
    for key in ('old_max','zero_max','channel_max','channel_legacy35_max')}
out['legacy35_v8_minus_same_pool_v7_max_observed_cu']={shape:max(x['cu'] for x in values)
    -summaries['legacy35_v7']['shapes'][shape][0]['cu']
    for shape,values in summaries['channel_legacy35_max']['shapes'].items()}
assert out['maximum_body_bytes']==40282
print(json.dumps(out,indent=2))
