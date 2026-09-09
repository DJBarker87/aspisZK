#!/usr/bin/env python3
"""Read-only audit of matched complete measurements and exact byte invariance."""
import contextlib,io,json,runpy,re,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
# Reuse the earlier assertion vocabulary; this only checks archived JSON,
# not a rebuild, proof replay, or rerun of unchanged transactions.
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(ROOT/'experiments/audit_zero_channel.py'))
check,summary=prior['check'],prior['summary']
def read(p): return json.loads(p.read_text())
def load(name,expected):
    rows={p.stem:check(read(p)) for p in sorted((ROOT/'evidence/copy'/name).glob('*.json'))}
    assert len(rows)==expected,(name,len(rows))
    for x in rows.values():
        assert x['execution']['txv1_declared_compute_unit_limit']==1200000
        assert x['grinding_security_credit_bits']==0
    return rows
sets={
    'channel_max':prior['sets']['channel_legacy35_max'],
    'suffix_max':load('copy-suffix-max-v1',24),
    'tag7_max':load('copy-tag7-max-v1',24),
    'tag7_ordinary':load('copy-tag7-ordinary-v1',24),
}
summaries={k:summary(v) for k,v in sets.items()}
def compare(a,b):
    out={}
    for shape,old in summaries[a]['shapes'].items():
        new=summaries[b]['shapes'][shape]
        assert [x['proof_sha256'] for x in old]==[x['proof_sha256'] for x in new]
        out[shape]=[x['cu']-y['cu'] for x,y in zip(old,new)]
    return out
for name,rows in sets.items():
    for x in rows.values():
        for role in ('pool','registry'):
            assert x['artifacts'][role]['sha256']==summaries['channel_max']['artifact_hashes'][role]
        if name.endswith('_max') and x['scenario']=='success':
            assert x['fixture']['proof_bytes']==40282
        assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant']=='legacy35'
rollback=load('copy-tag7-rollback-v1',2)
for x in rollback.values():
    assert x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['scenario']=='withdrawal-cpi-failure'
baseline=prior['summaries']['legacy35_v7']['shapes']
profile=read(ROOT/'experiments/terminal-channel-profile.json')
intervals={};previous=None
for i,line in enumerate(profile['execution']['logs']):
    if line.startswith('Program log: v8:'):
        remaining=int(re.fullmatch(r'Program consumption: (\d+) units remaining',profile['execution']['logs'][i+1])[1])
        if previous: intervals[line.removeprefix('Program log: ')]=previous[1]-remaining
        previous=(line,remaining)
out={
    'schema':'aspis.research.v8.copy-performance.v1',
    'base_revision':'32026b0a1dc139f2684dd9dad247901d8d5ecdd2',
    'variants':summaries,
    'same_proof_suffix_savings_cu':compare('channel_max','suffix_max'),
    'same_proof_tag7_savings_cu':compare('suffix_max','tag7_max'),
    'same_proof_combined_savings_cu':compare('channel_max','tag7_max'),
    'profile_intervals_including_logs':intervals,
    'post_verifier_rollback_cases':len(rollback),
    'maximum_body_bytes':697*16+52+24+22*621+2*296*26,
    'new_proof_values_or_transcript_messages':0,
    'all_measured_shapes_pass_actual_1200000':True,
    'universal_maximum_cu':None,'full_transaction_no_regression':False,
    'security':{'grinding_credit_bits':0,'global_recovery_error':None,
        'full_view_zk':'unresolved','resource_bounded_fs':'unresolved',
        'translated_full_acceptance_equivalence':'unresolved'},
}
out['worst_observed_cu']={k:max(y['cu'] for xs in s['shapes'].values() for y in xs) for k,s in summaries.items()}
out['remaining_margin_to_1200000']=1200000-out['worst_observed_cu']['tag7_max']
out['max_observed_v8_excess_over_same_pool_v7']={shape:max(y['cu'] for y in xs)-baseline[shape][0]['cu'] for shape,xs in summaries['tag7_max']['shapes'].items()}
assert out['maximum_body_bytes']==40282
print(json.dumps(out,indent=2))
