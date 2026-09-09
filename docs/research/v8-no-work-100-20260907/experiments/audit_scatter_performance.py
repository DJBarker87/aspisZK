#!/usr/bin/env python3
"""Exact comparison of archived matched SBF executions, not a CU extrapolation."""
import contextlib,io,json,re,runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
with contextlib.redirect_stdout(io.StringIO()):
    prior=runpy.run_path(str(ROOT/'experiments/audit_copy_performance.py'))
check,summary=prior['check'],prior['summary']
def load(name,count):
    rows={p.stem:check(json.loads(p.read_text())) for p in sorted((ROOT/'evidence/scatter'/name).glob('*.json'))}
    assert len(rows)==count,(name,len(rows))
    for x in rows.values():assert x['execution']['txv1_declared_compute_unit_limit']==1200000
    return rows
maximum=load('copy-scatter-max-v1',24);ordinary=load('copy-scatter-ordinary-v1',24)
rollback=load('copy-scatter-rollback-v1',2)
old=prior['sets']['tag7_max'];ms,os=summary(maximum),summary(ordinary)
old_summary=summary(old)
savings={}
for shape,values in ms['shapes'].items():
    baseline=old_summary['shapes'][shape]
    assert [x['proof_sha256'] for x in values]==[x['proof_sha256'] for x in baseline]
    assert all(x['body']==40282 for x in values)
    savings[shape]=[a['cu']-b['cu'] for a,b in zip(baseline,values)]
for rows in (maximum,ordinary):
    for key,x in rows.items():
        for role in ('pool','registry'):
            assert x['artifacts'][role]['sha256']==old_summary['artifact_hashes'][role]
        assert x['artifacts']['token_program']['explicit_pinned_sbf_control']['variant']=='legacy35'
        # Old and new malformed paths agree on their checked errors/outcomes.
        if rows is maximum:
            assert x['execution']['outcome']==old[key]['execution']['outcome']
            assert x['execution']['error']==old[key]['execution']['error']
for x in rollback.values():
    assert x['execution']['selected_verifier_cpi_observed_in_logs']
    assert x['scenario']=='withdrawal-cpi-failure'
v7=prior['baseline']
out={'schema':'aspis.research.v8.scatter-performance.v1',
    'base_revision':'0fa310741d483db87e91c3e69aa109a65f88e267',
    'maximum_body':ms,'ordinary':os,'same_proof_savings_cu':savings,
    'worst_observed_cu':max(y['cu'] for xs in ms['shapes'].values() for y in xs),
    'post_verifier_rollback_cases':len(rollback),
    'body_bytes':697*16+52+24+22*621+2*296*26,
    'new_proof_values_or_transcript_messages':0,
    'universal_maximum_cu':None,'global_security_certificate':None,
    'full_transaction_no_regression':False,'grinding_security_credit_bits':0}
out['margin_to_1200000']=1200000-out['worst_observed_cu']
out['max_observed_v8_excess_over_same_pool_v7']={s:max(x['cu'] for x in xs)-v7[s][0]['cu'] for s,xs in ms['shapes'].items()}
assert out['body_bytes']==40282
assert out['margin_to_1200000']>0
print(json.dumps(out,indent=2))
