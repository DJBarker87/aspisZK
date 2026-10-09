#!/usr/bin/env python3
"""Reconcile five paired runs; never call a failed run a verifier CU total."""
import hashlib,json,re,sys
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=Path(sys.argv[1]) if len(sys.argv)>1 else root/'results/r0-e2e-20261009'
load=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m1=load(root/'results/v8-state-only-cu-20261009/summary.json')
old=load(out/'measured-source-manifest.json');new=load(out/'source-manifest.json')
closure=[p for p in old['files'] if p.startswith(('crates/aspis-core/','crates/aspis-statement/','programs/aspis-verifier/')) or p in ['Cargo.toml','Cargo.lock']]
assert all(old['files'][p]==new['files'][p] for p in closure)
variants={}
for variant in ['transfer','withdrawal']:
    fixture=load(out/'final-fixtures'/f'{variant}.fixture.json')
    assert fixture['strict_native_accepted'] and fixture['roundtrip']
    for suffix in ['proof.bin','public.bin']:
        assert sha(out/f'{variant}.{suffix}')==sha(out/'final-fixtures'/f'{variant}.{suffix}')
    runs=[load(out/f'{variant}-run-{i}.json') for i in range(1,6)]
    signature=None
    for r in runs:
        assert r['simulation_execution_agree'] and r['identical_to_first_run'] and r['proof_and_public_accounts_unchanged']
        assert r['proof_sha256']==fixture['proof_sha256'] and r['public_sha256']==fixture['public_sha256']
        assert r['proof_bytes']==95712
        value=(r['execution']['error'],r['execution']['cu'],r['verifier_cu'],r['phase_markers'],r['elf_sha256'])
        if signature is not None: assert signature==value
        signature=value
    r=runs[0]; done=all(x['verifier_completed'] for x in runs)
    markers={x['phase']:x for x in r['phase_markers']}
    delta=lambda label:markers.get(label,{}).get('delta_from_previous_cu')
    merkle=[delta(f'merkle:{i}') for i in range(22)]
    v1=[delta(f'v1:{i}') for i in range(22)]
    completed_cu=r['verifier_cu'] if done else None
    variants[variant]={
      'proof_bytes':fixture['proof_bytes'],'proof_sha256':fixture['proof_sha256'],
      'prover_seconds':fixture['prover_seconds'],'prover_process_peak_rss_bytes':fixture['prover_process_peak_rss_bytes'],
      'prover_rss_scope':fixture['prover_rss_scope'],'native_verifier_seconds':fixture['native_verifier_seconds'],
      'runs':5,'simulation_execution_agree':True,'all_runs_identical':True,'strict_native_accepted':True,
      'sbf_verifier_completed':done,'completed_verifier_cu':completed_cu,
      'headroom_to_1300000_cu':1300000-completed_cu if done else None,
      'headroom_to_1400000_cu':1400000-completed_cu if done else None,
      'failed_invocation_consumed_cu':None if done else r['verifier_cu'],
      'raw_harness_consumed_cu':r['execution']['cu'],'runtime_error':r['execution']['error'],
      'failure_log':None if done else r['execution']['logs'][-1],
      'phase_cu':{'semantic':delta('semantic'),'chord_claims':delta('chord-claims'),
        'v1_per_fibre':v1,'v2_including_basis_construction':delta('v2'),
        'merkle_per_fibre':merkle,'merkle_total':sum(merkle) if all(v is not None for v in merkle) else None},
      'completed_instrumented_prefix':{'length_split_and_marker_cu':delta('parsed')},
      'txv1_bytes':r['txv1_bytes'],'txv1_scope':r['txv1_scope'],
      'fits_one_transaction_as_implemented':done and completed_cu<=1400000,
      'unavailable_reason':None if done else 'stack access violation before semantic completion; downstream CU is unmeasured, not zero',
    }
lines=(out/'sbf-build.log').read_text().splitlines()
diagnostics=[l for l in lines if l.startswith('Error:')]
(out/'sbf-stack-diagnostics.json').write_text(json.dumps({'build_exit_status':load(out/'sbf-build.json')['exit_status'],
    'runtime_safe_build':False,'diagnostics':diagnostics,
    'note':'Compiler diagnostics include unused generic/prover instantiations; the runtime crash independently confirms the live path is invalid.'},indent=2)+'\n')
cases=load(out/'corruption-cases.json')
summary={'schema':'aspis.r0-e2e.summary.v1','source_revision':new['source_revision'],
 'measured_elf_source_revision':old['source_revision'],'sbf_source_closure_unchanged_after_prover_fix':True,
 'sbf_closure_files_compared':len(closure),'variants':variants,'corruption_cases':len(cases),
 'M1_historical':m1,'comparison_limits':'M1 is atomic Rate512/q16 with PoW rejection disabled; R0 is strict PF P1+D13 q22. Different protocols and public-account transport; no CU extrapolation.',
 'resource_caps':{'MemoryHigh':4*2**30,'MemoryMax':6*2**30,'MemorySwapMax':0},
 'formal_axioms':'not applicable: Rust-only integration; no formal closure claim'}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'variants':variants,'corruption_cases':len(cases)},indent=2))
