"""Audit actual receipts and retained integration evidence; never run a prover."""
from pathlib import Path
import json,ast,subprocess,math
E=Path('evidence/pv-integ4-20261027');T=Path('tools/pv-integ4-20261027');candidate='03905a52594fadc50a1c00ab3f240a79632e8ffd';baseline='c57a344726745387efb38d1571d885c69ce829ee'
load=lambda p:json.loads(p.read_text())
allowed_failures={'build-default':1,'audit-corpus-scope-001':2};receipts=[]
for p in sorted(E.rglob('receipt/receipt.json')):
 r=load(p);scope=p.parent.parent;rel=str(scope.relative_to(E))
 expected=baseline if rel.startswith('combined/baseline/') else candidate
 assert r['source_revision']==expected,(rel,r['source_revision'])
 assert r['exit_status']==allowed_failures.get(rel,0),(rel,r['exit_status'])
 assert r['swaps']==0 and r['peak_rss_kib'] is not None
 lim=r['limits'];assert lim=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},(rel,lim)
 pre=scope/'admission-before.json'
 if not pre.exists():pre=scope/'reservation.json'
 assert load(pre)['allowed'] and load(scope/'admission-barrier.json')['allowed']
 assert r['print_axioms']=='N/A: no Lean compilation'
 receipts.append(dict(path=str(p.relative_to(E)),exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=expected))
for side in ['baseline','candidate']:
 assert load(E/f'combined-{side}-source-identity.json')['passed']
pre=load(E/'combined-candidate-source-identity.json');post=load(E/'combined-candidate-post-cost-source-identity.json');assert post['passed'] and pre['files']==post['files']
r=load(E/'combined/corpus-6000/pipeline-final.json');assert (r['complete'],r['passed'],r['completed_pairs'],r['fully_executed_proof_pairs'],r['rejected_prefix_pairs'],r['oracle_logged_pairs'])==(True,True,1000,600,100,4)
assert sorted(x['coin'] for x in r['cases'])==list(range(6000,7000))
for n in range(6000,7000):assert load(E/f'combined/corpus-6000/comparison-{n}.json')['passed']
a=load(E/'combined/record-ledger-audit.json');assert a['passed'] and a['records']==a['raw_records_identical']==a['canonical_records_byte_identical']==a['ledger_pairs_identical']==1000
res=r['final_resources'];assert res['pids_events']['max']==res['memory_events']['oom_kill']==res['memory_events']['oom']==res['swap_peak_bytes']==0
reviews=[json.loads(s) for s in (E/'combined/corpus-6000/pipeline-resource-reviews.jsonl').read_text().splitlines()];assert len(reviews)==21
assert load(E/'batch1-counts/fixture-equivalence.json')['passed'] and all(load(E/'batch1-counts/restored.json').values())
projection=load(E/'cost-projection.json');assert projection['complete']
for row in projection['rows']:
 assert math.isclose(row['percent_of_14_38s'],row['cumulative_delta_seconds']/14.38*100,abs_tol=1e-12)
cl=load(E/'cleanup-resume.json');assert not cl['remaining_targets'] and len(cl['retained_keys'])==3 and cl['keys_destroyed']==cl['keys_unlinked']==cl['keys_moved']==0 and not cl['quiet_timing_run']
for p in T.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
changed=subprocess.check_output(['git','diff','--name-only',candidate],text=True).splitlines();assert all(n.startswith(str(E)+'/') or n.startswith(str(T)+'/') for n in changed),changed
subprocess.run(['git','diff','--check'],check=True)
plan=(E/'TIMING-PLAN.md').read_text();assert 'combined-quiet-001' in plan and 'timing.py' in plan
report=dict(runtime_revision=candidate,control_revision=baseline,receipts_checked=receipts,expected_failed_receipts_retained=allowed_failures,admission_semantics='all executed scopes have allowed:true preflight and in-scope; pinned wrappers require exit0 as well',fixture_gate='PASS per explicit lead ruling; raw seconds-only differences retained',differential_pairs=1000,proof_pairs=600,rejected_prefix_pairs=100,oracle_log_pairs=4,canonical_and_ledger_pairs=1000,resource_reviews=21,post_cost_source_restoration=True,full_cost_projection=True,timing_gate_run=False,remaining_targets=[],keys_retained=3,keys_destroyed=0,implementation_and_lean_diff_empty=True,lean_attempts=0,kani_attempts=0,ids_used=[],ids_unused=[39500,39599],print_axioms='N/A no Lean compilation',premises=dict(removed=0,added=0,weakened=0,changed=0),trust_fields=['entropy_law','entropy_kernel','observation'],python_syntax='ast.parse PASS',diff_check='PASS',target='not yet established')
(E/'validation-resume.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS:',len(receipts),'scope receipts; 1000 pairs; cost, source restoration and cleanup verified')
