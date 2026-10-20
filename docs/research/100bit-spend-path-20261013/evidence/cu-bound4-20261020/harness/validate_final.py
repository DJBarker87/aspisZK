"""Independent complete-campaign assertions; no measurement-only PASS."""
import json,sys,collections
from pathlib import Path
H=Path(sys.argv[1]); A=H/'analysis';checks={}
sets=['control','variants','variants-extra','targeted','random-a','random-b']
read=lambda p:[json.loads(x) for x in p.read_text().splitlines()]
rows=[r for s in sets for r in read(H/f'sweep/{s}/sweep.jsonl')]
assert len({r['label'] for r in rows})==len(rows)
assert all(r['exit_status']==0 and r['outcome']=='accepted' and r['error'] is None and r['stage1_error'] is None for r in rows)
checks['accepted_per_kind']=dict(collections.Counter(r['kind'] for r in rows))
checks['random_per_kind']=dict(collections.Counter(r['kind'] for r in rows if r['label'].startswith('rand-')));assert min(checks['random_per_kind'].values())>=256
checks['position_range']=[min(r['pairs'] for r in rows),max(r['pairs'] for r in rows)];assert checks['position_range']==[0,2**20-1]
assert {r['inputs']['split'] for r in rows}=={10}
source={r['label']:r for r in rows};traces=[]
for ss in ['trace-main','trace-control']:
 p=json.loads((H/f'plan-{ss}.json').read_text());ts=read(H/f'sweep/{ss}/sweep.jsonl');by={r['label']:r for r in ts};assert len(by)==len(p['runs'])
 for run in p['runs']:
  t=by[run['label']];key=run['source'].split(':',1)[1] if run.get('source') else t['label'].removeprefix('trace-');s=source[key]
  assert t['exit_status']==0 and t['outcome']=='accepted'
  assert all(t[k]==s[k] for k in ['stage1_cu','settlement_cu','nested_stage2_cu']),t
  traces.append(t['label'])
checks['traces']=len(set(traces));checks['trace_cu_mismatches']=0
checks['coverage']={}
for role in ['stage1','stage2','pool']:
 d=json.loads((A/f'{role}.json').read_text()); assert d['text_identical_linked_vs_deployed'] and not d['irreducible_functions'] and d['loop_entry_mismatch_count']==0
 bs=[b for i,b in enumerate(d['branches']) if any(t['counts'][i] for t in d['traces'])];assert all('arms' in b for b in bs)
 checks['coverage'][role]=dict(executed_conditional_branches=len(bs),traces=len(d['traces']),irreducible_functions=0,loop_entry_mismatches=0)
r=json.loads((A/'residuals.json').read_text());assert not r['unclassified'];checks['unclassified_sites']=0
p=json.loads((A/'phase-attribution.json').read_text());assert not p['verifier_unexplained'] and not p['pool_unexplained'];checks['phase_consistency']=dict(verifier_varying=len(p['verifier']),pool_varying=len(p['pool']),unexplained=0)
b=json.loads((A/'bound.json').read_text());assert not b['sweep']['violations'];checks['sweep_violations']=0
for tx,vs in b['B'].items():
 for v,x in vs.items():
  parts=['worst_cu','residual_elf','residual_qscan','residual_parent_sha'] if tx=='stage1' else ['worst_cu','residual_stage2','residual_pool','residual_parent_sha']
  assert x['B']==sum(x[k] for k in parts)
checks['bound_arithmetic']='verified';checks['per_kind']=b['per_kind']
ledger=[r for s in sets+['trace-main','trace-control','profile'] for r in read(H/f'sweep/{s}/ledger.jsonl')]
assert all(r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*2**30 and int(r['limits']['memory.high'])==6*2**30 for r in ledger)
checks['run_receipts']=len(ledger);checks['max_run_peak_rss_kib']=max(r['peak_rss_kib'] for r in ledger);checks['swaps']=0
checks['accepted_splits']=[10];checks['admitted_domain_ruling']='LEAD-REVIEW-CU-BOUND-3-20261020.md'
(H/'validation.json').write_text(json.dumps(checks,indent=1)+'\n');print(json.dumps(checks,indent=1))
