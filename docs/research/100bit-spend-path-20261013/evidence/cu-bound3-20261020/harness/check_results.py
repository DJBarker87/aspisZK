"""Validate receipts, controls, trace parity, branch coverage and B arithmetic.
Usage: check_results.py host-root analysis-dir out.json
No PASS is inferred from measurements alone.
"""
import json,sys,collections,hashlib
from pathlib import Path
H,A,OUT=map(Path,sys.argv[1:]);checks={}
sets=['variants','variants-extra','targeted','random-a','random-b','control','fresh-control'];swept=[json.loads(l) for ss in sets for l in (H/'sweep'/ss/'sweep.jsonl').read_text().splitlines()]
assert len({r['label'] for r in swept})==len(swept)
assert all(r['exit_status']==0 and r.get('outcome')=='accepted' and r.get('error') is None and r.get('stage1_error') is None for r in swept)
checks['accepted_runs_per_kind']=dict(collections.Counter(r['kind'] for r in swept))
random=[r for r in swept if r['label'].startswith('rand-')];checks['random_accepted_per_kind']=dict(collections.Counter(r['kind'] for r in random));assert min(checks['random_accepted_per_kind'].values())>=256
checks['position_range']=[min(r['pairs'] for r in swept),max(r['pairs'] for r in swept)];assert checks['position_range']==[0,2**20-1]
checks['accepted_splits']=sorted({r['inputs']['split'] for r in swept});assert checks['accepted_splits']==[10]
source={r['label']:r for r in swept};traces=[]
for ss in ['trace-main','trace-control']:
 p=H/f'plan-{ss}.json';plan=json.loads(p.read_text());rows={r['label']:r for r in [json.loads(l) for l in (H/'sweep'/ss/'sweep.jsonl').read_text().splitlines()]}
 for run in plan['runs']:
  t=rows[run['label']];assert t['outcome']=='accepted'
  if run.get('source'):
   s=source[run['source'].split(':',1)[1]]
  else:
   ctl=[json.loads(l) for l in (H/'sweep/control/sweep.jsonl').read_text().splitlines()];s=next(r for r in ctl if r['label']==t['label'].removeprefix('trace-'))
  assert all(t[k]==s[k] for k in ['stage1_cu','settlement_cu','nested_stage2_cu']),t
  traces.append(t['label'])
checks['exact_input_traced_runs']=len(set(traces));checks['trace_cu_mismatches']=0
checks['coverage']={}
for role in ['stage1','stage2','pool']:
 d=json.loads((A/f'{role}.json').read_text());assert d['text_identical_linked_vs_deployed'];assert not d['irreducible_functions'];assert d['loop_entry_mismatch_count']==0
 executed=[(k,b) for k,b in enumerate(d['branches']) if any(t['counts'][k] for t in d['traces'])];assert all('arms' in b for _,b in executed)
 checks['coverage'][role]=dict(executed_conditional_branches=len(executed),traces=len(d['traces']),irreducible_functions=0,loop_entry_mismatches=0)
r=json.loads((A/'residuals.json').read_text());assert not r['unclassified'];checks['unclassified_sites']=0
p=json.loads((A/'phase-attribution.json').read_text());assert not p['verifier_unexplained'] and not p['pool_unexplained'];checks['phase_consistency']=dict(verifier_varying=len(p['verifier']),pool_varying=len(p['pool']),unexplained=0)
b=json.loads((A/'bound.json').read_text());assert not b['sweep']['violations'];checks['sweep_violations']=0
for tx,vs in b['B'].items():
 for V,x in vs.items():
  parts=['worst_cu','residual_elf','residual_qscan','residual_parent_sha'] if tx=='stage1' else ['worst_cu','residual_stage2','residual_pool','residual_parent_sha']
  assert x['B']==sum(x[k] for k in parts),(tx,V)
checks['bound_arithmetic']='verified';checks['per_kind']=b['per_kind']
ledger=[json.loads(l) for ss in sets+['trace-main','trace-control','profile','split11-rejection'] for l in (H/'sweep'/ss/'ledger.jsonl').read_text().splitlines()]
assert all(r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*2**30 for r in ledger)
checks['run_receipts']=len(ledger);checks['run_swaps']=0;checks['max_run_peak_rss_kib']=max(r['peak_rss_kib'] for r in ledger)
# Literal requested step-7 coverage cannot be fulfilled by this accepted domain.
checks['literal_both_accepted_splits_complete']=False
checks['split11_rejection_expected']=all(r['exit_status']==1 for r in ledger if r['label'].startswith('split11-'))
OUT.write_text(json.dumps(checks,indent=1));print(json.dumps(checks,indent=1))
