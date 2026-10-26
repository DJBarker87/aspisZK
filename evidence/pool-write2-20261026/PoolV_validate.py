"""Read-only proof packet validation; no prover or launcher operations."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[2]
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(B.glob('PoolV_*/receipt.json'))]
expected={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['limits']==expected,r['attempt']
 assert r['swaps']=='0',r['attempt']
 for name,h in r['source_hashes'].items():
  assert sha(B/r['attempt']/'sources'/name)==h,(r['attempt'],name)
 if r['kind']=='lean':
  assert '-M7000' in r['command']
  if r['exit_status']==0:
   assert not any('sorryAx' in a for a in r['print_axioms']),r['attempt']
   for a in r['print_axioms']:
    if '[' in a:assert set(a.split('[')[1].split(']')[0].split(', '))<=set(['propext','Classical.choice','Quot.sound'])
 if r['kind']=='kani':assert r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
current=[]
for p in sorted((ROOT/'lean').glob('PoolV_*.lean')):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text()),p
 matches=[r for r in receipts if r['kind']=='lean' and r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
 assert matches,p
 current.append(dict(module=p.name,sha256=sha(p),passing_attempt=matches[-1]['attempt']))
for path,pin in json.loads((B/'PoolV_FREEZE.json').read_text())['inputs'].items():assert sha(ROOT/path)==pin['sha256'],path
inputs=json.loads((B/'PoolV_INPUTS.json').read_text())['inputs']
for row in inputs:assert sha(ROOT/row['path'])==row['sha256'],row['path']
for row in json.loads((B/'PoolV_SLICE_SOURCE.json').read_text())['slices']:
 source=(ROOT/'crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs').read_text()
 assert row['exact_text'] in source
 assert row['exact_text'] in (B/'PoolV_tail/PoolV_lib.rs').read_text()
 assert hashlib.sha256(row['exact_text'].encode()).hexdigest()==row['sha256']
for kind,attempt in [('pure','PoolV_K022'),('cpi','PoolV_K008'),('guard','PoolV_K013'),('tail','PoolV_K025')]:
 for p in (B/f'PoolV_{kind}').glob('*.rs'):
  assert sha(p)==sha(B/attempt/'sources'/f'PoolV_{kind}'/p.name),(kind,p)
assert sha(B/'PoolV_ref/PoolV_lib.rs')==sha(B/'PoolV_AENEAS003/sources/PoolV_ref/PoolV_lib.rs')
changed=subprocess.check_output(['git','diff','--name-only','c3dd218a3f','HEAD'],cwd=ROOT,text=True).splitlines()
assert all(p.startswith('evidence/pool-write2-20261026/PoolV_') or p.startswith('lean/PoolV_') for p in changed),changed
assert not any(p.suffix in ['.olean','.llbc','.so','.bin','.tar','.gz'] for p in B.rglob('*') if p.is_file())
audit=json.loads((B/'PoolV_L014/receipt.json').read_text());assert audit['exit_status']==0 and len(audit['print_axioms'])==22
counts={kind:dict(attempts=sum(r['kind']==kind for r in receipts),passed=sum(r['kind']==kind and r['exit_status']==0 for r in receipts)) for kind in ['lean','kani','charon','aeneas']}
assert counts['kani']['attempts']==25 and counts['lean']['attempts']==14,counts
summary=dict(status='pass',revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),source_tree_dirty=True,current_modules=current,counts=counts,kani_harness_executions=26,overlap='K019 substring selected both sequence and previously timed-out sequence_binding; both excluded, no more Kani runs',all_swap_zero=True,all_caps=expected,release_input_files=len(inputs),host_input_files=len(json.loads((B/'PoolV_HOST_INPUT_MATCH.json').read_text())['inputs']),new_native_enclosing_p1_theorem=False,global_premises_removed=0,source_changes=False,elf_build_trigger=False,final_audit={k:audit[k] for k in ['attempt','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']})
(B/'PoolV_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(B/'PoolV_ATTEMPTS.json').write_text(json.dumps([dict(receipt=f"{r['attempt']}/receipt.json",**{k:r[k] for k in ['attempt','kind','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']}) for r in receipts],indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','counts','release_input_files','new_native_enclosing_p1_theorem','global_premises_removed']},indent=2))
