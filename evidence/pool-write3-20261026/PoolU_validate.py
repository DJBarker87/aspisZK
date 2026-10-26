"""Read-only packet validation; no build/launcher/monitor implementation."""
from pathlib import Path
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent
R=B.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(B.glob('PoolU_*/receipt.json'))]
assert len(receipts)==4
caps={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in receipts:
 assert r['kind']=='lean' and '-M7000' in r['command'] and r['limits']==caps
 assert r['swaps']=='0'
 for name,h in r['source_hashes'].items():assert sha(B/r['attempt']/'sources'/name)==h
 if r['exit_status']==0:
  for a in r['print_axioms']:
   assert 'sorryAx' not in a
   if '[' in a:assert set(a.split('[')[1].split(']')[0].split(', '))<= {'propext','Classical.choice','Quot.sound'}
current=[]
for p in sorted((R/'lean').glob('PoolU_*.lean')):
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b|set_option (maxHeartbeats|maxRecDepth)',p.read_text())
 passed=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(p.name)==sha(p)]
 assert passed,p
 current.append({'module':p.name,'sha256':sha(p),'receipt':passed[-1]['attempt']+'/receipt.json'})
for name,pin in json.loads((B/'PoolU_FREEZE.json').read_text())['source_pins'].items():assert sha(R/name)==pin['sha256']
inputs=json.loads((R/'evidence/pool-write2-20261026/PoolV_INPUTS.json').read_text())['inputs']
for row in inputs:assert sha(R/row['path'])==row['sha256'],row['path']
for row in json.loads((B/'PoolU_LEAF_INVENTORY.json').read_text())['records']:
 assert sha(R/row['receipt'])==row['receipt_sha256']
changed=subprocess.check_output(['git','diff','--name-only','83b9c6fbd1'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/PoolU_') or p.startswith('evidence/pool-write3-20261026/PoolU_') for p in changed),changed
assert not any(p.suffix in {'.olean','.so','.bin','.llbc','.gz','.tar'} for p in B.rglob('*') if p.is_file())
audit=receipts[-1];assert audit['attempt']=='PoolU_004' and audit['exit_status']==0 and len(audit['print_axioms'])==6
summary={'status':'pass','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'dirty_source_snapshots':True,'lean_attempts':len(receipts),'lean_passed':sum(r['exit_status']==0 for r in receipts),'kani_runs':0,'lean_allowance_exhausted':False,'current_modules':current,'all_caps':caps,'all_swap_zero':True,'inherited_compiler_inputs_checked':len(inputs),'native_p1_certificate_established':False,'global_premises_removed':0,'new_runtime_item':False,'shipped_changes':False,'elf_rebuild_trigger':False,'audit':{k:audit[k] for k in ['attempt','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms']}}
(B/'PoolU_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(B/'PoolU_ATTEMPTS.json').write_text(json.dumps([{'receipt':r['attempt']+'/receipt.json',**{k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']}} for r in receipts],indent=2)+'\n')
print(json.dumps(summary,indent=2))
