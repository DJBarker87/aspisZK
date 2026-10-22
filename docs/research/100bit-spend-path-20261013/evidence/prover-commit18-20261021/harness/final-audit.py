#!/usr/bin/env python3
"""Audit proof/evidence scope and exact endpoint/source retention locally."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
rows={}
for p in sorted((E/'lean').glob('attempts-*.jsonl')):
 for line in p.read_text().splitlines():
  r=json.loads(line);assert r['attempt'] not in rows;r['receipt_file']=str(p.relative_to(E));rows[r['attempt']]=r
allowed={'propext','Classical.choice','Quot.sound'}
for a,r in rows.items():
 assert 8656<=a<=8799
 snap=E/'lean/sources'/f"attempt-{a}-{Path(r['module']).stem}.lean.txt"
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==r['source_sha256']
 assert r['source_revision'] and len(r['deps_fingerprint'])==64
 assert r['swaps']==0 and r['cgroup_memory_max_gib']==8
 if r['accepted']:
  assert r['exit_status']==0 and not r['errors']
  for audit in r['axioms']:
   if 'depends on axioms:' in audit:
    names=set(x.strip() for x in audit.split('[',1)[1].split(']',1)[0].split(','))
    assert names<=allowed,(a,names)
final=rows[8674];assert final['accepted']
final_names={re.match(r"'([^']+)'",a)[1] for a in final['axioms']}
proofs=[]
for p in sorted((L/'R1Z').glob('ProverCommit*18.lean')):
 ns=re.search(r'^namespace (\S+)',p.read_text(),re.M)
 if not ns:continue
 current=hashlib.sha256(p.read_bytes()).hexdigest()
 relevant=[r for r in rows.values() if r['module']=='R1Z/'+p.name and r['accepted']]
 assert relevant and max(relevant,key=lambda r:r['attempt'])['source_sha256']==current,p
 for name in re.findall(r'^theorem (\S+)',p.read_text(),re.M):
  full=ns[1]+'.'+name
  assert full in final_names,full
  proofs.append(full)
assert len(proofs)==32 and len(final_names)==33
assert hashlib.sha256((L/'R1Z/ProverCommit18Audit.lean').read_bytes()).hexdigest()==final['source_sha256']
for name in ['Types','Funs']:
 p=L/'AspisR1SimulatorCoin18'/(name+'.lean')
 r=max((r for r in rows.values() if r['module']=='AspisR1SimulatorCoin18/'+name+'.lean' and r['accepted']),key=lambda r:r['attempt'])
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
rust=json.loads((E/'rust-attempts.json').read_text())
accepted={r['name'] for r in rust if r['accepted']}
assert accepted=={'entropy-os-failure-v1','entropy-first-success-v4','simcoin-transition-v1','simcoin-charon-v1','simcoin-aeneas-v1'}
for r in rust:
 assert r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if r['accepted'] and ('entropy-' in r['name'] or 'transition' in r['name']):
  assert 'VERIFICATION:- SUCCESSFUL' in (E/'receipts'/r['name']/'stdout.log').read_text()
assert json.loads((E/'extraction/simcoin/llbc.json').read_text())['has_errors'] is False
assert json.loads((E/'sim-llbc-v1.json').read_text())['has_errors'] is True
endpoint='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean'
base=subprocess.check_output(['git','show','c35b7b481:'+endpoint])
assert Path(endpoint).read_bytes()==base==(E/'endpoint-before.lean.txt').read_bytes()==(E/'endpoint-after.lean.txt').read_bytes()
assert not (E/'endpoint.diff').read_bytes()
changed=subprocess.check_output(['git','diff','--name-only','c35b7b481'],text=True).splitlines()
assert all('/lean/R1Z/SourceIdentification' not in p and '/lean/R1Z/RustRuntimeJoin' not in p and '/lean/R1Z/PrivacyR1FinalRelease' not in p for p in changed)
assert all(p.startswith('docs/research/') for p in changed)
for p in E.rglob('*'):
 if p.is_file():
  assert p.suffix not in {'.olean','.llbc','.tar','.gz','.so','.a'}
  assert not p.read_bytes().startswith(b'\x7fELF'),p
result=dict(status='Evidence/retention audit passes; deployed target not established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),new_theorems=len(proofs),final_axiom_audits=len(final_names),accepted_lean_attempts=sorted(a for a,r in rows.items() if r['accepted']),excluded_lean_attempts=sorted(a for a,r in rows.items() if not r['accepted']),prelaunch_retired_attempt=8668,accepted_rust_targets=sorted(accepted),endpoint_unchanged=True,production_and_concurrent_sources_unchanged=True,new_shipped_experiment=False,new_whole_run_joins=False,proofs=proofs)
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='proofs'},indent=2))
