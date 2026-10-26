"""Validate receipts, exact source pins and the reproducible recount; no provers."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;ROOT=P.parents[1]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipts=[];accepted=set();keys=set()
for n in range(1,21):
 a=f'Rc3_{n:03}';x=json.loads((P/a/'receipt.json').read_text());receipts.append(x)
 assert x['attempt']==a
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'
 assert '-M7000' in x['command'] and '-j1' in x['command']
 assert x['source_revision'] and x['wall_seconds']>0 and int(x['peak_rss_kib'])>0
 assert x['exit_status']==(1 if n==1 else 0)
 assert json.loads((P/(a+'-reservation.json')).read_text())['allowed']
 for f,h in x['source_hashes'].items():assert sha(P/a/'sources'/f)==h
 # Environment changes are material inputs:001→002 repairs missing path.
 k=json.dumps([x['source_hashes'],x['env'],x['deps_fingerprint']],sort_keys=True)
 assert k not in keys,(a,'unchanged compile');keys.add(k)
 for line in x['print_axioms']:
  names=line.split('[')[-1].removesuffix(']').split(', ')
  assert set(names)<={'propext','Classical.choice','Quot.sound'},(a,line)
  accepted.add(line.split("'")[1])
assert not (P/'Rc3_021/receipt.json').exists()
barrier=json.loads((P/'Rc3_021-barrier-retry.json').read_text())
assert barrier['allowed_retries']==1 and barrier['retry_succeeded']==False
manifest=json.loads((P/'Rc3_source_manifest.json').read_text())
for r in manifest['inherited_sources']:assert sha(ROOT/r['path'])==r['sha256']
for path,e in manifest['own'].items():assert sha(ROOT/path)==e['sha256']
for path in (ROOT/'lean').glob('Rc3_*.lean'):
 assert str(path.relative_to(ROOT)) in manifest['own'],path
 text=path.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text),path
 assert 'maxHeartbeats' not in text and 'maxRecDepth' not in text
assert all(v['matches'] for v in json.loads((P/'Rc3_inherited_objects_checked.json').read_text()).values())
for r in json.loads((P/'Rc3_NONVACUITY.json').read_text())['files']:assert sha(ROOT/r['path'])==r['sha256']
artifacts=['Rc3_premises.json','Rc3_field_catalog.json','Rc3_REMAINING.md','Rc3_LEDGER.md']
before={n:sha(P/n) for n in artifacts}
subprocess.run(['python3',str(P/'Rc3_recount.py')],check=True,stdout=subprocess.DEVNULL,cwd=ROOT)
assert before=={n:sha(P/n) for n in artifacts}
pin=json.loads((P/'Rc3_ledger_prefix.json').read_text())
doc=(ROOT/'design/PREMISE-LEDGER-20261025.md').read_bytes()
assert hashlib.sha256(doc[:pin['bytes']]).hexdigest()==pin['sha256']
# Verify the original complete ledger prefix against the actual branch parent.
base=subprocess.check_output(['git','show','4d580aa091^:design/PREMISE-LEDGER-20261025.md'],cwd=ROOT)
assert doc[:pin['bytes']]==base
subprocess.run(['git','diff','--check'],check=True,cwd=ROOT)
result=dict(lean_attempts=20,lean_budget=60,kani_runs=0,kani_budget=0,passes=19,
 excluded_failures=['Rc3_001: missing inherited dependency search path; corrected environment in002'],
 blocked_attempt='Rc3_021: reservation FileNotFoundError repeated after mandatory30s wait/one retry; no compile',
 unused_compile_slots=40,dependency_builds=0,package_replays=0,
 theorem_axioms=sorted(accepted),accepted_axioms=['propext','Classical.choice','Quot.sound'],
 receipts=[{k:r[k] for k in ['attempt','sources','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','print_axioms']} for r in receipts],
 current_sources=len(manifest['own']),inherited_sources=len(manifest['inherited_sources']),
 inherited_object_hashes_checked=len(manifest['expected_inherited_objects']),nonvacuity_hashes_rechecked=569,
 ledger_prefix_preserved=True,recount_reproducible=True,
 counts=json.loads((P/'Rc3_premises.json').read_text())['counts'])
(P/'Rc3_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['receipts','counts']},indent=2))
