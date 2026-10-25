"""Validate retained proof receipts and the append-only, reproducible recount.
No prover or build launcher is invoked by this checker.
"""
from pathlib import Path
import hashlib,json,re,subprocess
from collections import Counter
ROOT=Path(__file__).resolve().parents[2]; OUT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ledger=ROOT/'design/PREMISE-LEDGER-20261025.md'
before=ledger.read_bytes()
subprocess.run(['python3',str(OUT/'Cons_recount.py')],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert ledger.read_bytes()==before,'recount renderer changed output'
marker=b'\n## Recount on Cons_Top (2026-10-25)\n'
old=subprocess.check_output(['git','show','138146042f:design/PREMISE-LEDGER-20261025.md'],cwd=ROOT)
assert before.split(marker)[0]==old,'old ledger text changed'
data=json.loads((OUT/'Cons_premises.json').read_text())
assert len(data['diff'])==199
assert len({r['id'] for r in data['rows']})==len(data['rows'])
assert data['counts']['actual antecedent']['classes']=={'T':82,'P':174}
assert all(r.get('blocker') and r.get('owner') for r in data['rows'] if r['classification']=='P')
failed={1,12,13,15,18,19,20,21,23,26,28,30,32,34,35}
heartbeats={12,15,18,20,21,26,28,30,32,34,35}
expected_limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
receipts=[];matches={};seen_inputs=set()
standard={'propext','Classical.choice','Quot.sound'}
for i in range(1,40):
 d=OUT/f'Cons_{i:03}';r=json.loads((d/'receipt.json').read_text());log=(d/'stdout.log').read_text()
 assert r['attempt']==f'Cons_{i:03}'
 assert r['exit_status']==(1 if i in failed else 0)
 assert r['swaps']=='0' and r['limits']==expected_limits
 assert r['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
 assert len(r['sources'])==1
 for name,h in r['source_hashes'].items():
  assert sha(d/'sources'/name)==h
  current=ROOT/'lean'/name
  if i not in failed and current.exists() and sha(current)==h: matches[name]=r['attempt']
 fingerprint=json.dumps([r['source_hashes'],r['deps_fingerprint'].get('selected_objects',{})],sort_keys=True)
 assert fingerprint not in seen_inputs,('unchanged source+dependencies',i)
 seen_inputs.add(fingerprint)
 if i in heartbeats:assert 'maximum number of heartbeats (200000)' in log
 if i not in failed:
  assert 'sorryAx' not in log and ': error:' not in log
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^]]*)\]',line)
   assert not m or {x.strip() for x in m[1].split(',') if x.strip()}<=standard
 receipts.append({k:r[k] for k in ['attempt','sources','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']})
current=list((ROOT/'lean').glob('Cons_*.lean'))
assert set(p.name for p in current)==set(matches),set(p.name for p in current)-set(matches)
for p in current:
 s=p.read_text()
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option (?:maxHeartbeats|maxRecDepth)',s,re.M),p
assert matches['Cons_Top.lean']=='Cons_038'
assert matches['Cons_Pair.lean']=='Cons_037'
assert matches['Cons_Audit.lean']=='Cons_039'
audit=json.loads((OUT/'Cons_039/receipt.json').read_text())
assert len(audit['print_axioms'])==5
assert all(set(re.search(r'axioms: \[([^]]*)\]',l)[1].split(', '))==standard for l in audit['print_axioms'])
# Only own prefix sources/evidence and append-only ledger are changed since start.
base=subprocess.check_output(['git','rev-parse','1d39cf65d8^'],cwd=ROOT,text=True).strip()
paths=subprocess.check_output(['git','diff','--name-only',base],cwd=ROOT,text=True).splitlines()
assert all(p.startswith('lean/Cons_') or p.startswith('evidence/consolidate-20261026/') or p=='design/PREMISE-LEDGER-20261025.md' for p in paths),paths
sources=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p),bytes=p.stat().st_size,accepted_attempt=matches[p.name]) for p in sorted(current)]
(OUT/'Cons_source_manifest.json').write_text(json.dumps(sources,indent=2)+'\n')
# Reconcile final actual-top own dependency objects with their selected receipt hashes.
host=json.loads((OUT/'Cons_host_objects.json').read_text())
objects={Path(f['path']).name:f for r in host for f in r['files']}
closure=set()
def visit(name):
 if name in closure:return
 closure.add(name)
 source=ROOT/'lean'/(name+'.lean')
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():
    if child.startswith('Cons_'):visit(child)
visit('Cons_Audit')
for module in closure:
 r=json.loads((OUT/matches[module+'.lean']/'receipt.json').read_text())
 for key,obj in r['deps_fingerprint'].get('selected_objects',{}).items():
  name=Path(obj['path']).name
  if name in objects:assert obj['sha256']==objects[name]['sha256'],(module,name)
summary=dict(budget=dict(lean_used=39,lean_limit=60,dependency_builds=0,kani_used=0,kani_limit=0),
 final_theorem='AspisR1.Cons_Top.deployed',own_final_dependency_closure=sorted(closure),
 counts=data['counts'],failed_attempts=sorted(failed),heartbeat_failures=sorted(heartbeats),
 current_source_matches=sources,attempts=receipts,
 prior_ledger_sha256=hashlib.sha256(old).hexdigest(),append_only=True,
 baseline_sha256=data['baseline_sha256'],
 statement_and_expansions='Cons_039/stdout.log',field_expansions=['Cons_007/stdout.log','Cons_008/stdout.log','Cons_010/stdout.log'],
 method='Kernel printed signatures/fields; explicit manually reviewed classification and family deduplication, reproduced and consistency-checked by Python.',
 checks=['all 39 receipts and snapshots match','24 passing, 15 failed and excluded; all current sources have passing snapshots',
 'final five theorem audits standard-only','one module per attempt; caps exact; swap zero; no repeated source+dependency input',
 'all 199 baseline rows accounted; all P rows have owners/blockers; aliases separated',
 'prior ledger bytes preserved; no foreign/shipped changes',
 'no package/Rust/Kani/ELF rebuild; focused coherent cached proof, no release claim'])
(OUT/'Cons_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(validated=True,modules=len(sources),lean=39,kani=0,actual_counts=data['counts']['actual antecedent']),indent=2))
