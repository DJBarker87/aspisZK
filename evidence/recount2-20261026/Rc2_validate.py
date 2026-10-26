"""Read-only proof/source audit plus own-prefix reproducible output validation.
No prover, native gate, resource infrastructure, or dependency source is changed.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ledger=ROOT/'design/PREMISE-LEDGER-20261025.md'
before=ledger.read_bytes()
subprocess.run(['python3',str(OUT/'Rc2_recount.py')],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert ledger.read_bytes()==before
old=subprocess.check_output(['git','show','01f2b42853:design/PREMISE-LEDGER-20261025.md'],cwd=ROOT)
assert before.split(b'\n## Recount on Rc2_Top (2026-10-26)\n')[0]==old
x=json.loads((OUT/'Rc2_premises.json').read_text())
cons=json.loads((ROOT/x['baseline']).read_text())
assert len(x['diff'])==len(cons['rows'])+5
assert len({r['id'] for r in x['rows']})==len(x['rows'])
assert {r['id'] for r in x['diff'] if r['status']!='newly present'}=={r['id'] for r in cons['rows']}
assert all(r.get('blocker') and r.get('owner') for r in x['rows'] if r['classification']=='P')
assert x['counts']['actual antecedent']['classes']=={'T':82,'P':171}
assert x['counts']['deduplicated actual plus non-alias deployment']['classes']=={'T':88,'P':184}
assert x['lead_not_waiting_on_owner_routes']['deduplicated']==21
failed={2,5,7,8,9,11,14,16,21};standard={'propext','Classical.choice','Quot.sound'}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
attempts=[];matches={};seen=set()
for i in range(1,23):
 d=OUT/f'Rc2_{i:03}';r=json.loads((d/'receipt.json').read_text());log=(d/'stdout.log').read_text()
 assert r['exit_status']==(1 if i in failed else 0),(i,r['exit_status'])
 assert r['limits']==limits and r['swaps']=='0'
 assert r['command'][1:6]==['env','lean','-j1','-M7000','-DElab.async=false']
 assert len(r['sources'])==1
 for name,digest in r['source_hashes'].items():
  assert sha(d/'sources'/name)==digest
  if i not in failed and sha(ROOT/'lean'/name)==digest:matches[name]=r['attempt']
 fingerprint=json.dumps([r['source_hashes'],r['deps_fingerprint'].get('selected_objects',{})],sort_keys=True)
 assert fingerprint not in seen,('unchanged source/dependency',i)
 seen.add(fingerprint)
 if i not in failed:
  assert not re.search(r'error\(|sorryAx|: error:',log)
  for line in r['print_axioms']:
   m=re.search(r'axioms: \[([^]]*)\]',line)
   assert not m or set(m[1].split(', '))<=standard
 reservation=json.loads((OUT/f'Rc2_{i:03}-reservation.json').read_text())
 assert reservation['allowed'] and reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
 a={k:r[k] for k in ['attempt','sources','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']}
 a['resolved_source_revision']=subprocess.check_output(['git','rev-parse',r['source_revision']],cwd=ROOT,text=True).strip()
 attempts.append(a)
current=sorted((ROOT/'lean').glob('Rc2_*.lean'))
assert set(p.name for p in current)==set(matches)
for p in current:
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\b(?:native_decide|sorryAx)\b|set_option (?:maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
assert matches['Rc2_Top.lean']=='Rc2_019' and matches['Rc2_Audit.lean']=='Rc2_022'
# Exact new source selection, excluding development History, and unchanged
# transitive source provenance against the job's starting revision.
all_closure=set();own_closure=set();unchanged=[]
def visit(module):
 if module in all_closure:return
 p=ROOT/'lean'/(module+'.lean')
 if not p.exists():return # External package sources are selected by cached imports.
 all_closure.add(module)
 if module.startswith('Rc2_'):own_closure.add(module)
 else:
  original=subprocess.check_output(['git','show',f'01f2b42853:lean/{module}.lean'],cwd=ROOT)
  assert original==p.read_bytes(),module
  unchanged.append(dict(path=str(p.relative_to(ROOT)),sha256=sha(p),bytes=p.stat().st_size))
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():visit(child)
visit('Rc2_Top')
assert 'Rc2_History' not in own_closure
assert {'Rc2_Base','Rc2_Install','Rc2_Events','Rc2_Result','Rc2_Protection','Rc2_Top'}==own_closure
assert 'TwoTransactionLaw' not in (ROOT/'lean/Rc2_Top.lean').read_text()+(ROOT/'lean/Rc2_Result.lean').read_text()
# Certificate-source bindings reused; no rerun of foreign scripts that write.
np=ROOT/'evidence/native-p6-20261026'
npv=json.loads((np/'NP6_validation.json').read_text())
for p in npv['lean_sources']:assert sha(ROOT/p['source'])==p['sha256']
for path,pin in json.loads((np/'NP6_start.json').read_text())['pins'].items():
 if path!='design/PREMISE-LEDGER-20261025.md':assert sha(ROOT/path)==pin['sha256'] # Ledger is an append-only historical snapshot.
for name,digest in json.loads((np/'NP6_core-validation.json').read_text())['pins'].items():assert sha(ROOT/'crates/aspis-core'/name)==digest
# Current own dependency receipt graph agrees on accepted selected objects.
chosen={}
for module in own_closure|{'Rc2_Audit'}:
 r=json.loads((OUT/matches[module+'.lean']/'receipt.json').read_text())
 for key,pin in r['deps_fingerprint']['selected_objects'].items():
  if key.startswith('Rc2_'):
   if key in chosen:assert chosen[key]['sha256']==pin['sha256'],key
   chosen[key]=pin
paths=subprocess.check_output(['git','diff','--name-only','01f2b42853'],cwd=ROOT,text=True).splitlines()
assert all(p.startswith('lean/Rc2_') or p.startswith('evidence/recount2-20261026/') or p=='design/PREMISE-LEDGER-20261025.md' for p in paths),paths
sources=[dict(path=str(p.relative_to(ROOT)),sha256=sha(p),bytes=p.stat().st_size,accepted_attempt=matches[p.name],selected=p.stem in own_closure or p.stem=='Rc2_Audit') for p in current]
(OUT/'Rc2_source_manifest.json').write_text(json.dumps(dict(own=sources,unchanged_transitive_sources=sorted(unchanged,key=lambda r:r['path']),selected_own_objects=chosen),indent=2)+'\n')
summary=dict(validated=True,actual_theorem=x['actual_theorem'],budget=dict(lean_used=22,lean_limit=60,dependency_builds=0,kani_used=0,kani_limit=0),failed_attempts=sorted(failed),attempts=attempts,selected_own_closure=sorted(own_closure),excluded_development=['Rc2_History'],counts=x['counts'],lead_not_waiting_on_owner_routes=x['lead_not_waiting_on_owner_routes'],append_only=True,prior_ledger_sha256=hashlib.sha256(old).hexdigest(),sources=sources,checks=['complete statements and nested fields printed afresh','all 22 receipts/snapshots checked; 13 pass and nine failures excluded','six selected new theorem audits standard-only','one module/attempt, exact caps, swaps zero, no duplicate source+dependency input','all Cons retained rows diffed; every remaining P has owner/blocker/route tags','NP6 source certificate bindings checked without new native run','own selected dependency receipts agree; inherited sources unchanged','prior ledger bytes preserved; no foreign/shipped changes; no package replay or ELF rebuild'],limits='Focused coherent cached composition only; no frozen-release rebuild, global experiment association or runtime-law adoption')
(OUT/'Rc2_validation.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['validated','budget','lead_not_waiting_on_owner_routes']},indent=2))
