"""Read-only evidence validation; no theorem, compiler or host infrastructure repair."""
from pathlib import Path
import json,hashlib,re,sys,lzma
E=Path(__file__).resolve().parent
rows=[json.loads(l) for l in (E/'NMD_ATTEMPTS.jsonl').read_text().splitlines()]
budget=json.loads((E/'NMD_BUDGET.json').read_text());excluded=set(budget['no_kani_launch'])
actual=[r for r in rows if r['kind']=='kani' and r['attempt'] not in excluded]
assert len(actual)<=120
assert sum(r['kind']=='lean' for r in rows)<=60
for r in actual:
 a=r['attempt'];g=json.loads((E/(a+'-graph-check.json')).read_text());lock=json.loads((E/(a+'-lock-check.json')).read_text());src=json.loads((E/(a+'-source-check.json')).read_text())
 assert g['graph_matches_frozen'] and not src['errors'] and lock['unchanged'],a
 assert lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 features={p['name']:set(p['features']) for p in g['selected_closure']}
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe'],(a,features['aspis-r1-cost-probe'])
 assert 'r0' in features['aspis-core'] and {'r0','pool-v1-kernel'}<=features['aspis-statement'],a
 assert all(not({'prover','audit-eight-way','detail-phases','cu-profiling','no-entrypoint'} & f) for n,f in features.items() if n in ['aspis-r1-cost-probe','aspis-r1-cost-probe-program']),a
 if 'aspis-r1-cost-probe-program' in features:assert {'pool-adapter','private-leaf-salts'}<=features['aspis-r1-cost-probe-program'],a
modules=['NMD_CutState','NMD_SegmentFold','NMD_CandidateFold','NMD_ComputedFold']
for m in modules:
 p=E/(m+'.lean');t=p.read_text();h=hashlib.sha256(p.read_bytes()).hexdigest()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b|maxRecDepth|maxHeartbeats',t,re.M),m
 for n in re.findall(r'^theorem (\w+)',t,re.M):assert '#print axioms '+n in t,(m,n)
 assert any(r['kind']=='lean' and r['module']==m and r['exit_status']==0 and h in r['source_hashes'].values() for r in rows),m
assert hashlib.sha256((E/'NMD_HARNESSES.patch').read_bytes()).hexdigest()==(E/'NMD_HARNESSES.patch.sha256').read_text().strip()
assert all(p.stat().st_size<=20_000_000 for p in E.rglob('*') if p.is_file())
if '--final' in sys.argv:
 assert len(actual)==120,len(actual)
 assert not list(E.rglob('__pycache__'))
 roots=set(json.loads((E/'NMD_AUDIT_ROOTS.json').read_text())['roots']);found={}
 for f in (E/'NMD_audit').glob('batch*/proof*.json'):
  for result in json.loads(f.read_text()).get('results',[]):found[result['root']]=result
 assert roots<=set(found),roots-set(found)
 for root in roots:assert set(found[root]['walked_axioms'])<={'propext','Classical.choice','Quot.sound'},root
 assert json.loads((E/'NMD_audit/scan/scan.json').read_text())['exit_status']==0
 source_hash=hashlib.sha256((E/'NMD_COMBINED_IMPORT.lean').read_bytes()).hexdigest()
 assert any(r['module']=='NMD_COMBINED_IMPORT' and r['exit_status']==0 and source_hash in r['source_hashes'].values() for r in rows)
print(json.dumps({'actual_kani':len(actual),'scoped_kani_attempts':sum(r['kind']=='kani' for r in rows),'lean_compiles':sum(r['kind']=='lean' for r in rows),'new_modules':len(modules),'final':'--final' in sys.argv,'validated':True}))
