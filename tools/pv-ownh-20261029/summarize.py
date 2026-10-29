from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownh-20261029'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(receipts)<=60
for r in receipts:
 assert 63800<=r['attempt']<=63899
 p=R/r['source_path']
 if r['exit']==0:assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],r['module']
 for kind in ['before','launch','barrier']:
  a=json.loads((E/f'lean-{r["attempt"]}'/f'admission-{kind}.json').read_text());assert a['allowed'] is True
 assert r['swap']=='0'
 for line in re.findall(r"depends on axioms: \[([^\]]*)\]",str(r['print_axioms'])):
  assert set(x.strip() for x in line.split(',') if x.strip())<=set(['propext','Classical.choice','Quot.sound']),line
assert all(next(r for r in receipts if r['attempt']==a)['exit']==0 for a in [63853,63897,63898,63899])
manifest=json.loads((E/'frozen-proof-manifest.json').read_text())
for m in manifest['modules']:assert hashlib.sha256((R/m['path']).read_bytes()).hexdigest()==m['sha256']
native=json.loads((E/'native-harness/receipt.json').read_text());comparison=json.loads((E/'byte-comparison.json').read_text());assert native['exit']==0 and all(r['equal'] for r in comparison['runs'])
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_OWNH_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by)\b|import\s+\S*XR|set_option\s+(maxRecDepth|maxHeartbeats)',s)
# Hash current compiled objects and every recorded direct import under the
# unchanged env prefix. Newly rebuilt objects are consumed only as this cohort.
checks=[]
for r in receipts:
 if r['exit']==0:checks.append(dict(module=r['module'],source_sha256=r['source_sha256'],dependency_objects=r['dependency_objects']))
code='''from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-ownh-20261029');env=json.loads((D/'env-J.json').read_text());roots=[D/'lean-objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
def selected(m):return next(d/(m.replace('.','/')+'.olean') for d in roots if (d/(m.replace('.','/')+'.olean')).exists())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
objects=[]
for r in CHECKS:
 m=r['module'];source=D/'lean-sources'/(m+'.lean');assert sha(source)==r['source_sha256'],m
 for dep,want in r['dependency_objects'].items():assert sha(selected(dep))==want,(m,dep)
 objects.append(dict(module=m,object_sha256=sha(selected(m))))
print(json.dumps(objects))
'''.replace('CHECKS',repr(checks))
q=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert q.returncode==0,q.stderr
(E/'final-object-fingerprint.json').write_text(json.dumps(dict(objects=json.loads(q.stdout),all_recorded_direct_and_transitive_edges_verified=True,toolchain_and_lean_path='unchanged inherited env-J; private rebuilt objects first'),indent=2)+'\n')
summary=dict(lean_attempts=len(receipts),lean_success=sum(r['exit']==0 for r in receipts),failed=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit']) for r in receipts if r['exit']],native_scopes=1,kani=0,peak_lean_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),all_swaps_zero=True,standard_axioms_only=True,final_audit_ids=[63897,63898,63899],final_replay_count=1,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),target='V229/V230 focused D439 closure, not the privacy endpoint',native=native,comparison='byte-comparison.json',objects='final-object-fingerprint.json')
(E/'validation-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k!='native'})
