from pathlib import Path
import hashlib,json,re,sys
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029');B=D.parent/'codex-pv-b3p6-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for r in json.loads((D/'reuse.json').read_text())['rows'].values():
 assert sha(Path(r['path']))==r['sha256'];assert sha(Path(r['source']))==r['source_sha256'];rows.append(r['path'])
cache={r['module']:r for r in json.loads((B/'cache-verification-resume13.json').read_text())['objects']}
for m,r in json.loads((D/'b3p-reuse.json').read_text())['rows'].items():
 p=B/'lean-objects'/(m.replace('.','/')+'.olean');assert sha(p)==r['object_sha256']==cache[m]['object_sha256'];assert r['source_sha256']==cache[m]['source_sha256']
 for dep,q in r['dependencies'].items():assert sha(Path(q['path']))==q['sha256']
 rows.append(str(p))
records=[]
for p in sorted(D.glob('lean*-receipt.json')):
 r=json.loads(p.read_text());assert r['admission_exit']==0 and r['admission_allowed'] is True
 assert sha(D/(p.name.replace('-receipt.json','-source.lean.txt')))==r['source_sha256']
 assert r['swaps']=='0'
 records.append(r)
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^]]*)\]',r['print_axioms']):assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
# Every current private source/object is tied to its last accepted exact snapshot.
for p in (D/'sources').glob('PV*.lean'):
 hits=[r for r in records if r['module']==p.stem and r['exit']==0 and r['source_sha256']==sha(p)]
 if hits:
  r=hits[-1];obj=D/'objects'/(p.stem+'.olean');assert sha(obj)==r['object_sha256']
# Imported third-party objects are immutable and pinned under the earlier accepted external authority.
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(Path(r['path']))==r['object_sha256']
report=dict(phase=sys.argv[1],project_objects_checked=len(rows),external_checked=len(ext),attempts=len(records),accepted=sum(r['exit']==0 for r in records),rejected=[r['attempt'] for r in records if r['exit']!=0],mismatches=[],scope='two separately coherent cohorts, no b3p/runjoin combined import claim')
(D/('verification-'+sys.argv[1]+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(report)
