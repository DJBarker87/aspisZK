#!/usr/bin/env python3
"""Read-only final source/object/fingerprint and theorem-axiom audit in env J."""
import pathlib, subprocess, json, hashlib, re
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
LEAN=ROOT/'docs/research/v8-r0-zk-20261009/lean'
files=sorted([*(LEAN/'R1Z').glob('*Bin.lean'),*(LEAN/'R1J').glob('*Bin.lean')])
rows=[json.loads(x) for x in (HERE/'attempts.jsonl').read_text().splitlines()]
good={r['module']:r for r in rows if r['exit']==0}
mods={'.'.join(p.relative_to(LEAN).with_suffix('').parts):p for p in files}
script='''import pathlib, json, hashlib, re
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
mods=MODS
out={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else 'missing'
for m in mods:
 p=J/'sources'/(m.replace('.','/')+'.lean')
 o=J/'objects'/(m.replace('.','/')+'.olean')
 deps=re.findall(r'^import (\\S+)',p.read_text(),re.M)
 ds={d:sha(J/'objects'/(d.replace('.','/')+'.olean')) for d in sorted(deps)}
 out[m]=dict(source_sha256=sha(p),object_sha256=sha(o),object_bytes=o.stat().st_size,
   dependency_objects=ds,deps_fingerprint=hashlib.sha256(';'.join(f'{d}={s}' for d,s in ds.items()).encode()).hexdigest()[:16])
print(json.dumps(out))
'''.replace('MODS',repr(list(mods)))
remote=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
order=[]
def visit(m):
 if m in order:return
 for d in remote[m]['dependency_objects']:
  if d in mods:visit(d)
 order.append(m)
for m in mods:visit(m)
for m in order:
 p=mods[m];s=p.read_text();r=good[m];v=remote[m]
 assert hashlib.sha256(p.read_bytes()).hexdigest()==v['source_sha256']==r['source_sha256'],m+' source drift'
 assert r['deps_fingerprint']==v['deps_fingerprint'],m+' dependency drift'
 assert r['swaps']=='0',m+' swaps'
 for ax in r['axioms']:
  if 'depends on axioms: [' in ax:
   names=set(x.strip() for x in ax.split('depends on axioms: [')[1].split(']')[0].split(','))
   assert names <= {'propext','Classical.choice','Quot.sound'},(m,names)
 for th in re.findall(r"^theorem ([\w.']+)",s,re.M):
  assert '#print axioms '+th+'\n' in s,(m,'missing print',th)
  assert any(a.split("' depends on axioms:")[0].split("' does not depend")[0].endswith('.'+th) for a in r['axioms']),(m,'missing receipt',th)
 v.update(attempt=r['attempt'],repo_source=str(p.relative_to(ROOT)),axioms=r['axioms'])
 for d in v['dependency_objects']:
  if d in good:assert good[d]['attempt'] < r['attempt'],(m,d,'dependency order')
report=dict(base_revision='f9016d0a2',handover_revision='2d7d47218',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_dirty=bool(subprocess.check_output(['git','status','--porcelain','--','docs/research/v8-r0-zk-20261009/lean'],text=True).strip()),environment='J',order=[dict(module=m,**remote[m]) for m in order])
(HERE/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
print('Verified',len(order),'modules; source hashes, import-object fingerprints, dependency order, every theorem audit and standard axioms match.')
