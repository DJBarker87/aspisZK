"""Stage new job sources; reuse pinned b3q objects only after recursive h6 checks."""
from pathlib import Path
import subprocess,json,re,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=json.loads((R/'B3Q-SOURCE-PINS-D557.json').read_text())['modules'];sources={};auth={}
for row in rows+[{ 'module':m,'path':str(D/'lean'/(m+'.lean'))}for m in sys.argv[1:]]:
 m=row['module'];p=Path(row['path']);b=p.read_bytes();assert subprocess.check_output(['git','show',rev+':'+str(p)])==b
 sources[m]=b.decode();auth[m]=dict(module=m,path=str(p),blob=subprocess.check_output(['git','rev-parse',rev+':'+str(p)],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),authority='h5 HEAD; upstream blob retained in B3Q-SOURCE-PINS-D557.json'if m.startswith('PV_B3Q_')else'h5 HEAD',imports=re.findall(r'^import (\S+)',b.decode(),re.M),tracked_conflicts=[])
code='''from pathlib import Path
import json,hashlib,re,shutil
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028');S=SOURCES;A=AUTHORITY;revision=REVISION
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Resolve dependencies against the existing job cohort before writing new files.
env=json.loads((H/'env-J-private.json').read_text());roots=[H/'lean-objects']+[Path(p)for p in env['LEAN_PATH'].split(':')]
records={};objects={};visiting=set();decisions=[]
for job in ['codex-pv-b3q-20261029','codex-pv-b3q2-20261031']:
 J=H.parent/job
 for p in sorted(J.glob('lean-*/receipt/receipt.json')):
  r=json.loads(p.read_text())
  if r.get('exit_status')==0 and r.get('module')in S:
   m=r['module'];src=J/'lean'/(m+'.lean');obj=J/'lean-objects'/(m+'.olean')
   if src.is_file() and obj.is_file() and sha(src)==A[m]['sha256']:
    records[m]=(J,p,r);objects[m]=obj

def resolve(m):
 parts=m.split('.');top=parts[0]
 if len(parts)==1:
  return next((p/(m+'.olean')for p in roots if(p/(m+'.olean')).is_file()),None)
 root=next((p for p in roots if(p/top).is_dir()),None)
 return root/('/'.join(parts)+'.olean')if root else None

def check(m):
 if m in visiting:return
 visiting.add(m)
 assert m in records,('missing accepted source/object receipt',m)
 J,p,r=records[m]
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for dep,d in r['dependency_objects'].items():
  original=Path(d['path']);assert original.is_file()and sha(original)==d['sha256'],('original dependency changed',m,dep)
  selected=objects.get(dep)if dep in S and dep.startswith('PV_B3Q_')else resolve(dep)
  assert selected and selected.is_file() and sha(selected)==d['sha256'],('cohort mismatch; rebuild required',m,dep,str(selected))
  if dep.startswith('PV_B3Q_'):check(dep)
 decisions.append(dict(module=m,source_sha256=A[m]['sha256'],object_sha256=sha(objects[m]),accepted_receipt=str(p),receipt_sha256=sha(p),command=r['command'],dependency_objects=r['dependency_objects'],decision='reuse plain copies, matching dependency fingerprint; no cohort conflicts'))
for m in S:
 if m.startswith('PV_B3Q_'):check(m)
# All imported external/PV_B3P ancestors retain the preflight-verified local cohort.
for m,s in S.items():
 p=H/'lean'/(m+'.lean')
 if m.startswith('PV_B3Q_'):
  assert not p.exists()or sha(p)==A[m]['sha256']
 p.write_text(s)
for m in visiting:
 src=objects[m];dst=H/'lean-objects'/src.name
 assert not dst.exists()or sha(dst)==sha(src)
 for companion in src.parent.glob(m+'.*'):
  if companion.suffix in ['.olean','.ilean','.trace']or companion.name.startswith(m+'.olean.'):
   shutil.copyfile(companion,dst.parent/companion.name)
x=json.loads((H/'project-resolution-resume18.json').read_text());x['revision']=revision;x['modules'].update(A);(H/'project-resolution-resume18.json').write_text(json.dumps(x,indent=2)+'\\n')
(H/'resume18/B3Q-COHORT-REUSE-D557.json').write_text(json.dumps(dict(revision=revision,decisions=decisions,conflicts=[],external_preflight_sha256=sha(H/'external-verification-resume18.json'),private_preflight_sha256=sha(H/'cache-verification-resume18.json')),indent=2)+'\\n')
print(json.dumps(dict(staged=len(S),reused=len(visiting),cohort_conflicts=[])))
'''.replace('SOURCES',repr(sources)).replace('AUTHORITY',repr(auth)).replace('REVISION',repr(rev))
print(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True),end='')
