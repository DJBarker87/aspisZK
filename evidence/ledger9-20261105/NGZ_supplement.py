from pathlib import Path
import json,subprocess,hashlib,lzma,time
E=Path(__file__).resolve().parent;P=E.parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ledger9-20261105';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGZ_flat'
files=[]
x=json.loads((P/'slice-d-finish-20261105/NGM_RETENTION.json').read_text())
for r in x['objects']:files.append(dict(source=x['exports']+'/'+r['file'],relative=r['file'],sha256=r['sha256'],bytes=r['bytes']))

for pre in ['NGK','NGH','NGD','NFW','NGC','NGO','NGT','NGV','NGN','NGU','NGR','NGS']:
 d=next(P.glob('*/'+pre+'_HANDOFF.md')).parent
 for p in [*d.glob(pre+'_*EXPORT*.json'),*d.glob(pre+'_CACHE_END.json')]:
  x=json.loads(p.read_text())
  def walk(o):
   if isinstance(o,dict):
    path=o.get('path')
    if path and 'sha256'in o and any(t in path for t in ['.olean','.ir']) and '/'+pre+'_exports_'in path:
     rel=path.split('/'+pre+'_exports_',1)[1].split('/',1)[1]
     files.append(dict(source=path,relative=rel,sha256=o['sha256'],bytes=o['bytes']))
    for v in o.values():walk(v)
   elif isinstance(o,list):
    for v in o:walk(v)
  if isinstance(x,dict) and 'export'in x:
   for r in x.get('files',[]):
    if 'relative'in r:r.setdefault('path',x['export']+'/'+r['relative'])
  walk(x)

code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path(B);c=Path(C)
with (b/'NGZ_SUPPLEMENT_barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NGZ_SUPPLEMENT_admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((b/'NGZ_SUPPLEMENT_admission.json').read_text());assert r.returncode==0 and ad['allowed'] is True
for prefix,root in [('NBE_SlotLoop','/home/dombarker/project-offloads/codex-cx-cpilot-cache-20261028'),('NCO_LoopSteps','/home/dombarker/project-offloads/codex-cx-cpilot-cache-20261028/NCO_objects'),('NFA_','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104'),('NEP_','/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104'),('NGA_','/home/dombarker/project-offloads/codex-cx-slice-d-field2-cache-20261104/NGA_exports_20261104')]:
 for p in Path(root).glob(prefix+'*'):
  if p.is_file() and any(s in p.name for s in ['.olean','.ir']):files.append(dict(source=str(p),relative=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
for x in files:
 p=Path(x['source']);q=c/x['relative'];assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'];q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==x['sha256']
(b/'NGZ_SUPPLEMENT.json').write_text(json.dumps(dict(files=files,admission=ad,exit=r.returncode),indent=1));print(len(files))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+code,text=True,capture_output=True);print(r.stdout,r.stderr);assert r.returncode==0
for n in ['NGZ_SUPPLEMENT.json','NGZ_SUPPLEMENT_admission.json','NGZ_SUPPLEMENT_barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
