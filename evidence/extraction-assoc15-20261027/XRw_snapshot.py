"""Hash-check inherited read-only arithmetic objects before private reuse."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
pairs=json.loads((E/'XRw_dependency-order.json').read_text())
expected={m:hashlib.sha256(Path(s).read_bytes()).hexdigest() for m,s in pairs if m.startswith(('LPe_','LPf_','LPh_','LPi_'))}
code='''from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027')
u=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027')
expected=EXPECTED
records=[]
receipts=[json.loads(p.read_text()) for p in u.glob('*/receipt.json')]
for m,h in expected.items():
 p=u/'LPm_objects'/(m+'.olean')
 if not p.exists():continue
 accepted=[r for r in receipts if r.get('module')==m and r.get('exit_status')==0 and h in r.get('source_hashes',{}).values()]
 assert accepted,(m,'missing source acceptance receipt')
 r=accepted[-1]
 src=next(k for k,v in r['source_hashes'].items() if v==h)
 assert hashlib.sha256((u/src).read_bytes()).hexdigest()==h,(m,'source mismatch')
 files=[]
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.exists():
   hh=hashlib.sha256(q.read_bytes()).hexdigest();dst=b/'XRw_objects'/q.name
   assert not dst.exists(),dst
   shutil.copy2(q,dst);assert hashlib.sha256(dst.read_bytes()).hexdigest()==hh
   files.append(dict(source=str(q),destination=str(dst),sha256=hh,bytes=q.stat().st_size))
 records.append(dict(module=m,source_sha256=h,acceptance_attempt=r['attempt'],files=files))
(b/'XRw_reused-object-snapshot.json').write_text(json.dumps(records,indent=2)+'\\n')
'''.replace('EXPECTED',repr(expected))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True)
print(r.stdout,r.stderr);r.check_returncode()
subprocess.run(['scp','-q','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_reused-object-snapshot.json',str(E)],check=True)
