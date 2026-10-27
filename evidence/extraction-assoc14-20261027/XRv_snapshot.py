"""Inventory immutable inherited inputs; copy only required unchanged objects privately."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
mods=json.loads(Path('evidence/extraction-assoc12-20261027/XRt_remaining.json').read_text())
mods={m:s for m,s in mods.items() if m.startswith('XRn_') or m=='XRk_ResultTools'}
expected={m:hashlib.sha256(Path(s).read_bytes()).hexdigest() for m,s in mods.items()}
code='''from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc14-20261027')
u=Path('/home/dombarker/project-offloads/codex-cx-extraction-assoc13-20261027')
expected=EXPECTED
records=[]
for m,h in expected.items():
 s=u/'XRu_generated'/(m+'.lean');p=u/'XRu_objects'/(m+'.olean')
 assert hashlib.sha256(s.read_bytes()).hexdigest()==h,(m,'source mismatch')
 receipts=[json.loads(r.read_text()) for r in u.glob('XRu_L*/receipt.json')]
 accepted=[r for r in receipts if r['module']==m and r['exit_status']==0 and r['source_hashes'].get('XRu_generated/'+m+'.lean')==h]
 assert accepted,(m,'missing checked source receipt')
 files=[]
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.exists():
   hh=hashlib.sha256(q.read_bytes()).hexdigest();dst=b/'XRv_objects'/q.name
   shutil.copy2(q,dst);assert hashlib.sha256(dst.read_bytes()).hexdigest()==hh
   files.append(dict(source=str(q),destination=str(dst),sha256=hh,bytes=q.stat().st_size))
 records.append(dict(module=m,source_sha256=h,acceptance_attempt=accepted[-1]['attempt'],files=files))
(b/'XRv_reused-object-snapshot.json').write_text(json.dumps(records,indent=2)+'\\n')
'''.replace('EXPECTED',repr(expected))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True)
print(r.stdout,r.stderr);r.check_returncode()
subprocess.run(['scp','-q','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-extraction-assoc14-20261027/XRv_reused-object-snapshot.json',str(E)],check=True)
