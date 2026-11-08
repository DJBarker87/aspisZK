"""Read-only retained object inventory; no build, deletion or remote write."""
from pathlib import Path
import json,subprocess,time,hashlib
E=Path(__file__).resolve().parent
m=json.loads((E/'NNG_R4Final_AUDIT_ROOTS.json').read_text());env=json.loads((E/'NNG_REV4_ENV.json').read_text())
names=sorted(set(m['selected_receipts'])|{'NNG_Candidate094','NNG_Candidate087','NNG_Candidate137','NNG_Candidate136','RSL_Base','RSL_Verifier','RSL_TX1_094','RSL_TX1_328','RSL_TX1_345','NNG_R4Final_COMBINED'})
payload=json.dumps(dict(names=names,paths=env['LEAN_PATH'].split(':')))
code='''import json,pathlib,hashlib,shutil
x=json.loads(PAYLOAD);rows=[]
for name in x['names']:
 matches=[]
 for root in x['paths']:
  p=pathlib.Path(root)/(name.replace('.','/')+'.olean')
  if p.is_file():
   matches=[dict(path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest())for q in sorted(p.parent.glob(p.name+'*'))if q.is_file()];break
 assert matches,name
 rows.append(dict(module=name,objects=matches))
print(json.dumps(dict(read_only=True,objects=rows,disk=shutil.disk_usage('/home/dombarker/project-offloads')._asdict(),print_axioms='N/A: retained build-output hashes, no theorem evaluation')))
'''.replace('PAYLOAD',repr(payload))
start=time.monotonic()
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 if r.returncode!=255:break
 if retry<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);x.update(exit_status=r.returncode,wall_seconds=time.monotonic()-start,transport_retries=retry,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NNG_R4Final_RETENTION.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(modules=len(x['objects']),read_only=True,exit_status=0,free_bytes=x['disk']['free'])))
