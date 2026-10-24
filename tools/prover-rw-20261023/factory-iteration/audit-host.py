"""Read-only postrun inventory; never a retroactive identity gate."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=int(sys.argv[1]);O=D/'packet'/f'kani{a:03d}'
r=json.loads((O/'receipt.json').read_text())
# Retain exact changed input bytes and report; never silently repair byte drift.
changed=[]
for p,h in r['source_sha256'].items():
 p=Path(p)
 if not p.exists() or sha(p)!=h:
  row=dict(path=str(p),preflight_sha256=h,postrun_sha256=sha(p) if p.exists() else None)
  if p.exists() and p.stat().st_size<5_000_000:
   dest=O/('changed-input-'+str(len(changed))+'.txt');dest.write_bytes(p.read_bytes());row['retained_bytes']=dest.name
  changed.append(row)
outputs=[]
for p in sorted((D/'target').rglob('*')):
 if not p.is_file() or p.suffix not in ['.out','.json','.rlib','.so']:continue
 outputs.append(dict(path=str(p.relative_to(D)),sha256=sha(p),size=p.stat().st_size))
result=dict(schema='ProverRwFactoryIteration-postrun-v1',attempt=a,receipt_sha256=sha(O/'receipt.json'),changed_inputs=changed,output_metadata_only=outputs,scope='Postrun integrity assessment, not preflight proof or native identity; binaries and derived JSON above5MB retained on host only.')
(O/'postrun.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(attempt=a,changed_inputs=changed,outputs=len(outputs))))
