"""Read-only artifact recovery; never submits a compiler or prover."""
from pathlib import Path
import subprocess,json,sys,time,base64,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-borrow2-20261107'
names=sys.argv[1:]
code='''from pathlib import Path
import json,base64,hashlib,datetime
b=Path(B);out={n:base64.b64encode((b/n).read_bytes()).decode() for n in names if (b/n).is_file()}
if 'NIO_EXPORT.json' in names:
 s=b/'NIO_src';report=dict(recovered_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),mitigation_files={n:hashlib.sha256((s/n).read_bytes()).hexdigest() for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']},aeneas_exit='UNRECORDED: original finally error masked the translator return; no resubmission',overall_scope_exit=1,charon_exit=0,lean_outputs=0)
 out['NIO_EXTRACTION_RECOVERY.json']=base64.b64encode(json.dumps(report,indent=2).encode()).decode()
 for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
  p=b/'NIO_native'/name
  if p.exists():out['NIO_'+name+'_PIN.json']=base64.b64encode(json.dumps(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)).encode()).decode()
print(json.dumps(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nnames='+repr(names)+'\n'+code,text=True,capture_output=True)
 with (E/'NIO_RECOVERY_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr,read_only=True))+'\n')
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise SystemExit('Read-only recovery failed; no submission attempted')
for name,encoded in json.loads(r.stdout).items():
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(encoded))
print('Read-only export/recovery artifacts collected: '+str(len(json.loads(r.stdout))))
