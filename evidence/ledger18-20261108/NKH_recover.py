"""Read-only recovery after the host launcher exhausted disk; never resubmit."""
from pathlib import Path
import subprocess,json,lzma,hashlib,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,shutil,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-ledger18-20261108');a=b/'NKH_L025'
files={};stats=[]
for p in [b/'NKH_L025.json',a/'receipt.json',a/'stdout.log',a/'time.log']+list((b/'NKH_audit/batch16').glob('*')):
 if p.is_file():
  stats.append(dict(path=str(p),bytes=p.stat().st_size));files[str(p.relative_to(b))]=p.read_text()
print(json.dumps(dict(files=files,stats=stats,disk=shutil.disk_usage(b)._asdict(),process_query=subprocess.run(['pgrep','-af','NKH_'],capture_output=True,text=True).stdout)))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with(E/'NKH_RECOVERY_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr,read_only=True))+'\n')
 if r.returncode==0:break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError(r.stderr)
x=json.loads(r.stdout)
for n,t in x.pop('files').items():
 p=E/n
 if n.endswith('/receipt.json')and not t.strip():p=E/'NKH_L025/receipt.partial.json.txt'
 p.parent.mkdir(parents=True,exist_ok=True)
 raw=t.encode()
 if len(raw)>20000000:
  Path(str(p)+'.xz').write_bytes(lzma.compress(raw,preset=6));Path(str(p)+'.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
 else:p.write_bytes(raw)
x.update(status='HOST_INFRASTRUCTURE_STOP_DISK_FULL',submitted=True,resubmitted=False,scope='NKH_L025',launcher_error='S2W_run_host.py:24 receipt.json write: OSError [Errno28] No space left on device',budget_used=25,budget_total=40,further_launches_forbidden_by='local-lean.txt rule5 host-health/infrastructure stop',full_gate='INCOMPLETE_NO_PROMOTIONS')
(E/'NKH_HOST_FINDING.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(status=x['status'],files=len(x['stats']),disk=x['disk'])))
