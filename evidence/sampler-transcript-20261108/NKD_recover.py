"""Read-only receipt/evidence recovery after a completed submission. Never launches."""
from pathlib import Path
import json,subprocess,sys,base64,time
E=Path(__file__).resolve().parent;a=sys.argv[1];assert not (E/a/'receipt.json').exists()
B='/home/dombarker/project-offloads/codex-cx-sampler-transcript-20261108';x=json.loads((E/(a+'.json')).read_text())
code=f'''from pathlib import Path
import json,base64
b=Path({B!r});names=[str(p.relative_to(b))for p in (b/{a!r}).rglob('*')if p.is_file()]+[{(a+'.json')!r}]+{x.get('collect',[])!r}
for pattern in {x.get('collect_globs',[])!r}:names += [str(p.relative_to(b))for p in b.glob(pattern)if p.is_file()]
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in names if(b/n).is_file()}}))
'''
for i in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 with(E/'NKD_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,recovery=True,retry=i,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode==255 and i<10:time.sleep(60);continue
 raise RuntimeError(r.stderr)
for n,data in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(data))
rc=json.loads((E/a/'receipt.json').read_text());entry={k:v for k,v in rc.items()if k!='deps_fingerprint'};entry['full_receipt']=a+'/receipt.json';entry['read_only_recovery']=True
with(E/'NKD_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(entry)+'\n')
print(a+' recovered read-only; exit '+str(rc['exit_status']))
