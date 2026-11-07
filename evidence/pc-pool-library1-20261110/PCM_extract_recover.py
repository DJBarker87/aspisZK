"""Own serial validation client for the unchanged SInt2 scope runner."""
from pathlib import Path
import subprocess,json,hashlib,shlex,sys,time,re
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
H='dombarker@100.108.41.90'; T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
a,plan_name=sys.argv[1:];assert re.fullmatch(r'PCM_E\d{3}',a)
# read-only recovery
assert len(list(E.glob('PCM_E[0-9][0-9][0-9]/receipt.json')))<10

def ssh(code,data=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,code],input=data,text=True,capture_output=True)
  with (E/'PCM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,event='transport',retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255:return r
  if submitted:raise RuntimeError('Submitted: recover read-only; do not resubmit')
  if retry<10:time.sleep(60)
 raise RuntimeError('Transport exhausted')

import base64
r=ssh('python3',f"""from pathlib import Path
import json,base64,lzma,hashlib
b=Path({B!r});a={a!r};ps=list((b/a).rglob('*'))+[q for p in b.glob(a+'_*') for q in (p.rglob('*') if p.is_dir() else [p])]+[b/(a+'.llbc')];out={{}}
for p in ps:
 if not p.is_file():continue
 n=str(p.relative_to(b));raw=p.read_bytes()
 if len(raw)>20_000_000:
  out[n+'.sha256']=base64.b64encode((hashlib.sha256(raw).hexdigest()+'\\n').encode()).decode()
  out[n+'.xz']=base64.b64encode(lzma.compress(raw,preset=6)).decode()
 else:out[n]=base64.b64encode(raw).decode()
print(json.dumps(out))
""");assert r.returncode==0,r.stderr
for n,value in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(value))
rc=json.loads((E/a/'receipt.json').read_text())
with (E/'PCM_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
print(json.dumps({k:rc[k] for k in ['attempt','module','exit_status','wall_seconds','peak_rss_kib','swaps']}))
sys.exit(rc['exit_status'])
