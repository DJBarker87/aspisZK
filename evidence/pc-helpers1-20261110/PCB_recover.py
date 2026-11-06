"""Read-only recovery after submission: never launches or resubmits any scope."""
from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-pc-helpers1-20261110';H='dombarker@100.108.41.90';a=sys.argv[1]
assert a=='PCB_K040'
for retry in range(11):
 time.sleep(60)
 code=f'''from pathlib import Path
import json,subprocess
b=Path({B!r});a={a!r};names=[str(p.relative_to(b)) for p in (b/a).rglob('*') if p.is_file()]+[a+'.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-selected-features.txt',a+'-graph.stderr']
status=subprocess.run(['systemctl','--user','show','run-re15e092771894b69bc1d334c6a1b7ff6.scope','-p','ActiveState','-p','SubState'],capture_output=True,text=True)
print(json.dumps(dict(files={{n:(b/n).read_text() for n in names if (b/n).is_file()}},scope_status=status.stdout,scope_stderr=status.stderr)))
'''
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,'python3'],input=code,capture_output=True,text=True)
 with (E/'PCB_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,recovery=True,retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==255:
  print(a+' recovery transport retry '+str(retry),flush=True);continue
 assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);(E/(a+'-recovery-'+str(retry)+'.json')).write_text(json.dumps(dict(scope_status=x['scope_status'],scope_stderr=x['scope_stderr'],files=list(x['files']))))
 for n,s in x['files'].items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
 if a+'/receipt.json' not in x['files']:
  if 'ActiveState=active' in x['scope_status'] or 'SubState=running' in x['scope_status']:print(a+' still active; read-only wait',flush=True);continue
  raise RuntimeError('Unresolved receipt after transport recovery; never resubmit')
 rc=json.loads(x['files'][a+'/receipt.json']);assert rc['attempt']==a
 if not any(json.loads(l)['attempt']==a for l in (E/'PCB_ATTEMPTS.jsonl').read_text().splitlines()):
  with (E/'PCB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(rc)+'\n')
 print(json.dumps({k:rc.get(k) for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True);sys.exit(0)
raise RuntimeError('STOP: ten consecutive read-only recovery transport failures; never resubmit')
