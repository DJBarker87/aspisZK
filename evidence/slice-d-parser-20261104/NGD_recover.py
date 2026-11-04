"""Read-only recovery after submission; never starts or resubmits a scope."""
from pathlib import Path
import subprocess,json,time,sys
E=Path(__file__).resolve().parent;a=sys.argv[1];assert a=='NGD_L034';B='/home/dombarker/project-offloads/codex-cx-slice-d-parser-20261104';H='dombarker@100.108.41.90'
for retry in range(1,11):
 code=f'''from pathlib import Path
import json,subprocess
b=Path({B!r});a={a!r};p=b/a
files={{str(q.relative_to(b)):q.read_text()for q in p.rglob('*')if q.is_file()}}if p.exists()else{{}}
if (b/(a+'.json')).exists():files[a+'.json']=(b/(a+'.json')).read_text()
print(json.dumps(dict(files=files,processes=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines())))
'''
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,capture_output=True,text=True)
 with (E/'NGD_TRANSPORT.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,recovery=True,retry=retry,utc=time.time(),exit=r.returncode,submitted=True,stderr=r.stderr))+'\n')
 if r.returncode==255:
  if retry<10:print('Transport retry '+str(retry),flush=True);time.sleep(60);continue
  raise SystemExit('STOP persistent transport failure; submitted attempt unresolved, no resubmit')
 assert r.returncode==0,r.stderr
 x=json.loads(r.stdout)
 for n,t in x['files'].items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
 active=[p for p in x['processes']if 'S2W_run_host.py '+a+'.json'in p and 'python3 -'not in p]
 (E/(a+'-RECOVERY.json')).write_text(json.dumps(dict(retry=retry,active=active,receipt_present=a+'/receipt.json'in x['files']),indent=2)+'\n')
 if a+'/receipt.json'in x['files']:
  receipt=json.loads(x['files'][a+'/receipt.json']);old=[json.loads(l)['attempt']for l in (E/'NGD_ATTEMPTS.jsonl').read_text().splitlines()]
  if a not in old:
   with (E/'NGD_ATTEMPTS.jsonl').open('a')as f:f.write(json.dumps(receipt)+'\n')
  print(json.dumps({k:receipt[k]for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print(x['files'].get(a+'/stdout.log','')[-2000:]);break
 if active:raise SystemExit('Still active; recover read-only later, no parallel launch')
 raise SystemExit('Unresolved missing receipt; no resubmit')
