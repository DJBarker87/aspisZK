"""Recover original logs and retain every rejected source by committed blob."""
from pathlib import Path
import subprocess,json,shlex,hashlib,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjn-20261029'
records=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
code=r'''import json,sys,pathlib,hashlib
records=json.load(sys.stdin);out=[]
for v in records:
 for kind in ['output','time']:
  q=pathlib.Path(v[kind+'_path']);b=q.read_bytes();h=hashlib.sha256(b).hexdigest();assert h==v[kind+'_sha256']
  out.append(dict(module=v['module'],kind=kind,path=str(q),sha256=h,text=b.decode()))
print(json.dumps(out))
'''
for retry in range(11):
 p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(records),text=True,capture_output=True)
 if p.returncode!=255:break
 (E/f'collect-retry-{time.time_ns()}.json').write_text(json.dumps(dict(retry=retry,exit=255,stderr=p.stderr))+'\n')
 if retry==10:raise RuntimeError('transport retry limit')
 time.sleep(60)
assert p.returncode==0,p.stderr
logs=json.loads(p.stdout);(E/'original-module-logs.json').write_text(json.dumps(logs,indent=2)+'\n')
failures=[]
for v in records:
 if v['accepted']:continue
 pin=v['source'];rev=pin.get('revision',v['source_revision']);b=subprocess.check_output(['git','show',rev+':'+pin['path']]);h=hashlib.sha256(b).hexdigest();assert h==v['source_sha256']
 failures.append(dict(module=v['module'],revision=rev,path=pin['path'],git_blob=pin['git_blob'],sha256=h,retained=True,failure_class='proof/elaboration',source_changed_before_resubmit=True))
(E/'retained-failed-sources.json').write_text(json.dumps(failures,indent=2)+'\n')
print('Recovered',len(logs),'original logs; retained',len(failures),'rejected source blobs')
