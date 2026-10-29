"""Recover original per-module compiler output read-only, without resubmission."""
from pathlib import Path
import json,subprocess,shlex,hashlib
E=Path('evidence/pv-l1e-20261029');rows=[v for f in E.glob('modules-*.json') for v in json.loads(f.read_text())]
requests={v[k+'_path']:v[k+'_sha256'] for v in rows for k in ['output','time']}
code='''import sys,json,pathlib,hashlib
x=json.load(sys.stdin);out={}
for p,h in x.items():
 q=pathlib.Path(p);assert str(q).startswith('/home/dombarker/project-offloads/codex-pv-l1e-20261029/evidence/')
 b=q.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;out[q.name]=b.decode()
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(requests),text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'raw').mkdir(exist_ok=True)
for name,s in json.loads(r.stdout).items():(E/'raw'/name).write_text(s)
print('Recovered',len(requests),'original output/time files')
