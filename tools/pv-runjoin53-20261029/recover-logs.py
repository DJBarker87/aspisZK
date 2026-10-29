"""Recover original module outputs and metrics read-only; never resubmit."""
from pathlib import Path
import subprocess,json,hashlib,shlex,lzma
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin53-20261029'
rows=[dict(v,attempt=int(p.stem.split('-')[1])) for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
request=[dict(attempt=v['attempt'],output=v['output_path'],time=v['time_path']) for v in rows]
code='''import json,sys,pathlib
x=json.load(sys.stdin);print(json.dumps([dict(attempt=v['attempt'],output=pathlib.Path(v['output']).read_text(),time=pathlib.Path(v['time']).read_text()) for v in x]))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(request),capture_output=True,text=True);assert r.returncode==0,r.stderr
logs=json.loads(r.stdout);index={v['attempt']:v for v in rows}
for v in logs:
 original=index[v['attempt']]
 assert hashlib.sha256(v['output'].encode()).hexdigest()==original['output_sha256']
 assert hashlib.sha256(v['time'].encode()).hexdigest()==original['time_sha256']
b=json.dumps(logs,indent=2).encode();(E/'original-module-logs.json.xz').write_bytes(lzma.compress(b));(E/'original-module-logs.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'\n')
failed=[]
for v in rows:
 if v['accepted']:continue
 pin=v['source'];b=subprocess.check_output(['git','show',pin['revision']+':'+pin['path']],cwd=R)
 assert hashlib.sha256(b).hexdigest()==v['source_sha256']
 failed.append(dict(attempt=v['attempt'],module=v['module'],revision=pin['revision'],path=pin['path'],git_blob=pin['git_blob'],sha256=v['source_sha256'],hash_verified=True))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
print('Hash verified original logs',len(logs),'and failed source blobs',len(failed))
