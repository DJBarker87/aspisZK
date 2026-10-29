"""Recover original per-module logs and retain every failed source by Git blob."""
from pathlib import Path
import json,hashlib,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjq-20261029'
records=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
paths=[v[k] for v in records for k in ['output_path','time_path']]
code='import json,sys,pathlib;print(json.dumps({p:pathlib.Path(p).read_text() for p in json.load(sys.stdin)}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(paths),text=True,capture_output=True);assert r.returncode==0,r.stderr
logs=json.loads(r.stdout)
for v in records:
 for k in ['output','time']:
  assert hashlib.sha256(logs[v[k+'_path']].encode()).hexdigest()==v[k+'_sha256']
(E/'original-module-logs.json').write_text(json.dumps(logs,indent=2)+'\n')
failed=[]
for v in records:
 if v['accepted']:continue
 pin=v['source'];blob=pin['git_blob'];b=subprocess.check_output(['git','cat-file','blob',blob]);assert hashlib.sha256(b).hexdigest()==v['source_sha256']
 failed.append(dict(attempt=next(p.stem.split('-')[-1] for p in E.glob('modules-*.json') if v in json.loads(p.read_text())),module=v['module'],sha256=v['source_sha256'],git_blob=blob,revision=pin['revision'],path=pin['path'],retention='verified Git blob; no unchanged resubmission'))
(E/'retained-failed-sources.json').write_text(json.dumps(failed,indent=2)+'\n')
print(len(records),'launches;',sum(v['accepted'] for v in records),'accepted;',len(failed),'failed; original logs verified')
