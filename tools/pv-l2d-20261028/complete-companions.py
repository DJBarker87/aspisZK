"""Correct own external-overlay input omission; retain exact existing pinned objects."""
from pathlib import Path
import subprocess,json,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
code=r'''import json,pathlib,hashlib
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028/embedding');checks=json.load(open(p/'evidence/external-check.json'));out=[]
for v in checks:
 q=pathlib.Path(v['path']);assert hashlib.sha256(q.read_bytes()).hexdigest()==v['expected'],v['module']
 c=q.with_suffix('.ir')
 if c.is_file():
  d=p/'external'/(v['module'].replace('.','/')+'.ir');assert not d.exists();d.symlink_to(c)
  out.append(dict(module=v['module'],path=str(c),sha256=hashlib.sha256(c.read_bytes()).hexdigest()))
(p/'evidence/external-ir-companions.json').write_text(json.dumps(out,indent=2));print(json.dumps(dict(count=len(out),init_prelude=next(x for x in out if x['module']=='Init.Prelude'),objects_unchanged=True)))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'ir-correction-transport.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');assert r.returncode==0,r.stderr
subprocess.run(['scp','-q','dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-l2d-20261028/embedding/evidence/external-ir-companions.json',str(E/'external-ir-companions.json')],check=True)
print(r.stdout)
