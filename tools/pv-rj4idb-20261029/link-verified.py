"""Link only the already h6-verified cohort into this job's new prefix."""
from pathlib import Path
import json,subprocess,shlex
E=Path('evidence/pv-rj4idb-20261029');x=json.load(open(E/'h6-result.json'))['result']
code=r'''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rj4idb-20261029/objects');checks=[]
for v in x['checks']:
 q=pathlib.Path(v['object_path']);assert hashlib.sha256(q.read_bytes()).hexdigest()==v['object_sha256'];d=p/(v['module'].replace('.','/')+'.olean');d.parent.mkdir(parents=True,exist_ok=True)
 if d.exists():assert d.resolve()==q.resolve()
 else:d.symlink_to(q)
 checks.append(dict(module=v['module'],path=str(d),target=str(q),sha256=v['object_sha256']))
 for suffix in ['.olean.server','.olean.private','.ir']:
  companion=q.with_suffix(suffix)
  if companion.exists():
   dest=d.with_suffix(suffix);digest=hashlib.sha256(companion.read_bytes()).hexdigest()
   if dest.exists():assert dest.resolve()==companion.resolve()
   else:dest.symlink_to(companion)
   assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
   checks.append(dict(module=v['module'],path=str(dest),target=str(companion),sha256=digest))
print(json.dumps(dict(checks=checks,all_match=True,reason='Private overlay resolves modules added to runjoin after the older rjdec prefix was built. Source and object unchanged; environment changed after 64604 missing import and 64606 missing companion; all companion links preserve the original cohort bytes.')))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'private-overlay.json').write_text(r.stdout);print(len(x['checks']),'verified objects linked')
