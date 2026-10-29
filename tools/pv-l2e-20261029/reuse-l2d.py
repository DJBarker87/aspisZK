"""h6 read-only reuse of a Mathlib-only L2D helper; no recompilation."""
import json,hashlib,subprocess,shlex,sys
from pathlib import Path
E=Path('evidence/pv-l2e-20261029');m=sys.argv[1]
manifest=json.load(open('evidence/pv-l2d-20261028/final-focused-manifest.json'))['replay']
v=next(v for v in manifest if v['module']==m)
r=next(v for v in json.load(open('evidence/pv-l2d-20261028/final-private-object-manifest.json')) if v['module']==m)
b=subprocess.check_output(['git','show','HEAD:'+v['source_path']]);assert hashlib.sha256(b).hexdigest()==v['source_sha256']==r['source_sha256']
import re
imports=re.findall(r'^import (\S+)',b.decode(),re.M)
external=json.load(open('evidence/pv-fib-20261029/prepare-PV_FIB_Restricted.json'))['result']['external_checks']
auth={v['module']:v for v in external}
assert all(i in auth for i in imports),('only external-import helpers supported',imports)
code=r'''
import json,sys,pathlib,hashlib
x=json.load(sys.stdin);H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2e-20261029');P=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028/embedding')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.load(open(H/'J.json'));b=json.load(open(P/'J.json'));assert a['LEAN_GITHASH']==b['LEAN_GITHASH'];ar=[pathlib.Path(p) for p in a['LEAN_PATH'].split(':')];br=[pathlib.Path(p) for p in b['LEAN_PATH'].split(':')]
def resolve(roots,m):return next(p/(m.replace('.','/')+'.olean') for p in roots if (p/(m.replace('.','/')+'.olean')).exists())
checks=[]
# All external objects (not merely direct Mathlib import roots).
for v in x['external']:
 q=resolve(ar,v['module']);r=resolve(br,v['module']);assert sha(q)==sha(r)==v['sha256'],v['module']
 checks.append(dict(module=v['module'],loaded=str(q),previous=str(r),sha256=v['sha256']))
q=pathlib.Path(x['object']['path']);assert sha(q)==x['object']['sha256']
# Copy/link companions that Lean 4.32 requires, while retaining read-only source.
out=H/'objects'/(x['module']+'.olean')
for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
 src=q.with_suffix(suffix);dst=out.with_suffix(suffix)
 if src.exists():
  if dst.exists():assert sha(dst)==sha(src)
  else:dst.symlink_to(src)
print(json.dumps(dict(module=x['module'],source_sha256=x['source_sha256'],object=x['object'],toolchain=a['LEAN_GITHASH'],current_prefix=a['LEAN_PATH'],previous_prefix=b['LEAN_PATH'],external_checks=checks,imports=x['imports'],read_only=True)))
'''
payload=dict(module=m,source_sha256=v['source_sha256'],object=r['objects'][0],external=external,imports=imports)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
(E/('reuse-'+m+'.json')).write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2))
assert r.returncode==0,r.stderr+r.stdout
print('PASS',m,'source/object and full external-cohort verification')
