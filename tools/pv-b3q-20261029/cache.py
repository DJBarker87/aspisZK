"""Verify transitive inherited objects against successful receipts and HEAD sources."""
from pathlib import Path
import json,hashlib,re,shutil,sys
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029');B=H.parent/'codex-pv-b3p6-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
authority=json.loads((H/'source-authority.json').read_text()); env=json.loads((B/'env-J-private.json').read_text())
(H/'env-J-private.json').write_text(json.dumps(env,indent=2)+'\n')
search=[B/'lean-objects']+[Path(p)for p in env['LEAN_PATH'].split(':')]
receipts={};expected={}
for p in sorted(B.glob('lean-*/receipt/receipt.json')):
 r=json.loads(p.read_text())
 if r.get('exit_status')==0 and r.get('module'):
  receipts.setdefault(r['module'],[]).append(r)
  for d,v in r.get('dependency_objects',{}).items():expected.setdefault(d,set()).add(v['sha256'])
for m in json.loads((B/'cache-verification-resume14.json').read_text())['objects']:
 expected.setdefault(m['module'],set()).add(m['object_sha256'])
external={r['module'].replace('/','.'):r for r in json.loads((B/'external-object-manifest.json').read_text())}
seen={};bad=[];O=H/'lean-objects';O.mkdir(exist_ok=True)
def visit(m):
 if m in seen:return
 obj=next((p/(m.replace('.','/')+'.olean')for p in search if (p/(m.replace('.','/')+'.olean')).exists()),None)
 if obj is None:raise RuntimeError(('missing',m))
 actual=sha(obj)
 if m in external:
  assert actual==external[m]['object_sha256'],('external',m,actual);seen[m]=dict(kind='external',object=str(obj),sha256=actual);return
 assert m in authority,('source authority missing',m)
 src=authority[m];rs=[r for r in receipts.get(m,[])if r['source_sha256']==src['sha256']]
 assert rs,('no successful matching receipt',m,src)
 assert actual in expected.get(m,set()),('unrecorded object hash',m,actual)
 r=rs[-1];seen[m]=dict(kind='project',object=str(obj),object_sha256=actual,authority=src,receipt_source_sha256=r['source_sha256'])
 for dep,v in r['dependency_objects'].items():
  q=next((p/(dep.replace('.','/')+'.olean')for p in search if(p/(dep.replace('.','/')+'.olean')).exists()),None)
  assert q and sha(q)==v['sha256'],('cohort dependency differs',m,dep,v,str(q))
  visit(dep)
 # Link immutable validated companions into this job's own overlay.
 target=O/(m.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
 for p in obj.parent.glob(obj.stem+'.*'):
  dest=target.parent/p.name
  if not dest.exists():dest.symlink_to(p)
try:
 for m in sys.argv[1:]:visit(m)
except Exception as e:bad.append(repr(e))
x=dict(roots=sys.argv[1:],objects=seen,mismatches=bad,toolchain=env['LEAN_GITHASH'],LEAN_PATH_prefix=env['LEAN_PATH'],read_only_reuse=True)
(H/'cache-verification.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(checked=len(seen),mismatches=bad)));assert not bad,bad
