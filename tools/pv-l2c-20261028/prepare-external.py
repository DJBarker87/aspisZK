"""Complete the private path with manifest-identical external objects, never rebuild them."""
from pathlib import Path
import json,subprocess,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
rows=json.loads((R/'evidence/pv-runjoin20-20261027/external-object-manifest.json').read_text())
code='''import sys,json,pathlib,hashlib
rows=json.load(sys.stdin);H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');e=json.load(open(H/'J.json'));roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')];out=[]
for r in rows:
 rel=r['module'].replace('.','/')+'.olean';p=pathlib.Path(r['path']);dest0=H/'objects'/rel;added=not dest0.is_file()
 # Lean can select dangling symlinks earlier in a prefix. A complete private
 # manifest view avoids that ambiguity without changing any shared path.
 assert p.is_file(),(r['module'],str(p))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
 companions=[]
 if True:
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
   q=pathlib.Path(str(p)[:-6]+suffix)
   if not q.is_file():continue
   dest=H/'objects'/(rel[:-6]+suffix);dest.parent.mkdir(parents=True,exist_ok=True)
   if dest.exists() or dest.is_symlink():
    assert dest.is_file() and hashlib.sha256(dest.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest(),str(dest)
   else:dest.symlink_to(q.resolve())
   companions.append(dict(path=str(dest),retained=str(q.resolve()),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
 out.append(dict(module=r['module'],added=added,object_sha256=r['object_sha256'],path=str(p),companions=companions))
# A second selection pass has NO fallback. Every manifest module is now selectable.
for r in rows:
 rel=r['module'].replace('.','/')+'.olean';p=next(d/rel for d in roots if (d/rel).is_file());assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
print(json.dumps(out))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(rows),text=True,capture_output=True)
assert p.returncode==0,p.stderr
out=json.loads(p.stdout);(E/'external-private-path.json').write_text(json.dumps(out,indent=2)+'\n')
print('All',len(out),'external objects selectable and verified; linked',sum(x['added'] for x in out),'previously absent objects')
