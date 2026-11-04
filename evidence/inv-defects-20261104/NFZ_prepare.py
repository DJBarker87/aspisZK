"""Recover byte-identical frozen Cargo workspace source; no live worktree reads."""
import subprocess,json,pathlib,tomllib,posixpath,lzma,hashlib
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def git(p):return subprocess.check_output(['git','show',REV+':'+p],cwd=R)
roots=set(tomllib.loads(git('Cargo.toml').decode())['workspace']['members']);queue=list(roots)
while queue:
 p=queue.pop();m=tomllib.loads(git(p+'/Cargo.toml').decode())
 for section in ['dependencies','dev-dependencies','build-dependencies']:
  for d in m.get(section,{}).values():
   if isinstance(d,dict) and 'path' in d:
    q=posixpath.normpath(p+'/'+d['path'])
    if q not in roots:roots.add(q);queue.append(q)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'--',*sorted(roots)],cwd=R,text=True).splitlines()
paths=[p for p in paths if p.endswith(('.rs','.toml'))]+['Cargo.toml','Cargo.lock']
files={p:git(p).decode() for p in paths};raw=json.dumps(files,sort_keys=True).encode()
(E/'NFZ_FROZEN_SOURCE.json.xz').write_bytes(lzma.compress(raw));(E/'NFZ_FROZEN_SOURCE.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'NFZ_SOURCE_PINS.json').write_text(json.dumps(dict(revision=REV,roots=sorted(roots),files={p:hashlib.sha256(t.encode()).hexdigest() for p,t in files.items()}),indent=1)+'\n')
print(len(files),len(raw))
