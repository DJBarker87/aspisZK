"""Freeze the freshly elaborated R72 cone, recording all imports and artifact hashes."""
from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');x=json.loads((D/'inherited-resolution.json').read_text());pre=json.loads((D/'preflight.json').read_text());fresh=set(pre['fresh_required']);roots=list(map(Path,pre['environment']['LEAN_PATH'].split(':')))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(m):return next(r/(m.replace('.','/')+'.olean') for r in roots if(r/(m.replace('.','/')+'.olean')).exists())
rows=[]
for m in x['order']:
 r=x['modules'][m];p=obj(m);source=D/'lean-sources'/(m.replace('.','/')+'.lean');assert sha(source)==r['sha256']
 if m in fresh:assert p.is_file()and not p.is_symlink()and p.is_relative_to(D)
 rows.append(dict(module=m,source=r,object_path=str(p),object_sha256=sha(p),object_bytes=p.stat().st_size,fresh=m in fresh,imports=[dict(module=i,path=str(obj(i)),sha256=sha(obj(i)))for i in r['imports']],companions=[dict(path=str(q),sha256=sha(q))for q in [p.with_suffix('.ir'),Path(str(p)+'.server'),Path(str(p)+'.private')]if q.exists()]))
for r in pre['external']:assert sha(Path(r['path']))==r['actual']
j=dict(authority='D434: unchanged pinned sources freshly elaborated in dependency order; fresh coherent R72 closure is authority for this cone',modules=rows,external=pre['external'],env=pre['environment'],all_consumers_unedited=True,reused_affected_objects=False,source_revision=x['head'])
(D/'r72-cohort.json').write_text(json.dumps(j,indent=2));print(json.dumps(dict(modules=len(rows),fresh=sum(r['fresh']for r in rows),R72=[r for r in rows if r['module'].startswith('AspisR72')]),indent=2))
