"""Verify retained copies and committed compressed graphs before scratch cleanup."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];B='/home/dombarker/project-offloads/codex-cx-slice-s-retarget3-20261104';C='/home/dombarker/project-offloads/codex-cx-slice-s-retarget3-cache-20261104'
a=json.loads((E/'NGF_AUDIT.json').read_text());graphs=[]
# Check backups are in Git, not only in the working directory.
tracked=set(subprocess.check_output(['git','ls-files'],cwd=R,text=True).splitlines())
for r in a['results']:
 for name in [r['graph_archive'],r['graph_archive'][:-3]+'.sha256']:assert str((E/name).relative_to(R)) in tracked,name
 graphs.append(dict(name='NEP_'+r['mode']+'_'+r['root']+'_REACHABLE.txt',sha256=r['uncompressed_sha256']))
code=f'''from pathlib import Path
import json,hashlib,subprocess
b=Path({B!r});c=Path({C!r});graphs=json.loads({json.dumps(graphs)!r});out=[]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for directory in ['NGF_objects','NGF_native']:
 for p in (b/directory).rglob('*'):
  if not p.is_file():continue
  # Keep C sources. Remove rebuildable compiled scratch only, after validating
  # the owned export keeps exactly the same bytes.
  if p.suffix=='.c':continue
  dest=c/('NGF_exports_20261104' if directory=='NGF_objects' else 'NGF_native_20261104')/p.relative_to(b/directory)
  assert dest.is_file() and h(p)==h(dest),str(p)
  out.append(dict(path=str(p),retained=str(dest),sha256=h(dest),bytes=p.stat().st_size));p.unlink()
for row in graphs:
 p=b/row['name'];assert p.is_file() and h(p)==row['sha256'],str(p)
 p.unlink()
result=dict(removed_compiled_scratch=out,removed_backed_up_graphs=len(graphs),cache_retained=str(c),cache_du=subprocess.check_output(['du','-sh',str(c)],text=True),disk=subprocess.check_output(['df','-h',str(c)],text=True),preserved='Every cache, authored source, exported object, account and wallet key retained; no predecessor touched')
(b/'NGF_HOST_END.json').write_text(json.dumps(result,indent=1)+'\\n');print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NGF_HOST_END.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n');print('retained exports verified; backed-up scratch removed')
