"""Remove only owned rebuildable outputs after hash-verified retained export."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-retarget-20261105';C='/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104'
exp=json.loads((E/'NGK_EXPORT.json').read_text())['exports'];graphs=[]
for p in E.glob('NGK_NEP_*_REACHABLE.txt.sha256'):
 assert Path(str(p).removesuffix('.sha256')+'.xz').is_file()
 graphs.append(dict(relative=p.name.removeprefix('NGK_').removesuffix('.sha256'),sha256=p.read_text().strip()))
code='''from pathlib import Path
import json,hashlib,subprocess
b=Path(B);c=Path(C);byname={Path(r['path']).name:r for r in exp};removed=[]
for directory in [b/'NGK_objects',b/'NGK_native']:
 for p in directory.iterdir():
  if not p.is_file():continue
  r=byname[p.name];q=Path(r['path']);assert q.is_relative_to(c)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']==hashlib.sha256(q.read_bytes()).hexdigest()
  removed.append(dict(path=str(p),sha256=r['sha256'],bytes=p.stat().st_size,retained=str(q)));p.unlink()
for r in graphs:
 p=b/r['relative'];assert p.parent==b
 if not p.exists():continue
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 removed.append(dict(path=str(p),sha256=r['sha256'],bytes=p.stat().st_size,retained='committed local .xz/.sha256'));p.unlink()
active=[]
for p in Path('/proc').glob('[0-9]*'):
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
  if cwd==b and any(s in cmd for s in ['/bin/lean ','/bin/lake ','S2W_run_host.py']):active.append(dict(pid=p.name,command=cmd))
 except (OSError,RuntimeError):pass
report=dict(removed=removed,removed_files=len(removed),removed_bytes=sum(r['bytes'] for r in removed),owned_cache_retained=str(c),no_cache_file_deleted=True,sources_and_receipts_retained=True,active_owned_provers=active,disk=subprocess.check_output(['df','-h',str(c)],text=True))
(b/'NGK_HOST_END.json').write_text(json.dumps(report,indent=1)+'\\n');print(json.dumps(report))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nexp='+repr(exp)+'\ngraphs='+repr(graphs)+'\n'+code,text=True,capture_output=True)
(E/'NGK_HOST_END_TRANSPORT.log').write_text(r.stderr);assert r.returncode==0,r.stderr
(E/'NGK_HOST_END.json').write_text(r.stdout);x=json.loads(r.stdout);assert x['active_owned_provers']==[];print(x['removed_files'],'owned rebuildable outputs hash-verified and removed;',x['removed_bytes'],'bytes; cache retained')
