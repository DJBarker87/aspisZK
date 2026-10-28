from NCG_host import *
r=py(f'''from pathlib import Path
import os,json,shutil
b=Path({B!r});active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:c=(p/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
 except (FileNotFoundError,ProcessLookupError,PermissionError):continue
 if str(b) in c and any(x in c for x in ['cargo-kani kani','cbmc --','S2W_run_host.py NCG_','S2W_lean_host.py NCG_','lake env lean']):
  if 'python3 -c' not in c and 'ssh ' not in c:active.append(dict(pid=p.name,command=c))
assert not active,active
removed=[]
for name in ['NCG_target','NCG_tmp']:
 p=b/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028');assert cache.is_dir()
print(json.dumps(dict(active_processes=active,removed=removed,cache_retained=str(cache),corpus_retained=str((b/'NCG_src').resolve())),indent=2))
''');(E/'NCG_CLEANUP.json').write_text(r.stdout);assert r.returncode==0,r.stderr
