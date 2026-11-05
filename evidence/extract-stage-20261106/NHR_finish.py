"""Final stronger preflight, retain owned exports, remove only owned build outputs."""
from pathlib import Path
import hashlib,json,shutil,subprocess
E=Path(__file__).resolve().parent
subprocess.run(['python3','NHR_stage.py','--check','--out','NHR_final_preflight'],cwd=E,check=True)
exports=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHR_exports_20261106')
objects=E/'NHR_objects';pins=[]
for p in sorted(objects.rglob('*')):
 if not p.is_file():continue
 q=exports/p.relative_to(objects);q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(p.read_bytes()).hexdigest()
 if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,q)
 pins.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=h))
(E/'NHR_EXPORT.json').write_text(json.dumps(dict(exports=str(exports),files=pins),indent=2)+'\n')
versions={}
for version in ['1.94.1','nightly-2026-09-17']:
 for tool in ['cargo','rustc']:
  r=subprocess.run(['/home/dombarker/.cargo/bin/'+tool,'+'+version,'-Vv'],capture_output=True,text=True)
  assert r.returncode==0,r.stderr
  versions[tool+'+'+version]=r.stdout+r.stderr
(E/'NHR_TOOL_VERSIONS.json').write_text(json.dumps(versions,indent=2)+'\n')
removed=[]
for name in ['NHR_target','NHR_objects','.lake']:
 p=E/name
 if p.exists():
  size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
size=sum(q.stat().st_size for q in E.rglob('*') if q.is_file())
assert size<15_000_000_000
(E/'NHR_HOST_END.json').write_text(json.dumps(dict(remaining_bytes=size,removed=removed,exports_retained=str(exports),cache_never_deleted=True),indent=2)+'\n')
print(json.dumps(dict(remaining_bytes=size,removed=removed,exported_files=len(pins))))
