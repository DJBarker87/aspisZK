"""Remove only rebuildable scratch of this job, after retained export checks."""
from pathlib import Path
import json,hashlib,shutil,time
B=Path('/home/dombarker/project-offloads/codex-cx-verify-observed2-20261106');report=json.loads((B/'NHG_EXPORT.json').read_text());C=Path(report['export_path']);assert C.name=='NHG_exports_20261106'
for item in report['exported_files'].values():
 p=Path(item['path']);assert p.is_relative_to(C)and p.stat().st_size==item['bytes']and hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']
removed=[]
for name in ['NHG_target','NHG_objects','NHG_native','NHG_extract_target','NHG_extraction_target']:
 p=B/name
 if p.exists():
  assert p.parent==B and p.is_dir()and not p.is_symlink();size=sum(f.stat().st_size for f in p.rglob('*')if f.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
temps=[];tmp=B/'NHG_tmp'
if tmp.is_dir():
 for p in tmp.rglob('*'):
  if p.is_file()and(p.name.startswith('external-sat')or p.name.startswith('smt2_dec_problem')):
   temps.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
x=dict(kind='packaging_io_cleanup',formal_tool_invocations=0,retained_export=str(C),retained_export_verified=True,cache_deleted=False,removed=removed,solver_temps=temps,disk_free_bytes=shutil.disk_usage(B).free)
(B/'NHG_CLEANUP.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
