"""Pin retained own objects and export after the focused own-root audit."""
from NNC_formal import *
roots=json.loads((E/'NNC_AUDIT_ROOTS.json').read_text())
modules=[l[7:] for l in (E/'NNC_COMBINED_IMPORT.lean').read_text().splitlines() if l.startswith('import NNC_')]
modules+=['NNC_COMBINED_IMPORT','TCK_WeakRoot0','TAS_Interfaces']
# This scope hashes only already-selected dependencies, seeds and own export;
# no all-roots replay or scan is performed.
code='''from pathlib import Path
import json,hashlib,shutil
b=Path.cwd();selected={};receipts=[]
for p in sorted(b.glob('NNC_L*/receipt.json')):
 x=json.loads(p.read_text());receipts.append(x['attempt'])
 for name,v in x['deps_fingerprint']['selected_objects'].items():
  if name in selected:assert selected[name]['sha256']==v['sha256'],name
  selected[name]=v
for name,v in selected.items():
 p=Path(name);assert p.is_file(),name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256'],name
out=b/'NNC_exports_20261111';out.mkdir(exist_ok=True);export=[]
for n in MODULES:
 p=b/'NNC_objects'/(n+'.olean');assert p.is_file(),p
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not q.is_file():continue
  dest=out/q.name
  if dest.exists():assert dest.read_bytes()==q.read_bytes()
  else:shutil.copy2(q,dest)
  export.append(dict(path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),bytes=dest.stat().st_size))
(b/'NNC_EXPORT.json').write_text(json.dumps(dict(directory=str(out),modules=MODULES,files=export,selected_dependencies_verified=len(selected)),indent=1)+'\\n')
size=sum(p.stat().st_size for p in b.rglob('*') if p.is_file())
(b/'NNC_RETENTION.json').write_text(json.dumps(dict(workspace=str(b),workspace_bytes=size,free_bytes=shutil.disk_usage(b).free,deleted_files=0,own_cache_retained=True,selected_dependencies_verified=len(selected)),indent=1)+'\\n')
print(json.dumps(dict(exported=len(export),selected_dependencies_verified=len(selected),workspace_bytes=size)))
'''.replace('MODULES',repr(modules))
r=run('NNC_L053','inspect','NNC_Retention',['python3','-c',code])
sys.exit(r['exit_status'])
