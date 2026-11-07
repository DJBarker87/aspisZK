"""Hash retained own objects in place; never delete or modify a cache object."""
from pathlib import Path
import json,hashlib
B=Path.cwd();selected=json.loads((B/'NNG_S094_AUDIT_ROOTS.json').read_text())['selected_receipts']
rows=[]
for mod in sorted(selected):
 found=False
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  f=B/'NNG_objects'/(mod.replace('.','/')+suffix)
  if not f.exists():continue
  found=True;h=hashlib.sha256()
  with f.open('rb') as stream:
   for chunk in iter(lambda:stream.read(1024*1024),b''):h.update(chunk)
  rows.append(dict(module=mod,path=str(f),sha256=h.hexdigest(),bytes=f.stat().st_size))
 assert found,mod
(B/'NNG_RETAINED_OBJECTS.json').write_text(json.dumps(dict(status='PINNED IN PLACE; NO DELETIONS',workspace=str(B),modules=len(selected),objects=rows,pinned_dependencies='Exact Aeneas/other imports are in every scope receipt deps_fingerprint; rev3 RSL resolves NNG_RSL3 first',candidates={'136':'AspisR1.NNG_Candidate136.candidate','137':'AspisR1.NNG_Candidate137.candidate','087':'AspisR1.NNG_Candidate087.candidate'},finding='AspisR1.NNG_Nonempty094.no_candidate'),indent=1))
print(json.dumps(dict(modules=len(selected),artifacts=len(rows),bytes=sum(r['bytes']for r in rows),deleted=0)))
