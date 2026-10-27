from pathlib import Path
import hashlib,json,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-sampler-diag-20261027')
rows=[]
for name in ['SDX_objects','SDX_target']:
 p=B/name
 for f in sorted(p.rglob('*')) if p.exists() else []:
  if f.is_file():rows.append({'path':str(f.relative_to(B)),'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(B/'SDX_cleanup.json').write_text(json.dumps({'deleted_build_outputs':rows,'bytes':sum(r['bytes'] for r in rows),'keys_and_source_material':'untouched'},indent=2)+'\n')
for name in ['SDX_objects','SDX_target']:
 p=B/name
 if p.exists():shutil.rmtree(p)
print(json.dumps({'files':len(rows),'bytes':sum(r['bytes'] for r in rows)}))
