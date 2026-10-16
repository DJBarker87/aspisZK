import json,hashlib
from pathlib import Path
ws=Path('/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015')
q=json.loads(Path('/tmp/focused-recheck-queue.json').read_text())
issues=[]; imports=[]
for it in q['items']:
 n=it['order']
 if n<=49: label=f'queue144-{n:03d}'
 elif n==50: label='queue144-050-repair7'
 elif 51<=n<=64: label=f'queue144-{n:03d}'
 elif 65<=n<=73: label=f'queue144-repair7-{n:03d}'
 elif n==74: label='queue144-repair7-v6fix1-074'
 else: label=f'queue144-repair8-{n:03d}'
 d=ws/'attempts'/f"{label}-{it['module'].replace('.', '_')}"
 rec=json.loads((d/'receipt.json').read_text())
 for dep in rec['direct_imports']:
  p=Path(dep['object_path'])
  current=hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
  ok=current==dep['object_sha256']
  imports.append({'target_order':n,'target':it['module'],'module':dep['module'],'object_path':dep['object_path'],'pinned_sha256':dep['object_sha256'],'current_sha256':current,'match':ok})
  if not ok: issues.append(imports[-1])
  sp=dep.get('source_path')
  if sp and dep.get('source_sha256'):
   s=Path(sp); sh=hashlib.sha256(s.read_bytes()).hexdigest() if s.exists() else None
   if sh!=dep['source_sha256']:
    issues.append({'target_order':n,'target':it['module'],'module':dep['module'],'source_path':sp,'pinned_source_sha256':dep['source_sha256'],'current_source_sha256':sh,'issue':'source mismatch'})
print(json.dumps({'direct_import_edges':len(imports),'object_import_edges_matching':sum(1 for x in imports if x['match']),'issues':issues},indent=2))
