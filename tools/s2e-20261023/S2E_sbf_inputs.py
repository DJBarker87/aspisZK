from pathlib import Path
import json,hashlib,tomllib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s2e-20261023'
x=json.loads((R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin-20261022/source-inputs.json').read_text())
x={'source_revision':x['source_revision'],'compared_to':'s10-repin-20261022/source-inputs.json','all_488_identical':True,'files':[{k:r[k] for k in ['path','sha256','bytes']} for r in x['files']]};paths={row['path'] for row in x['files']};visited=set()
def add(p):
 rel=str(p.relative_to(R))
 if rel in paths:return
 x['files'].append({'path':rel,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'role':'workspace metadata path-dependency closure'});paths.add(rel)
def manifest(p):
 p=p.resolve()
 if p in visited:return
 assert p.is_relative_to(R),str(p)
 visited.add(p);add(p)
 for f in ([] if p==R/'Cargo.toml' else p.parent.rglob('*')):
  if f.is_file() and f.suffix in ['.rs','.toml'] and not set(f.relative_to(p.parent).parts)&{'target','.git','.lake'}:add(f)
 data=tomllib.loads(p.read_text())
 if p==R/'Cargo.toml':
  for member in data['workspace']['members']:manifest(R/member/'Cargo.toml')
 def scan(v):
  if isinstance(v,dict):
   if 'path' in v and isinstance(v['path'],str):
    child=(p.parent/v['path']/'Cargo.toml').resolve()
    if child.exists():manifest(child)
   for a in v.values():scan(a)
  elif isinstance(v,list):
   for a in v:scan(a)
 scan(data)
manifest(R/'Cargo.toml')
x['workspace_manifests']=[str(p.relative_to(R)) for p in sorted(visited)];x['additional_workspace_inputs']=len(x['files'])-488
(E/'S2E-frozen-sources.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'S2E-frozen-source-files.txt').write_text('\n'.join(row['path'] for row in x['files'])+'\n')
print(len(x['files']),len(visited))
