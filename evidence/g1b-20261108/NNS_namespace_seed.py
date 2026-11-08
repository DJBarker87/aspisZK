from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();cfg=json.loads((B/'NNS_SEED_CONFIG.json').read_text());rows=[]
# Retire flattened package roots. Lean resolves a package hierarchy from its
# root module, so a root without the full directory masks the retained package.
for src in (B/'NNS_seed').glob('*.olean'):
 if (B/'NNS_seed'/src.stem).is_dir():continue
 candidates=[Path(r) for r in cfg['paths'] if (Path(r)/src.stem).is_dir() and (Path(r)/src.name).is_file()]
 if not candidates:continue
 h=hashlib.sha256(src.read_bytes()).hexdigest()
 root=next((r for r in candidates if hashlib.sha256((r/src.name).read_bytes()).hexdigest()==h),None)
 assert root is not None,src.name
 for s in [src,Path(str(src)+'.private'),Path(str(src)+'.server'),src.with_suffix('.ir')]:
  if not s.exists():continue
  d=B/'NNS_flat_namespace_roots'/s.name;d.parent.mkdir(exist_ok=True)
  assert not d.exists();shutil.move(s,d)
  rows.append(dict(retained=str(d),sha256=hashlib.sha256(d.read_bytes()).hexdigest(),active_package_root=str(root)))
(B/'NNS_NAMESPACE_REPAIR.json').write_text(json.dumps(rows,indent=1)+'\n')
print(json.dumps(rows))
