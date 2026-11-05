"""Verify retained exports, then remove only owned rebuildable scratch."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path.cwd().resolve();assert B.name=='codex-cx-pool-b4-20261107'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while part:=f.read(1024*1024):h.update(part)
 return h.hexdigest()
x=json.loads((B/'NIE_EXPORT.json').read_text())
for r in x['exports']:
 p=Path(r['path']);assert p.is_file() and sha(p)==r['sha256'],r['path']
removed=[]
for name in ['NIE_target','NIE_extract_target','NIE_objects','NIE_native','NIE_tmp']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():
  count=sum(z.stat().st_size for z in p.rglob('*') if z.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=count))
usage=shutil.disk_usage(B)
result=dict(removed=removed,bytes_removed=sum(r['bytes'] for r in removed),exports_verified=len(x['exports']),cache_retained=x['cache_retained'],cache_deleted=False,source_inputs_retained=str(B/'NIE_src'),disk=dict(total=usage.total,used=usage.used,free=usage.free),wallet_or_key_operation=False)
(B/'NIE_HOST_END.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(bytes_removed=result['bytes_removed'],exports_verified=result['exports_verified'],cache_deleted=False,disk_free_bytes=usage.free)))
