"""Stage only exact historical provider bytes, symlinking unchanged sources."""
from pathlib import Path
import json,hashlib,base64
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022')
d=json.loads((T/'EJS_provider-payload.json').read_text());root=U/'EJS_provider';rs=[]
for r in d['rows']:
 original=Path(r['host_path']);dest=root/'sources'/(r['module']+'.lean');dest.parent.mkdir(parents=True,exist_ok=True)
 if r['module']=='R1Z/CertBuildExtracted':
  b=base64.b64decode(d['provider_source_base64']);assert hashlib.sha256(b).hexdigest()==r['source_sha256'];assert not dest.exists();dest.write_bytes(b)
 else:
  assert hashlib.sha256(original.read_bytes()).hexdigest()==r['source_sha256']
  if not dest.exists():dest.symlink_to(original)
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==r['source_sha256']
 rs.append(dict(r,workspace='EJS_provider',host_path=str(dest)))
(root/'objects').mkdir(exist_ok=True)
(T/'EJS_provider-sources.json').write_text(json.dumps(rs,indent=2)+'\n');print('staged',len(rs))
