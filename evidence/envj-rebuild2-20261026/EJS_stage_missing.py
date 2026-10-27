"""Restore uniquely source-attested missing dependencies under the EJS prefix."""
from pathlib import Path
import json,hashlib,base64,os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');root=U/'EJS_missing';out=[]
for r in json.loads((T/'EJS_missing-payload.json').read_text())['rows']:
 b=base64.b64decode(r.pop('source_base64'));assert hashlib.sha256(b).hexdigest()==r['source_sha256'];dest=root/'sources'/(r['module']+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(b)
 r.update(workspace='EJS_missing',host_path=str(dest));out.append(r)
(root/'objects').mkdir(exist_ok=True)
for m in ['Aeneas','AeneasMeta']:
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  src=J/'objects'/(m+ext);dest=root/'objects'/(m+ext)
  if src.is_file() and not dest.exists():os.link(src.resolve(),dest)
(T/'EJS_missing-sources.json').write_text(json.dumps(out,indent=2)+'\n');print('staged',len(out),'exact source hashes')
