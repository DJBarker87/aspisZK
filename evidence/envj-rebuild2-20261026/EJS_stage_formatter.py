"""Stage exact historical formatter repair, retaining two consumer contexts."""
from pathlib import Path
import json,hashlib,base64,os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');out=[]
for r in json.loads((T/'EJS_formatter-payload.json').read_text())['rows']:
 root=U/r['workspace'];dest=root/'sources'/(r['module']+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists()
 if r.get('source_base64'):
  b=base64.b64decode(r.pop('source_base64'));assert hashlib.sha256(b).hexdigest()==r['source_sha256'];dest.write_bytes(b)
 else:
  src=Path(r['host_path']);assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'];os.link(src,dest)
 assert hashlib.sha256(dest.read_bytes()).hexdigest()==r['source_sha256'];r['host_path']=str(dest);out.append(r);(root/'objects').mkdir(exist_ok=True)
(T/'EJS_formatter-sources.json').write_text(json.dumps(out,indent=2)+'\n');print('staged',len(out))
