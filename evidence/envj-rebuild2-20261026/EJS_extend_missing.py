from pathlib import Path
import json,hashlib,base64,os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');root=U/'EJS_missing';out=json.loads((T/'EJS_missing-sources.json').read_text());known={r['module'] for r in out}
payload=os.environ.get('EJS_EXTENSION_PAYLOAD','EJS_missing-extension-payload.json');assert payload.startswith('EJS_') and '/' not in payload
for r in json.loads((T/payload).read_text())['rows']:
 assert r['module'] not in known;r=r.copy();b=base64.b64decode(r.pop('source_base64'));assert hashlib.sha256(b).hexdigest()==r['source_sha256'];dest=root/'sources'/(r['module']+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(b);r.update(workspace='EJS_missing',host_path=str(dest));out.append(r);known.add(r['module'])
(T/'EJS_missing-sources.json').write_text(json.dumps(out,indent=2)+'\n');print('missing profile entries',len(out))
