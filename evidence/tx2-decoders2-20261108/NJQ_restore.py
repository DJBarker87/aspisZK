"""Restore missing incremental historical inputs with exact pinned bytes, never relax pins."""
from NJQ_transport import *
import hashlib,lzma,base64
sha=lambda raw:hashlib.sha256(raw).hexdigest()
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r});p=json.loads((b/'NIJ_SOURCE_PINS.json').read_text())
print(json.dumps({{n:h for n,h in p.items() if not (b/'NIJ_src'/n).exists()}}))
''');assert r.returncode==0,r.stderr
missing=json.loads(r.stdout);payload={};archive={}
# Complete historical payload is content-addressed on this branch's imported receipt inputs.
idx=json.loads((E/'NJQ_INPUTS.json').read_text())
for obj in idx['objects'].values():
 raw=lzma.decompress((E/obj['path']).read_bytes());archive[sha(raw)]=raw
for n,h in missing.items():
 raw=archive.get(h)
 if raw is None:
  p=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True)
  assert p.returncode==0 and sha(p.stdout)==h,('missing nonfrozen historical input',n,h)
  raw=p.stdout
 assert sha(raw)==h
 payload[n]=base64.b64encode(raw).decode()
 q=E/'NJQ_INPUTS'/(h+'.xz')
 if not q.exists():q.write_bytes(lzma.compress(raw))
 idx['objects'][h]=dict(path=str(q.relative_to(E)),bytes=len(raw),archive_sha256=sha(q.read_bytes()))
(E/'NJQ_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r})/'NIJ_src';files=json.loads({json.dumps(payload)!r})
for n,v in files.items():
 p=b/n;assert not p.exists();p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
print(len(files))
''');assert r.returncode==0,r.stderr
(E/'NJQ_RESTORED.json').write_text(json.dumps(missing,indent=1)+'\n');print('Restored exact pinned incremental inputs:',len(missing))
# cfg(kani)-only tree_reference path is outside the Cargo member closure.
files=subprocess.check_output(['git','ls-tree','-r','--name-only','4bb3b3f5','tools/r1-builder-reference'],text=True).splitlines()
payload={};pins={}
for n in files:
 raw=subprocess.check_output(['git','show','4bb3b3f5:'+n]);h=sha(raw);payload[n]=base64.b64encode(raw).decode();pins[n]=h
 q=E/'NJQ_INPUTS'/(h+'.xz')
 if not q.exists():q.write_bytes(lzma.compress(raw))
 idx['objects'][h]=dict(path=str(q.relative_to(E)),bytes=len(raw),archive_sha256=sha(q.read_bytes()))
(E/'NJQ_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
r=ssh('python3',f'''from pathlib import Path
import json,base64,hashlib
b=Path({B!r})/'NIJ_src';files=json.loads({json.dumps(payload)!r})
for n,v in files.items():
 p=b/n;raw=base64.b64decode(v)
 if p.exists():assert p.read_bytes()==raw
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
print(len(files))
''');assert r.returncode==0,r.stderr
(E/'NJQ_TREE_REFERENCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');print('Restored frozen cfg(kani) tree_reference:',len(files))
