"""Read-only lane-A object/source resolution into SPEC's own directory."""
from pathlib import Path
import json,lzma,hashlib
P=Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107')
A=Path('/home/dombarker/project-offloads/codex-pv-lib-20261107/lane-A')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((A/'J.json').read_text());mods={}
for root in env['LEAN_PATH'].split(':'):
 d=Path(root)
 for p in d.rglob('*.olean'):
  name='.'.join(p.relative_to(d).with_suffix('').parts)
  if name not in mods:mods[name]={'path':str(p),'sha256':sha(p)}
(P/'LANEA_OBJECT_AUTHORITY.json.xz').write_bytes(lzma.compress(json.dumps({'modules':mods}).encode()))
pins=json.loads((P/'SESSION7_LANEA_SOURCE_PINS.json').read_text())
for module,expected in pins.items():
 s=A/'sources'/(module+'.lean');assert sha(s)==expected,(module,sha(s),expected)
records=[]
for f in (A/'evidence').glob('receipt-*.json'):
 r=json.loads(f.read_text())
 if r.get('target') in pins and r.get('accepted',r.get('exit')==0):
  records.append(r)
(P/'evidence'/'SESSION7_LANEA_OBJECTS.json.xz').write_bytes(lzma.compress(json.dumps({'env':env,'modules':{m:v for m,v in mods.items() if m in pins},'receipts':records}).encode()))
print('read-only lane-A sources pinned; resolution modules',len(mods))
