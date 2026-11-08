"""Pin lane A's checked repair cohort read-only; write only SPEC host files."""
from pathlib import Path
import json,hashlib,lzma
P=Path('/home/dombarker/project-offloads/codex-pv-lib-spec-20261107')
A=Path('/home/dombarker/project-offloads/codex-pv-lib-20261107/lane-A')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((A/'J-c18-s16.json').read_text());mods={}
for root in env['LEAN_PATH'].split(':')+[env['LEAN_SYSROOT']+'/lib/lean']:
 d=Path(root)
 for p in d.rglob('*.olean'):
  name='.'.join(p.relative_to(d).with_suffix('').parts)
  if name not in mods:mods[name]={'path':str(p),'sha256':sha(p)}
receipts=[]
for attempt in [55981,55983,55985,55986,55987,55988]:
 r=json.loads((A/'evidence'/f'receipt-{attempt}.json').read_text())
 assert int(r['exit'])==0 and r.get('accepted',True)
 m=r['target'];assert sha(A/'sources'/(m+'.lean'))==r['source_sha256']
 assert mods[m]['sha256']==r['object_sha256']
 receipts.append(r)
O=P/'objects-active19';O.mkdir(exist_ok=True)
env['LEAN_PATH']=str(O)+':'+env['LEAN_PATH']
(P/'J-active19.json').write_text(json.dumps(env))
(P/'ACTIVE19_OBJECT_AUTHORITY.json.xz').write_bytes(lzma.compress(json.dumps({'modules':mods}).encode()))
(P/'evidence'/'SESSION19_REPAIR_COHORT.json').write_text(json.dumps({'environment':env,'receipts':receipts,'modules':len(mods),'read_only':True},indent=2)+'\n')
print('pinned',len(mods),'objects; verified',len(receipts),'repair receipts')
