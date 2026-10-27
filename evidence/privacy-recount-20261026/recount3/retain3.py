"""Retain audit-referenced text; other source text remains recoverable from pinned Git."""
from pathlib import Path
import json,re
P=Path(__file__).resolve().parent;man=json.loads((P/'manifest.json').read_text());by={(m['ref'],m['path']):m for m in man};keep=set()
rows=json.loads((P/'rows3.json').read_text())
for r in rows:
 for e in r['recount3_evidence']:
  p=P/e
  if p.is_file() and e.startswith('snapshots/'):keep.add(e)
for c in json.loads((P/'checks.json').read_text()):
 for x in c['imports']:
  k=(x['ref'],'docs/research/v8-r0-zk-20261009/lean/R1Z/'+x['module']+'.lean')
  if k in by:keep.add(by[k]['snapshot'])
# One exact original defining source per row, all candidate theorem sources and consumer roots.
for a in json.loads((P/'definition-audit3.json').read_text()):
 if a['sources']:
  x=a['sources'][0];m=by[x['ref'],x['path']]
  if x['path'].endswith('.lean'):keep.add(m['snapshot'])
for c in json.loads((P/'import-closures.json').read_text()):
 path='docs/research/v8-r0-zk-20261009/lean/'+c['root'].replace('.','/')+'.lean'
 if (c['ref'],path) in by:keep.add(by[c['ref'],path]['snapshot'])
# Explicit later evidence is kept beside the requested D235 horizon.
for k,path in [('srcid','evidence/pv-srcid3-20261026/REPORT.md'),('srcid','evidence/pv-srcid3-20261026/MERGE-GATE.md')]:
 import subprocess,hashlib
 key=k,path
 if key not in by:
  pin=json.loads((P/'pins.json').read_text())[k];raw=subprocess.check_output(['git','show',pin+':'+path]);p=P/'snapshots'/k/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw);m=dict(ref=k,revision=pin,path=path,sha256=hashlib.sha256(raw).hexdigest(),snapshot=str(p.relative_to(P)));man.append(m);by[key]=m
 keep.add(by[key]['snapshot'])
removed=0
for m in man:
 p=P/m['snapshot'];m['retained_snapshot']=m['snapshot'] in keep
 if not m['retained_snapshot'] and p.exists():
  assert p.is_relative_to(P/'snapshots') and p.name.endswith(('.lean.txt','.md','.json','.rs'))
  p.unlink();removed+=1
(P/'manifest.json').write_text(json.dumps(man,indent=2)+'\n')
(P/'retention.json').write_text(json.dumps(dict(retained=len(keep),omitted_text_copies=removed,recovery='git show <pins.json ref>:<manifest path>; sha256 must match manifest; no keys or original evidence deleted'),indent=2)+'\n')
print('Retained',len(keep),'audit text snapshots; omitted',removed,'redundant generated copies')
