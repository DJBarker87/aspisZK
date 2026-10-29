from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
E=json.loads((D/'env-J.json').read_text());roots=[D/'objects']+list(map(Path,E['LEAN_PATH'].split(':')))
source={r['module']:Path(r['source']) for r in json.loads((D/'preflight.json').read_text())['project']}
publication=json.loads((D/'publication-inputs.json').read_text())
for r in publication['modules']:source[r['module']]=D.parent/'aspis-joint-20261019/sources'/(r['module'].replace('.','/')+'.lean')
for p in (D/'sources/R1Z').glob('*.lean'):source['R1Z.'+p.stem]=p
pins=json.loads((D/'final-source-pins.json').read_text());pinmap={r['module']:r for r in pins}
external=json.loads((D.parent/'codex-pv-rdb1-20261028/external-object-manifest.json').read_text());ext={r['module'].replace('/','.'):r['object_sha256'] for r in external}
checked=[]
for m,h in ext.items():
 rel=m.replace('.','/')+'.olean';p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p and sha(p)==h,m
 checked.append(dict(module=m,path=str(p),sha256=h))
seen={};pending=['R1Z.PV_RDEAC_Statements']
while pending:
 m=pending.pop()
 if m in seen or m in ext:continue
 p=source[m];h=sha(p);assert m in pinmap and h==pinmap[m]['source_sha256'],(m,str(p),h)
 imports=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):imports.extend(line[7:].split())
 deps=[]
 for dep in imports:
  rel=dep.replace('.','/')+'.olean';q=next((r/rel for r in roots if (r/rel).is_file()),None)
  assert q,(m,dep)
  deps.append(dict(module=dep,path=str(q),object_sha256=sha(q)))
  if dep not in ext:pending.append(dep)
 obj=D/'objects'/(m.replace('.','/')+'.olean')
 seen[m]=dict(module=m,source=str(p),source_sha256=h,source_blob=pinmap[m]['blob'],object=str(obj),object_sha256=sha(obj) if obj.is_file() else None,imports=deps)
(D/'final-preflight.json').write_text(json.dumps(dict(source_revision=(D/'revision.txt').read_text().strip(),external=checked,projects=list(seen.values()),void_predecessor_recompiled=dict(id=61101,module='R1Z.PV_RDEA_CloneExecution',sha256=sha(D/'objects/R1Z/PV_RDEA_CloneExecution.olean')),uncompiled_root_allowed='R1Z.PV_RDEAC_Statements',ok=True),indent=2)+'\n');print('verified',len(checked),'external and',len(seen),'project source/import identities')
