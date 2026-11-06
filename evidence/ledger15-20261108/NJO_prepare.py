from pathlib import Path
import json,re,lzma,hashlib,difflib
E=Path(__file__).resolve().parent;P=E.parent/'ledger14-20261108'
specs=[('ledger14-20261108','NJK'),('multiproof2-20261107','NJE'),('terminal-20261107','NJB'),('verify-observed6-20261107','NJG'),('multiproof-20261107','NJA')]
(E/'NJO_SPECS.json').write_text(json.dumps(specs,indent=1)+'\n')
roots=set();expected={};conflicts=[];seeds=[];extra=[];pins=[]
C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NJO_20261108'
for folder,pre in specs:
 p=E.parent/folder;x=json.loads((p/f'{pre}_AUDIT_ROOTS.json').read_text());roots.update(x.get('roots',sum(x.get('groups',[]),[])) if isinstance(x,dict) else x)
 for l in (p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];xs=x['imports']
  if m in expected and expected[m]!=xs:conflicts.append(dict(module=m,earlier=expected[m],later=xs,provider=pre))
  else:expected[m]=xs
 f=p/f'{pre}_EXPORT.json'
 if f.exists():
  x=json.loads(f.read_text());rs=x.get('files',x.get('exports',x.get('own_exports',[])))
  if isinstance(rs,dict):rs=list(rs.values())
  for row in rs:
   src=row.get('destination',row.get('path',row.get('name','')))
   if not src.startswith('/'):src=x.get('path',x.get('directory',''))+'/'+src
   if not any(src.endswith(s)for s in ['.olean','.olean.private','.olean.server','.ir']):continue
   # Preserve module-relative subdirectories.
   rel=row.get('module','').replace('.','/')+'.olean' if row.get('module')and src.endswith('.olean')else src.split('/')[-1]
   if not row.get('module')and row.get('path')and not row['path'].startswith('/'):rel=row['path']
   seeds.append(dict(tag=pre,path=src,relative=rel,sha256=row['sha256'],bytes=row['bytes']))
 q=p/f'{pre}_CONSUMER_PATHS.json'
 if q.exists():paths=json.loads(q.read_text());paths=paths.get('paths',paths.get('LEAN_PATH',[])) if isinstance(paths,dict) else paths
 elif (p/f'{pre}_EXPORT_ENV.json').exists():paths=json.loads((p/f'{pre}_EXPORT_ENV.json').read_text())['LEAN_PATH'].split(':')
 elif (p/f'{pre}_PATHS.json').exists():paths=json.loads((p/f'{pre}_PATHS.json').read_text())
 else:
  cfgs=[]
  for f in p.glob(f'{pre}_L[0-9][0-9][0-9].json'):
   a=json.loads(f.read_text())
   if 'LEAN_PATH'in a.get('env',{}):cfgs.append((f.name,a['env']['LEAN_PATH'].split(':')))
  assert cfgs,pre
  paths=sorted(cfgs)[-1][1]
 if isinstance(paths,str):paths=paths.split(':')
 extra+=paths
 for f in p.iterdir():
  if f.is_file()and any(k in f.name for k in ['HANDOFF','CLOSED.json','LEDGER_DELTA','COMBINED_IMPORT.lean','EXPORT.json','AUDIT_ROOTS','EXPECTED_IMPORTS','PHYSICAL','PLAN_STATUS','LEDGER.json.xz','validate.py']):pins.append(dict(path=str(f.relative_to(E.parents[1])),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
roots=sorted(roots);n=30
(E/'NJO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NJO_AUDIT_MODULES.json').write_text(json.dumps([['NJO_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
(E/'NJO_COMBINED_IMPORT.lean').write_text(''.join(f'import {pre}_COMBINED_IMPORT\n'for _,pre in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NJK_{name}.lean').read_text();t=s.replace('NJK_','NJO_');(E/f'NJO_{name}.lean').write_text(t);(E/f'NJO_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NIU_'+name,tofile='NJO_'+name)))
for p in E.glob('NJO_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NJO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'NJO_EXPECTED_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
(E/'NJO_SEED_INPUTS.json').write_text(json.dumps(seeds,indent=1)+'\n');(E/'NJO_INPUT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
paths=[C+'/'+pre+'_seed' for _,pre in specs]+extra
(E/'NJO_PATHS.json').write_text(json.dumps(list(dict.fromkeys(paths)),indent=1)+'\n')
for name in ['run','batch','pin','setup','queue']:
 s=(P/f'NJK_{name}.py').read_text().replace('NJK_','NJO_').replace('codex-cx-ledger14-20261108','codex-cx-ledger15-20261108')
 if name=='run':s=s.replace("E.parent/'ledger13-20261107/NIU_CLOSURE_PINS.json.xz'","E.parent/'ledger14-20261108/NJK_CLOSURE_PINS.json.xz'")
 (E/f'NJO_{name}.py').write_text(s)
print(json.dumps(dict(stage='prepare',roots=len(roots),seeds=len(seeds),expected_conflicts=len(conflicts))))
