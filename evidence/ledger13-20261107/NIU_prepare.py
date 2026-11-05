from pathlib import Path
import json,re,difflib,hashlib,lzma,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'ledger12-20261107'
specs=[('ledger12-20261107','NIR'),('slice-d-entry6-20261107','NIS'),('verify-observed4-20261107','NIH'),('slice-d-pair6-20261107','NIT'),('tx2-native3-20261107','NIL'),('pool-borrow2-20261107','NIO')]
(E/'NIU_COMBINED_IMPORT.lean').write_text(''.join(f'import {pre}_COMBINED_IMPORT\n'for _,pre in specs)+'#print axioms AspisR1.RPx_Deployed.deployed\n')
roots=set();expected={};conflicts=[]
for folder,pre in specs:
 p=E.parent/folder;d=json.loads((p/f'{pre}_AUDIT_ROOTS.json').read_text())
 roots.update(d.get('roots',sum(d.get('groups',[]),[])) if isinstance(d,dict)else d)
 for l in (p/f'{pre}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(l);m=x['module'];xs=x['imports']
  if m in expected and expected[m]!=xs:conflicts.append(dict(module=m,earlier=expected[m],later=xs,provider=pre))
  else:expected[m]=xs
roots=sorted(roots);n=30
(E/'NIU_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NIU_AUDIT_MODULES.json').write_text(json.dumps([['NIU_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
for name in ['Driver','ProofDriver','OwnerStatements']:
 s=(P/f'NIR_{name}.lean').read_text();t=s.replace('NIR_','NIU_');(E/f'NIU_{name}.lean').write_text(t)
 (E/f'NIU_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='NIR_'+name,tofile='NIU_'+name)))
s=(P/'NIR_batch.py').read_text().replace('NIR_','NIU_')
s=s[:s.index("if mode=='batch27':")]
(E/'NIU_batch.py').write_text(s)
for p in E.glob('NIU_*.lean'):expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NIU_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'NIU_EXPECTED_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
# Pin required large inputs once. No source duplication and no sibling writes.
pins=[]
for folder,pre in specs:
 for p in (E.parent/folder).iterdir():
  if p.is_file() and any(k in p.name for k in ('HANDOFF','CLOSED.json','LEDGER_DELTA','COMBINED_IMPORT.lean','EXPORT.json','AUDIT_ROOTS','EXPECTED_IMPORTS','PHYSICAL','PLAN_STATUS','LEDGER.json.xz','validate.py')):
   pins.append(dict(path=str(p.relative_to(E.parents[1])),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(E/'NIU_INPUT_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
print(json.dumps(dict(stage='prepare',roots=len(roots),expected_conflicts=len(conflicts),groups=n)))
