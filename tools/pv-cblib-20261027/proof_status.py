"""Current-source acceptance inventory; old green snapshots never certify edits."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
receipts=[]
for p in out.glob('[0-9]*.json'):
 try:r=json.loads(p.read_text())
 except ValueError:continue
 if 'module' in r and 'exit' in r and 'source_sha256' in r:receipts.append(r)
rows=[]
for p in sorted((root/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_CBL_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();module='R1Z/'+p.stem
 matching=[r for r in receipts if r['module']==module and r['source_sha256']==sha]
 latest=max(matching,key=lambda r:r['attempt']) if matching else None
 bad=[]
 if latest:
  for line in latest.get('axioms',[]):
   m=re.search(r'depends on axioms: \[([^\]]*)\]',line,re.S)
   if m:bad += [x.strip() for x in m[1].split(',') if x.strip() not in ['propext','Classical.choice','Quot.sound']]
 rows.append({'bad_axioms':bad,'module':module,'sha256':sha,'status':'accepted' if latest and latest['exit']==0 and not bad else 'rejected' if latest else 'draft','receipt':latest['attempt'] if latest else None})
result={'scope':'current source hashes and focused compile receipts; not a dependency-closure or native-equivalence certificate','counts':{s:sum(r['status']==s for r in rows) for s in ['accepted','rejected','draft']},'modules':rows}
(out/'proof-status.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['counts']))
