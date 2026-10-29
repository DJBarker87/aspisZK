"""Inventory active proofs by exact successful source snapshots, never by filename."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[];excluded=[]
for source in sorted(E.glob('NED_*.lean')):
 if source.stem=='NED_FinalAudit':continue # audit is generated, never its own dependency
 module=source.stem;matches=[]
 for p in E.glob('NED_L*/receipt.json'):
  r=json.loads(p.read_text());snapshot=p.parent/'NED_SOURCE.lean.txt'
  if r['module']==module and r['exit_status']==0 and snapshot.exists() and snapshot.read_bytes()==source.read_bytes():matches.append((p,r))
 if not matches:
  excluded.append(dict(module=module,reason='No successful exact-current-source receipt; not an active theorem'))
  continue
 p,r=sorted(matches,key=lambda t:t[0].parent.name)[-1]
 names=[]
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  name=re.search(r"^'([^']+)'",line)
  if name:names.append(name[1])
 rows.append(dict(module=module,source=source.name,source_sha256=sha(source.read_bytes()),receipt=str(p.relative_to(E)),receipt_sha256=sha(p.read_bytes()),theorems=names))
imports='\n'.join('import '+r['module'] for r in rows)
prints='\n'.join('#print axioms '+n for r in rows for n in r['theorems'])
(E/'NED_FinalAudit.lean').write_text(imports+'\nset_option autoImplicit false\n'+prints+'\n')
(E/'NED_ACTIVE_PROOFS.json').write_text(json.dumps(dict(active=rows,excluded=excluded,method='exact source bytes and successful receipt with standard axioms; no native-credit inference'),indent=1)+'\n')
print(json.dumps(dict(active_modules=len(rows),top_theorems=sum(len(r['theorems']) for r in rows),excluded=excluded)))
