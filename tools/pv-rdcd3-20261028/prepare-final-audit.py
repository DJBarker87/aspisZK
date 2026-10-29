"""Prepare the final statement/axioms target from actual successful receipts.
Call once at the final freeze; do not replace failed modules with audit claims.
"""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd3-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
mods={};names=set()
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit'] or j['attempt']>=60697:continue
 source=R/j['source_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==j['source_sha256'],source
 mods[j['module']]=dict(source_path=j['source_path'],source_sha256=j['source_sha256'],receipt=str(p.relative_to(E)))
 for line in j['axioms']:
  assert 'sorryAx' not in line
  names.add(re.match(r"'([^']+)'",line)[1])
 # Every new theorem, including any absent from an older print list.
 if 'PV_RDCD3_' in j['module']:
  stack=[]
  for line in source.read_text().splitlines():
   m=re.match(r'namespace\s+(\S+)',line)
   if m:stack.append(m[1]);continue
   if re.match(r'end(?:\s|$)',line):
    if stack:stack.pop()
    continue
   m=re.match(r'theorem\s+(\S+)',line)
   if m:names.add('.'.join(stack+[m[1]]))
imports=''.join('import '+m.replace('/','.')+'\n' for m in sorted(mods))
checks='\n#check @R1Z.PV_RDCD3_V260Complete.complete\n#check @R1Z.PV_RDCD3_V265.complete\n'
s=imports+checks+''.join('#print axioms '+n+'\n' for n in sorted(names))
(L/'PV_RDCD3_FinalAudit.lean').write_text(s)
(E/'final-source-freeze.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=mods,printed_declarations=sorted(names),scope='Successful focused source cohort only; failed/uncompiled drafts excluded; source/Result row limits retained'),indent=2)+'\n')
print(len(mods),'successful modules;',len(names),'axioms targets; final audit source prepared')
