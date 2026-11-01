"""Prepare the final statement/axioms target from actual successful receipts.
Call once at the final freeze; do not replace failed modules with audit claims.
"""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
mods={};names=set()
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit'] or j['attempt']>=66397:continue
 source=R/j['source_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==j['source_sha256'],source
 mods[j['module']]=dict(source_path=j['source_path'],source_sha256=j['source_sha256'],receipt=str(p.relative_to(E)))
 for line in j['axioms']:
  assert 'sorryAx' not in line
  names.add(re.match(r"'([^']+)'",line)[1])
 # Every new theorem, including any absent from an older print list.
 if 'PV_RDCD4_' in j['module']:
  stack=[]
  for line in source.read_text().splitlines():
   m=re.match(r'namespace\s+(\S+)',line)
   if m:stack.append(m[1]);continue
   if re.match(r'end(?:\s|$)',line):
    if stack:stack.pop()
    continue
   m=re.match(r'theorem\s+(\S+)',line)
   if m:names.add('.'.join(stack+[m[1]]))
reuse=E/'reused-projects.json'
if reuse.exists():
 for module,pin in json.load(open(reuse))['modules'].items():
  assert module not in mods,module
  source=R/pin['source_path'];assert hashlib.sha256(source.read_bytes()).hexdigest()==pin['source_sha256']
  mods[module]=dict(source_path=pin['source_path'],source_sha256=pin['source_sha256'],reused=True,original_receipt=pin['original_receipt']['path'])
  for line in pin['original_receipt'].get('print_axioms',[]):
   assert 'sorryAx' not in line
   names.add(re.match(r"'([^']+)'",line)[1])
imports=''.join('import '+m.replace('/','.')+'\n' for m in sorted(mods))
checks='\n#check @R1Z.PV_RDCD4_V201.source_reference\n'
# Whole-row theorem checks are driven by final row dispositions, never by drafts.
for n in [220,237,236,233,197]:
 p=E/f'rows/V{n}.json'
 if p.exists():
  row=json.load(open(p))
  if row['status']=='RESTORED':checks+='\n#check @'+row['kernel_theorem']+'\n'
s=imports+checks+''.join('#print axioms '+n+'\n' for n in sorted(names))
(L/'PV_RDCD4_FinalAudit.lean').write_text(s)
(E/'final-source-freeze.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=mods,printed_declarations=sorted(names),scope='Successful focused source cohort only; failed/uncompiled drafts excluded; source/Result row limits retained'),indent=2)+'\n')
print(len(mods),'successful modules;',len(names),'axioms targets; final audit source prepared')
