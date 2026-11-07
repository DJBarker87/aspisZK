"""Prepare the single final combined import and unchanged raw walker gate."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
# Add only independently checked modules. Failed probes/templates are never imported.
tops=['PCI_Note','PCI_CountState','PCI_RootAddress','PCI_ValidatePacket','PCI_SinglePacket','PCI_DepositReferenceModel','PCI_DepositLimits','PCI_DepositExtents','PCI_DepositSuffix','PCI_ByteArrayComparison','PCI_ListWindow','PCI_IteTransport']
extra=E/'PCI_GATE_EXTRA.json'
if extra.exists():tops+=json.loads(extra.read_text())
mods=['RPx_Deployed','NLX_COMBINED_IMPORT','NLF_SdkBorrowLaw','PCE_COMBINED_IMPORT','PCG_COMBINED_IMPORT','PCF_COMBINED_IMPORT']+tops
(E/'PCI_COMBINED_IMPORT.lean').write_text(''.join('import '+m+'\n' for m in mods)+'#print axioms AspisR1.RPx_Deployed.deployed\n#print axioms PCI_ValidatePacket.full\n#print axioms PCI_SinglePacket.full\n#print axioms PCI_RootAddress.complete\n#print axioms PCI_CountState.complete\n#print axioms PCI_Note.forwarding\n')
expected={}
for folder,prefix in [('ledger24-20261110','NLX'),('pool-ledger1-20261110','PCE'),('pc-helpers2-20261110','PCG'),('pc-deposit-children1-20261110','PCF'),('pc-helpers1-20261110','PCB')]:
 p=E.parent/folder/(prefix+'_EXPECTED_IMPORTS.jsonl')
 if p.exists():
  for line in p.read_text().splitlines():
   r=json.loads(line);m=r['module'];im=r['imports']
   if m in expected:assert expected[m]==im, m
   expected[m]=im
# Canonical source imports for local modules and the four unchanged private dependencies.
for p in E.glob('*.lean'):
 if p.name.startswith('PCI_dependency_'):m=p.name[len('PCI_dependency_'):-5]
 else:m=p.stem
 im=['Init']+sum((l[7:].split() for l in p.read_text().splitlines() if l.startswith('import ')),[])
 expected[m]=list(dict.fromkeys(im))
(E/'PCI_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps({'module':m,'imports':v})+'\n' for m,v in sorted(expected.items())))
closure=set()
def visit(m):
 if not m.startswith('PCI_') or m in closure:return
 closure.add(m)
 for im in expected[m]:visit(im)
for m in tops:visit(m)
records=[json.loads(s) for s in (E/'PCI_ATTEMPTS.jsonl').read_text().splitlines()]
latest={r['module']:r for r in records if r['kind']=='lean' and r['exit_status']==0}
own=[]
for m in sorted(closure):
 assert m in latest,'missing focused green: '+m
 for line in latest[m].get('print_axioms',[]):
  found=re.match(r"'([^']+)'",line)
  if found:own.append(found[1])
roots=list(dict.fromkeys(['AspisR1.RPx_Deployed.deployed']+own))
(E/'PCI_AUDIT_ROOTS_ALL.json').write_text(json.dumps({'roots':roots,'own':own,'module_closure':sorted(closure)},indent=1)+'\n')
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';x=json.loads((E/'PCI_TASKS.json').read_text())
x['PCI_L101']={'kind':'lean','target':'PCI_COMBINED_IMPORT'}
x['PCI_L102']={'kind':'lean','target':'PCI_AuditDriver','native':True}
x['PCI_L103']={'kind':'link','target':'PCI_AuditDriver','command':[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','PCI_native/PCI_AuditDriver','PCI_native/PCI_AuditDriver.c','PCI_native/PCI_WALKER.c','PCI_native/PCI_MemoryLimit.c'],'files':{'PCI_native/PCI_WALKER.c':'PCI_WALKER.c','PCI_native/PCI_MemoryLimit.c':'PCI_MemoryLimit.c'}}
x['PCI_L104']={'kind':'audit','target':'Eight unchanged NEP fixtures, same final binary','command':['PCI_native/PCI_AuditDriver','fixtures']}
x['PCI_L105']={'kind':'audit','target':'NFX whole combined import scan','command':['PCI_native/PCI_AuditDriver','scan'],'files':{'PCI_EXPECTED_IMPORTS.jsonl':'PCI_EXPECTED_IMPORTS.jsonl','PCI_AUDIT_ROOTS.json':'PCI_AUDIT_ROOTS_ALL.json'},'collect':['PCI_LOADED_scan.jsonl']}
batches=[roots[i:i+25] for i in range(0,len(roots),25)]
for i,b in enumerate(batches):
 n=f'PCI_ROOTS_{i:02}.json';(E/n).write_text(json.dumps({'roots':b},indent=1)+'\n');x[f'PCI_L{106+i:03}']={'kind':'audit','target':f'All own raw ax2 roots batch{i}','command':['PCI_native/PCI_AuditDriver',f'proof{i}'],'files':{'PCI_AUDIT_ROOTS.json':n}}
(E/'PCI_TASKS.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'PCI_GATE_PLAN.json').write_text(json.dumps({'combined':'PCI_L101','driver':'PCI_L102','link':'PCI_L103','fixtures':'PCI_L104','scan':'PCI_L105','raw':[f'PCI_L{106+i:03}' for i in range(len(batches))],'own_roots':own,'total_roots':len(roots),'walker_sha256':hashlib.sha256((E/'PCI_WALKER.c').read_bytes()).hexdigest(),'baseline':'exact ledger24 and accepted NLF/PCE/PCG/PCF hashes; unchanged accepted raw gates retained, no unchanged whole-verifier replay'},indent=1)+'\n')
print('PCI final gate prepared: '+str(len(own))+' own roots, '+str(len(batches))+' raw batches')
