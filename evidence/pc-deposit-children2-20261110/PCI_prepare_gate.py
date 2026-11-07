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
used=sum(r['kind'] in ['lean','link','audit'] for r in records)
base=max(int(r['attempt'][-3:]) for r in records if r['kind'] in ['lean','link','audit'])+1
numraw=120-used-6
assert 1<=numraw<=14
buckets=[[] for _ in range(14)]
def bucket(n):
 if n=='AspisR1.RPx_Deployed.deployed':return 0
 if n.startswith('PCI_Note.'):return 1
 if n.startswith(('PCI_Count.','PCI_CountState.')):return 2
 if n.startswith('PCI_RootAddress.'):return 3
 if n.startswith(('PCI_ValidateWords.','PCI_ValidateCarrier.','PCI_DigestCarrier.','PCI_DigestRoundtrip.')):return 4
 if n.startswith(('PCI_Mul.','PCI_ValidateField.','PCI_ValidateSub.','PCI_SizeArithmetic.')):return 5
 if n.startswith('PCI_ValidatePrefix.'):return 6
 if n.startswith('PCI_ValidateScan.'):return 7
 if n.startswith(('PCI_ValidateDomainAtoms.','PCI_ValidateDomains.')):return 8
 if n.startswith(('PCI_ValidateComplete.','PCI_ValidateFull.','PCI_ValidatePacket.','PCI_SharedScanner.')):return 9
 if n.startswith('PCI_Single'):return 10
 if n.startswith(('PCI_DepositRead.','PCI_DepositWords.','PCI_DepositWordWindow.','PCI_DepositDigestLaw.')):return 11
 if n.startswith(('PCI_DepositRange.','PCI_DepositConvert.','PCI_DepositExtents.','PCI_DepositSuffix.','PCI_DepositCopyExtents.','PCI_DepositHeader.','PCI_ListWindow.')):return 12
 if n.startswith(('PCI_DepositReferenceModel.','PCI_DepositLimits.','PCI_DepositErrorCarrier.','PCI_Byte','PCI_ArrayCanonical.','PCI_IteTransport.')):return 13
 raise AssertionError(n)
for root in roots:buckets[bucket(root)].append(root)
assert all(buckets)
while len(buckets)>numraw:
 # Merge neighbouring small semantic groups; no root repeated or dropped.
 i=min(range(1,len(buckets)-1),key=lambda i:len(buckets[i])+len(buckets[i+1]))
 buckets[i:i+2]=[buckets[i]+buckets[i+1]]
aid=lambda i:f'PCI_L{base+i:03}'
x[aid(0)]={'kind':'lean','target':'PCI_COMBINED_IMPORT'}
x[aid(1)]={'kind':'lean','target':'PCI_AuditDriver','native':True}
x[aid(2)]={'kind':'link','target':'PCI_AuditDriver','command':[T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','PCI_native/PCI_AuditDriver','PCI_native/PCI_AuditDriver.c','PCI_native/PCI_WALKER.c','PCI_native/PCI_MemoryLimit.c'],'files':{'PCI_native/PCI_WALKER.c':'PCI_WALKER.c','PCI_native/PCI_MemoryLimit.c':'PCI_MemoryLimit.c'}}
wrapper={'PCI_audit_once.py':'PCI_audit_once.py'}
x[aid(3)]={'kind':'audit','target':'Eight unchanged NEP fixtures, same final binary','command':['python3','PCI_audit_once.py','fixtures'],'files':wrapper,'collect':['PCI_BINARY_BASE.json','PCI_BINARY_fixtures.json']}
x[aid(4)]={'kind':'audit','target':'NFX whole combined import scan','command':['python3','PCI_audit_once.py','scan'],'files':dict(wrapper,**{'PCI_EXPECTED_IMPORTS.jsonl':'PCI_EXPECTED_IMPORTS.jsonl','PCI_AUDIT_ROOTS.json':'PCI_AUDIT_ROOTS_ALL.json'}),'collect':['PCI_LOADED_scan.jsonl','PCI_BINARY_scan.json']}
for i,b in enumerate(buckets):
 n=f'PCI_ROOTS_{i:02}.json';(E/n).write_text(json.dumps({'roots':b},indent=1)+'\n');x[aid(5+i)]={'kind':'audit','target':f'Disjoint raw ax2 semantic group{i}','command':['python3','PCI_audit_once.py',f'proof{i}'],'files':dict(wrapper,**{'PCI_AUDIT_ROOTS.json':n}),'raw_expected':b,'collect':[f'PCI_BINARY_proof{i}.json']}
last=aid(5+len(buckets))
x[last]={'kind':'audit','target':'Final raw artifacts and immutable accepted object export','command':['python3','PCI_collect_final.py'],'files':{'PCI_collect_final.py':'PCI_collect_final.py','PCI_AUDIT_ROOTS_ALL.json':'PCI_AUDIT_ROOTS_ALL.json'},'collect':['PCI_RAW_BUNDLE.tar.xz','PCI_RAW_BUNDLE.tar.xz.sha256','PCI_RAW_MANIFEST.json','PCI_AUDIT_BINARY_PINS.json','PCI_IMPORTS.json.xz','PCI_EXPORT.json']}
(E/'PCI_TASKS.json').write_text(json.dumps(x,indent=2)+'\n')
(E/'PCI_GATE_PLAN.json').write_text(json.dumps({'combined':aid(0),'driver':aid(1),'link':aid(2),'fixtures':aid(3),'scan':aid(4),'raw':[aid(5+i) for i in range(len(buckets))],'collect':last,'own_roots':own,'total_roots':len(roots),'walker_sha256':hashlib.sha256((E/'PCI_WALKER.c').read_bytes()).hexdigest(),'formal_used_before_gate':used,'formal_after_gate':used+6+len(buckets),'partition':'disjoint semantic groups; every own root once; headline separate','baseline':'exact ledger24 and accepted NLF/PCE/PCG/PCF hashes; unchanged accepted raw gates retained'},indent=1)+'\n')
print('PCI final gate prepared: '+str(len(own))+' own roots, '+str(len(buckets))+' disjoint raw groups, formal total120')
