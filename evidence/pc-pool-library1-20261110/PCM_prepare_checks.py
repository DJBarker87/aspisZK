from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent
specs=sorted(p.stem for p in E.glob('PCM_Spec_POOL_*.lean'))
inst=sorted(p.stem for p in E.glob('PCM_Inst_*.lean'))
(E/'PCM_SUPPORT_IMPORT.lean').write_text(''.join('import '+n+'\n' for n in specs+inst+['PCM_Top'])+'-- Supporting closure only; excludes blocked headline/bundle import.\n')
required=['RPx_Deployed','NMQ_COMBINED_IMPORT','LIB_BUNDLE_IMPORT','NLF_COMBINED_IMPORT','PCB_COMBINED_IMPORT','PCE_COMBINED_IMPORT','PCG_COMBINED_IMPORT','PCF_COMBINED_IMPORT','PCI_COMBINED_IMPORT','PCD_COMBINED_IMPORT','PCM_SUPPORT_IMPORT']
(E/'PCM_COMBINED_IMPORT.lean').write_text(''.join('import '+n+'\n'for n in required)+'#print axioms AspisR1.RPx_Deployed.deployed\n#print axioms PCM_Top.check\n')
# Canonical scanner source is unchanged except its declared input/output names.
s=(E.parent/'ledger25-20261111/NMQ_Driver.lean').read_text().replace('NMQ_COMBINED_IMPORT','PCM_SUPPORT_IMPORT').replace('NMQ_EXPECTED_IMPORTS','PCM_EXPECTED_IMPORTS').replace('NMQ_LOADED_scan','PCM_LOADED_scan')
s=s.replace('import NFA_WALKER\n','').replace('import NFA_MemoryLimit\n','').replace('  NFA_MemoryLimit.set\n','')
s=s.replace('let (modules, roots) :=','let (modules, roots) : Array Name × Array Name :=')
s=s[:s.index('  let ctx : Command.Context')]+ '  return 0\n'
(E/'PCM_Scan.lean').write_text(s)

expected={};conflicts=[]
for folder in ['ledger25-20261111','lib-20261111','pc-helpers1-20261110','pc-helpers2-20261110','pool-ledger1-20261110','pc-deposit-children1-20261110','pc-deposit-children2-20261110','pc-terminal-children1-20261110','sdk-borrow-20261109']:
 for p in (E.parent/folder).glob('*EXPECTED_IMPORTS.jsonl*'):
  if p.suffix=='.xz':raw=lzma.decompress(p.read_bytes()).decode()
  elif p.suffix=='.jsonl':raw=p.read_text()
  else:continue
  for line in raw.splitlines():
   r=json.loads(line);m=r['module'];v=r['imports']
   if m in expected and expected[m]!=v:conflicts.append(dict(module=m,old=expected[m],new=v,source=str(p)))
   expected[m]=v
for r in json.loads((E/'PCM_EXPECTED_SUPPLEMENT.json').read_text()):
 expected[r['module']]=r['imports']
for p in list(E.glob('PCM_*.lean'))+list((E/'PCM_dependency_inputs').glob('*.lean')):
 expected[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'PCM_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(expected.items())))
(E/'PCM_IMPORT_CONFLICTS.json').write_text(json.dumps(conflicts,indent=1)+'\n')
# Audit every printed new root only, including all frozen rejection checks.
groups=[];roots=[]
for p in sorted(E.glob('PCM_*.lean')):
 if p.stem in ['PCM_COMBINED_IMPORT','PCM_InspectChildren']:continue
 stack=[]
 for line in p.read_text().splitlines():
  if line.startswith('namespace '):stack.append(line.split()[1])
  elif re.match(r'^(?:noncomputable )?section(?: |$)',line):stack.append(None)
  elif line=='end' or line.startswith('end '):
   if stack:stack.pop()
  elif line.startswith('#print axioms '):
   name=line.split()[2]
   if '.' not in name:name='.'.join([n for n in stack if n]+[name])
   if name.startswith(('PCM.','PCM_')) and name not in roots:roots.append(name)
# Small groups avoid pathological aggregate walks; a theorem's closure is never reduced.
prior=E/'PCM_AUDIT_ROOTS.json'
if prior.exists():
 old=json.loads(prior.read_text());assert set(old['roots'])<=set(roots)
 groups=old['groups'];added=[n for n in roots if n not in old['roots']]
 for i in range(0,len(added),20):groups.append(added[i:i+20])
 roots=old['roots']+added
else:
 for i in range(0,len(roots),20):groups.append(roots[i:i+20])
(E/'PCM_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=groups),indent=1)+'\n')
(E/'PCM_AUDIT_MODULES.json').write_text(json.dumps([['PCM_SUPPORT_IMPORT']]*len(groups))+'\n')
(E/'PCM_AUDITOR_PIN.json').write_bytes((E.parent/'lib-20261111/LIB_AUDITOR_PIN.json').read_bytes())
print(json.dumps(dict(new_roots=len(roots),raw_groups=len(groups),expected_imports=len(expected),conflicts=len(conflicts))))
