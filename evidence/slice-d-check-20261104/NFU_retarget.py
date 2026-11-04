"""Namespace-only coherent reuse of retained opaque leaf modules.

No theorem body is rewritten. The type change replaces an UNUSED copied
Phase declaration with the adopted canonical owner; all changes are in manifest.
"""
from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
sources={p.stem:p for root in ['evidence/leaf-p6-10-20261027','evidence/leaf-p6-12-20261027']for p in (R/root).glob('*.lean')}
seen=set();order=[]
def visit(n):
 if n in seen or n not in sources:return
 seen.add(n)
 for line in sources[n].read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():visit(child)
 order.append(n)
for n in ['LPl_Check','LPn_ExpandTrace']:visit(n)
manifest=[];diff=[]
for n in order:
 raw=sources[n].read_text();s=raw;name='NFU_'+n
 s=re.sub(r'^import (\S+)',lambda m:'import '+('NFU_'+m[1] if m[1] in seen else m[1]),s,flags=re.M)
 # Canonical Phase replaces the unused old owner before it can enter the forest.
 if n=='LPl_Kit_Types':
  start=s.index('@[import_union_discriminant]\ninductive verifier.Phase where');end=s.index('\n\n',start)
  s=s[:start]+'abbrev verifier.Phase := NFN_PhaseTransport.Owned'+s[end:]
  s=s.replace('@[import_union_discriminant', '@[import_union_discriminant isize')
  s='import NFN_PhaseTransport\n'+s
 lines=s.splitlines(True);last=max(i for i,l in enumerate(lines) if l.startswith('import '));lines.insert(last+1,'\nnamespace NFU_Retarget\n');s=''.join(lines)+'\nend NFU_Retarget\n'
 # Every theorem already has its retained #print axioms; preserve those audits.
 (E/(name+'.lean')).write_text(s)
 manifest.append(dict(module=name,origin=str(sources[n].relative_to(R)),origin_sha256=sha(raw.encode()),source_sha256=sha(s.encode()),transformation='Imports -> NFU_; enclosing namespace NFU_Retarget; unused Phase -> NFN_PhaseTransport.Owned; explicit isize discriminant adapter argument'  if n=='LPl_Kit_Types' else 'Imports -> NFU_; enclosing namespace NFU_Retarget; all proof terms unchanged'))
 diff+=difflib.unified_diff(raw.splitlines(True),s.splitlines(True),fromfile='a/'+str(sources[n].relative_to(R)),tofile='b/'+str((E/(name+'.lean')).relative_to(R)))
(E/'NFU_RETARGET.json').write_text(json.dumps(manifest,indent=1)+'\n');(E/'NFU_RETARGET.diff').write_text(''.join(diff))
(E/'NFU_RETARGET_QUEUE.json').write_text(json.dumps([dict(attempt=f'NFU_L{i:03}',kind='lean',target=x['module'],exit=0)for i,x in enumerate(manifest,11)],indent=1)+'\n')
# Consume only the prefixed modules, excluding every colliding old declaration.
p=E/'NFU_CompactLeaves.lean';s=p.read_text().replace('import LPn_ExpandTrace','import NFU_LPn_ExpandTrace').replace('import LPl_Check','import NFU_LPl_Check')
s=s.replace('open Aeneas Aeneas.Std Result','open Aeneas Aeneas.Std Result\nopen NFU_Retarget');p.write_text(s)
print(json.dumps(dict(modules=len(manifest),first='NFU_L011',last=f'NFU_L{10+len(manifest):03}')))
