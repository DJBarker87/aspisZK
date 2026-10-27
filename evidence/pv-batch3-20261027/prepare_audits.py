from pathlib import Path
import re,json
D=Path(__file__).resolve().parent;L=D/'lean';groups={'Source':[],'Canonical':[]}
for p in sorted(L.glob('PV_B3_*.lean')):
 if 'Audit' in p.stem:continue
 groups['Canonical' if p.stem.startswith('PV_B3_Canonical') else 'Source'].append(p)
manifest={}
for kind,ps in groups.items():
 names=[]
 for p in ps:
  stack=[]
  for line in p.read_text().splitlines():
   m=re.match(r'namespace (\S+)',line)
   if m:stack.append(m.group(1));continue
   if re.match(r'end(?:\s|$)',line):
    if stack:stack.pop()
    continue
   m=re.match(r'\s*(?:(?:noncomputable|protected)\s+)?(?:def|theorem|structure|inductive|abbrev)\s+(\S+)',line)
   if m:
    name=m.group(1).split('(')[0]
    names.append('.'.join(stack+[name]))
 s=''.join('import '+p.stem+'\n' for p in ps)
 s+='-- One axioms audit over the exact private closure; no target theorem is assumed.\n'
 s+=''.join('#print axioms '+n+'\n' for n in sorted(set(names)))
 (L/f'PV_B3_Audit{kind}.lean').write_text(s)
 manifest[kind]=dict(modules=[p.stem for p in ps],declarations=sorted(set(names)))
s='''import PV_B3_AuditSource
import PV_B3_AuditCanonical
namespace PV_B3_AuditManifest
open Aeneas Aeneas.Std Result
set_option autoImplicit false
 theorem forest134 := PV_B3_BoundedPacket.forest134
 theorem mask117 := PV_B3_BoundedPacket.mask117
 theorem polynomial121 := PV_B3_BoundedPacket.polynomial121
#print axioms forest134
#print axioms mask117
#print axioms polynomial121
#print axioms PV_B3_Canonical.prepared_mul
#print axioms PV_B3_Canonical.reconstruct_channels
end PV_B3_AuditManifest
'''
# Lean theorem declarations need an explicit type; exact aliases are definitions.
s=s.replace(' theorem forest134 :=',' def forest134 := ').replace(' theorem mask117 :=',' def mask117 := ').replace(' theorem polynomial121 :=',' def polynomial121 := ')
(L/'PV_B3_AuditManifest.lean').write_text(s)
(D/'audit-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print({k:(len(v['modules']),len(v['declarations']))for k,v in manifest.items()})
