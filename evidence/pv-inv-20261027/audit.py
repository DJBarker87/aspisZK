"""Compile-free audit manifest generator; final three distinct Lean audit targets."""
from pathlib import Path
import re,json,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parents[1];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('J*/receipt.json'))]
latest={}
for d in receipts:
 if d['exit']==0:latest[(d['module'],d['source_sha256'])]=d
modules=[]
for p in sorted(L.glob('PV_Inv_*.lean')):
 if 'Audit' in p.stem:continue
 s=p.read_text();h=hashlib.sha256(s.encode()).hexdigest();key=('R1Z/'+p.stem,h)
 assert key in latest, f'No successful current source receipt: {p.name}'
 assert not re.search(r'^\s*(?:.*\b)?(?:sorry|admit|axiom|native_decide|implemented_by)\b', '\n'.join(l for l in s.splitlines() if not l.strip().startswith(('--','/-','*')))),p
 ns=re.findall(r'^namespace (\S+)',s,re.M)[0]
 prints=re.findall(r'^#print axioms (\S+)',s,re.M)
 thms=re.findall(r'^\s*(?:private )?theorem (\w+)',s,re.M)
 assert set(thms)<=set(prints), (p.name,set(thms)-set(prints))
 full=[n if n.startswith('R1Z.') else ns+'.'+n for n in prints]
 success=latest[key]
 assert all('sorryAx' not in line for line in success['axioms'])
 modules.append(dict(module='R1Z.'+p.stem,path=str(p.relative_to(R)),sha256=h,receipt=success['attempt'],declarations=full))
(E/'AUDIT-MANIFEST.json').write_text(json.dumps(modules,indent=2)+'\n')
# Split by dependency family only for moderate-sized #print streams, not a change of theorem scope.
groups=[modules[::2],modules[1::2]]
for n,group in enumerate(groups,1):
 lines=['import '+m['module'] for m in group]+['','/-! Focused final dependency/import and accepted-axioms audit. Not a frozen release replay. -/']
 for m in group:lines+=['#print axioms '+d for d in m['declarations']]
 (L/f'PV_Inv_Audit{n}.lean').write_text('\n'.join(lines)+'\n')
(L/'PV_Inv_Audit3.lean').write_text('''import R1Z.PV_Inv_Audit1
import R1Z.PV_Inv_Audit2
/-! Final focused union audit. Native association and headline instantiation remain open. -/
#print axioms R1Z.PV_Inv_NativeQ.subtract_nonzero
#print axioms R1Z.PV_Inv_NativeNormQ.norm_operand
#print axioms R1Z.PV_Inv_NativeNormC.norm_operand
#print axioms R1Z.PV_Inv_InterpolationSource.source_inverse_operand
#print axioms R1Z.PV_Inv_RegistrySlot.producer
#print axioms R1Z.PV_Inv_RegistrySlot.consumer
#print axioms R1Z.PV_Inv_NativeRegistry.producer
#print axioms R1Z.PV_Inv_GlobalNative.all_reached_tests
#print axioms R1Z.PV_Inv_GlobalScan.native_guarded
#print axioms R1Z.PV_Inv_PoleMass.mass
#print axioms R1Z.PV_Inv_PoleUnion.eight_attempts
''')
print(len(modules),'modules;',sum(len(m['declarations']) for m in modules),'axioms-print declarations')
