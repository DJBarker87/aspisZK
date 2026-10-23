from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
f=(E/'current-children/Funs.lean').read_text();ext=(E/'current-children/FunsExternal_Template.lean').read_text()
a=f.index('def verifier.accumulate_batched_with_node_loop0_loop0.body')
b=f.index('/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::finish]',a)
body=f[a:b]
pat=lambda n:r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])'
blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',ext,re.M)
fields=[];mapping={}
for name,typ in blocks:
 if not re.search(pat(name),body):continue
 typ=typ.strip();field='op'+str(len(fields));mapping[name]=field
 if typ.startswith(':'):typ=typ[1:].strip()
 else:
  depth=0
  for j,ch in enumerate(typ):
   if ch in '({':depth+=1
   elif ch in ')}':depth-=1
   elif ch==':' and depth==0:break
  typ='∀ '+typ[:j].rstrip()+', '+typ[j+1:].lstrip()
 fields.append('  '+field+' : '+typ.replace('\n','\n    '))
fields.append('  widePartialEq : core.cmp.PartialEq aspis_core.field.wide_exact.WideExact aspis_core.field.wide_exact.WideExact')
for n in sorted(mapping,key=len,reverse=True):body=re.sub(pat(n),'ops.'+mapping[n],body)
body=body.replace('aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact','ops.widePartialEq')
internal=re.findall(r'(?:^def|^impl_def)\s+([A-Za-z0-9_.]+)',body,re.M)
for n in sorted(internal,key=len,reverse=True):
 body=re.sub(pat(n),'('+n+' ops)',body)
 body=re.sub(r'\bdef\s+\('+re.escape(n)+r' ops\)', 'def '+n+' (ops : Ops)',body)
header='''import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeQueryBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
structure Ops where
'''
s=header+'\n'.join(fields)+'\n\n'+body+'\n'
for n in internal:s+='#print axioms '+n+'\n'
s+='end AspisR1.Port3_NativeQueryBody\nend\n'
(L/'Port3_NativeQueryBody.lean').write_text(s)
(E/'query-current-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(f.encode()).hexdigest(),'module_sha256':hashlib.sha256(s.encode()).hexdigest(),'external_operations':mapping,'internal_functions':internal,'qualification':'Current emitted source and release wrapping arithmetic; local std/opening/arithmetic/push/comparison/trace/mark leaves explicit. No native/reference query equality assumed, no type/function template imported.'},indent=2)+'\n')
