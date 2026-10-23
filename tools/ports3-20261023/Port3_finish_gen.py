from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
f=(E/'current-children/Funs.lean').read_text();ext=(E/'current-children/FunsExternal_Template.lean').read_text()
a=f.index('def verifier.finish_relation\n');b=f.index('/-- [aspis_r1_cost_probe::verifier::candidate::tx2_common]',a)
body=f[a:b]
body=re.sub(r'core.cmp.PartialEq.ne.trait_default\s*aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact','ops.ne',body)
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
fields.append('  ne : aspis_core.field.wide_exact.WideExact → aspis_core.field.wide_exact.WideExact → Result Bool')
for n in sorted(mapping,key=len,reverse=True):body=re.sub(pat(n),'ops.'+mapping[n],body)
body=body.replace('def verifier.finish_relation\n','def verifier.finish_relation (ops : Ops W)\n')
header='''import Port3_NativePendingPrefix
import Stage2FinishBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeFinishBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
variable {W : Type}
structure Ops (W : Type) where
'''
s=(header+'\n'.join(fields)+'\n\n'+body+'\n#print axioms verifier.finish_relation\nend AspisR1.Port3_NativeFinishBody\nend\n').replace('weights.Weights','W')
(L/'Port3_NativeFinishBody.lean').write_text(s)
(E/'finish-current-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(f.encode()).hexdigest(),'module_sha256':hashlib.sha256(s.encode()).hexdigest(),'external_operations':mapping,'qualification':'Exact current finish parent with explicit local source round/table/pair/dot/folds/mark/trace and composite derived-ne callback; W is only a callee carrier parameter. No template imported and no whole-finish equality premise.'},indent=2)+'\n')
