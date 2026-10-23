from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/ports3-20261023';L=R/'docs/research/100bit-spend-path-20261013/lean'
f=(E/'current-children/Funs.lean').read_text();ext=(E/'current-children/FunsExternal_Template.lean').read_text()
a=f.index('def\n  verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut')
b=f.index('/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]',a)
# The accumulate loop comments begin before its entry declaration; trim at first loop.
b=f.index('/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]',a)
body=f[a:b]
blocks=re.findall(r'^axiom\s+([A-Za-z0-9_.]+)\s*([\s\S]*?)(?=\n/--|\Z)',ext,re.M)
pat=lambda n:r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])'
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
# Typed unwrap erases only Debug formatting; no external template is imported.
fields.append('  unwrap8 : core.result.Result (Array U8 8#usize) core.array.TryFromSliceError → Result (Array U8 8#usize)')
for n in sorted(mapping,key=len,reverse=True):body=re.sub(pat(n),'ops.'+mapping[n],body)
body=body.replace('core.result.Result.unwrap core.fmt.DebugTryFromSliceError','ops.unwrap8')
internal=re.findall(r'(?:^def|^impl_def)\s+([A-Za-z0-9_.]+)',body,re.M)
for n in sorted(internal,key=len,reverse=True):
 body=re.sub(pat(n),'('+n+' ops)',body)
 body=re.sub(r'\bdef\s+\('+re.escape(n)+r' ops\)', 'def '+n+' (ops : Ops)',body)
body=body.replace('8#i32','8#u32')
header='''import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeBatchBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
inductive multiproof.Arity where
  | Two | Eight
abbrev verifier.candidate.batch_tree.closure (H : Type) := Unit
structure Ops where
'''
s=header+'\n'.join(fields)+'\n\n'+body+'\n'
for n in internal:s+='#print axioms '+n+'\n'
s+='end AspisR1.Port3_NativeBatchBody\nend\n'
(L/'Port3_NativeBatchBody.lean').write_text(s)
(E/'batch-current-emission.json').write_text(json.dumps({'source_sha256':hashlib.sha256(f.encode()).hexdigest(),'module_sha256':hashlib.sha256(s.encode()).hexdigest(),'external_operations':mapping,'internal_functions':internal,'qualification':'Current emitted bodies with explicit external operations, typed unwrap and shift-literal ABI correction 8#i32 -> 8#u32 (same numeric shift8); carrier aliases use current Stage2 layouts. No template imported. Source/rejection interpretation and P6 leaf/node lowering remain separate.'},indent=2)+'\n')
