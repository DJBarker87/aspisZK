"""Project exact pre-spawn Vec<ScopedJoinHandle<...>> instantiation."""
from pathlib import Path
import json,sys,hashlib
L=Path(__file__).resolve().parent;R=L.parents[2]
s=(L/'session12_kinds.py').read_text();exec(s[:s.index('kinds={}')])
fn=expand(x['fun_decls'][15]);call=next(z['kind']['Call']['call'] for z in fn['body']['Structured']['body']['statements'] if z['id']==3398)
element=call['func']['Regular']['generics']['types'][0]
def subst(z,types):
 if isinstance(z,dict):
  if set(z)=={'TypeVar'} and 'Free' in z['TypeVar']:return types[z['TypeVar']['Free']]
  return {k:subst(v,types) for k,v in z.items()}
 if isinstance(z,list):return [subst(v,types) for v in z]
 return z
def field(i,n):return expand(x['type_decls'][i]['kind']['Struct'][n]['ty'])
vec=subst(expand(x['fun_decls'][164]['signature']['output']),[element]);rawvec=subst(field(0,0),vec['Adt']['generics']['types']);inner=subst(field(7,0),rawvec['Adt']['generics']['types']);marker=subst(field(7,1),rawvec['Adt']['generics']['types'])
kinds={k:{'Adt':[v['Adt'],None,None]} for k,v in [('vectorKind',vec),('rawKind',rawvec),('innerKind',inner),('markerKind',marker)]}
src='\n'.join(['import PV_LIB_SPEC_NativeChecks14','set_option autoImplicit false','namespace PV_LIB_SPEC_VectorKinds14','open PV_STX2_Syntax']+['def '+k+' : Data := '+data(v) for k,v in kinds.items()]+['#print axioms '+k for k in kinds]+['end PV_LIB_SPEC_VectorKinds14',''])
record={'revision':rev,'source':path,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'caller':15,'statement':3398,'kinds':kinds}
for p,t in [(R/'lean/PV_LIB_SPEC_VectorKinds14.lean',src),(L/'SESSION14_VECTOR_SOURCE.json',json.dumps(record,indent=2)+'\n')]:
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print('PASS frozen3398 vector result tags')
