"""Project frozen hook result types and instantiate their finite source fields."""
from pathlib import Path
import json,hashlib,sys,copy
L=Path(__file__).resolve().parent;R=L.parents[2]
s=(L/'session12_kinds.py').read_text();exec(s[:s.index('kinds={}')])
def fields(i):return expand(x['type_decls'][i]['kind']['Struct'])
def kind(ty,v=None):return {'Adt':[ty['Adt'],v,None]}
def subst(z,types):
 if isinstance(z,dict):
  if set(z)=={'TypeVar'} and 'Free' in z['TypeVar']:return types[z['TypeVar']['Free']]
  return {k:subst(v,types) for k,v in z.items()}
 if isinstance(z,list):return [subst(v,types) for v in z]
 return z
child=expand(x['fun_decls'][453]['signature']['output']);hooks=fields(130)[0]['ty'];vec=fields(130)[1]['ty'];opt=fields(142)[0]['ty']
rawvec=subst(fields(0)[0]['ty'],vec['Adt']['generics']['types'])
inner=subst(fields(7)[0]['ty'],rawvec['Adt']['generics']['types']);marker=subst(fields(7)[1]['ty'],rawvec['Adt']['generics']['types'])
# RawVecInner is non-generic except the removed allocator argument.
inner_fields=fields(18)
print('RawVecInner fields:',[(f['name'],f['ty']) for f in inner_fields])
kinds={k:kind(v) for k,v in [('childKind',child),('hooksKind',hooks),('vectorKind',vec),('rawKind',rawvec),('innerKind',inner),('markerKind',marker)]}
kinds['noneKind']=kind(opt,0)
text='\n'.join(['import PV_LIB_SPEC_StackSize14','set_option autoImplicit false','namespace PV_LIB_SPEC_HookKinds14','open PV_STX2_Syntax']+['def '+k+' : Data := '+data(v) for k,v in kinds.items()]+['#print axioms '+k for k in kinds]+['end PV_LIB_SPEC_HookKinds14',''])
record={'source_revision':rev,'source_path':path,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'kinds':kinds,'raw_inner_fields':inner_fields}
for p,t in [(R/'lean/PV_LIB_SPEC_HookKinds14.lean',text),(L/'SESSION14_HOOK_SOURCE.json',json.dumps(record,indent=2)+'\n')]:
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
