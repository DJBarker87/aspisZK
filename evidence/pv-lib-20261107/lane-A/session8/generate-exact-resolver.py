"""Generate exact no-clause Destruct method selection from retained LLBC.
Constrained impls and unsupported shapes are retained as missing, never guessed.
"""
from pathlib import Path
import ast,hashlib,json,lzma,sys
E=Path('evidence/pv-lib-20261107/lane-A/session8');S=Path('evidence/pv-lib-20261107/lane-A/session5/thread-llbc.json.xz');p=json.loads(lzma.decompress(S.read_bytes()))['translated'];d={}
def walk(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:i,v=x['HashConsedValue'];d[i]=v
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(p)
def normal(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:return normal(x['HashConsedValue'][1])
  if 'Deduplicated'in x:return normal(d[x['Deduplicated']])
  return {k:normal(v) for k,v in x.items()}
 if isinstance(x,list):return list(map(normal,x))
 return x
ns={'json':json};src=Path('evidence/pv-lib-20261107/lane-A/session7/generate-intermediate-d685.py.txt').read_text();exec(compile(ast.Module(body=[n for n in ast.parse(src).body if isinstance(n,ast.FunctionDef)],type_ignores=[]),'helper','exec'),ns)
rows=[];impl=[];adt=[];templates=[]
for x in p['trait_impls']:
 if x['impl_trait']['id']!=5:continue
 i=x['def_id'];g=x['generics'];methods=x['methods'];assert len(methods)==1
 method=methods[0];fid=method['skip_binder']['id'];ty=normal(x['impl_trait']['generics']['types'][0]);r=dict(impl=i,function=fid,type=ty,types=len(g['types']),regions=len(g['regions']),selected=False)
 if not g['trait_clauses'] and not g['const_generics'] and not method['params']['types'] and not method['params']['trait_clauses']:
  assert len(method['params']['regions'])==1
  r['selected']=True;templates.append('  | '+str(i)+' => some ('+ns['data'](normal(method['skip_binder']['generics']))+')');impl.append('  | '+str(i)+' => some ('+str(fid)+', '+str(len(g['types']))+', '+str(len(g['regions']))+')')
  if 'Adt'in ty:
   a=ty['Adt'];tg=a['generics']
   if tg['types']!=[{'TypeVar':{'Free':n}}for n in range(len(g['types']))] or tg['trait_refs'] or tg['const_generics']:
    r['by_type']='UNSUPPORTED nontrivial impl pattern';rows.append(r);continue
   adt.append('  | '+ns['data'](a['id'])+' => some '+str(i))
 rows.append(r)
text='\n'.join(['import PV_LIB_A_TypedDestruct','set_option autoImplicit false','namespace PV_LIB_A_ExactDestructMethods','open PV_STX2_Syntax PV_LIB_A_CellSetBegin PV_LIB_A_TypedDestruct','/- Exact Destruct::drop_glue method0 mappings from retained thread LLBC. -/','def implementation : Nat → Option (Nat × Nat × Nat)',*impl,'  | _ => none','def methodGenerics : Nat → Option Data',*templates,'  | _ => none','def adtImpl : Data → Option Nat',*adt,'  | _ => none', '''
def concrete (id : Nat) (g : Generics) : Option Resolution := do
  let (fid,types,regions) ← implementation id
  if g.types.length = types ∧ g.regions.length = regions ∧
      g.constants = [] ∧ g.traits = [] then
    let template ← methodGenerics id
    let instantiated ← substitute 64 g.types template
    let method ← generics instantiated
    pure (.call (fnPtr fid {method with regions := g.regions ++ [.atom "Erased"]}))
  else none

/-- UntrackedDestruct dispatch uses the actual normalized type. Constrained
impls, unknown types, slices and dynamic vtables remain explicitly unbound. -/
def byType (ty : Data) : Option Resolution := do
  match ty with
  | .object [("Literal",_)] => pure .noop
  | .object [("Ref",_)] => pure .noop
  | .object [("RawPtr",_)] => pure .noop
  | .object [("Adt",a)] =>
    let id ← member "id" a
    let raw ← member "generics" a
    let g ← generics raw
    let i ← adtImpl id
    concrete i g
  | _ => none

/-- One named resolver for the exact emitted Destruct witness. No-op requires
NoopDestruct itself; UntrackedDestruct does not imply no-op. -/
def resolve (ty witness : Data) : Option Resolution := do
  let kind ← member "kind" witness
  match member "TraitImpl" kind with
  | some impl =>
    let .number id ← member "id" impl | none
    let raw ← member "generics" impl
    let g ← generics raw
    concrete id g
  | none =>
    let builtin ← member "BuiltinOrAuto" kind
    match member "builtin_data" builtin with
    | some (.atom "NoopDestruct") => pure .noop
    | some (.atom "UntrackedDestruct") => byType ty
    | _ => none

/-- A concrete method uses the exact emitted type arguments, including default
allocator parameters. It is not the argument list on the enclosing ADT. -/
theorem method_types (fid : Nat) (g : Generics) :
    member "types" (encode g) = some (.array g.types) := rfl

#print axioms implementation
#print axioms adtImpl
#print axioms concrete
#print axioms byType
#print axioms resolve
#print axioms method_types
#print axioms methodGenerics
end PV_LIB_A_ExactDestructMethods
'''])
q=Path('lean/PV_LIB_A_ExactDestructMethods.lean');manifest=dict(input=str(S),input_sha256=hashlib.sha256(S.read_bytes()).hexdigest(),source=str(q),source_sha256=hashlib.sha256(text.encode()).hexdigest(),implementations=rows,images_defined=0)
if '--check'in sys.argv:assert q.read_text()==text;assert json.loads((E/'EXACT_DESTRUCT_METHODS.json').read_text())==manifest
else:q.write_text(text);(E/'EXACT_DESTRUCT_METHODS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(impl),'concrete methods; remaining explicit in manifest')
