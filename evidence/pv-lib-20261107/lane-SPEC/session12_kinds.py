"""Project exact constructor result metadata; no extraction or source mutation."""
import pathlib,subprocess,json,lzma,hashlib,sys
L=pathlib.Path(__file__).resolve().parent
rev='41e76d01fdead952101594b8b0f36a7561d180f2';path='evidence/pv-evhB-20261103/thread-line/generated/N95807/OrderedFamilies.llbc.xz'
raw=lzma.decompress(subprocess.check_output(['git','show',rev+':'+path]));x=json.loads(raw)['translated'];hs={}
def collect(z):
 if isinstance(z,dict):
  if 'HashConsedValue' in z:hs[z['HashConsedValue'][0]]=z['HashConsedValue'][1]
  for v in z.values():collect(v)
 elif isinstance(z,list):
  for v in z:collect(v)
collect(x)
def expand(z):
 if isinstance(z,dict):
  if 'HashConsedValue' in z:return expand(z['HashConsedValue'][1])
  if 'Deduplicated' in z:return expand(hs[z['Deduplicated']])
  return {k:expand(v) for k,v in z.items()}
 if isinstance(z,list):return [expand(v) for v in z]
 return z
def data(z):
 if z is None:return '.null'
 if isinstance(z,bool):return '.boolean '+str(z).lower()
 if isinstance(z,int):return '.number '+str(z)
 if isinstance(z,str):return '.atom '+json.dumps(z)
 if isinstance(z,list):return '.array ['+', '.join('('+data(a)+')' for a in z)+']'
 return '.object ['+', '.join('('+json.dumps(k)+', ('+data(v)+'))' for k,v in z.items())+']'
kinds={}
for name,i in [('atomicBool',123),('unsafeCell',455),('maybeDangling',456)]:
 out=expand(x['fun_decls'][i]['signature']['output'])['Adt'];kinds[name]={'Adt':[out,None,None]}
# AtomicBool.v is UnsafeCell<bool>, unlike AtomicUsize's UnsafeCell<usize>.
a=expand(x['fun_decls'][123]['signature']['output'])['Adt']['id']['Adt']
assert x['type_decls'][a]['kind']=='Opaque'
cell={'id':{'Adt':116},'generics':{'regions':[],'types':[{'Literal':'Bool'}],'const_generics':[],'trait_refs':[]}}
kinds['boolCell']={'Adt':[cell,None,None]}
text='\n'.join(['import PV_LIB_SPEC_NativeModel','set_option autoImplicit false','namespace PV_LIB_SPEC_NativeKinds','open PV_STX2_Syntax']+['def '+k+' : Data := '+data(v) for k,v in kinds.items()]+['#print axioms '+k for k in kinds]+['end PV_LIB_SPEC_NativeKinds',''])
report={'source_revision':rev,'source_path':path,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'metadata':kinds,'functions':{str(i):x['fun_decls'][i]['item_meta']['name'] for i in [123,455,456]},'limits':'Three result tags are exact LLBC. boolCell is an UNUSED historical incorrect UnsafeCell<bool> tag, not an extracted opaque field. NativeConstructors.boolCell supplies u8. No successful original history or physical correspondence.'}
for p,s in [(pathlib.Path('lean/PV_LIB_SPEC_NativeKinds.lean'),text),(L/'SESSION12_NATIVE_SOURCE.json',json.dumps(report,indent=2)+'\n')]:
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('PASS retained LLBC result tags; unused historical boolCell mistake explicitly recorded (SPEC-C9)')
