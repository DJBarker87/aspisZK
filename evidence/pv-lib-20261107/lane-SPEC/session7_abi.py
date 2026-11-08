"""Read-only projection of frozen N95807 and adopted binary. No extraction/build."""
from pathlib import Path
import subprocess,json,lzma,hashlib,sys
L=Path(__file__).resolve().parent
rev='41e76d01fdead952101594b8b0f36a7561d180f2' # read-only source snapshot; N95807 content pin below
p='evidence/pv-evhB-20261103/thread-line/generated/N95807/OrderedFamilies.llbc.xz'
raw=lzma.decompress(subprocess.check_output(['git','show',rev+':'+p]));root=json.loads(raw);x=root['translated'];hs={}
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
assert root['has_errors'] is False
assert x['target_information']==[{'key':'x86_64-unknown-linux-gnu','value':{'target_pointer_size':8,'is_little_endian':True}}]
ls=x['fun_decls'][170]['body']['Structured']['locals']['locals']
metadata={name:expand(ls[i]['ty'])['Adt'] for name,i in [('optionType',6),('resultType',5),('flowType',4),('residualType',12)]}
atomic=expand(x['fun_decls'][121]['signature']['output'])['Adt'];assert atomic['id']=={'Adt':57}
metadata['atomicKind']={'Adt':[atomic,None,None]}
metadata['unsafeCellKind']={'Adt':[{'id':{'Adt':116},'generics':{'regions':[],'types':[{'Literal':{'UInt':'Usize'}}],'const_generics':[],'trait_refs':[]}},None,None]}
assert [f['name'] for f in x['type_decls'][68]['kind']['Struct']]==['strong','weak','data']
assert [f['name'] for f in x['type_decls'][112]['kind']['Struct']]==['scope','result','_marker']
report={'llbc_git_revision':subprocess.check_output(['git','rev-parse',rev],text=True).strip(),'llbc_path':p,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'target':x['target_information'],'metadata':metadata,'atomic_type_name':x['type_decls'][57]['item_meta']['name'],'unsafe_cell_type_name':x['type_decls'][116]['item_meta']['name'],'arc_fields':expand(x['type_decls'][68]['kind']),'packet_fields':expand(x['type_decls'][112]['kind']),'binary_sha256':'fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558','binary_cut':[0xe057a,0xe05b7],'layout':{'width':48,'alignment':8,'strongOffset':0,'weakOffset':8,'dataOffset':16,'dataWidth':32},'initial_write_words':{'0':1,'8':1,'16':'scope pointer (r14)','24':2**63+2},'unwritten_byte_offsets':[32,48],'qualification':'Exact adopted x86_64 binary writes, not compiler correctness, source reachability or full OwnInit nonemptiness.'}
def data(z):
 if z is None:return '.null'
 if isinstance(z,bool):return '.boolean '+str(z).lower()
 if isinstance(z,int):return '.number '+str(z)
 if isinstance(z,str):return '.atom '+json.dumps(z)
 if isinstance(z,list):return '.array ['+', '.join('('+data(a)+')' for a in z)+']'
 return '.object ['+', '.join('('+json.dumps(k)+', ('+data(v)+'))' for k,v in z.items())+']'
text='\n'.join(['import PV_LIB_SPEC_NativeRuntime','set_option autoImplicit false','namespace PV_LIB_SPEC_FrozenABI','open PV_STX2_Syntax', '/-- Concrete metadata projected from frozen N95807; no ABI parameter. -/']+['def '+k+' : Data := '+data(v) for k,v in metadata.items()]+['#print axioms '+k for k in metadata]+['end PV_LIB_SPEC_FrozenABI',''])
outputs={L/'SESSION7_ABI_SOURCE.json':json.dumps(report,indent=2)+'\n',Path('lean/PV_LIB_SPEC_FrozenABI.lean'):text}
for path,s in outputs.items():
 if '--check' in sys.argv:assert path.read_text()==s,str(path)
 else:path.write_text(s)
print('PASS: frozen metadata projection; ABI byte image is sparse; exact association with the old total image is checked separately')
