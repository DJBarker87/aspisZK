"""Adversarial LLBC mutations, never a substitute native-source extraction.
Each backend invocation counts separately; all operation cases share one crate.
"""
from pathlib import Path
import json,copy,hashlib
D=Path(__file__).resolve().parent
j=json.loads((D/'ProverRwRngExtractorsynthetic.llbc').read_text()); cache={}
def expand(x):
 if isinstance(x,list):return [expand(v) for v in x]
 if not isinstance(x,dict):return x
 if 'HashConsedValue' in x:
  k,v=x['HashConsedValue']; v=expand(v);cache[k]=v;return {'ExpandedTy':v}
 if 'Deduplicated' in x:return {'ExpandedTy':copy.deepcopy(cache[x['Deduplicated']])}
 return {k:expand(v) for k,v in x.items()}
j=expand(j);t=j['translated'];pattern=copy.deepcopy(t['type_decls'][6]['kind']['Struct'][0]['ty']);i32={'ExpandedTy':{'Literal':{'Int':'I32'}}};boolean={'ExpandedTy':{'Literal':'Bool'}}
place=lambda i,ty:dict(kind={'Local':i},ty=ty)
base=copy.deepcopy(t['fun_decls'][2]);span=base['body']['Structured']['span'];counter=10000

def function(name,inp,out,kinds):
 global counter
 f=copy.deepcopy(base);idx=len(t['fun_decls']);f['def_id']=idx
 f['item_meta']['name']=[{'Ident':['prover_rw_rng_extractor',0]},{'Ident':[name,0]}]
 f['item_meta']['source_text']='Adversarial LLBC mutation: '+name
 f['signature']['inputs']=[inp];f['signature']['output']=out
 b=f['body']['Structured']; b['locals']={'arg_count':1,'locals':[dict(index=i,name=None,span=span,ty=ty) for i,ty in enumerate([out,inp,inp])]}
 kinds=[{'StorageLive':0},{'StorageLive':2},*kinds,'Return']
 b['body']['statements']=[]
 for k in kinds:
  counter+=1;b['body']['statements'].append(dict(span=span,id=counter,kind=k,comments_before=[]))
 t['fun_decls'].append(f);t['ordered_decls'].append({'Fun':{'NonRec':idx}});t['item_names'].append(dict(key={'Fun':idx},value=f['item_meta']['name']))
 return f
assign=lambda dest,rvalue:{'Assign':[dest,rvalue]}
use=lambda i,ty:{'Use':[{'Move':place(i,ty)},'Yes']}
# Direct leaf operations must never gain a proof or implicit scalar coercion.
function('negative_compare',pattern,boolean,[assign(place(0,boolean),{'BinaryOp':['Eq',{'Copy':place(1,pattern)},{'Copy':place(1,pattern)}]})])
function('negative_cast',pattern,i32,[assign(place(0,i32),{'UnaryOp':[{'Cast':{'Scalar':[{'Int':'I32'},{'Int':'I32'}]}},{'Move':place(1,pattern)}]})])
function('negative_mutate',pattern,pattern,[assign(place(0,pattern),{'UnaryOp':['Not',{'Move':place(1,pattern)}]})])
function('negative_transmute_out',pattern,i32,[assign(place(0,i32),{'UnaryOp':[{'Cast':{'Transmute':[pattern,i32]}},{'Move':place(1,pattern)}]})])
function('negative_transmute_in',i32,pattern,[assign(place(0,pattern),{'UnaryOp':[{'Cast':{'Transmute':[i32,pattern]}},{'Move':place(1,i32)}]})])
# Missing assignment and double move must preserve Bottom handling.
function('negative_uninitialized',pattern,pattern,[assign(place(0,pattern),use(2,pattern))])
function('negative_moved',pattern,pattern,[assign(place(2,pattern),use(1,pattern)),assign(place(0,pattern),use(1,pattern))])
# A literal with refined type must not manufacture membership, including zero.
for n in ['0','1']:
 c=dict(kind={'Literal':{'Scalar':{'Signed':['I32',n]}}},ty=pattern)
 function('negative_construct_'+n,pattern,pattern,[assign(place(0,pattern),{'Use':[{'Const':c},'Yes']})])
# Serialize a fresh, consistent hashcons table after mutation.
ids={}
def pack(x):
 if isinstance(x,list):return [pack(v) for v in x]
 if not isinstance(x,dict):return x
 if 'ExpandedTy' in x:
  v=x['ExpandedTy'];key=json.dumps(v,sort_keys=True)
  if key in ids:return {'Deduplicated':ids[key]}
  idx=len(ids);ids[key]=idx;return {'HashConsedValue':[idx,pack(v)]}
 return {k:pack(v) for k,v in x.items()}
p=D/'ProverRwRngExtractornegative007.llbc';p.write_text(json.dumps(pack(j),separators=(',',':'))+'\n')
(D/'negative007-input.json').write_text(json.dumps(dict(parent_sha256=hashlib.sha256((D/'ProverRwRngExtractorsynthetic.llbc').read_bytes()).hexdigest(),input_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),cases=[x['item_meta']['name'][-1] for x in t['fun_decls'][len(t['fun_decls'])-9:]],scope='Mutated LLBC robustness probes; no native source claim'),indent=2)+'\n')
