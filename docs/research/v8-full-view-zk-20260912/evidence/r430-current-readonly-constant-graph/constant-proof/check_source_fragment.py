#!/usr/bin/env python3
"""Check exact R429 readonly graph, recording primitive/layout trust boundary."""
import pathlib,json,hashlib,sys
H=pathlib.Path(__file__).resolve().parent;W=next(p for p in H.parents if (p/'.git').exists())
P=pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else W/'.r21-scratch/r429-actual-freeze-fold/root-launch-c/saved-output/R429ActualFreezeFold.llbc'
raw=P.read_bytes();sha=hashlib.sha256(raw).hexdigest();assert sha=='c7c658bff6e44b6bf8397ea1bc7d37f05f3d33810cffc72ae5eaa0bff06d7465'
D=json.loads(raw);assert D['has_errors'] is False;T=D['translated'];checks=[]
def check(name,v):
 checks.append({'check':name,'pass':bool(v)})
 assert v,name
F={x['def_id']:x for x in T['fun_decls'] if x};G={x['def_id']:x for x in T['global_decls'] if x};Y={x['def_id']:x for x in T['type_decls'] if x}
def names(x):return [p['Ident'][0] for p in x['item_meta']['name'] if 'Ident' in p]
def kinds(f):return [s['kind'] for s in f['body']['Structured']['body']['statements']]
def callfun(x):return x['kind']['Fun']['Regular']
def emptygen(x):return x=={'regions':[],'types':[],'const_generics':[],'trait_refs':[]}
check('native target x86_64 little endian/64-bit pointers',T['target_information']==[{'key':'x86_64-unknown-linux-gnu','value':{'target_pointer_size':8,'is_little_endian':True}}])
check('QM31 selected type identity',names(Y[2])==['aspis_core','field','QM31'])
l=Y[2]['layout'];check('exact captured QM31 size/align',len(l)==1 and l[0]['key']=='x86_64-unknown-linux-gnu' and l[0]['value']['size']==16 and l[0]['value']['align']==4)
check('intrinsic exact name/body',names(F[153])==['core','intrinsics','size_of'] and F[153]['body']=={'Intrinsic':{'name':'size_of','arg_names':[]}} and F[153]['signature']['inputs']==[])
# Resolve all type hashcons values, rejecting inconsistent reuse.
HCONS={}
def walk(x):
 if isinstance(x,dict):
  if 'HashConsedValue' in x:
   i,v=x['HashConsedValue'];check(f'hashcons {i} consistent',i not in HCONS or HCONS[i]==v);HCONS[i]=v
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(T)
def resolve(x):
 if isinstance(x,dict) and 'Deduplicated' in x:return resolve(HCONS[x['Deduplicated']])
 if isinstance(x,dict) and 'HashConsedValue' in x:return resolve(x['HashConsedValue'][1])
 if isinstance(x,dict):return {k:resolve(v) for k,v in x.items()}
 if isinstance(x,list):return [resolve(v) for v in x]
 return x
inst=next(x['Instantiated'] for x in F[153]['item_meta']['name'] if 'Instantiated' in x)['skip_binder'];check('size intrinsic actual QM31 instantiation',resolve(inst['types'])==[{'Adt':{'id':{'Adt':2},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}}])
qm31={'Adt':{'id':{'Adt':2},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}}
for entry in [G[31],G[32],F[142],F[145],F[153]]:
 inst=next(x['Instantiated'] for x in entry['item_meta']['name'] if 'Instantiated' in x)
 check(f"entry{entry['def_id']} monomorphic QM31",resolve(inst['skip_binder'])=={'regions':[],'types':[qm31],'const_generics':[],'trait_refs':[]} and all(not v for v in inst['params'].values()))
check('global and initializer scalar result types',resolve(G[31]['ty'])==resolve(F[142]['signature']['output'])=={'Literal':'Bool'} and resolve(G[32]['ty'])==resolve(F[145]['signature']['output'])==resolve(F[153]['signature']['output'])=={'Literal':{'UInt':'Usize'}})
for gid,fid,member in [(31,142,'IS_ZST'),(32,145,'SIZE')]:
 g=G[gid];check(f'global{gid} exact scalar initializer',g['item_meta']['opacity']=='Transparent' and names(g)==['core','mem','SizedTypeProperties',member] and g['value']['kind']=={'Call':[{'kind':{'Fun':{'Regular':fid}},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}},[]]})
 check(f'function{fid} no runtime args',F[fid]['signature']['inputs']==[] and F[fid]['body']['Structured']['locals']['arg_count']==0)
a=kinds(F[145]);check('SIZE initializer exact statement order',len(a)==3 and a[0]=={'StorageLive':0} and a[2]=='Return');c=a[1]['Call'];b=c['call'];check('SIZE initializer empty-arg intrinsic call',callfun(b['func']['Regular'])==153 and emptygen(b['func']['Regular']['generics']) and b['args']==[] and b['dest']['kind']=={'Local':0});check('SIZE unwind retained', [s['kind'] for s in c['on_unwind']['statements']]==['UnwindResume'])
a=kinds(F[142]);check('IS_ZST exact statement order',len(a)==3 and a[0]=={'StorageLive':0} and a[2]=='Return');dest,rv=a[1]['Assign'];op,left,right=rv['BinaryOp'];check('IS_ZST exact equality',dest['kind']=={'Local':0} and op=='Eq' and left['Copy']['kind']=={'Global':{'id':32,'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}} and right['Const']['kind']=={'Literal':{'Scalar':{'Unsigned':['Usize','0']}}});check('IS_ZST operand types scalar usize',resolve(left['Copy']['ty'])==resolve(right['Const']['ty'])=={'Literal':{'UInt':'Usize'}})
# Exact selected scalar reads; this checker does not mutate the native AST.
reads=[]
def readwalk(x,path=''):
 if isinstance(x,dict):
  if 'Copy' in x and isinstance(x['Copy'],dict) and 'Global' in x['Copy'].get('kind',{}) and x['Copy']['kind']['Global']['id'] in [31,32]:reads.append({'path':path,'operand':x})
  for k,v in x.items():readwalk(v,path+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):readwalk(v,path+'/'+str(i))
readwalk(F[70]['body']);check('selected fold contains readonly size-global scalar copies',len(reads)==4)
# Bind the exact successfully compiled Lean input, including the finite model tables.
lean=H/'R430ReadonlyConstantGraph.UNVERIFIED.lean'
leanraw=lean.read_bytes(); leansha=hashlib.sha256(leanraw).hexdigest()
check('exact successful Lean source',leansha=='9bb531624461a6ba3d6605a870f779d5cc603ab670551dd44c3755c718dc7335' and leanraw==(H/'attempt-a/source.lean').read_bytes())
leantext=leanraw.decode()
def table(name,nextname):
 return ' '.join(leantext.split('def '+name+' ',1)[1].split('def '+nextname+' ',1)[0].split('--',1)[0].split())
check('Lean target layout table matches captured type/layout',table('targetLayoutSize','functionBody')=='(typeId : Nat) : Option Usize := if typeId = 2 then some (16#usize) else none')
check('Lean function body table matches checked native graph',table('functionBody','globalInitializer')=='(id : Nat) : Option Expr := if id = 153 then some (.sizeOf 2) else if id = 145 then some (.call 153) else if id = 142 then some (.eq (.global 32) (.literal (.word (0#usize)))) else none')
check('Lean global initializer table matches checked native graph',table('globalInitializer','valueEq')=='(id : Nat) : Option Nat := if id = 32 then some 145 else if id = 31 then some 142 else none')
# Keep compact checks plus source rows; repetitive global hashcons comparisons are summarized.
consistency=[x for x in checks if x['check'].startswith('hashcons')];checks=[x for x in checks if not x['check'].startswith('hashcons')];checks.append({'check':'all hashcons bindings consistent','pass':all(x['pass'] for x in consistency),'occurrences':len(consistency)})
fragment={'source_llbc_sha256':sha,'target':T['target_information'],'functions':[F[i] for i in [142,145,153]],'globals':[G[i] for i in [31,32]],'QM31_type':Y[2],'selected_fold_scalar_reads':reads}
(H/'source-fragment.json').write_text(json.dumps(fragment,indent=2)+'\n')
report={'status':'PASS','checks':checks,'source_llbc':str(P),'source_llbc_sha256':sha,'lean_source_sha256':leansha,'boundary':'Exact constant graph recognition and scalar-copy operand shape. Size-of returns target layout size is an explicit primitive rule of the proposed constant interpreter; this checker does not prove Rust compiler/primitive semantics, pointer behavior, full fold execution, or validate a translator change.','source_fragment_sha256':hashlib.sha256((H/'source-fragment.json').read_bytes()).hexdigest()}
(H/'source-fragment-check.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS',len(checks),'structural checks; primitive boundary explicit')
