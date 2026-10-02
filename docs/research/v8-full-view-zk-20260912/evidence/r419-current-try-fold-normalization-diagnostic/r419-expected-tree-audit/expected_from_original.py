#!/usr/bin/env python3
"""Generate a full expected decoded LLBC tree from immutable R396 only."""
import copy, hashlib, importlib.util, json, re
from pathlib import Path
ROOT=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
HERE=ROOT/'.r21-scratch/r419-try-fold-equality-elimination/audit'
SRC=ROOT/'docs/research/v8-full-view-zk-20260912/evidence/r405-generic-batch-translation-frontier/provenance/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc'
CENSUS=ROOT/'.r21-scratch/r418-binder-substitution-preflight/decoded-reference-census.json'
SRC_SHA='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
CENSUS_SHA='35795e54a400bbcdbde24967d6919c65f35750074da60299e6d2d03a422146e8'
EMPTY={'regions':[],'types':[],'const_generics':[],'trait_refs':[]}
FUN_SLOTS={58:(1,'B'),120:(2,'Acc'),169:(1,'B')}
METHOD_ROWS=[('trait_decls',0),('trait_impls',2),('trait_impls',4),('trait_impls',11),('trait_impls',15)]
spec=importlib.util.spec_from_file_location('cmp',HERE/'compare_llbc_hardened.py')
cmp=importlib.util.module_from_spec(spec); spec.loader.exec_module(cmp)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(SRC)==SRC_SHA, 'R396 immutable input hash mismatch'
raw=json.loads(SRC.read_text()); table={}; cmp.collect_hashcons(raw,table); original=cmp.decode(raw,table)
expected=copy.deepcopy(original); trace=[]

def is_binder(x): return isinstance(x,dict) and 'skip_binder' in x and ('regions' in x or 'params' in x)
def path_get(root,path):
 for k in path: root=root[k]
 return root
def parse_census_path(s):
 return [a if a else int(b) for a,b in re.findall(r'\.([A-Za-z_][A-Za-z_0-9]*)|\[(\d+)\]',s)]

def transform_bound_refs(x,delta,depth=0):
 """Move a term through one empty binder; all bound namespaces shift capture-avoidably."""
 if isinstance(x,dict):
  if set(x)=={'Bound'}:
   pair=x['Bound']
   if not isinstance(pair,list) or len(pair)!=2 or any(type(q)is not int for q in pair): raise ValueError(f'bad de Bruijn pair {pair!r}')
   db,idx=pair
   cutoff=depth if delta>0 else depth+1
   return {'Bound':[db+delta,idx]} if db>=cutoff else copy.deepcopy(x)
  if is_binder(x): return {k:transform_bound_refs(v,delta,depth+1 if k=='skip_binder' else depth) for k,v in x.items()}
  return {k:transform_bound_refs(v,delta,depth) for k,v in x.items()}
 if isinstance(x,list): return [transform_bound_refs(v,delta,depth) for v in x]
 return copy.deepcopy(x)

def typevar(x):
 if not isinstance(x,dict) or set(x)!={'TypeVar'}: return None
 t=x['TypeVar']
 if isinstance(t,dict) and len(t)==1 and 'Free'in t and type(t['Free'])is int:return ('Free',t['Free'])
 if isinstance(t,dict) and len(t)==1 and 'Bound'in t and isinstance(t['Bound'],list) and len(t['Bound'])==2 and all(type(q)is int for q in t['Bound']):return ('Bound',t['Bound'][0],t['Bound'][1])
 raise ValueError(f'unsupported TypeVar form: {x!r}')

def target_occurs(x,mode,slot,depth=0):
 tv=typevar(x)
 if tv and ((mode=='Free' and tv==('Free',slot)) or (mode=='Bound' and tv==('Bound',depth,slot))): return True
 if isinstance(x,dict): return any(target_occurs(v,mode,slot,depth+1 if is_binder(x) and k=='skip_binder' else depth) for k,v in x.items())
 if isinstance(x,list): return any(target_occurs(v,mode,slot,depth) for v in x)
 return False

def reindex_proj(x,mode,slot,depth=0):
 tv=typevar(x)
 if tv:
  if mode=='Free' and tv[1]>slot:return {'TypeVar':{'Free':tv[1]-1}}
  if mode=='Bound' and tv[1]==depth and tv[2]>slot:return {'TypeVar':{'Bound':[depth,tv[2]-1]}}
  return copy.deepcopy(x)
 if isinstance(x,dict):return {k:reindex_proj(v,mode,slot,depth+1 if is_binder(x) and k=='skip_binder' else depth) for k,v in x.items()}
 if isinstance(x,list):return [reindex_proj(v,mode,slot,depth) for v in x]
 return copy.deepcopy(x)

def lift_proj(x,amount,depth=0):
 if isinstance(x,dict):
  if set(x)=={'Bound'}:
   db,idx=x['Bound']; return {'Bound':[db+amount,idx]} if db>=depth else copy.deepcopy(x)
  return {k:lift_proj(v,amount,depth+1 if is_binder(x) and k=='skip_binder' else depth) for k,v in x.items()}
 if isinstance(x,list):return [lift_proj(v,amount,depth) for v in x]
 return copy.deepcopy(x)

def map_vars(x,mode,slot,proj,depth=0,path=()):
 tv=typevar(x)
 if tv:
  hit=(mode=='Free' and tv==('Free',slot)) or (mode=='Bound' and tv==('Bound',depth,slot))
  if hit:
   trace.append({'op':'substitute_target_TypeVar','path':list(path),'mode':mode,'slot':slot,'depth':depth})
   return lift_proj(proj,depth) if mode=='Bound' else copy.deepcopy(proj)
  if mode=='Free' and tv[0]=='Free' and tv[1]>slot:
   trace.append({'op':'reindex_Free_TypeVar','path':list(path),'old':tv[1],'new':tv[1]-1})
   return {'TypeVar':{'Free':tv[1]-1}}
  if mode=='Bound' and tv[0]=='Bound' and tv[1]==depth and tv[2]>slot:
   trace.append({'op':'reindex_Bound_TypeVar','path':list(path),'depth':depth,'old':tv[2],'new':tv[2]-1})
   return {'TypeVar':{'Bound':[depth,tv[2]-1]}}
  return copy.deepcopy(x)
 if isinstance(x,dict):return {k:map_vars(v,mode,slot,proj,depth+1 if is_binder(x) and k=='skip_binder' else depth,path+(k,)) for k,v in x.items()}
 if isinstance(x,list):return [map_vars(v,mode,slot,proj,depth,path+(i,)) for i,v in enumerate(x)]
 return copy.deepcopy(x)

def proj_from_params(params,label):
 cs=params.get('trait_type_constraints')
 if not isinstance(cs,list) or len(cs)!=1:raise ValueError(f'{label}: expected exactly one constraint')
 rb=cs[0]
 if rb.get('regions')!=[]:raise ValueError(f'{label}: constraint RegionBinder not empty')
 c=rb.get('skip_binder')
 if not isinstance(c,dict) or not {'trait_ref','type_id','ty'}<=set(c) or type(c['type_id'])is not int:raise ValueError(f'{label}: malformed constraint')
 return {'TraitType':[copy.deepcopy(c['trait_ref']),c['type_id'],copy.deepcopy(EMPTY)]}

def verify_drop_constraint(params,label):
 if len(params.get('trait_type_constraints',[]))!=1:raise ValueError(f'{label}: constraint count changed before reflexivity check')
 rb=params['trait_type_constraints'][0]; c=rb['skip_binder']
 wanted={'TraitType':[copy.deepcopy(c['trait_ref']),c['type_id'],copy.deepcopy(EMPTY)]}
 if c['ty']!=wanted:raise ValueError(f'{label}: transformed equality is not reflexive')
 trace.append({'op':'verify_reflexive_equality','path':label+'.trait_type_constraints[0]','expected':wanted,'actual':copy.deepcopy(c['ty'])})
 params['trait_type_constraints'].pop(0)
 trace.append({'op':'drop_singleton_constraint','path':label+'.trait_type_constraints[0]'})

def drop_param(params,slot,name,label):
 ts=params.get('types')
 if not isinstance(ts,list) or slot>=len(ts) or ts[slot].get('index')!=slot or ts[slot].get('name')!=name:raise ValueError(f'{label}: source slot/name mismatch')
 old=copy.deepcopy(ts[slot]); del ts[slot]
 for i,p in enumerate(ts):
  if p.get('index')!=(i if i<slot else i+1):raise ValueError(f'{label}: bad original type indices')
  p['index']=i
 trace.append({'op':'drop_type_parameter','path':label+'.types','index':slot,'removed':old})

def transform_fun(fid,slot,name):
 rows=expected['translated']['fun_decls']; ix=next((i for i,r in enumerate(rows) if isinstance(r,dict) and r.get('def_id')==fid),None)
 if ix is None:raise ValueError(f'missing Fun{fid}')
 row=rows[ix]; params=row['generics']
 if len(params.get('types',[]))<=slot or params['types'][slot].get('name')!=name:raise ValueError(f'Fun{fid}: wrong target slot')
 proj=proj_from_params(params,f'Fun{fid}')
 if target_occurs(proj,'Free',slot):raise ValueError(f'Fun{fid}: projection depends on target Free type')
 proj=transform_bound_refs(proj,-1); proj=reindex_proj(proj,'Free',slot)
 row=map_vars(row,'Free',slot,proj,path=('translated','fun_decls',ix)); rows[ix]=row
 verify_drop_constraint(row['generics'],f'translated.fun_decls[{fid}].generics')
 drop_param(row['generics'],slot,name,f'translated.fun_decls[{fid}].generics')
 trace.append({'op':'transform_function_row','def_id':fid,'slot':slot,'name':name,'projection':proj})

def transform_method(table,ident):
 rows=expected['translated'][table]; ix=next((i for i,r in enumerate(rows) if isinstance(r,dict) and r.get('def_id')==ident),None)
 if ix is None:raise ValueError(f'missing {table}:{ident}')
 m=rows[ix]['methods'][36]; params=m['params']
 if not params.get('types') or params['types'][0].get('name')!='B':raise ValueError(f'{table}:{ident}: method36 type slot0 is not B')
 proj=proj_from_params(params,f'{table}:{ident}.method36')
 proj=transform_bound_refs(proj,-1)
 if target_occurs(proj,'Bound',0):raise ValueError(f'{table}:{ident}: projection depends on outer method B')
 proj=reindex_proj(proj,'Bound',0)
 # Method-level binder is the ambient Bound0 context; nested Binder/RegionBinder nodes count.
 m['params']=map_vars(params,'Bound',0,proj,path=('translated',table,ix,'methods',36,'params'))
 m['skip_binder']=map_vars(m['skip_binder'],'Bound',0,proj,path=('translated',table,ix,'methods',36,'skip_binder'))
 verify_drop_constraint(m['params'],f'translated.{table}[{ident}].methods[36].params')
 drop_param(m['params'],0,'B',f'translated.{table}[{ident}].methods[36].params')
 trace.append({'op':'transform_method_row','table':table,'def_id':ident,'method_id':36,'slot':0,'projection':proj})

def main():
 census=json.loads(CENSUS.read_text()); census_sha=sha(CENSUS)
 if census_sha!=CENSUS_SHA: raise ValueError('R418 census fingerprint mismatch')
 # Only original decoded tree plus census identities drive edits; candidate is never opened.
 direct=census['direct_fun_decl_refs_id58']
 refs=[]
 for row in direct:
  fid=row['fun_decl_id']; slot,arity={58:(1,5),120:(2,6),169:(1,5)}[fid]
  if row['arity']['types']!=arity:raise ValueError('R418 direct ref arity mismatch')
  path=('translated',)+tuple(parse_census_path(row['path']))
  ref=path_get(expected,path); g=ref.get('generics')
  if ref.get('id')!=fid or len(g.get('types',[]))!=arity:raise ValueError(f'direct ref path/id/arity mismatch: {path}')
  refs.append((path,fid,slot,arity))
 if len(refs)!=5 or {fid:sum(1 for _,f,_,_ in refs if f==fid) for fid in (58,120,169)}!={58:3,120:1,169:1}:raise ValueError('direct ref census mismatch')
 dispatch=[]
 for row in census['trait_dispatch_calls_method36']:
  if row['method_id']!=36 or row['arity']['types']!=3:raise ValueError('method dispatch census mismatch')
  path=('translated',)+tuple(parse_census_path(row['path'])); call=path_get(expected,path)
  kind=call.get('kind',{}).get('Trait')
  if not isinstance(kind,list) or len(kind)!=2 or kind[1]!=36 or kind[0].get('trait_decl_ref',{}).get('skip_binder',{}).get('id')!=0:raise ValueError('dispatch is not Iterator.method36')
  dispatch.append(path)
 if len(dispatch)!=4:raise ValueError('expected four method36 refs')
 # Transform only the five declaration binders, using exact R396 rows.
 for fid,(slot,name) in FUN_SLOTS.items():transform_fun(fid,slot,name)
 for table,ident in METHOD_ROWS:transform_method(table,ident)
 # Remove only the exact inventoried argument positions, with original arity/id guards.
 for path,fid,slot,arity in refs:
  ref=path_get(expected,path); types=ref['generics']['types']
  if len(types)!=arity:raise ValueError(f'edited direct ref arity changed at {path}')
  removed=copy.deepcopy(types[slot]);del types[slot]
  trace.append({'op':'drop_direct_FunDeclRef_argument','path':list(path)+['generics','types'],'fun_id':fid,'index':slot,'removed':removed,'arity_before':arity,'arity_after':len(types)})
 for path in dispatch:
  types=path_get(expected,path)['generics']['types']
  if len(types)!=3:raise ValueError('edited method dispatch arity changed')
  removed=copy.deepcopy(types[0]);del types[0]
  trace.append({'op':'drop_Iterator_method36_argument','path':list(path)+['generics','types'],'index':0,'removed':removed,'arity_before':3,'arity_after':2})
 out=HERE/'expected-delta';out.mkdir(exist_ok=True)
 tree=out/'R419ExpectedDecodedFromOriginalR396.json';tree.write_text(json.dumps(expected,indent=2,ensure_ascii=False)+'\n')
 tracefile=out/'operation-trace.json';tracefile.write_text(json.dumps({'classification':'independent expected tree built from frozen original only; candidate not read','original_sha256':SRC_SHA,'r418_census_sha256':census_sha,'operation_count':len(trace),'operations':trace},indent=2,ensure_ascii=False)+'\n')
 manifest={'classification':'expected delta generation; no transform applied to real/compiler AST; not a source-correspondence result','original_sha256':SRC_SHA,'r418_census_sha256':census_sha,'expected_tree_sha256':sha(tree),'expected_tree_bytes':tree.stat().st_size,'operation_trace_sha256':sha(tracefile),'operation_count':len(trace),'candidate_read':False,'edited_declaration_rows':{'functions':[58,120,169],'trait_decl_method':[0,36],'trait_impl_methods':[[2,36],[4,36],[11,36],[15,36]]},'known_limits':['This JSON visitor is a review draft of the lead-specified binder formula, not the pinned Rust AST implementation.','No candidate output was used to choose paths or expected values.','Any unsupported binder/index shape aborts generation.']}
 (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps(manifest,indent=2))
if __name__=='__main__':main()
