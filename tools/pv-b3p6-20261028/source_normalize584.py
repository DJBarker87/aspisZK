"""Scalar projection normalization: immutable NamedConst literals and slice::len.
No opaque return value is inferred. Each rewrite keeps its original source in
receipts. Only the scalar observation is replaced; effects/pointer meaning are
retained separately and are not a whole-body equality claim.
"""
import copy
from initializer_source578 import compact
from frame_indices578 import root,dicts
from fixed_indices572 import literal

def constants(ll,fs):
 out={};bindings=[]
 for g in ll['global_decls']:
  if not g or g['global_kind']!='NamedConst' or not isinstance(g.get('value'),dict):continue
  v=g['value']['kind']
  if not isinstance(v,dict) or 'Call'not in v:continue
  f,args=v['Call'];fid=f.get('kind',{}).get('Fun',{}).get('Regular');body=fs.get(fid,{}).get('body')
  if args or not isinstance(body,dict):continue
  b=body['Structured'];s=compact(b['body']['statements'])
  if b['locals']['arg_count']!=0 or len(s)!=3 or s[0]['kind']!={'StorageLive':0} or s[2]['kind']!='Return':continue
  a=s[1]['kind'].get('Assign')
  if not a or a[0]!={'kind':{'Local':0}} or 'Use'not in a[1]:continue
  op=a[1]['Use'][0]
  if 'Const'not in op or literal(op['Const'])is None:continue
  out[g['def_id']]=copy.deepcopy(op['Const']);bindings.append(dict(global_id=g['def_id'],initializer=fid,value=literal(op['Const']),global_source=g,initializer_source=s))
 return out,bindings

def normalize(body,global_values,parameters=None):
 parameters=parameters or {}
 b=copy.deepcopy(body);changes=[]
 # These caller-supplied fat references are never reassigned, moved, dropped,
 # or exposed by address. Borrowing their POINTEE does not expose the stack
 # slot containing the fat reference and cannot change its length.
 for slot in parameters:
  for x in dicts(b):
   k=x.get('kind')
   if isinstance(k,dict):
    if 'Assign'in k:
     dest,rhs=k['Assign'];assert dest['kind'].get('Local')!=slot,('parameter reassigned',slot)
     for tag in ['Ref','RawPtr']:
      if tag in rhs:assert rhs[tag]['place']['kind'].get('Local')!=slot,('parameter address exposed',slot)
    assert k.get('StorageLive')!=slot,('parameter recreated',slot)
    if 'Drop'in k:assert k['Drop']['place']['kind'].get('Local')!=slot
   if 'Move'in x:assert x['Move']['kind'].get('Local')!=slot,('parameter moved',slot)

 for x in dicts(b):
  for tag in ['Copy','Move']:
   p=x.get(tag)
   if isinstance(p,dict)and 'Global'in p.get('kind',{}):
    gid=p['kind']['Global']['id']
    if gid in global_values:
     changes.append(dict(kind='named_const_scalar',global_id=gid,source=copy.deepcopy(x)))
     x.clear();x['Const']=copy.deepcopy(global_values[gid]);break
 exposed={root(x[tag]['place'])for x in dicts(b)for tag in ('Ref','RawPtr')if tag in x and isinstance(x[tag],dict)and 'place'in x[tag]}
 exposed-=set(parameters)
 def walk(block,initial):
  meta=dict(initial)
  def operand(o):
   for tag in ['Copy','Move']:
    if tag in o and 'Local'in o[tag]['kind']:return meta.get(root(o[tag]))
  def moves(x):
   for n in dicts(x):
    if 'Move'in n:meta.pop(root(n['Move']),None)
  for st in block['statements']:
   k=st['kind'];value=None
   if not isinstance(k,dict):
    if k in ['Return','UnwindResume']:return {},False
    meta={slot:val for slot,val in meta.items()if slot in parameters};continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];value=operand(rhs['Use'][0])if 'Use'in rhs else None
    if 'Ref'in rhs:
     place=rhs['Ref']['place']['kind']
     if 'Projection'in place and place['Projection'][1]=='Deref':
      base=place['Projection'][0]['kind'].get('Local')
      if base in meta:value=meta[base]
    moves(rhs);meta.pop(root(dest),None)
    if 'Local'in dest['kind']and value is not None:meta[root(dest)]=value
    elif 'Local'not in dest['kind']:
     for slot in exposed:meta.pop(slot,None)
   elif 'Call'in k:
    c=k['Call']['call'];f=c['func'].get('Regular',{});fun=f.get('kind',{}).get('Fun',{})
    if fun=={'Builtin':'ArrayToSliceShared'}and len(c['args'])==1:
     cs=f.get('generics',{}).get('const_generics',[])
     n=literal(cs[0])if len(cs)==1 else None
     if n is not None:value=(n,st['id'])
    idx=fun.get('Builtin',{}).get('Index',{})if isinstance(fun.get('Builtin'),dict)else{}
    if idx.get('is_array')is False and idx.get('is_range')is False and len(c['args'])==2:
     observed_meta=operand(c['args'][0])
     if observed_meta is not None:
      n,origin=observed_meta;changes.append(dict(kind='slice_index_scalar_shape',statement=st['id'],metadata_origin=origin,length=n,source=copy.deepcopy(st)))
      idx['is_array']=True
      f['generics']['const_generics']=[{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize',str(n)]}}}}]
    if fun=={'Regular':23}and len(c['args'])==1:
     value0=operand(c['args'][0])
     if value0 is not None:
      n,origin=value0;changes.append(dict(kind='slice_metadata',statement=st['id'],coercion=origin,length=n,source=copy.deepcopy(st)))
      # Replace only the scalar result, leaving all other invalidation intact.
      replacement={'Assign':[copy.deepcopy(c['dest']),{'Use':[{'Const':{'kind':{'Literal':{'Scalar':{'Unsigned':['Usize',str(n)]}}}}},'Yes']}]}
     else:replacement=None
    else:replacement=None
    moves(c['args']);meta.pop(root(c.get('dest',{})),None)
    for slot in exposed:meta.pop(slot,None)
    if value is not None:meta[root(c['dest'])]=value
    if replacement is not None:st['kind']=replacement
    if k['Call'].get('on_unwind'):walk(k['Call']['on_unwind'],meta)
   elif 'StorageDead'in k or 'StorageLive'in k:meta.pop(next(iter(k.values())),None)
   elif 'Switch'in k:
    tag,v=next(iter(k['Switch'].items()));moves(v[0]);bs=v[1:]if tag=='If'else[q for _,q in v[1]]+([v[2]]if v[2]else[])if tag=='Match'else[q for _,q in v[2]]+([v[3]]if v[3]else[])
    outs=[out[0]for q in bs if(out:=walk(q,meta))[1]]
    if not outs:return {},False
    meta={slot:val for slot,val in outs[0].items()if all(o.get(slot)==val for o in outs[1:])}
   elif 'Loop'in k:
    stable={slot:val for slot,val in meta.items()if slot in parameters}
    walk(k['Loop'],stable);meta=stable
   elif any(t in k for t in ['Break','Continue','Abort']):return {},False
   else:meta={slot:val for slot,val in meta.items()if slot in parameters}
  return meta,True
 if isinstance(b,dict)and 'Structured'in b:walk(b['Structured']['body'],{slot:(length,'caller parameter')for slot,length in parameters.items()})
 return b,changes
