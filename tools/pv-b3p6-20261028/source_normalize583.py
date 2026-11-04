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

def normalize(body,global_values):
 b=copy.deepcopy(body);changes=[]
 for x in dicts(b):
  for tag in ['Copy','Move']:
   p=x.get(tag)
   if isinstance(p,dict)and 'Global'in p.get('kind',{}):
    gid=p['kind']['Global']['id']
    if gid in global_values:
     changes.append(dict(kind='named_const_scalar',global_id=gid,source=copy.deepcopy(x)))
     x.clear();x['Const']=copy.deepcopy(global_values[gid]);break
 exposed={root(x[tag]['place'])for x in dicts(b)for tag in ('Ref','RawPtr')if tag in x and isinstance(x[tag],dict)and 'place'in x[tag]}
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
   if not isinstance(k,dict):meta.clear();continue
   if 'Assign'in k:
    dest,rhs=k['Assign'];value=operand(rhs['Use'][0])if 'Use'in rhs else None
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
    outs=[walk(q,meta)for q in bs];meta={slot:val for slot,val in outs[0].items()if all(o.get(slot)==val for o in outs[1:])}if outs else{}
   elif 'Loop'in k:walk(k['Loop'],{});meta.clear()
   else:meta.clear()
  return meta
 if isinstance(b,dict)and 'Structured'in b:walk(b['Structured']['body'],{})
 return b,changes
