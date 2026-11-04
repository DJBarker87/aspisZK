"""Resolve straight-line checked scalar constant initializers; bind the one
foreign scalar constant to its exact frozen deployed Rust literal declaration.
This remains a structural source projection with V370 retained.
"""
import copy,re,subprocess,hashlib
from pathlib import Path
from initializer_source578 import compact
from fixed_indices572 import literal
from source_normalize583 import constants as base
REV='1f96955af7a6b511bb69df2f748bbcb574fc440e'
def constants(ll,fs):
 out,bindings=base(ll,fs);path='crates/aspis-core/src/state_only_hiding.rs';frozen=subprocess.check_output(['git','show',REV+':'+path]);assert Path(path).read_bytes()==frozen
 match=re.search(rb'^pub const STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS: usize = (\d+);$',frozen,re.M);assert match and int(match[1])==10
 f=fs[40];assert f['body']=='Opaque'and f['item_meta']['name']==[{'Ident':['aspis_core',0]},{'Ident':['state_only_hiding',0]},{'Ident':['STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS',0]}]
 globals={g['def_id']:g for g in ll['global_decls']if g}
 assert compact(globals[2]['value'])=={'kind':{'Call':[{'kind':{'Fun':{'Regular':40}}},[]]}}and globals[2]['global_kind']=='NamedConst'
 out[2]={'kind':{'Literal':{'Scalar':{'Unsigned':['Usize','10']}}}}
 bindings.append(dict(global_id=2,initializer=40,route='own-1 frozen deployed Rust literal scalar projection; not an opaque whole-body equality',revision=REV,path=path,source_sha256=hashlib.sha256(frozen).hexdigest(),declaration=match[0].decode(),value=10))
 pending=set(globals)-set(out)
 def evaluate(f):
  if not isinstance(f.get('body'),dict):raise ValueError()
  b=f['body']['Structured'];assert b['locals']['arg_count']==0;env={};events=[];returned=False
  def operand(o):
   if'Const'in o:
    n=literal(o['Const'])
    if n is None:raise ValueError()
    return n
   tag,p=next(iter(o.items()));assert tag in['Copy','Move'];k=p['kind']
   if'Global'in k:
    if k['Global']['id']not in out:raise ValueError()
    return literal(out[k['Global']['id']])
   assert'Local'in k;return env[k['Local']]
  for st in b['body']['statements']:
   assert not returned;k=st['kind']
   if k=='Return':returned=True;continue
   assert isinstance(k,dict)
   if'StorageLive'in k or'StorageDead'in k:continue
   assert list(k)==['Assign'];dest,rhs=k['Assign'];assert'Local'in dest['kind']
   if'Use'in rhs:v=operand(rhs['Use'][0])
   else:
    operator,a,b=rhs['BinaryOp'];assert operator in[{'Add':'Panic'},{'Sub':'Panic'},{'Mul':'Panic'}];a,b=operand(a),operand(b)
    v=a+b if operator=={'Add':'Panic'}else a-b if operator=={'Sub':'Panic'}else a*b
    assert 0<=v<2**32 # works for both supported pointer widths; no overflow
   env[dest['kind']['Local']]=v;events.append(st['id'])
  assert returned and 0 in env
  return env[0],events
 for _ in range(len(pending)):
  changed=False
  for gid in sorted(pending.copy()):
   gl=globals[gid]
   if gl['global_kind']!='NamedConst':continue
   try:
    f,args=gl['value']['kind']['Call'];assert not args;fid=f['kind']['Fun']['Regular'];n,events=evaluate(fs[fid])
   except(AssertionError,ValueError,KeyError,TypeError):continue
   out[gid]={'kind':{'Literal':{'Scalar':{'Unsigned':['Usize',str(n)]}}}};pending.remove(gid);changed=True
   bindings.append(dict(global_id=gid,initializer=fid,value=n,events=events,source=compact(fs[fid]['body'])))
  if not changed:break
 return out,bindings
