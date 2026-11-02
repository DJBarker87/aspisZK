"""Inspect all six actual Drain specializations and compare reached source arm.
This is source parity, not a native/model association or Kani credit.
"""
from pathlib import Path
import json,lzma,re,hashlib
R=Path('evidence/pv-b3p6-20261028/resume18');sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((R/'imports-b3q/pv-b3q2-20261031/direct3-instantiated-callcone.json').read_text())
llbc=json.loads(lzma.decompress((R/'imports-b3q/pv-b3q2-20261031/PV_B3Q_DirectCone3.llbc.xz').read_bytes()))['translated']
types={t['def_id']:t for t in llbc['type_decls'] if t}
# Resolve shared JSON hash-consed types without changing any source graph.
dedup={}
def collect(v):
 if isinstance(v,dict):
  if 'HashConsedValue'in v:
   ident,p=v['HashConsedValue'];dedup[ident]=p
  for y in v.values():collect(y)
 elif isinstance(v,list):
  for y in v:collect(y)
collect(llbc)
def resolve(v):
 if isinstance(v,dict):
  if 'HashConsedValue'in v:return resolve(v['HashConsedValue'][1])
  if 'Deduplicated'in v:return resolve(dedup[v['Deduplicated']])
  return {k:resolve(y)for k,y in v.items()}
 if isinstance(v,list):return [resolve(y)for y in v]
 return v
# Inspect carrier shapes, not host size_of of a different Rust build.
inspected={}
def plain_size(v):
 v=resolve(v)
 if 'Literal'in v:
  kind=v['Literal'];assert 'UInt'in kind,kind
  return {'U32':4,'Usize':8}[kind['UInt']]
 ident=v['Adt']['id']['Adt'];t=types[ident];kind=resolve(t['kind']);assert 'Struct'in kind,(ident,kind)
 fields=kind['Struct'];total=sum(plain_size(f['ty'])for f in fields)
 inspected[str(ident)]=dict(name=t['item_meta']['name'],fields=fields,plain_field_bytes=total,drop_status='plain integer/struct carrier; this is not an executed drop/source proof')
 return total
rows=[]
for key,i in x['instances'].items():
 if i['id']!=447:continue
 size=plain_size(i['environment']['types'][0]);assert size>0
 rows.append(dict(instance=key,element=i['environment']['types'][0],non_zst=True,plain_field_bytes=size,layout_boundary='x86_64 Usize width from captured target; source-to-code remains V370',remaining='valid region/cursor and pointer add/read realization; closure, partial-initialization and drop/source composition'))
assert len(rows)==6
# The branch body has no string literals containing braces; balanced braces are sufficient.
def arm(v):
 p=R/'std559-source'/v/'array/drain.rs.xz';s=lzma.decompress(p.read_bytes()).decode();start=s.index('fn call_mut(');start=s.index('} else {',start)+len('} else ');depth=1;i=start+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 return s[start:i]
a,b=arm('1.94.1'),arm('nightly-2026-06-01')
def tokens(s):
 s=re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
 return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',s)
assert tokens(a)==tokens(b)
expected='{ let p = self.ptr; self.ptr = unsafe { self.ptr.add(1) }; (self.f)(unsafe { p.read() }) }'
assert tokens(a)==tokens(expected)
out=dict(instances=rows,inspected_types=inspected,old_non_zst_arm=a,new_non_zst_arm=b,non_zst_arm_token_identical=True,statement_order=['save old pointer','advance stored pointer','read old pointer','invoke unchanged closure'],qualification='STRUCTURAL source parity for reached non-ZST call_mut arm only, not a model proof; no Kani credit or source-cone/dictionary discharge',drop_remaining='Drain::drop differs between Rust versions and still needs constructor/end-pointer invariant, tail ownership and source/model association, including unwind; no drop credit released')
(R/'DRAIN-SOURCE-PARITY-D559.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(instances=6,non_zst_arm_token_identical=True,drop_association='OPEN')))
