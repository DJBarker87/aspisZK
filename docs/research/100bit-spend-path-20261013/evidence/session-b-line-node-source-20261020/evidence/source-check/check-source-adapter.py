#!/usr/bin/env python3
"""Reverse-check source cut line_node and its retained explicit fibre_point owner.
Only the recorded API/opaque-operation substitutions are accepted."""
from pathlib import Path
import re, json, hashlib, sys
root=Path(__file__).resolve().parents[2]
raw=(root/'sources/extracted-owner/Funs.lean').read_text()
adapt=(root/'sources/proof/R17FibrePointLineNodeActual.lean').read_text()
selected_path=root/'sources/dependencies/Funs-selected-narrow.lean'
old=selected_path.read_text()
selected_sha=hashlib.sha256(old.encode()).hexdigest()
if selected_sha != 'ca34b291966b1289d1e50c867e2d7fafc91e7f55a2cb6fdb94461f4968d4ce58':
 raise SystemExit(f'selected Funs source pin mismatch: {selected_sha}')
def block(s, marker):
 i=s.index(marker); j=s.find('\n\n',i)
 if j<0: j=len(s)
 return s[i:j].strip()
def norm(s): return re.sub(r'\s+',' ',s).strip()
def require_block(a,b,name,repls):
 x=block(a,repls[0][0]); y=block(b,repls[0][1])
 for src,dst in repls[1:]:
  if src not in y: raise SystemExit(f'{name}: missing adapter token {src!r}')
  y=y.replace(src,dst,1)
 if norm(x)!=norm(y):
  print('expected raw:\n'+x+'\nnormalized adapter:\n'+y,file=sys.stderr)
  raise SystemExit(f'{name}: reverse body mismatch')
 return {'raw_sha256':hashlib.sha256(x.encode()).hexdigest(),
         'adapter_sha256':hashlib.sha256(block(b,repls[0][1]).encode()).hexdigest()}
# The old retained owner has the same literal Rust bodies, parameterizing only
# opaque CM31 constructors. This child is the one used by the theorem.
checks={}
checks['table_value']=require_block(raw,old,'table_value',[
 ('def fast_domain.table_value\n  (value : (Std.U32 × Std.U32))', 'def fast_domain.table_value\n  (ops : CM31Ops) (value : (Std.U32 × Std.U32))'),
 ('  (ops : CM31Ops) ',''),('ops.new','field.CM31.new')])
checks['fibre_point']=require_block(raw,old,'fibre_point',[
 ('def fast_domain.fibre_point\n  (u : domain.FibreIndex)', 'def fast_domain.fibre_point\n  (ops : CM31Ops) (u : domain.FibreIndex)'),
 ('  (ops : CM31Ops) ',''),
 ('fast_domain.table_value ops p','fast_domain.table_value p'),
 ('fast_domain.table_value ops p1','fast_domain.table_value p1'),
 ('ops.mul left right','field.CM31.mul left right')])
# line_node adaptation: add the two explicit operation bundles; map its child
# call to the retained explicit fibre_point owner; map M31 calls and ONE.
rawline=block(raw,'def fast_domain.line_node (u : domain.FibreIndex)')
adaptline=block(adapt,'def line_node (cmops : CM31Ops) (ops : M31Ops)')
repls=[
 ('def line_node (cmops : CM31Ops) (ops : M31Ops) (u : domain.FibreIndex) :','def fast_domain.line_node (u : domain.FibreIndex) :'),
 ('fast_domain.fibre_point cmops u','fast_domain.fibre_point u'),
 ('ops.mul','field.M31.mul'),('ops.double','field.M31.double'),
 ('ops.sub','field.M31.sub'),('(1#u32)','field.M31.ONE')]
for src,dst in repls:
 if src not in adaptline: raise SystemExit(f'line_node: missing adapter token {src!r}')
 adaptline=adaptline.replace(src,dst,1)
if norm(rawline)!=norm(adaptline):
 print('expected raw:\n'+rawline+'\nnormalized adapter:\n'+adaptline,file=sys.stderr)
 raise SystemExit('line_node: reverse body mismatch')
checks['line_node']={'raw_sha256':hashlib.sha256(rawline.encode()).hexdigest(),
                     'adapter_sha256':hashlib.sha256(block((root/'sources/proof/R17FibrePointLineNodeActual.lean').read_text(),'def line_node (cmops : CM31Ops) (ops : M31Ops)').encode()).hexdigest(),
                     'inverse_substitutions':repls}
# Confirm the one constant maps to the literal used by the old field API.
if 'def field.M31.ONE : field.M31 := 1#u32' not in raw:
 raise SystemExit('raw field.M31.ONE definition changed')
# Check ordered table contents agree exactly between the raw extracted arrays
# and the exact narrow Funs child selected by R17FibrePointActualSuccess.
def pairs_between(s,start,end):
 a=s.index(start); b=s.index(end,a); part=s[a:b]
 return [(int(x),int(y)) for x,y in re.findall(r'\((\d+)#u32,\s*(\d+)#u32\)',part)]
for letter in 'AB':
 rawpairs=pairs_between(raw,f'def fast_domain.TABLE_{letter} :',f'def fast_domain.TABLE_{"B" if letter=="A" else ""}') if False else None
# Explicit region terminators avoid matching later function names.
for letter,terminator in [('A','def fast_domain.TABLE_B :'),('B','def fast_domain.table_value')]:
 rr=pairs_between(raw,f'def fast_domain.TABLE_{letter} :',terminator)
 oo=[]
 for i in range(16):
  nm=f'def fast_domain.TABLE_{letter}_chunk_{i:02d} :'
  nxt=(f'def fast_domain.TABLE_{letter}_chunk_{i+1:02d} :' if i<15 else
       (f'def fast_domain.TABLE_{"B"}_chunk_00 :' if letter=='A' else 'def fast_domain.TABLE_B_entries'))
  oo.extend(pairs_between(old,nm,nxt))
 if len(rr)!=512 or len(oo)!=512 or rr!=oo:
  raise SystemExit(f'TABLE_{letter} ordered literal mismatch: raw={len(rr)}, retained={len(oo)}')
 checks[f'TABLE_{letter}']={'ordered_pair_count':len(rr),'ordered_pairs_sha256':hashlib.sha256(repr(rr).encode()).hexdigest(),'equal':True}
checks['selected_owner']={'path':'sources/dependencies/Funs-selected-narrow.lean','sha256':selected_sha,
 'role':'exact selected narrow Funs child source used by R17FibrePointActualSuccess; chunked TABLE_A/B and source bodies for table_value/fibre_point'}
print(json.dumps({'result':'PASS','checks':checks},indent=2))
