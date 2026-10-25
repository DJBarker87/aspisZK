#!/usr/bin/env python3
"""Exact textual IR inventory/shape guard; not a native semantic theorem."""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';P=E/'s1-claims-box-wrapper-ir-v3';s=(P/'functions.txt').read_text();headers=list(re.finditer(r'(?m)^([^\n]+) /\* ([^\n]+) \*/$',s));D={m[2]:(m[1],s[m.end():headers[n+1].start()if n+1<len(headers)else len(s)])for n,m in enumerate(headers)};assert len(D)==len(headers)==133
rootNames=['core::mem::MaybeUninit::<[[aspis_core::field::QM31; 29]; 3]>::as_mut_ptr','alloc::boxed::Box::<core::mem::MaybeUninit<[[aspis_core::field::QM31; 29]; 3]>>::assume_init']
roots=[next(k for k,v in D.items()if v[0]==name)for name in rootNames];selected=set();missing=set();todo=roots[:]
while todo:
 k=todo.pop()
 if k in selected:continue
 selected.add(k);name,body=D[k]
 for line in body.splitlines():
  if not re.match(r'^\s*CALL\b',line):continue
  m=re.match(r'^\s*CALL(?: .*? :=)? (\w+)\(',line);assert m,line
  callee=m[1]
  if callee in D:todo.append(callee)
  else:missing.add(callee)
# Exact pointer-only shape of the real MaybeUninit::as_mut_ptr body.
body=D[roots[0]][1];lines=[l.strip()for l in body.splitlines()if l.strip()and not l.strip().startswith('//')and not l.startswith('^^^^')];aliases={}
def alias(m):
 k=m[0]
 if k not in aliases:aliases[k]='V'+str(len(aliases))
 return aliases[k]
normalized=[re.sub(r'_R[A-Za-z0-9_]+(?:::[A-Za-z0-9_]+)*',alias,l)for l in lines]
assert normalized==['DECL V0 : struct tag-_262990846129430720794961562193052722729[29][3]*','DECL V1 : union tag-_176197306909822943064038706870462422083*','ASSIGN V1 := address_of(*V2)','ASSIGN V0 := cast(V1, struct tag-_262990846129430720794961562193052722729[29][3]*)','SET RETURN VALUE V0','DEAD V1','DEAD V0','GOTO 1','1: END_FUNCTION'],normalized
assert not missing,missing
assert all(not re.search(r'alloc::alloc::(?:alloc|dealloc|realloc)\b',D[k][0])for k in selected)
out=dict(schema='focused-extractor-proof-packet-v1',kind='EXACT_IR_SHAPE_AND_CALL_INVENTORY_ONLY',text_sha256=hashlib.sha256((P/'functions.txt').read_bytes()).hexdigest(),normalized_as_mut_ptr=normalized,reversible_aliases=aliases,roots=rootNames,missing_calls=sorted(missing),selected_functions=[dict(symbol=k,name=D[k][0],body=D[k][1],body_sha256=hashlib.sha256(D[k][1].encode()).hexdigest())for k in sorted(selected)],qualifications=['as_mut_ptr has address_of-dereference then pointer cast, no payload value load and no call in this emitted body','assume_init call closure is inventoried, not a proved heap/read-footprint law','source-to-native/SBF/compiler semantics and original SDK composition are not established by syntax inspection'])
q=E/'s1-claims-box-wrapper-ir-audit-v1';q.mkdir(exist_ok=False);(q/'inventory.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS exact as_mut_ptr body shape; inventoried',len(selected),'actual helper bodies; no missing callees/no allocator calls. No whole-source refinement claim.')
