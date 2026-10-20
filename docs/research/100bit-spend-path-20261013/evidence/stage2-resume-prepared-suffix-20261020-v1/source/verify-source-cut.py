#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
RESEARCH=Path(__file__).resolve().parents[2]
CAND=Path(__file__).resolve().parent
C8=RESEARCH/'lean-candidates/stage2-polynomial-source-cut-20261020/original-polynomial-fold-adapter-v2-evidence/pins/frozen-verifier-c8.rs'
sha=lambda b:hashlib.sha256(b).hexdigest()
def block(s,marker):
 i=s.index(marker); b=s.index('{',i); depth=0
 for j in range(b,len(s)):
  if s[j]=='{': depth+=1
  elif s[j]=='}':
   depth-=1
   if depth==0:return s[i:j+1]
 raise ValueError(marker)
orig=C8.read_bytes().decode(); cand=(CAND/'input/lib.rs').read_text()
assert sha(C8.read_bytes())=='8a704eea668d04ca173290ca894c7cb0ab1f29abef4fec9bb49fbb36476779ea'
expr='Ok((Box::new(Prepared{variant:v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state}),Accumulator{weights,rhs,power,next:bytes[9] as usize}))'
start=orig.index(expr); end=start+len(expr)
assert (start,end)==(16861,17015)
assert sha(orig[start:end].encode())=='44811860590a17d7fdea122f38e1f8efea957783b86b17b2ef9c4eaaf7c02a8c'
assert orig.count(expr)==1 and cand.count(expr)==1
call='resume_prepared_suffix(bytes,v,roots,gamma,kappa,alpha,rho,queries,semantic_alpha,z,claim,state,weights,rhs,power)'
assert cand.count(call)==1
layouts={}
for name,expected in [('pub struct Prepared','00b77d1dce81b9c15286d83dffb0b81a2f8a8777a27d7fff3c13706db833ce88'),('pub struct Accumulator','16408fdb6f95a080f2f9386f20f279dc309f4cc25734dbca92f3a5c259bd66c1')]:
 a=block(orig,name);b=block(cand,name);assert a==b and sha(a.encode())==expected;layouts[name]=expected
print(json.dumps({'status':'pass','frozen_source_sha256':sha(C8.read_bytes()),'suffix_span_bytes':[start,end],'suffix_sha256':sha(orig[start:end].encode()),'layout_hashes':layouts,'candidate_lib_sha256':sha((CAND/'input/lib.rs').read_bytes()),'helper_call_count':cand.count(call),'claim':'source-cut only; full resume reachability is open'},indent=2))
