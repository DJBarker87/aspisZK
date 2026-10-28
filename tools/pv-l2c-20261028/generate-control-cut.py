"""Verbatim native reachable control declarations; no replacement bodies or stubs.
The complete-crate Kani attempt fails in unrelated cfg(kani) record tests.
This finite Rust source cut preserves every reachable type/constant/function.
"""
from pathlib import Path
import re,hashlib,json,sys
R=Path(__file__).resolve().parents[2];T=R/'tools/pv-l2c-20261028/kani';E=R/'evidence/pv-l2c-20261028'
paths=['crates/aspis-prover/src/host_forest.rs']+['crates/aspis-statement/src/pool_v1/'+n+'.rs' for n in ['pair_tree_hiding','pair_forest_hiding','pair_tree_profile']]
src={p:(R/p).read_text() for p in paths};parts=[];records=[]
def balanced(p,start):
 s=src[p];a=s.index('{',start);depth=1;b=a+1
 while depth:
  depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[start:b]
def take(p,pattern,derive=False):
 s=src[p];m=re.search(pattern,s,re.M);assert m,(p,pattern);start=m.start()
 if derive:
  d=s.rfind('#[derive',0,start);assert d>=0 and s[d:start].count('\n')<=2;start=d
 text=balanced(p,start);parts.append(text);records.append(dict(path=p,line=1+s[:start].count('\n'),sha256=hashlib.sha256(text.encode()).hexdigest(),text=text))
h=paths[0];tree=paths[1]
for name in ['PoolV1PairCopyRowLinkKindV1','PoolV1PairCopyRowLinkV1','PoolV1PairHidingLayoutErrorV1']:
 take(tree,r'^pub (?:enum|struct) '+name+r'\b',True)
take(h,r'^pub struct Schedule\b',True);take(h,r'^impl Schedule\b')
for name in ['link','build_pool_v1_pair_copy_row_schedule_v1','endpoint_counts','build_pool_v1_pair_forest_copy_row_schedule_v1','pool_v1_pair_forest_copy_active_rows_v1','mask_endpoint_bump','pool_v1_pair_forest_copy_active_row_masks_v1','path_kind','schedule_at','flag_at','append_forest_level']:
 take(h,r'^(?:pub )?fn '+name+r'\b')
for p,name in [(paths[2],'pool_v1_pair_forest_path_base_row_v1'),(paths[2],'pool_v1_pair_forest_membership_hash_block_v1'),(paths[3],'pool_v1_pair_path_base_row_v1')]:
 take(p,r'^pub const fn '+name+r'\b')
constants={}
for p,s in src.items():
 for m in re.finditer(r'^(?:pub )?const ([A-Z][A-Z0-9_]+)\s*:',s,re.M):
  start=m.start();a=s.index('=',start)+1;b=a;depth=0
  while s[b]!=';' or depth:
   depth+=(s[b] in '[({')-(s[b] in '])}');b+=1
  constants.setdefault(m[1],[]).append((p,start,s[start:b+1]))
need=set(re.findall(r'\b(?:POOL_V1_[A-Z0-9_]+|MASK_LINKS)\b','\n'.join(parts)));added=set()
while need-added:
 n=sorted(need-added)[0];choices=constants.get(n,[]);assert len(choices)==1,(n,choices)
 p,start,text=choices[0];parts.insert(0,text);records.append(dict(path=p,line=1+src[p][:start].count('\n'),sha256=hashlib.sha256(text.encode()).hexdigest(),text=text));added.add(n);need.update(re.findall(r'\bPOOL_V1_[A-Z0-9_]+\b',text))
out='// Generated verbatim source cut; see control-cut-sources.json.\n'+'\n\n'.join(parts)+'\n'
q=T/'control_cut.rs'
if '--check' in sys.argv:assert q.read_text()==out
else:q.write_text(out)
(E/'control-cut-sources.json').write_text(json.dumps(dict(declarations=records,source_files={p:hashlib.sha256(s.encode()).hexdigest() for p,s in src.items()},cut_sha256=hashlib.sha256(out.encode()).hexdigest(),stubs=[],field_arithmetic_reachable=False),indent=2)+'\n')
print('Verified' if '--check' in sys.argv else 'Generated',len(records),'verbatim control declarations')
