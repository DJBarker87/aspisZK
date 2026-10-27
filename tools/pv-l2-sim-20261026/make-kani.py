from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
bindings=[]
def item(path,start):
 s=(R/path).read_text();a=s.index(start);b=s.index('{',a);depth=1;i=b+1
 while depth:
  if s[i]=='{':depth+=1
  if s[i]=='}':depth-=1
  i+=1
 out=s[a:i]
 bindings.append({'path':path,'line':s[:a].count('\n')+1,'item':start,'source_sha256':hashlib.sha256(s.encode()).hexdigest(),'item_sha256':hashlib.sha256(out.encode()).hexdigest()})
 return out+'\n'
p='crates/aspis-core/src/r0_transcript.rs';t='crates/aspis-core/src/transcript.rs';m='crates/aspis-r1-cost-probe/src/multiproof.rs';s='crates/aspis-r1-cost-probe/src/sampler.rs'
code='#![allow(dead_code,non_snake_case)]\n// Exact source items. Only surrounding imports/derives and cfg(kani) proofs are local.\ntype Rank=[u32;8];\nconst P:u32=0x7fff_ffff;\nconst QUERY_COUNT:usize=22;\nconst QUERY_BOUND:u32=1<<18;\nconst QUERY_MAX_DRAWS:usize=64;\nconst MAX_BATCH:usize=16;\nconst LEAF_BITS:u32=18;\n'
code+=item(p,'fn block_rank(')+item(p,'fn query_words(')
code+='#[derive(Clone,Copy,Debug,PartialEq,Eq)]\n'+item(t,'pub enum QuerySampleError')
code+='#[derive(Default)]\n'+item(p,'struct QueryScan')+item(p,'impl QueryScan')+item(p,'pub fn queries_from_pairs(')
code+='#[derive(Clone,Copy)]\n'+item(m,'pub enum Arity')+item(m,'impl Arity')+item(m,'fn well_formed(')+item(m,'fn index_at(')+item(m,'pub fn node_count(')
code+=item(s,'fn qm31_div_pass(')+item(s,'fn add_small_base_p(')
code+=(D/'proofs.rs').read_text()
(D/'PV_L2_native.rs').write_text(code)
(D/'source-binding.json').write_text(json.dumps(bindings,indent=2)+'\n')
print(len(bindings),'exact source items')
