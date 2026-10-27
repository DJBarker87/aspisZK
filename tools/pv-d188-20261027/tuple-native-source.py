from pathlib import Path
import json,hashlib
out=Path('evidence/pv-d188-20261027');bind=[]
def item(path,needle):
 t=Path(path).read_text();a=t.index(needle);b=t.index('{',a);depth=1;i=b+1
 while depth:
  if t[i]=='{':depth+=1
  elif t[i]=='}':depth-=1
  i+=1
 s=t[a:i];bind.append(dict(path=path,line=t.count('\n',0,a)+1,sha256=hashlib.sha256(s.encode()).hexdigest()));return s
p='crates/aspis-statement/src/pool_v1/pair_trace.rs';forest='crates/aspis-statement/src/pool_v1/pair_forest_trace.rs'
s='mod field;use field::M31;\nconst MERKLE_NODE_COMPRESSION_V3_TWEAK:M31=M31(0x4153_1005);\n'
for needle in ['pub enum PoolV1PairTraceBankV1','pub struct PoolV1PairTraceCellV1','pub enum PoolV1PairTupleLimbV1','pub struct PoolV1PairCopyTupleV1']:
 s+='#[derive(Clone,Copy,Debug)]\n'+item(p,needle)+'\n'
s+='#[derive(Clone,Copy,Debug)]\n'+item('crates/aspis-statement/src/trace_v4.rs','pub struct TraceCell')+'\n'
s+=item(p,'fn bank_for_row')+'\n'+item(p,'fn tuple_cells')+'\n'
s+='mod forest{use super::*;'+item(forest,'fn tuple_cells').replace('fn tuple_cells','pub fn tuple_cells',1)+'}\n'
s+='''fn flatten(v:PoolV1PairCopyTupleV1)->Vec<Vec<u32>> {v.limbs.into_iter().map(|l|match l{PoolV1PairTupleLimbV1::Zero=>vec![],PoolV1PairTupleLimbV1::Cell{source,offset}=>vec![source.cell.row as u32,source.cell.column as u32,offset.0,match source.bank{PoolV1PairTraceBankV1::Stable=>0,PoolV1PairTraceBankV1::Late=>1}]}).collect()}
fn main(){println!("tuple {:?}",flatten(tuple_cells(550,3,3,true)));println!("forest {:?}",flatten(forest::tuple_cells(550,3,3,true)));}
'''
(out/'tests/native2-files/native3.rs').write_text(s);(out/'native3-source-binding.json').write_text(json.dumps(dict(fragments=bind,adaptations=['Add original Copy/Clone/Debug derives to copied record declarations','Expose private forest function to main by pub (body unchanged)'],constant='poseidon2.rs:465 0x41531005'),indent=2)+'\n')
