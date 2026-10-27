from pathlib import Path
R=Path.cwd();D=R/'crates/aspis-r1-cost-probe/src'
(D/'host_multilinear.rs').write_text('''//! Drop-free prover-local sparse multilinear evaluation. The field operation
//! order, literal Boolean suffix test and wrong-length rejection are retained.
use aspis_core::field::QM31;
#[derive(Clone,Copy)]
pub struct SparseWeights {pub data:[(usize,QM31);1024],pub len:usize}
pub fn sparse_eq_weights(point:&[QM31;10])->SparseWeights {
 let mut prefix_len=10usize;
 while prefix_len>0 && (point[prefix_len-1]==QM31::ZERO || point[prefix_len-1]==QM31::ONE){prefix_len-=1;}
 let trailing_boolean=10-prefix_len;
 let mut suffix=0usize;let mut coordinate=prefix_len;
 while coordinate<10{suffix=(suffix<<1u32)|usize::from(point[coordinate]==QM31::ONE);coordinate+=1;}
 let mut output=SparseWeights{data:[(0,QM31::ZERO);1024],len:1usize<<prefix_len};
 let mut prefix=0usize;while prefix<output.len {
  let row=(prefix<<trailing_boolean)|suffix;let mut weight=QM31::ONE;let mut coordinate=0usize;
  while coordinate<prefix_len {let bit=(prefix>>(prefix_len-1-coordinate))&1;
   weight=weight.mul(if bit==0{QM31::ONE.sub(point[coordinate])}else{point[coordinate]});coordinate+=1;}
  output.data[prefix]=(row,weight);prefix+=1;
 }
 output
}
pub fn multilinear_evaluate_qm31(column:&[QM31],point:&[QM31;10])->Option<QM31>{
 if column.len()!=1024{return None;}
 let weights=sparse_eq_weights(point);let mut sum=QM31::ZERO;let mut i=0usize;
 while i<weights.len{let (row,weight)=weights.data[i];sum=sum.add(weight.mul(column[row]));i+=1;}Some(sum)
}
''')
p=D/'lib.rs';p.write_text(p.read_text()+'\n#[cfg(feature = "prover")]\npub mod host_multilinear;\n')
for file in ['host_semantic.rs','sim.rs']:
 p=D/file;s=p.read_text().replace('multilinear_evaluate_qm31,','');s='use crate::host_multilinear::multilinear_evaluate_qm31;\n'+s;p.write_text(s)
p=R/'crates/aspis-prover/src/host_forest.rs';s=p.read_text();a=s.index('fn tuple_value(');b=s.index('\nfn copy_weight(',a)
s=s[:a]+'''fn tuple_value(trace:&PoolV1PairForestTraceV1,tuple:PoolV1PairCopyTupleV1)->[M31;16]{
 let mut out=[M31::ZERO;16];let mut i=0usize;while i<16{
  out[i]=match tuple.limbs[i]{PoolV1PairTupleLimbV1::Zero=>M31::ZERO,PoolV1PairTupleLimbV1::Cell{source,offset}=>{
   let columns=match source.bank{PoolV1PairTraceBankV1::Stable=>&trace.stable.c1,PoolV1PairTraceBankV1::Late=>&trace.late};
   columns[source.cell.column as usize][source.cell.row as usize].add(offset)}};i+=1;
 }out
}
fn compress_tuple(tag:M31,values:&[M31;16],lambda:QM31)->QM31{
 let mut value=QM31::from_cm31(aspis_core::field::CM31::from_m31(tag));let mut power=lambda;let mut i=0usize;
 while i<16{value=value.add(power.mul_m31(values[i]));power=power.mul(lambda);i+=1;}value
}
'''+s[b:]
a=s.index('pub fn pool_v1_pair_forest_copy_rows_v1(');b=s.index('\npub fn build_pool_v1_pair_forest_copy_helper_v1(',a)
rows=s[a:b].replace('Result<Vec<CopyLogUpRow>', 'Result<[CopyLogUpRow;1024]').replace('vec![empty; 1024]', '[empty;1024]')
a2=rows.index('        for (tuple, producer) in');b2=rows.index('        i += 1;',a2)
rows=rows[:a2]+'''        let mut side=0usize;while side<2 {
            let tuple=if side==0{link.producer}else{link.consumer};let row=&mut rows[tuple.row as usize];
            let (values,weights)=if side==0{(&mut row.producer_values,&mut row.producer_weights)}else{(&mut row.consumer_values,&mut row.consumer_weights)};
            let slot=if weights[0]==M31::ZERO{0}else if weights[1]==M31::ZERO{1}else{return Err(PoolV1PairTraceErrorV1::CopyLayout)};
            values[slot]=compress_tuple(link.tag,&tuple_value(trace,tuple),lambda);weights[slot]=weight;side+=1;
        }
'''+rows[b2:]
s=s[:a]+rows+s[b:]
a=s.index('pub fn build_pool_v1_pair_forest_copy_helper_v1(');b=s.index('\nfn forest_path_aux_cell_is_used(',a)
s=s[:a]+'''pub fn build_pool_v1_pair_forest_copy_helper_v1(trace:&PoolV1PairForestTraceV1,append_index:u64,lambda:QM31,chi:QM31)->Result<[QM31;1024],PoolV1PairTraceErrorV1>{
 let rows=pool_v1_pair_forest_copy_rows_v1(trace,append_index,lambda)?;let mut helper=[QM31::ZERO;1024];let mut r=0usize;
 while r<1024 {let row=rows[r];let mut value=QM31::ZERO;let mut slot=0usize;
  while slot<2{let weight=row.producer_weights[slot];if weight!=M31::ZERO{let inv=match chi.sub(row.producer_values[slot]).try_inv(){Some(v)=>v,None=>return Err(PoolV1PairTraceErrorV1::CopyImbalance)};value=value.add(inv.mul_m31(weight));}slot+=1;}
  slot=0;while slot<2{let weight=row.consumer_weights[slot];if weight!=M31::ZERO{let inv=match chi.sub(row.consumer_values[slot]).try_inv(){Some(v)=>v,None=>return Err(PoolV1PairTraceErrorV1::CopyImbalance)};value=value.sub(inv.mul_m31(weight));}slot+=1;}
  helper[r]=value;r+=1;
 }Ok(helper)
}
pub fn materialize_copy_helper(trace:&PoolV1PairForestTraceV1,append_index:u64,lambda:QM31,chi:QM31)->Result<Vec<QM31>,PoolV1PairTraceErrorV1>{
 let helper=build_pool_v1_pair_forest_copy_helper_v1(trace,append_index,lambda,chi)?;Ok(helper.to_vec())
}
'''+s[b:]
s=s.replace('use aspis_statement::logup::{build_copy_logup_helper, compress_tagged_tuple, CopyLogUpRow};','use aspis_statement::logup::CopyLogUpRow;').replace('use std::{vec, vec::Vec};','use std::vec::Vec;');p.write_text(s)
p=D/'host_semantic.rs';s=p.read_text().replace('use crate::host_forest::build_pool_v1_pair_forest_copy_helper_v1;', 'use crate::host_forest::materialize_copy_helper as build_pool_v1_pair_forest_copy_helper_v1;');p.write_text(s)
