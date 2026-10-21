//! Symbolic local S8 comparisons. Long-loop composition is proved in Lean.
use super::*;
fn same(a:K,b:K) {assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);}
#[kani::proof] #[kani::unwind(20)]
fn compact_one_chunk() {
 let bytes:[u8;16]=kani::any();
 assert_eq!(check_values(&bytes),check_values_owned(&bytes));
}
#[kani::proof] #[kani::unwind(36)]
fn compact_remainder() {
 let bytes:[u8;31]=kani::any();let len:usize=kani::any();kani::assume(len<=31);
 assert_eq!(check_values(&bytes[..len]),check_values_owned(&bytes[..len]));
}
#[kani::proof] #[kani::unwind(52)]
fn compact_two_chunks() {
 let bytes:[u8;47]=kani::any();let len:usize=kani::any();kani::assume(len<=47);
 assert_eq!(check_values(&bytes[..len]),check_values_owned(&bytes[..len]));
}
#[kani::proof] #[kani::unwind(20)]
fn value_all_u64() {
 let row:[u64;4]=kani::any();let pending=BatchedWeights{raw:vec![row],terms:0};
 same(pending.value(0),value_owned(row));
}
#[kani::proof] #[kani::unwind(8)]
fn finish_one_row() {
 let row:[u64;4]=kani::any();let pending=BatchedWeights{raw:vec![row],terms:kani::any()};
 let old:[u32;4]=kani::any();let k=K{c0:CM31{a:M31(old[0]),b:M31(old[1])},c1:CM31{a:M31(old[2]),b:M31(old[3])}};
 let mut weights=[k];pending.finish(&mut weights);
 let result=finish_owned(vec![row],vec![k]);same(weights[0],result[0]);
}
#[kani::proof] #[kani::unwind(8)]
fn finish_step_frame() {
 let rows:[[u64;4];2]=kani::any();let index:usize=kani::any();kani::assume(index<2);
 let old:[u32;8]=kani::any();
 let a=K{c0:CM31{a:M31(old[0]),b:M31(old[1])},c1:CM31{a:M31(old[2]),b:M31(old[3])}};
 let b=K{c0:CM31{a:M31(old[4]),b:M31(old[5])},c1:CM31{a:M31(old[6]),b:M31(old[7])}};
 let before=[a,b];let mut weights=before;
 let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
 // Exact frozen loop-body statement, at arbitrary iterator ordinal.
 weights[index]=pending.value(index);
 same(weights[index],value_owned(rows[index]));
 same(weights[1-index],before[1-index]);
 assert_eq!(index+1,index.checked_add(1).unwrap());
}
#[kani::proof] #[kani::unwind(8)]
fn finish_empty_and_short_destination() {
 let rows:[[u64;4];2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);
 let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
 let mut weights=vec![K::ONE;n];pending.finish(&mut weights);
 let result=finish_owned(rows.to_vec(),vec![K::ONE;n]);
 assert_eq!(result.len(),n);for j in 0..n {same(weights[j],result[j]);}
}

// Independent bit-level reducer postcondition, valid for every u64.
fn reduce_spec(x:u64)->u32 {
 let a=(x&0x7fffffff)+(x>>31);
 let b=((a&0x7fffffff)+(a>>31)) as u32;
 if b>=0x7fffffff {b-0x7fffffff} else {b}
}
#[kani::ensures(|out: &[u32;4]| out[0]==reduce_spec(row[0]) && out[1]==reduce_spec(row[1]) && out[2]==reduce_spec(row[2]) && out[3]==reduce_spec(row[3]))]
fn checked_value(row:[u64;4])->[u32;4] {let q=value_owned(row);[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
#[kani::proof_for_contract(checked_value)]
#[kani::unwind(6)]
fn value_contract() {let row:[u64;4]=kani::any();checked_value(row);}
#[kani::proof]
#[kani::stub_verified(checked_value)]
#[kani::unwind(6)]
fn finish_step_verified_value() {
 let row:[u64;4]=kani::any();let out=checked_value(row);
 assert_eq!(out[0],reduce_spec(row[0]));assert_eq!(out[1],reduce_spec(row[1]));
 assert_eq!(out[2],reduce_spec(row[2]));assert_eq!(out[3],reduce_spec(row[3]));
}
#[kani::proof] #[kani::unwind(36)]
fn compact_step_at_ordinal() {
 let bytes:[u8;32]=kani::any();let ordinal:usize=kani::any();kani::assume(ordinal<2);
 let chunk=bytes.chunks_exact(16).nth(ordinal).unwrap();
 let at=16*ordinal;
 assert_eq!(K::from_le_bytes(chunk).is_some(),K::from_le_bytes(&bytes[at..at+16]).is_some());
}

#[kani::proof] #[kani::unwind(32)]
fn compact_fixed_y1_29() {
 let bytes:[u8;464]=kani::any();
 assert_eq!(check_values(&bytes),check_values_owned(&bytes));
}
#[kani::proof] #[kani::unwind(70)]
fn finish_fixed_production64() {
 let rows:[[u64;4];64]=kani::any();
 let pending=BatchedWeights{raw:rows.to_vec(),terms:kani::any()};
 let mut weights=vec![K::ONE;64];pending.finish(&mut weights);
 let result=finish_owned(rows.to_vec(),vec![K::ONE;64]);
 for j in 0..64 {same(weights[j],result[j]);}
}
