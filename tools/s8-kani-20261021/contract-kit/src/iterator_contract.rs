use super::*;
fn finish_iterator_contract(pending:&BatchedWeights,weights:&mut[K]) {
 let len=weights.len();
 #[kani::loop_invariant(kani::index <= len)]
 for (i,w) in weights.iter_mut().enumerate(){*w=pending.value(i);}
}
#[kani::proof]
#[kani::stub_verified(aspis_core::field::M31::reduce_u64)]
#[kani::unwind(6)]
fn finish_iterator_ordinals() {
 let rows:[[u64;4];64]=kani::any();
 let pending=BatchedWeights{raw:rows.to_vec(),terms:0};
 let mut weights=[K::default();64];finish_iterator_contract(&pending,&mut weights);
}
