from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
rows=','.join('kani::any::<[u64;4]>()' for _ in range(64))
q=lambda:'K{c0:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())},c1:aspis_core::field::CM31{a:M31(kani::any()),b:M31(kani::any())}}'
s+='''
static mut NBO_ROW_PTR:*const [u64;4]=core::ptr::null();
static mut NBO_ROW_FLUSH:bool=false;
static mut NBO_ROW_POWER:K=K::ZERO;
static mut NBO_ROW_BASIS:M31=M31::ZERO;
static mut NBO_ROW_REPLY:[u64;4]=[0;4];
static mut NBO_ROW_CALLS:usize=0;
fn NBO_update(row:&mut[u64;4],power:K,basis:M31,flush:bool) {unsafe {
 assert_eq!(NBO_ROW_CALLS,0);NBO_ROW_CALLS=1;assert_eq!(row as *const _,NBO_ROW_PTR);
 assert_eq!(flush,NBO_ROW_FLUSH);assert_eq!(basis,NBO_ROW_BASIS);
 let k=NBO_COORD%4;let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];
 assert_eq!(words(power)[k],words(NBO_ROW_POWER)[k]);*row=NBO_ROW_REPLY;}}
// Frozen BatchedWeights::push body with its native Vec slice projection
// factored at the dereference cut, and all other expressions unchanged.
fn NBO_push_borrowed(raw:&mut[[u64;4]],terms:usize,index:usize,power:K,basis:M31) {
 let flush=terms&3==3;
 update_residue_row(&mut raw[index],power,basis,flush);
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::update_residue_row,NBO_update)]
fn NBO_borrowed_push_frame() {
 let mut raw:[[u64;4];64]=['''+rows+'''];let terms:usize=kani::any();let i:usize=kani::any();kani::assume(i<64);
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=raw[j][k];let power='''+q()+''';let basis=M31(kani::any());let reply:[u64;4]=kani::any();
 unsafe{NBO_ROW_PTR=raw.as_ptr().add(i);NBO_ROW_FLUSH=terms&3==3;NBO_ROW_POWER=power;NBO_ROW_BASIS=basis;NBO_ROW_REPLY=reply;NBO_COORD=k;}
 NBO_push_borrowed(&mut raw,terms,i,power,basis);
 assert_eq!(raw[j][k],if i==j {reply[k]}else{before});unsafe{assert_eq!(NBO_ROW_CALLS,1);}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i!=j);kani::cover!(terms&3==3);kani::cover!(terms&3!=3);
}
static mut NBO_REDUCE_INPUT:[u64;4]=[0;4];
static mut NBO_REDUCE_OUTPUT:[u32;4]=[0;4];
static mut NBO_REDUCE_CALLS:usize=0;
fn NBO_reduce(x:u64)->M31 {unsafe {let i=NBO_REDUCE_CALLS;assert!(i<4);NBO_REDUCE_CALLS+=1;assert_eq!(x,NBO_REDUCE_INPUT[i]);M31(NBO_REDUCE_OUTPUT[i])}}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(aspis_core::field::M31::reduce_u64,NBO_reduce)]
fn NBO_finish_one_store() {
 let raw:[[u64;4];64]=['''+rows+'''];let b=BatchedWeights{raw:Vec::from(raw),terms:kani::any()};
 let mut out:[K;64]=['''+','.join(q() for _ in range(64))+'''];
 let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let words=|q:K|[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0];let before=words(out[j])[k];
 let returned:[u32;4]=kani::any();kani::assume(returned[0]<2147483647);kani::assume(returned[1]<2147483647);kani::assume(returned[2]<2147483647);kani::assume(returned[3]<2147483647);
 unsafe{NBO_REDUCE_OUTPUT=returned;if i<64 {NBO_REDUCE_INPUT=b.raw[i];}}
 {let mut iter=out.iter_mut().enumerate();if i>0 {let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 assert_eq!(words(out[j])[k],if i<64&&i==j {returned[k]}else{before});
 unsafe{assert_eq!(NBO_REDUCE_CALLS,if i<64 {4}else{0});}
 assert_eq!(b.raw.len(),64);
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
