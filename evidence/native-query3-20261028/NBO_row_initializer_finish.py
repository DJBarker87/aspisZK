from pathlib import Path
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
qraw=lambda:'NBO_qfrom(kani::any::<[u32;4]>())'
raw=','.join('kani::any::<[u64;4]>()' for _ in range(64))
basis=','.join('M31(kani::any())' for _ in range(256))
s+='''
fn NBO_any_q()->K {let w:[u32;4]=kani::any();kani::assume(w[0]<2147483647);kani::assume(w[1]<2147483647);kani::assume(w[2]<2147483647);kani::assume(w[3]<2147483647);NBO_qfrom(w)}
static mut NBO_ROW_TRACE_CALLS:usize=0;
static mut NBO_ROW_TRACE_INDEX:usize=0;
static mut NBO_ROW_WEIGHT_WORDS:[u32;4]=[0;4];
fn NBO_row_trace(slot:u16,index:usize,value:E){unsafe{
 let call=NBO_ROW_TRACE_CALLS;assert!(call<2);NBO_ROW_TRACE_CALLS+=1;assert_eq!(index,NBO_ROW_TRACE_INDEX);
 let k=NBO_COORD;assert_eq!(slot,if call==0 {12}else{13});
 let expected=if call==0 {if k<4 {NBO_ROW_WEIGHT_WORDS[k]}else{0}}else{if k==0 {NBO_ROW_BASIS.0}else{0}};
 assert_eq!(value.to_limbs()[k],expected);
}}
// Frozen release ONE-row body. cfg(prover) is false in the adopted builds.
fn NBO_row_body(a:&Accumulator,weights:&mut BatchedWeights,basis:&[M31;256],j:usize,width:usize){
 weights.push(j,a.power,basis_at(basis,j));
 crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
 crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(basis,j)));
}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::update_residue_row,NBO_update)]
#[kani::stub(crate::trace::value,NBO_row_trace)]
fn NBO_full_row_body(){
 let next:usize=kani::any();kani::assume(next<10);let terms:usize=kani::any();let j:usize=kani::any();kani::assume(j<64);let i:usize=kani::any();kani::assume(i<64);let k:usize=kani::any();kani::assume(k<8);
 let a=Accumulator{weights:Vec::from(['''+','.join('NBO_any_q()' for _ in range(64))+''']),rhs:NBO_any_e(),power:NBO_any_q(),next};
 let mut weights=BatchedWeights{raw:Vec::from(['''+raw+''']),terms};let basis:[M31;256]=['''+basis+'''];kani::assume(basis[j].0<2147483647);
 let reply:[u64;4]=kani::any();let old=weights.raw[i][k%4];let aptr=a.weights.as_ptr();let bptr=weights.raw.as_ptr();
 unsafe{NBO_COORD=k;NBO_ROW_PTR=weights.raw.as_ptr().add(j);NBO_ROW_FLUSH=terms&3==3;NBO_ROW_POWER=a.power;NBO_ROW_BASIS=basis[j];NBO_ROW_REPLY=reply;NBO_ROW_TRACE_INDEX=next*64+j;NBO_ROW_WEIGHT_WORDS=NBO_qwords(a.weights[j]);}
 NBO_row_body(&a,&mut weights,&basis,j,64);
 assert_eq!(weights.raw[i][k%4],if i==j {reply[k%4]}else{old});assert_eq!(weights.terms,terms);assert_eq!(weights.raw.len(),64);assert_eq!(a.weights.as_ptr(),aptr);assert_eq!(weights.raw.as_ptr(),bptr);
 unsafe{assert_eq!(NBO_ROW_CALLS,1);assert_eq!(NBO_ROW_TRACE_CALLS,2);}
 kani::cover!(j==0);kani::cover!(j==63);kani::cover!(i!=j);kani::cover!(k==0);kani::cover!(k==7);
}
// ONE literal constructor while-body on arbitrary reached backing contents.
#[kani::proof]
#[kani::unwind(4096)]
fn NBO_initializer_borrowed_step(){
 let weights:[K;64]=['''+','.join(qraw() for _ in range(64))+'''];let mut raw:[[u64;4];64]=['''+raw+'''];let mut index:usize=kani::any();kani::assume(index<=64);let old_index=index;
 let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);let before=raw[j][k];let mut chosen=0;
 if index<weights.len(){let w=weights[index];chosen=NBO_qwords(w)[k]as u64;raw[index]=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];index+=1;}
 assert_eq!(index,old_index+usize::from(old_index<64));assert_eq!(raw[j][k],if old_index<64&&old_index==j {chosen}else{before});
 kani::cover!(old_index==0);kani::cover!(old_index==63);kani::cover!(old_index==64);kani::cover!(old_index!=j);
}
static mut NBO_FINISH_SELF:*const BatchedWeights=core::ptr::null();
static mut NBO_FINISH_INDEX:usize=0;
static mut NBO_FINISH_VALUE:K=K::ZERO;
static mut NBO_FINISH_CALLS:usize=0;
fn NBO_finish_value_reply(b:&BatchedWeights,index:usize)->K {unsafe{
 assert_eq!(b as *const _,NBO_FINISH_SELF);assert_eq!(index,NBO_FINISH_INDEX);assert_eq!(b.raw.len(),64);NBO_FINISH_CALLS+=1;NBO_FINISH_VALUE
}}
#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::BatchedWeights::value,NBO_finish_value_reply)]
fn NBO_finish_vec_capacity_step(){
 let cap:usize=kani::any();kani::assume(cap>=64&&cap<=isize::MAX as usize/core::mem::size_of::<K>());
 let initial:[K;64]=['''+','.join(qraw() for _ in range(64))+'''];let mut weights:Vec<K>=Vec::with_capacity(cap);weights.extend_from_slice(&initial);
 let b=BatchedWeights{raw:Vec::from(['''+raw+''']),terms:kani::any()};let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=NBO_qwords(weights[j])[k];let ptr=weights.as_ptr();let result=NBO_any_q();
 unsafe{NBO_FINISH_SELF=&b;NBO_FINISH_INDEX=i;NBO_FINISH_VALUE=result;}
 {let mut iter=weights.as_mut_slice().iter_mut().enumerate();if i>0{let _=iter.nth(i-1);}if let Some((index,w))=iter.next(){*w=b.value(index);}}
 assert_eq!(weights.as_ptr(),ptr);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),cap);assert_eq!(NBO_qwords(weights[j])[k],if i<64&&i==j {NBO_qwords(result)[k]}else{before});
 unsafe{assert_eq!(NBO_FINISH_CALLS,if i<64{1}else{0});}
 kani::cover!(cap==64);kani::cover!(cap>64);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}
'''
(E/'NBO_native.rs.txt').write_text(s)
