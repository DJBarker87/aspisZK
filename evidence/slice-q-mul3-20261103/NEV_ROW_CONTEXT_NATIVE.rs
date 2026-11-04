// The BW mutation itself is the CLOSED NEI push bridge, not a second native
// proof of its arithmetic. This local record checks the caller's exact input
// to that endpoint, followed by its two real diagnostic conversion calls.
struct NEV_PushCallLog {called:bool,index:usize,power:[u32;4],basis:u32}
impl NEV_PushCallLog {
 fn call(&mut self,index:usize,power:QM31,basis:M31) {
  assert!(!self.called);self.called=true;self.index=index;
  self.power=NEV_qwords(power);self.basis=basis.0;
 }
}
#[kani::proof] #[kani::unwind(260)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn accumulate_row_context() {
 let basis:[M31;256]=kani::any();
 let weights=kani::vec::exact_vec::<QM31,64>();
 let power=NEV_any_qm();let next:usize=kani::any();kani::assume(next<22);
 let j:usize=kani::any();kani::assume(j<64);
 let basis_word=basis[j].0;kani::assume(basis_word<2147483647);
 let weight=weights[j];let pointer=weights.as_ptr();let capacity=weights.capacity();
 let observed:usize=kani::any();kani::assume(observed<64);let before=weights[observed];
 let mut log=NEV_PushCallLog {called:false,index:0,power:[0;4],basis:0};
 let mut iter=j..64;let index=iter.next().unwrap();
 let m=basis_at(&basis,index);log.call(index,power,m);
 let offset=next*weights.len()+index;
 let lift_q=E::from_qm31(accumulated_weight_at(&weights,index));
 crate::trace::value(12,offset,lift_q);
 let lift_m=<E as aspis_core::r0::CodeField>::from_m31(basis_at(&basis,index));
 crate::trace::value(13,next*weights.len()+index,lift_m);
 assert!(log.called && log.index==j && log.power==NEV_qwords(power) && log.basis==basis_word);
 assert!(iter.start==j+1 && iter.end==64 && offset==next*64+j && offset<1408);
 assert!(weights.len()==64 && weights.capacity()==capacity && weights.as_ptr()==pointer);
 assert_eq!(weights[observed],before);
 let got=lift_q.to_limbs();let w=NEV_qwords(weight);
 for limb in 0..4 {assert_eq!(got[limb],w[limb]%2147483647);assert_eq!(got[limb+4],0);}
 let expected=[basis_word,0,0,0,0,0,0,0];
 let at:usize=kani::any();kani::assume(at<8);
 assert_eq!(lift_m.to_limbs()[at],if cfg!(NEV_wrong_row_context){expected[at]^1}else{expected[at]});
}
