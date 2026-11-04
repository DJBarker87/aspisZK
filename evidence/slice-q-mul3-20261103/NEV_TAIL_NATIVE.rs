fn NEV_any_wide()->E {
 let limbs:[u32;8]=kani::any();
 for word in limbs {kani::assume(word<2147483647);}
 E::from_limbs(limbs).unwrap()
}
fn NEV_any_qm()->QM31 {
 let limbs:[u32;4]=kani::any();
 for word in limbs {kani::assume(word<2147483647);}
 QM31 {c0:CM31{a:M31(limbs[0]),b:M31(limbs[1])},
       c1:CM31{a:M31(limbs[2]),b:M31(limbs[3])}}
}
fn NEV_qwords(q:QM31)->[u32;4] { [q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0] }
struct NEV_TailLog {
 phase:u8, product_left:[u32;8],product_right:[u32;4],
 add_left:[u32;8],add_right:[u32;8],power_left:[u32;4],power_right:[u32;4],
 product_reply:E,add_reply:E,power_reply:QM31,
}
impl NEV_TailLog {
 fn product(&mut self,x:E,q:QM31)->E {
  assert_eq!(self.phase,0);self.phase=1;
  self.product_left=x.to_limbs();self.product_right=NEV_qwords(q);self.product_reply
 }
 fn add(&mut self,x:E,y:E)->E {
  assert_eq!(self.phase,1);self.phase=2;
  self.add_left=x.to_limbs();self.add_right=y.to_limbs();self.add_reply
 }
 fn power(&mut self,x:QM31,y:QM31)->QM31 {
  assert_eq!(self.phase,2);self.phase=3;
  self.power_left=NEV_qwords(x);self.power_right=NEV_qwords(y);self.power_reply
 }
}
// The native tail after the row loop on independent TX1/TX2 counters. Field
// calls are local owned records, and trace::value is the real deployed no-op.
// This cut does not assume a successful preceding whole-loop result.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn accumulate_tail_context() {
 let mut a=Accumulator {weights:kani::vec::exact_vec::<QM31,64>(),rhs:NEV_any_wide(),power:NEV_any_qm(),next:kani::any()};
 let mut weights=BatchedWeights {raw:kani::vec::exact_vec::<[u64;4],64>(),terms:kani::any()};
 kani::assume(a.next<22 && weights.terms<22);
 let rho=NEV_any_qm();let value=NEV_any_wide();
 let old_next=a.next;let old_terms=weights.terms;let old_rhs=a.rhs;let old_power=a.power;
 let observed:usize=kani::any();let lane:usize=kani::any();kani::assume(observed<64 && lane<4);
 let old_weight=a.weights[observed];let old_raw=weights.raw[observed][lane];
 let ap=a.weights.as_ptr();let bp=weights.raw.as_ptr();
 let ac=a.weights.capacity();let bc=weights.raw.capacity();
 let mut log=NEV_TailLog {phase:0,product_left:[0;8],product_right:[0;4],add_left:[0;8],add_right:[0;8],power_left:[0;4],power_right:[0;4],product_reply:NEV_any_wide(),add_reply:NEV_any_wide(),power_reply:NEV_any_qm()};
 weights.terms+=1;
 let product=log.product(value,a.power);a.rhs=log.add(a.rhs,product);
 crate::trace::value(11,a.next,a.rhs);
 a.power=log.power(a.power,rho);a.next+=1;
 assert_eq!(log.phase,3);
 assert_eq!(log.product_left,value.to_limbs());assert_eq!(log.product_right,NEV_qwords(old_power));
 assert_eq!(log.add_left,old_rhs.to_limbs());assert_eq!(log.add_right,log.product_reply.to_limbs());
 assert_eq!(log.power_left,NEV_qwords(old_power));assert_eq!(log.power_right,NEV_qwords(rho));
 assert_eq!(a.rhs.to_limbs(),log.add_reply.to_limbs());assert_eq!(NEV_qwords(a.power),NEV_qwords(log.power_reply));
 assert!(a.next==old_next+1 && weights.terms==old_terms+1);
 assert!(a.weights.len()==64 && weights.raw.len()==64 && a.weights.capacity()==ac && weights.raw.capacity()==bc && a.weights.as_ptr()==ap && weights.raw.as_ptr()==bp);
 assert_eq!(a.weights[observed],old_weight);
 assert_eq!(weights.raw[observed][lane],if cfg!(NEV_wrong_tail_context){old_raw^1}else{old_raw});
}
