use super::*;
// Native constructor, arbitrary advance, next, write and borrow restoration.
// No product or field operation is reached. The row is the actual full array.
#[kani::proof]
#[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn iterator_context() {
 let before:[u64;4]=kani::any(); let mut row=before;
 let offset:usize=kani::any(); kani::assume(offset<=4);
 let replacement:u64=kani::any();
 let reply;
 {
  let mut it=(&mut row).into_iter();
  for _ in 0..offset { let _ = it.next().unwrap(); }
  assert_eq!(it.len(),4-offset);
  reply=match it.next() {
   Some(word)=>{let old=*word; *word=replacement; Some(old)},
   None=>None
  };
  assert_eq!(it.len(),4-offset-usize::from(offset<4));
 }
 if offset<4 {assert_eq!(reply,Some(before[offset]));}else{assert_eq!(reply,None);}
 let at:usize=kani::any(); kani::assume(at<4);
 let expected=if at==offset {replacement}else{before[at]};
 assert_eq!(row[at],if cfg!(NEV_wrong_iterator){expected^1}else{expected});
}
#[kani::proof]
#[kani::unwind(7)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn copy_row_window() {
 let before:[u64;4]=kani::any();let after=before;
 let at:usize=kani::any();kani::assume(at<4);
 assert_eq!(after[at],if cfg!(NEV_wrong_row_copy){before[at]^1}else{before[at]});
}
// Caller allocation: BatchedWeights::new allocates exactly 64 four-word rows.
// One arbitrary mutable index, row result and disjoint row/lane window.
#[kani::proof]
#[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn vector_row_context() {
 let mut raw=kani::vec::exact_vec::<[u64;4],64>();
 let index:usize=kani::any(); let at:usize=kani::any();let lane:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4);
 let before=raw[at][lane];let old=raw[index];
 let replacement:[u64;4]=kani::any();let reply;
 let pointer=raw.as_ptr();let capacity=raw.capacity();
 {let row=&mut raw[index];reply=*row;*row=replacement;}
 assert_eq!(reply,old);
 assert!(raw.len()==64 && raw.capacity()==capacity && raw.as_ptr()==pointer);
 let expected=if at==index {replacement[lane]}else{before};
 assert_eq!(raw[at][lane],if cfg!(NEV_wrong_vector_row){expected^1}else{expected});
}
// Genuine split of timed-out vector_row_context: Vec-to-slice borrow geometry.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn vector_row_geometry() {
 let mut raw=kani::vec::exact_vec::<[u64;4],64>();
 let index:usize=kani::any();kani::assume(index<64);
 let pointer=raw.as_mut_ptr();let capacity=raw.capacity();
 let got={let row=&mut raw[index];row as *mut [u64;4]};
 let expected=unsafe{pointer.add(if cfg!(NEV_wrong_row_geometry){(index+1)%64}else{index})};
 assert_eq!(got,expected);
 assert!(raw.as_mut_ptr()==pointer && raw.len()==64 && raw.capacity()==capacity);
 // The actual allocated vector's disjoint byte window, not a guard array.
 let observed:usize=kani::any();let byte:usize=kani::any();kani::assume(observed<64 && observed!=index && byte<32);
 assert!(core::mem::size_of::<[u64;4]>()==32);
 let start=got as usize;let address=unsafe{pointer.add(observed).cast::<u8>().add(byte)} as usize;
 let outside=address<start || start+32<=address;
 assert!(if cfg!(NEV_wrong_disjoint){!outside}else{outside});
}
// Other split: one arbitrary native nested-slice write and disjoint window.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn slice_row_lane() {
 let before:[[u64;4];64]=kani::any();let mut rows=before;
 let index:usize=kani::any();let lane:usize=kani::any();let at:usize=kani::any();let col:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4 && col<4);
 let value:u64=kani::any();let old;
 {let slice:&mut [[u64;4]]=&mut rows;let row=&mut slice[index];old=row[lane];row[lane]=value;}
 assert_eq!(old,before[index][lane]);
 let expected=if index==at && lane==col {value}else{before[at][col]};
 assert_eq!(rows[at][col],if cfg!(NEV_wrong_slice_row){expected^1}else{expected});
}

// Further isolation: one before-window, no full 2 KiB carrier duplication.
#[kani::proof] #[kani::unwind(68)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn slice_row_write_window() {
 let mut rows:[[u64;4];64]=kani::any();
 let index:usize=kani::any();let lane:usize=kani::any();let at:usize=kani::any();let col:usize=kani::any();
 kani::assume(index<64 && at<64 && lane<4 && col<4);
 let before=rows[at][col];let selected=rows[index][lane];let replacement:u64=kani::any();let reply;
 {let slice:&mut [[u64;4]]=&mut rows;let row=&mut slice[index];let word=&mut row[lane];reply=*word;*word=replacement;}
 assert_eq!(reply,selected);
 let expected=if index==at && lane==col {replacement}else{before};
 assert_eq!(rows[at][col],if cfg!(NEV_wrong_slice_window){expected^1}else{expected});
}

// Fresh actual getter assertions and immutable full-carrier frame; these do
// not restore or rename the older NCI contract evidence.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn residue_getter() {
 let row:[u64;4]=kani::any();let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<4 && observed<4);
 let before=row[observed];let expected=row[index];let got=residue_limb_at(&row,index);
 assert_eq!(got,if cfg!(NEV_wrong_residue_getter){expected^1}else{expected});assert_eq!(row[observed],before);
}
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn power_getter() {
 let limbs:[u32;4]=kani::any();let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<4 && observed<4);
 let before=limbs[observed];let expected=limbs[index];let got=power_limb_at(&limbs,index);
 assert_eq!(got,if cfg!(NEV_wrong_power_getter){expected^1}else{expected});assert_eq!(limbs[observed],before);
}

// Independent real callee needed by the dot finish path. Full Option tag and
// all eight returned raw coordinates; no function contract or multiplication.
#[kani::proof] #[kani::unwind(80)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn wide_from_limbs() {
 let words:[u32;8]=kani::any();let got=E::from_limbs(words).map(|v|v.to_limbs());
 let mut valid=true;for word in words {valid &= word<2147483647;}
 let mut expected=if valid{Some(words)}else{None};
 if cfg!(NEV_wrong_wide_ctor){expected=if let Some(mut out)=expected{out[0]^=1;Some(out)}else{Some([0;8])};}
 assert_eq!(got,expected);
}

// Small documented outside-Q constructor; actual frozen trait/body executes.
#[kani::proof] #[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn codefield_m31_lift() {
 let word:u32=kani::any();let observed:usize=kani::any();kani::assume(observed<8);
 let actual=<E as aspis_core::r0::CodeField>::from_m31(M31(word)).to_limbs();
 let expected=if observed==0{word%2147483647}else{0};
 assert_eq!(actual[observed],if cfg!(NEV_wrong_lift){expected^1}else{expected});
}
// Local opaque product call. No native multiplication executes here; each
// specialization is paired with NEI_PrefixProduct.actual (ALL raw M31 words).
#[derive(Default)]
struct NEV_BasisProductLog { called:bool, lhs:u32, rhs:u32, reply:u32 }
impl NEV_BasisProductLog {
 fn call(&mut self,left:M31,right:M31)->M31 {
  assert!(!self.called);
  self.called=true;self.lhs=left.0;self.rhs=right.0;
  M31(self.reply)
 }
}
// ONE native inner iteration at an arbitrary pre-state and arbitrary observed
// frame cell. Source body's only replacement is product -> local call record.
// No full-array duplication; the actual 256-cell carrier is retained.
#[kani::proof] #[kani::unwind(260)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn basis_inner_iteration() {
 let mut basis:[M31;256]=kani::any();
 let node=M31(kani::any());let n:usize=kani::any();let j:usize=kani::any();
 kani::assume(n>0 && n<=32 && j<n);
 let observed:usize=kani::any();kani::assume(observed<256);
 let before=basis[observed].0;let operand=basis[j].0;
 let mut product=NEV_BasisProductLog {reply:kani::any(),..Default::default()};
 kani::assume(product.reply<2147483647);
 let mut iter=j..n;
 let selected=iter.next().unwrap();
 basis[n+selected]=product.call(basis[selected],node);
 assert!(product.called && product.lhs==operand && product.rhs==node.0);
 assert!(iter.start==j+1 && iter.end==n);
 let expected=if observed==n+j{product.reply}else{before};
 assert_eq!(basis[observed].0,if cfg!(NEV_wrong_basis_inner){expected^1}else{expected});
}
// ONE outer scalar update after its inner loop: square is the sole opaque
// operation. The actual M31::double and M31::sub execute on its canonical reply.
#[kani::proof] #[kani::unwind(64)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEV_copy::KMX_copy_nonoverlapping)]
fn basis_outer_scalar() {
 let mut node=M31(kani::any());let original=node.0;
 let mut n:usize=kani::any();kani::assume(n>0 && n<=32);let old_n=n;
 let mut product=NEV_BasisProductLog {reply:kani::any(),..Default::default()};
 kani::assume(product.reply<2147483647);
 node=product.call(node,node).double().sub(M31::ONE);n*=2;
 assert!(product.called && product.lhs==original && product.rhs==original);
 assert_eq!(n,old_n+old_n);
 let twice=product.reply+product.reply;
 let reduced=if twice>=2147483647{twice-2147483647}else{twice};
 let expected=if reduced==0{2147483646}else{reduced-1};
 assert_eq!(node.0,if cfg!(NEV_wrong_basis_outer){expected^1}else{expected});
 assert!(node.0<2147483647);
}

use aspis_core::field::{QM31,CM31};
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
