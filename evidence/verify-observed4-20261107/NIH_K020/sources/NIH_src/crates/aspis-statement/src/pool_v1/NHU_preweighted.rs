struct PackLog{count:usize,lanes:[QM31;4],reply:QM31,muls:usize,left:QM31,right:QM31,product:QM31}
fn pack_cut(lanes:&[QM31;4],log:&mut PackLog)->QM31{log.count+=1;log.lanes=*lanes;log.reply}
fn shared_cut(left:QM31,right:QM31,log:&mut PackLog)->QM31{log.muls+=1;log.left=left;log.right=right;log.product}
fn canonical_q()->QM31{let w:[u32;4]=kani::any();for v in w{kani::assume(v<2147483647);}QM31{c0:aspis_core::field::CM31{a:M31(w[0]),b:M31(w[1])},c1:aspis_core::field::CM31{a:M31(w[2]),b:M31(w[3])}}}
fn add_word(a:u32,b:u32)->u32{let v=a+b;if v>=2147483647{v-2147483647}else{v}}
include!("NHU_preweighted_body.rs");
include!("NHU_preweighted_shared_selector_body.rs");
fn NHU_preweighted_window<const N:usize>(shared:bool){
 let mut packed:[QM31;24]=core::array::from_fn(|_|canonical_q());let before=packed;
 let values:[QM31;N]=core::array::from_fn(|_|canonical_q());
 let start:usize=kani::any();kani::assume(start<=96);kani::assume(start+N<=96);let first=start/4;let last=(start+N-1)/4;
 let group:usize=kani::any();kani::assume(first<=group&&group<=last);
 let done:bool=kani::any();let mut iter=if done{last..=last}else{group..=last};if done{let _=iter.next();}
 let selector=canonical_q();let reply=canonical_q();let product=canonical_q();
 let mut log=PackLog{count:0,lanes:[QM31::ZERO;4],reply,muls:0,left:QM31::ZERO,right:QM31::ZERO,product};
 if shared{NHU_preweighted_shared_selector_cut(&mut packed,start,&values,selector,&mut iter,&mut log);}else{NHU_preweighted_cut(&mut packed,start,&values,&mut iter,&mut log);}
 let j:usize=kani::any();kani::assume(j<24);let limb:usize=kani::any();kani::assume(limb<4);
 let expected=if !done&&j==group{add_word(words(before[j])[limb],words(if shared{product}else{reply})[limb])}else{words(before[j])[limb]};
 assert_eq!(words(packed[j])[limb],expected^if cfg!(NHU_invert){1}else{0});
 assert_eq!(log.count,if done{0}else{1});assert_eq!(log.muls,if !done&&shared{1}else{0});
 assert_eq!(*iter.end(),last);assert_eq!(*iter.start(),if done{last}else if group<last{group+1}else{last});assert_eq!(iter.is_empty(),done||group==last);
 if !done{let slot:usize=kani::any();kani::assume(slot<4);let source=4*group+slot;let expected=if source>=start&&source<start+N{values[source-start]}else{QM31::ZERO};assert_eq!(words(log.lanes[slot])[limb],words(expected)[limb]);if shared{assert_eq!(log.left,selector);assert_eq!(log.right,reply);}}
}

#[kani::proof]#[kani::unwind(30)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_preweighted_2(){NHU_preweighted_window::<2>(false);}

#[kani::proof]#[kani::unwind(30)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_preweighted_12(){NHU_preweighted_window::<12>(false);}

#[kani::proof]#[kani::unwind(30)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_preweighted_16(){NHU_preweighted_window::<16>(false);}

#[kani::proof]#[kani::unwind(30)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_preweighted_17(){NHU_preweighted_window::<17>(false);}

#[kani::proof]#[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_preweighted_shared33(){NHU_preweighted_window::<33>(true);}
