include!("NHU_expand_prefix_body.rs");
include!("NHU_expand_left_body.rs");
include!("NHU_expand_right_body.rs");
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand_prefix64(){let weights:[QM31;64]=core::array::from_fn(|_|canonical_q());let coordinate=canonical_q();let prepared=aspis_core::field::PreparedQm31Multiplier::new(coordinate);let reply=canonical_q();let remaining:usize=kani::any();kani::assume(remaining<=32);let mut range=0..remaining;let mut log=ExpandLog{count:0,owner:core::ptr::null(),parent:QM31::ZERO,reply};let out=NHU_expand_prefix_cut(&weights,&prepared,&mut range.by_ref().rev(),&mut log);assert!(out.is_some()==((remaining>0)^cfg!(NHU_invert)));assert_eq!(range.start,0);assert_eq!(range.end,remaining.saturating_sub(1));assert_eq!(log.count,if remaining>0{1}else{0});if let Some((i,parent,right))=out{assert_eq!(i,remaining-1);assert_eq!(parent,weights[i]);assert_eq!(right,reply);assert_eq!(log.parent,parent);assert_eq!(log.owner,&prepared as *const _);}}
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand_left64(){let mut weights:[QM31;64]=core::array::from_fn(|_|canonical_q());let before=weights;let parent=canonical_q();let right=canonical_q();let index:usize=kani::any();kani::assume(index<32);NHU_expand_left_cut(&mut weights,index,parent,right);let j:usize=kani::any();kani::assume(j<64);let limb:usize=kani::any();kani::assume(limb<4);let expected=if j==2*index{sub_word(words(parent)[limb],words(right)[limb])}else{words(before[j])[limb]};assert_eq!(words(weights[j])[limb],expected^if cfg!(NHU_invert){1}else{0});}
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand_right64(){let mut weights:[QM31;64]=core::array::from_fn(|_|canonical_q());let before=weights;let right=canonical_q();let index:usize=kani::any();kani::assume(index<32);NHU_expand_right_cut(&mut weights,index,right);let j:usize=kani::any();kani::assume(j<64);let limb:usize=kani::any();kani::assume(limb<4);let expected=if j==2*index+1{words(right)[limb]}else{words(before[j])[limb]};assert_eq!(words(weights[j])[limb],expected^if cfg!(NHU_invert){1}else{0});}
