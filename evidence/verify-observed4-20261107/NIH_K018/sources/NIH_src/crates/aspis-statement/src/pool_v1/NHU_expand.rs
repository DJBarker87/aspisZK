struct ExpandLog{count:usize,owner:*const aspis_core::field::PreparedQm31Multiplier,parent:QM31,reply:QM31}
fn expand_product(prepared:&aspis_core::field::PreparedQm31Multiplier,parent:QM31,log:&mut ExpandLog)->QM31{log.count+=1;log.owner=prepared as *const _;log.parent=parent;log.reply}
include!("NHU_expand_body.rs");
fn sub_word(a:u32,b:u32)->u32{if a>=b{a-b}else{2147483647-(b-a)}}
fn NHU_expand_window<const N:usize>(){let mut weights:[QM31;N]=core::array::from_fn(|_|canonical_q());let before=weights;let coordinate=canonical_q();let prepared=aspis_core::field::PreparedQm31Multiplier::new(coordinate);let reply=canonical_q();let len:usize=kani::any();kani::assume(len>0&&len<=N/2);let remaining:usize=kani::any();kani::assume(remaining<=len);let mut range=0..remaining;let mut log=ExpandLog{count:0,owner:core::ptr::null(),parent:QM31::ZERO,reply};NHU_expand_inner_cut(&mut weights,&prepared,&mut range.by_ref().rev(),&mut log);let j:usize=kani::any();kani::assume(j<N);let limb:usize=kani::any();kani::assume(limb<4);let expected=if remaining>0&&j==2*(remaining-1){sub_word(words(before[remaining-1])[limb],words(reply)[limb])}else if remaining>0&&j==2*(remaining-1)+1{words(reply)[limb]}else{words(before[j])[limb]};assert_eq!(words(weights[j])[limb],expected^if cfg!(NHU_invert){1}else{0});assert_eq!(log.count,if remaining>0{1}else{0});assert_eq!(range.start,0);assert_eq!(range.end,remaining.saturating_sub(1));if remaining>0{assert_eq!(log.parent,before[remaining-1]);assert_eq!(log.owner,&prepared as *const _);}}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand16(){NHU_expand_window::<16>();}
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand64(){NHU_expand_window::<64>();}
