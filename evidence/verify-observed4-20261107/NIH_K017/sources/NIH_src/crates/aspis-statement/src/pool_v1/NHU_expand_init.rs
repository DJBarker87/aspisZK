include!("NHU_expand_init_body.rs");
fn NHU_expand_init_window<const N:usize>(){let (weights,len)=NHU_expand_init_cut::<N>();let j:usize=kani::any();kani::assume(j<N);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(words(weights[j])[limb],if j==0&&limb==0{1}else{0}^if cfg!(NHU_invert){2}else{0});assert_eq!(len,1);}
#[kani::proof]#[kani::unwind(20)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand_init16(){NHU_expand_init_window::<16>();}
#[kani::proof]#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_expand_init64(){NHU_expand_init_window::<64>();}
