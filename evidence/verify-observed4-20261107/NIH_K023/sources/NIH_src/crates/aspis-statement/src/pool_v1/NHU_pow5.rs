struct PowLog{count:usize,kinds:[u8;3],left:[QM31;3],right:[QM31;3],replies:[QM31;3]}
fn pow_square(value:QM31,log:&mut PowLog)->QM31{let i=log.count;log.count+=1;log.kinds[i]=0;log.left[i]=value;log.replies[i]}
fn pow_mul(left:QM31,right:QM31,log:&mut PowLog)->QM31{let i=log.count;log.count+=1;log.kinds[i]=1;log.left[i]=left;log.right[i]=right;log.replies[i]}
include!("NHU_pow5_body.rs");
#[kani::proof]#[kani::unwind(8)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_pow5(){let x=canonical_q();let replies:[QM31;3]=core::array::from_fn(|_|canonical_q());let mut log=PowLog{count:0,kinds:[9;3],left:[QM31::ZERO;3],right:[QM31::ZERO;3],replies};let out=NHU_pow5_cut(x,&mut log);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(words(out)[limb],words(replies[2])[limb]^if cfg!(NHU_invert){1}else{0});assert_eq!(log.count,3);assert_eq!(log.kinds,[0,0,1]);assert_eq!(log.left,[x,replies[0],replies[1]]);assert_eq!(log.right,[QM31::ZERO,QM31::ZERO,x]);}
