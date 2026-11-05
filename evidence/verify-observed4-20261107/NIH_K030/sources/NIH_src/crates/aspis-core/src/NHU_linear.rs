include!("NHU_linear_body.rs");
#[kani::proof]#[kani::unwind(15)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_linears_step(){let point:[QM31;10]=core::array::from_fn(|_|canonical_q());let suffix=canonical_q();let weighted=canonical_q();let n:usize=kani::any();kani::assume(n<=10);let (s,w,next)=NHU_linear_step(&point,suffix,weighted,n);let limb:usize=kani::any();kani::assume(limb<4);let expect_s=if n==0{words(suffix)[limb]}else{add(words(suffix)[limb],words(point[n-1])[limb])};let expect_w=if n>1{add(words(weighted)[limb],expect_s)}else{words(weighted)[limb]};assert_eq!(next,if n==0{0}else{n-1});assert_eq!(words(s)[limb],expect_s^if cfg!(NHU_invert){1}else{0});assert_eq!(words(w)[limb],expect_w);assert!(words(s)[limb]<P&&words(w)[limb]<P);}
struct ScalarLog{count:usize,inputs:[QM31;4],scalars:[u32;4],replies:[QM31;4]}
fn scalar_cut(value:QM31,scalar:M31,log:&mut ScalarLog)->QM31{assert!(words(value).iter().all(|&x|x<P));assert!(scalar.0<P);let i=log.count;log.inputs[i]=value;log.scalars[i]=scalar.0;log.count+=1;log.replies[i]}
include!("NHU_linear_suffix_body.rs");
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_linears_suffix(){let suffix=canonical_q();let weighted=canonical_q();let replies:[QM31;4]=core::array::from_fn(|_|canonical_q());let mut log=ScalarLog{count:0,inputs:[QM31::ZERO;4],scalars:[0;4],replies};let (a,b)=NHU_linear_suffix(suffix,weighted,&mut log);assert_eq!(log.count,4);let call:usize=kani::any();kani::assume(call<4);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(log.scalars[call],[3,22,275,150][call]);assert_eq!(words(log.inputs[call])[limb],words(if call%2==0{suffix}else{weighted})[limb]^if cfg!(NHU_invert){1}else{0});assert_eq!(words(a)[limb],add(words(replies[0])[limb],words(replies[1])[limb]));assert_eq!(words(b)[limb],add(words(replies[2])[limb],words(replies[3])[limb]));}
