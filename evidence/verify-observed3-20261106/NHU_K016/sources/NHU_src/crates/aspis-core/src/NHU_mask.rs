include!("NHU_coeff0_body.rs");
include!("NHU_coeff1_body.rs");
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_coeff0(){let input:[QM31;16]=core::array::from_fn(|_|canonical_q());let mut coefficients:[QM31;27]=core::array::from_fn(|_|canonical_q());let col:usize=kani::any();kani::assume(col<=16);let observed:usize=kani::any();kani::assume(observed<27);let limb:usize=kani::any();kani::assume(limb<4);let old=words(coefficients[observed])[limb];let expected=if col<16&&observed==usize::from(FACTOR_EXPONENTS[col]){words(mul_tower_basis(input[col],col&3))[limb]}else{old};let next=NHU_coeff0_cut(&input,&mut coefficients,col);assert_eq!(next,if col<16{col+1}else{16});assert_eq!(words(coefficients[observed])[limb],expected^if cfg!(NHU_invert){1}else{0});assert!(words(coefficients[observed])[limb]<P);}
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_coeff1(){let input:[QM31;10]=core::array::from_fn(|_|canonical_q());let mut coefficients:[QM31;27]=core::array::from_fn(|_|canonical_q());let col:usize=kani::any();kani::assume(col<=10);let observed:usize=kani::any();kani::assume(observed<27);let limb:usize=kani::any();kani::assume(limb<4);let old=words(coefficients[observed])[limb];let expected=if col<10&&observed==usize::from(MASK_ONLY_FACTOR_EXPONENTS[col]){words(mul_tower_basis(input[col],col&3))[limb]}else{old};let next=NHU_coeff1_cut(&input,&mut coefficients,col);assert_eq!(next,if col<10{col+1}else{10});assert_eq!(words(coefficients[observed])[limb],expected^if cfg!(NHU_invert){1}else{0});assert!(words(coefficients[observed])[limb]<P);}
struct PreparedLog{count:usize,p:PreparedQm31Multiplier,input:QM31,reply:QM31}
fn prepared_cut(p:PreparedQm31Multiplier,input:QM31,log:&mut PreparedLog)->QM31{assert!(words(input).iter().all(|&x|x<P));log.p=p;log.input=input;log.count+=1;log.reply}
include!("NHU_horner_body.rs");
#[kani::proof]#[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_horner(){let coefficients:[QM31;27]=core::array::from_fn(|_|canonical_q());let linear=canonical_q();let prepared=PreparedQm31Multiplier::new(linear);let shared=canonical_q();let reply=canonical_q();let n:usize=kani::any();kani::assume(n<=26);let mut log=PreparedLog{count:0,p:PreparedQm31Multiplier::new(QM31::ZERO),input:QM31::ZERO,reply};let (out,next)=NHU_horner_cut(&coefficients,prepared,shared,n,&mut log);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(next,if n==0{0}else{n-1});assert_eq!(log.count,if n==0{0}else{1});if n>0{assert_eq!(log.p,prepared);assert_eq!(words(log.input)[limb],words(shared)[limb]);}let expected=if n==0{words(shared)[limb]}else{add(words(reply)[limb],words(coefficients[n-1])[limb])};assert_eq!(words(out)[limb],expected^if cfg!(NHU_invert){1}else{0});}
struct TailLog{powers:usize,products:usize,power_arg:QM31,a:QM31,b:QM31,power_reply:QM31,product_reply:QM31}
fn power_tail(v:QM31,log:&mut TailLog)->QM31{assert!(words(v).iter().all(|&x|x<P));log.powers+=1;log.power_arg=v;log.power_reply}
fn multiply_tail(a:QM31,b:QM31,log:&mut TailLog)->QM31{assert!(words(a).iter().all(|&x|x<P));assert!(words(b).iter().all(|&x|x<P));log.products+=1;log.a=a;log.b=b;log.product_reply}
include!("NHU_mask_tail_body.rs");
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_mask_tail(){let shared=canonical_q();let linear=canonical_q();let g=canonical_q();let power=canonical_q();let product=canonical_q();let mut log=TailLog{powers:0,products:0,power_arg:QM31::ZERO,a:QM31::ZERO,b:QM31::ZERO,power_reply:power,product_reply:product};let out=NHU_mask_tail_cut(shared,linear,g,&mut log);let limb:usize=kani::any();kani::assume(limb<4);assert_eq!(log.powers,1);assert_eq!(log.products,1);assert_eq!(words(log.power_arg)[limb],words(linear)[limb]);assert_eq!(words(log.a)[limb],add(words(power)[limb],if limb==0{1}else{0}));assert_eq!(words(log.b)[limb],words(g)[limb]);assert_eq!(words(out)[limb],add(words(shared)[limb],words(product)[limb])^if cfg!(NHU_invert){1}else{0});}
