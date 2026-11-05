#[derive(Clone,Copy)]struct Call{kind:u8,a:QM31,b:QM31}
struct PowerLog{events:[Call;6],replies:[QM31;6],count:usize}
fn multiply_cut(a:QM31,b:QM31,log:&mut PowerLog)->QM31{assert!(words(a).iter().all(|&x|x<P));assert!(words(b).iter().all(|&x|x<P));let i=log.count;log.events[i]=Call{kind:1,a,b};log.count+=1;log.replies[i]}
fn square_cut(a:QM31,log:&mut PowerLog)->QM31{assert!(words(a).iter().all(|&x|x<P));let i=log.count;log.events[i]=Call{kind:0,a,b:a};log.count+=1;log.replies[i]}
include!("NHU_power_body.rs");
#[kani::proof]#[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NHU_power26(){let v=canonical_q();let replies:[QM31;6]=core::array::from_fn(|_|canonical_q());let zero=Call{kind:0,a:QM31::ZERO,b:QM31::ZERO};let mut log=PowerLog{events:[zero;6],replies,count:0};let out=NHU_power26_cut(v,&mut log);assert_eq!(log.count,6);let i:usize=kani::any();kani::assume(i<6);let limb:usize=kani::any();kani::assume(limb<4);let left=match i{0=>v,1=>replies[0],2=>replies[1],3=>replies[2],4=>replies[3],_=>replies[4]};let right=match i{0=>v,1=>replies[0],2=>replies[1],3=>replies[2],4=>replies[2],_=>replies[0]};assert_eq!(log.events[i].kind,if i<4{0}else{1});assert_eq!(words(log.events[i].a)[limb],words(left)[limb]^if cfg!(NHU_invert){1}else{0});assert_eq!(words(log.events[i].b)[limb],words(right)[limb]);assert_eq!(words(out)[limb],words(replies[5])[limb]);}
