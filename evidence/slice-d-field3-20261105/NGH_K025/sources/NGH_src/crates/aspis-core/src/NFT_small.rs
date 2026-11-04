use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn any_cm()->CM31{CM31{a:M31(kani::any()),b:M31(kani::any())}}
fn any_q()->QM31{QM31{c0:any_cm(),c1:any_cm()}}
fn canonical(v:QM31)->bool{v.c0.a.0<P&&v.c0.b.0<P&&v.c1.a.0<P&&v.c1.b.0<P}
struct Log<const N:usize>{left:[QM31;N],right:[QM31;N],reply:QM31,count:u8}
fn child<const N:usize>(log:&mut Log<N>,left:[QM31;N],right:[QM31;N])->QM31{assert!(N>=2&&N<=4);for i in 0..N{assert!(canonical(left[i])&&canonical(right[i]));}log.left=left;log.right=right;log.count+=1;let r=any_q();kani::assume(canonical(r));log.reply=r;r}
fn wrapper<const N:usize>(left:[QM31;N],right:[QM31;N],log:&mut Log<N>)->QM31{child(log,left,right)}
fn check<const N:usize>(left:[QM31;N],right:[QM31;N]){for i in 0..N{kani::assume(canonical(left[i])&&canonical(right[i]));}let mut log=Log{left:[QM31::ZERO;N],right:[QM31::ZERO;N],reply:QM31::ZERO,count:0};let got=wrapper(left,right,&mut log);let i:usize=kani::any();kani::assume(i<N);assert!(log.count==1&&log.left[i]==left[i]&&log.right[i]==right[i]);assert!((got==log.reply)!=cfg!(NFT_invert));}
struct Sequence{index:[usize;4],count:usize}
fn control<const N:usize>(log:&mut Sequence){let mut index=0usize;while index<N{log.index[log.count]=index;log.count+=1;index+=1;}}
fn check_control<const N:usize>(){let mut log=Sequence{index:[99;4],count:0};control::<N>(&mut log);assert!(log.count==N);let i:usize=kani::any();kani::assume(i<N);assert!(log.index[i]==if cfg!(NFT_invert){i+1}else{i});}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn wrapper2(){check([any_q(), any_q()],[any_q(), any_q()]);}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn control2(){check_control::<2>();}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn wrapper3(){check([any_q(), any_q(), any_q()],[any_q(), any_q(), any_q()]);}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn control3(){check_control::<3>();}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn wrapper4(){check([any_q(), any_q(), any_q(), any_q()],[any_q(), any_q(), any_q(), any_q()]);}

#[kani::proof] #[kani::unwind(45)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn control4(){check_control::<4>();}
