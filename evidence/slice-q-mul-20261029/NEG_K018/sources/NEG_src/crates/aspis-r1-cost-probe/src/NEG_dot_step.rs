use super::*;
const MAX_PRODUCT:u64=4611686009837453316;
#[derive(Clone,Copy)] struct Log{left:[u32;8],right:[u32;8],value:[u64;8],count:usize}
fn product(log:&mut Log,a:u32,b:u32)->u64{
 assert!(a<2147483647 && b<2147483647);let value:u64=kani::any();kani::assume(value<=MAX_PRODUCT);
 {let i=log.count;assert!(i<8);log.left[i]=a;log.right[i]=b;log.value[i]=value;log.count=i+1;}value
}
// Literal eight assignment statements from frozen fast_dots.rs:27-34, with
// only each arithmetic product replaced by the bounded log oracle.
fn term(sums:&mut[u64;8],coefficient:[u32;8],scalar:M31,log:&mut Log){
 sums[0]+=product(log,coefficient[0],scalar.0);
 sums[1]+=product(log,coefficient[1],scalar.0);
 sums[2]+=product(log,coefficient[2],scalar.0);
 sums[3]+=product(log,coefficient[3],scalar.0);
 sums[4]+=product(log,coefficient[4],scalar.0);
 sums[5]+=product(log,coefficient[5],scalar.0);
 sums[6]+=product(log,coefficient[6],scalar.0);
 sums[7]+=product(log,coefficient[7],scalar.0);
}
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn term_check(){
 let coefficient:[u32;8]=kani::any();let scalar:u32=kani::any();let n:u8=kani::any();let old:[u64;8]=kani::any();
 kani::assume(n<4 && scalar<2147483647);
 let bound=match n{0=>0,1=>4611686009837453316,2=>9223372019674906632,_=>13835058029512359948};
 for j in 0..8{kani::assume(coefficient[j]<2147483647 && old[j]<=bound);}
 let mut log=Log{left:[0;8],right:[0;8],value:[0;8],count:0};let mut sums=old;term(&mut sums,coefficient,M31(scalar),&mut log);
 {
 assert!(log.count==8);
 let j:usize=kani::any();kani::assume(j<8);
 assert!(log.left[j]==coefficient[j] && log.right[j]==scalar);
 let correct=sums[j]==old[j]+log.value[j];
 assert!(if cfg!(NEG_wrong_term){!correct}else{correct});
 }
}
// Arbitrary outer-loop prestate; literal eight frozen folding assignments.
fn fold_step(limbs:&mut[u64;8],sums:[u64;8]){
 limbs[0]+=(sums[0]&0x7fff_ffff)+(sums[0]>>31);
 limbs[1]+=(sums[1]&0x7fff_ffff)+(sums[1]>>31);
 limbs[2]+=(sums[2]&0x7fff_ffff)+(sums[2]>>31);
 limbs[3]+=(sums[3]&0x7fff_ffff)+(sums[3]>>31);
 limbs[4]+=(sums[4]&0x7fff_ffff)+(sums[4]>>31);
 limbs[5]+=(sums[5]&0x7fff_ffff)+(sums[5]>>31);
 limbs[6]+=(sums[6]&0x7fff_ffff)+(sums[6]>>31);
 limbs[7]+=(sums[7]&0x7fff_ffff)+(sums[7]>>31);
}
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn fold_check(){
 let old:[u64;8]=kani::any();let sums:[u64;8]=kani::any();
 for j in 0..8{kani::assume(old[j]<(1u64<<37));}
 let mut limbs=old;fold_step(&mut limbs,sums);
 let j:usize=kani::any();kani::assume(j<8);
 let correct=limbs[j]==old[j]+(sums[j]&0x7fff_ffff)+(sums[j]>>31);
 assert!(if cfg!(NEG_wrong_fold){!correct}else{correct});
 assert!(limbs[j]<(1u64<<38));
}
#[kani::proof]
fn windows_check(){
 let slot:usize=kani::any();let term:usize=kani::any();kani::assume(slot<4 && term<26);
 let lo=slot*120+term*4;let hi=slot*120+term*4+4;
 let correct=hi<=608 && hi-lo==4 && slot*120+120<=608 && 480+slot*32+32<=608;
 assert!(if cfg!(NEG_wrong_windows){!correct}else{correct});
}
