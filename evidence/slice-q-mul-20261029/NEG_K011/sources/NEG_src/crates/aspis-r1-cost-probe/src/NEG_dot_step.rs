use super::*;
const MAX_PRODUCT:u64=4611686009837453316;
#[derive(Clone,Copy)] struct Log{left:[u32;8],right:[u32;8],value:[u64;8],count:usize}
static mut LOG:Log=Log{left:[0;8],right:[0;8],value:[0;8],count:0};
fn product(a:u32,b:u32)->u64{
 assert!(a<2147483647 && b<2147483647);let value:u64=kani::any();kani::assume(value<=MAX_PRODUCT);
 unsafe{let i=LOG.count;assert!(i<8);LOG.left[i]=a;LOG.right[i]=b;LOG.value[i]=value;LOG.count=i+1;}value
}
// Literal eight assignment statements from frozen fast_dots.rs:27-34, with
// only each arithmetic product replaced by the bounded log oracle.
fn term(sums:&mut[u64;8],coefficient:[u32;8],scalar:M31){
 sums[0]+=product(coefficient[0],scalar.0);
 sums[1]+=product(coefficient[1],scalar.0);
 sums[2]+=product(coefficient[2],scalar.0);
 sums[3]+=product(coefficient[3],scalar.0);
 sums[4]+=product(coefficient[4],scalar.0);
 sums[5]+=product(coefficient[5],scalar.0);
 sums[6]+=product(coefficient[6],scalar.0);
 sums[7]+=product(coefficient[7],scalar.0);
}
#[kani::proof] #[kani::unwind(12)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEG_copy::KMX_copy_nonoverlapping)]
fn term_check(){
 let coefficient:[u32;8]=kani::any();let scalar:u32=kani::any();let n:u8=kani::any();let old:[u64;8]=kani::any();
 kani::assume(n<4 && scalar<2147483647);
 let bound=match n{0=>0,1=>4611686009837453316,2=>9223372019674906632,_=>13835058029512359948};
 for j in 0..8{kani::assume(coefficient[j]<2147483647 && old[j]<=bound);}
 unsafe{LOG.count=0;}let mut sums=old;term(&mut sums,coefficient,M31(scalar));
 unsafe{
 assert!(LOG.count==8);
 let j:usize=kani::any();kani::assume(j<8);
 assert!(LOG.left[j]==coefficient[j] && LOG.right[j]==scalar);
 let correct=sums[j]==old[j]+LOG.value[j];
 assert!(if cfg!(NEG_wrong_term){!correct}else{correct});
 }
}
