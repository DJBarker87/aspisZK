#[cfg(kani)]
mod PV_L2_proofs {
use super::*;
fn arbitrary_scan(len:usize,draws:usize)->QueryScan {
 QueryScan {accepted:kani::any(),accepted_len:len,draws}
}
fn equal_prefix(a:&QueryScan,b:&QueryScan) {
 assert_eq!(a.accepted_len,b.accepted_len); assert_eq!(a.draws,b.draws);
 for i in 0..22 {if i<a.accepted_len {assert_eq!(a.accepted[i],b.accepted[i]);}}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_stop_count() {
 let mut a=arbitrary_scan(22,kani::any());kani::assume(a.draws<=64);
 let mut b=QueryScan{accepted:a.accepted,accepted_len:22,draws:a.draws};
 let x:[u8;32]=kani::any();let y:[u8;32]=kani::any();
 assert!(a.scan(&x));assert!(b.scan(&y));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_stop_draws() {
 let len:usize=kani::any();kani::assume(len<=22);
 let mut a=arbitrary_scan(len,64);let mut b=QueryScan{accepted:a.accepted,accepted_len:len,draws:64};
 assert!(a.scan(&kani::any()));assert!(b.scan(&kani::any()));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_query_words() {
 let x:[u8;32]=kani::any();let w=query_words(&x);
 for i in 0..8 {assert!(w[i]<QUERY_BOUND);assert_eq!(w[i],u32::from_le_bytes([x[4*i],x[4*i+1],x[4*i+2],x[4*i+3]]) & (QUERY_BOUND-1));}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_scan_unused_suffix() {
 let len:usize=kani::any();kani::assume(len<=22);let draws:usize=kani::any();kani::assume(draws<=64);
 let mut a=arbitrary_scan(len,draws);let mut b=arbitrary_scan(len,draws);
 for i in 0..22 {if i<len {b.accepted[i]=a.accepted[i];}}
 let block:[u8;32]=kani::any();assert_eq!(a.scan(&block),b.scan(&block));equal_prefix(&a,&b);
}
#[kani::proof] #[kani::unwind(34)]
fn F5_finish_success() {
 let a=arbitrary_scan(22,kani::any());let accepted=a.accepted; assert_eq!(a.finish(),Ok(accepted));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_finish_failure() {
 let len:usize=kani::any();kani::assume(len<22);let a=arbitrary_scan(len,kani::any());
 assert_eq!(a.finish(),Err(QuerySampleError::DrawLimitExhausted{accepted:len,max_draws:64}));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_pairs_failure_advances() {
 let block:[u8;32]=[0;32];let blocks=[block;8];let advances:[[u8;32];8]=kani::any();
 assert_eq!(queries_from_pairs(&blocks,&advances),Err(QuerySampleError::DrawLimitExhausted{accepted:1,max_draws:64}));
}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_add() {
 let digits:[u32;8]=kani::any();let add:u32=kani::any();kani::assume(add<=257);
 for i in 0..8 {kani::assume(digits[i]<P);}
 let mut a=digits;let mut b=digits;let ca=add_small_base_p(&mut a,add);let cb=add_small_base_p(&mut b,add);
 assert_eq!(ca,cb); for i in 0..8 {assert_eq!(a[i],b[i]);assert!(a[i]<P);}
}
#[kani::proof] #[kani::unwind(34)]
fn F5_div_pass() {
 let rank:[u32;8]=kani::any();let (a,r)=qm31_div_pass(rank);let (b,s)=qm31_div_pass(rank);
 assert!(r<P);assert_eq!(r,s);for i in 0..8 {assert_eq!(a[i],b[i]);}
}
#[kani::proof] #[kani::unwind(34)]
fn F6_well_formed() {
 let xs:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);
 let a=well_formed(&xs[..n]);let b=well_formed(&xs[..n]);assert_eq!(a,b);
 if a {assert!(n>0);for i in 0..16 {if i<n {assert!(xs[i]<1<<18);}if i+1<n {assert!(xs[i]<xs[i+1]);}}}
}
#[kani::proof] #[kani::unwind(34)]
fn F6_single_binary() {let x:u32=kani::any();kani::assume(x<1<<18);assert_eq!(node_count(Arity::Two,&[x]),Some(18));}
#[kani::proof] #[kani::unwind(34)]
fn F6_single_eight() {let x:u32=kani::any();kani::assume(x<1<<18);assert_eq!(node_count(Arity::Eight,&[x]),Some(42));}
#[kani::proof] #[kani::unwind(34)]
fn F6_pair_binary() {
 let x:u32=kani::any();kani::assume(x<1<<17);assert_eq!(node_count(Arity::Two,&[2*x,2*x+1]),Some(17));
}
#[kani::proof] #[kani::unwind(34)]
fn F6_arbitrary_binary() {let xs:[u32;16]=kani::any();let n:usize=kani::any();kani::assume(n<=16);let a=node_count(Arity::Two,&xs[..n]);let b=node_count(Arity::Two,&xs[..n]);assert_eq!(a,b);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_empty() {assert_eq!(node_count(Arity::Two,&[]),None);assert_eq!(node_count(Arity::Eight,&[]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_range() {let x:u32=kani::any();kani::assume(x>=1<<18);assert_eq!(node_count(Arity::Two,&[x]),None);assert_eq!(node_count(Arity::Eight,&[x]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F6_bad_order() {let x:u32=kani::any();let y:u32=kani::any();kani::assume(x>=y);assert_eq!(node_count(Arity::Two,&[x,y]),None);}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_zero() {let mut x=[0;8];assert!(!add_small_base_p(&mut x,0));for i in 0..8 {assert_eq!(x[i],0);}}
#[kani::proof] #[kani::unwind(34)]
fn F5_gamma_wrap() {let mut x=[P-1;8];assert!(add_small_base_p(&mut x,1));for i in 0..8 {assert_eq!(x[i],0);}}
#[kani::proof] #[kani::unwind(34)]
fn F5_div_zero() {let (q,r)=qm31_div_pass([0;8]);assert_eq!(r,0);for i in 0..8 {assert_eq!(q[i],0);}}
}
