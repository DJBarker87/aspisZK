use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn arbitrary_e()->E {let a:[u32;8]=kani::any();let mut i=0;while i<8 {kani::assume(a[i]<2147483647);i+=1;}E::from_limbs(a).unwrap()}
// The product value stays opaque: this records the exact two operands, then
// returns an unconstrained canonical reply. Lean substitutes wide_mul's law.
struct ProductLog {left:E,right:E,reply:E,calls:usize}
fn product(log:&mut ProductLog,left:E,right:E)->E {log.left=left;log.right=right;log.calls+=1;log.reply}
// Source iteration: only p.mul(x) is replaced by the explicit local-record call.
fn step<const N:usize>(out:&mut [E;N],p:&mut E,i:&mut usize,x:E,log:&mut ProductLog)->bool {
 if *i<N {
  out[*i]=*p;
  *i+=1;
  if *i==N {return true;}
  *p=product(log,*p,x);
  false
 } else {true}
}
fn check<const N:usize>(){
 let mut out=[E::ZERO;N];let mut j=0;while j<N{out[j]=arbitrary_e();j+=1;}
 let row:usize=kani::any();let word:usize=kani::any();kani::assume(row<N&&word<8);
 let before=out[row].to_limbs()[word];let old=arbitrary_e();let x=arbitrary_e();let reply=arbitrary_e();
 let mut p=old;let at:usize=kani::any();kani::assume(at<=N);let mut i=at;
 let mut log=ProductLog{left:E::ZERO,right:E::ZERO,reply,calls:0};
 let done=step(&mut out,&mut p,&mut i,x,&mut log);
 let expected=if at<N&&row==at{old.to_limbs()[word]}else{before};
 assert!((out[row].to_limbs()[word]==expected)!=cfg!(NFW_invert));
 assert_eq!(i,if at<N{at+1}else{at});
 assert_eq!(done,at>=N||at+1==N);
 if at+1<N {assert_eq!(log.calls,1);assert_eq!(log.left.to_limbs()[word],old.to_limbs()[word]);assert_eq!(log.right.to_limbs()[word],x.to_limbs()[word]);assert_eq!(p.to_limbs()[word],reply.to_limbs()[word]);}
 else {assert_eq!(log.calls,0);assert_eq!(p.to_limbs()[word],old.to_limbs()[word]);}
}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn powers7_step(){check::<7>();}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn powers29_step(){check::<29>();}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_e(){let src=arbitrary_e();let mut dst=arbitrary_e();unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};let word:usize=kani::any();kani::assume(word<8);assert!((dst.to_limbs()[word]==src.to_limbs()[word])!=cfg!(NFW_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn powers4_step(){check::<4>();}
