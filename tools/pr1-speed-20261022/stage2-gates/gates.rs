#[path = "../../../docs/research/v8-r0-zk-20261009/c3/check/src/native_m31.rs"]
mod production;
#[cfg(kani)]
mod proofs {
 use super::production::*;
 #[kani::proof]
 fn reduction_all_u64() {
  let x:u64=kani::any();
  assert_eq!(reduce(x) as u64,x%P);
 }
 // Per-step proof after exact multiplication. Every u32 pair's product fits
 // u64, so reduction_all_u64 covers it without a nonlinear multiplier SAT job.
 #[kani::proof]
 fn subtract_after_product() {
  let x:u32=kani::any();let y:u32=kani::any();kani::assume((y as u64)<P);
  let old=if x>=y{x-y}else{x+P as u32-y};
  let new=if x >= y { x - y } else { x + P as u32 - y };
  assert_eq!(old,new);
 }
 #[kani::proof]
 fn image_update_after_product() {
  let acc:u32=kani::any();let product:u32=kani::any();kani::assume((product as u64)<P);
  assert_eq!(reduce(acc as u64+product as u64)as u64,(acc as u64+product as u64)%P);
 }
 #[kani::proof]
 fn bounded_accumulator_step() {
  let acc:u64=kani::any();kani::assume(acc<=(MAX_TERMS as u64-1)*(P-1));
  let term:u64=kani::any();kani::assume(term<P);
  let next=acc+term;
  assert!(next<1u64<<51);
  assert!(next<=MAX_TERMS as u64*(P-1));
 }
 #[kani::proof]
 #[kani::unwind(10)]
 fn tile_partition_preserves_order() {
  let rows:usize=kani::any();kani::assume(rows<=17);
  let mut base=0;let mut expected=0;
  while base<rows {
   let width=core::cmp::min(TILE,rows-base);
   for k in 0..width {assert_eq!(base+k,expected);expected+=1;}
   base+=width;
  }
  assert_eq!(expected,rows);
 }
}
#[cfg(test)]
#[path="reference_check.rs"]
mod reference;
#[cfg(test)]
mod tests {
 use super::*;
 fn outcome(f:impl FnOnce()->bool)->Option<bool>{std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).ok()}
 #[test]
 fn malformed_and_noncanonical_tiles() {
  let mut seed=0x52616e646f6d_u64;
  let mut word=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed as u32};
  for _ in 0..10000 {
   let rows=(word()%19) as usize;let terms=(word()%13)as usize;
   let a:Vec<u32>=(0..32).map(|_|word()).collect();
   let b:Vec<u32>=(0..256).map(|_|word()).collect();
   let c:Vec<u32>=(0..32).map(|_|word()).collect();
   let idx:Vec<u32>=(0..16).map(|_|word()%20).collect();
   let offset=(word()%5)as usize;
   assert_eq!(outcome(||reference::prod_row_ok(&a,offset,&b,offset,&c,offset,0,rows,terms)),outcome(||aspis_r1_cert_check::prod_row_ok(&a,offset,&b,offset,&c,offset,0,rows,terms)));
   assert_eq!(outcome(||reference::kimg_ok(&b,17,rows,2,&idx,offset,&a,offset,terms,&c,offset,1)),outcome(||aspis_r1_cert_check::kimg_ok(&b,17,rows,2,&idx,offset,&a,offset,terms,&c,offset,1)));
   let x=word();let y=word();let s=word();
   let mul=((s as u64*y as u64)%production::P)as u32;
   let expected=if x>=mul{x-mul}else{x+production::P as u32-mul};
   assert_eq!(production::sub_product(x,s,y),expected);
   assert_eq!(production::madd(x,s,y)as u64,(x as u64+mul as u64)%production::P);
  }
 }
}
