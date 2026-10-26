use aspis_core::field::P;
// The original loop body, with its mutable-reference state made explicit.
pub fn shipped_limb(mut limb:u32,mut remainder:u64)->(u32,u64) {
    let dividend = (remainder << 32) | u64::from(limb);
    limb = (dividend / u64::from(P)) as u32;
    remainder = dividend % u64::from(P);
    (limb,remainder)
}
pub fn reference_limb(word:u32,remainder:u64)->(u32,u64) {
    let dividend=(remainder<<32u32)|u64::from(word);
    ((dividend/u64::from(P)) as u32,dividend%u64::from(P))
}
#[cfg(kani)]
mod checks {
 use super::*;
 #[kani::proof] #[kani::unwind(2)]
 fn sampler_single_limb() {
  let word:u32=kani::any();let remainder:u64=kani::any();
  kani::assume(remainder<u64::from(P));
  let a=shipped_limb(word,remainder);let b=reference_limb(word,remainder);
  assert_eq!(a.0,b.0);assert_eq!(a.1,b.1);
 }
 #[kani::proof] #[kani::unwind(2)]
 fn sampler_limb_remainder_bound() {
  let word:u32=kani::any();let remainder:u64=kani::any();
  kani::assume(remainder<u64::from(P));
  let next=shipped_limb(word,remainder);
  assert!(next.1<u64::from(P));
 }
 #[kani::proof] #[kani::unwind(10)]
 fn sampler_reverse_iterator_next() {
  let rank:[u32;8]=kani::any();let consumed:usize=kani::any();kani::assume(consumed<=8);
  let mut iter=rank.iter().rev();let mut i=0usize;
  while i<consumed {assert_eq!(iter.next(),Some(&rank[7-i]));i+=1;}
  if consumed<8 {assert_eq!(iter.next(),Some(&rank[7-consumed]));} else {assert_eq!(iter.next(),None);}
 }
}
