//! Proof-only live-index invariant. Full scratch outside the two live
//! intervals is arbitrary; no distinct-query assumption is imposed.
use super::frozen as f;
#[derive(Clone,Copy)] pub struct IndexHash;
impl aspis_core::Digest32 for IndexHash {
 fn digest(&self,_:&[&[u8]])->[u8;32] {[0;32]}
}
pub fn assume_inv(k:&[u32;16],n:usize,i:usize,w:usize) {
 for a in 0..16 {for b in 0..16 {
  if a<b && b<w {kani::assume(k[a]<k[b]);}
  if i<=a && a<b && b<n {kani::assume(k[a]<k[b]);}
  if a<w && i<=b && b<n {kani::assume(k[a]<k[b]/2);}
 }}
}
// One exact generated binary_group, without reference recursion, hash stubs,
// or a chosen concrete input/cursor. Arbitrary a,b,j observe the full invariant.
pub fn check_step() {
 let mut idx:[u32;16]=kani::any();let before=idx;
 let mut val:[[u8;32];16]=kani::any();
 let n:usize=kani::any();let mut i:usize=kani::any();let mut w:usize=kani::any();
 let nodes:[u8;32]=kani::any();let length:usize=kani::any();let mut at:usize=kani::any();
 kani::assume(n>0 && n<=16 && i<n && w<=i && at<=length && length<=32);
 assume_inv(&idx,n,i,w);
 let (old_i,old_w,old_at)=(i,w,at);
 let paired=i+1<n && idx[i+1]==idx[i]^1;
 let model_pair=i+1<n && idx[i]%2==0 && idx[i+1]==idx[i]+1;
 assert_eq!(paired,model_pair);
 let ok=f::multiproof::binary_group(IndexHash,&mut idx,&mut val,n,&nodes[..length],&mut at,&mut w,&mut i);
 let a:usize=kani::any();let b:usize=kani::any();let j:usize=kani::any();
 kani::assume(a<16 && b<16 && j<16);
 if ok {
  assert_eq!(i,if model_pair {old_i+2}else{old_i+1});assert_eq!(w,old_w+1);
  assert!(w<=i && i<=n);assert_eq!(idx[j],if j==old_w {before[old_i]/2}else{before[j]});
  if a<b && b<w {assert!(idx[a]<idx[b]);}
  if i<=a && a<b && b<n {assert!(idx[a]<idx[b]);}
  if a<w && i<=b && b<n {assert!(idx[a]<idx[b]/2);}
  assert_eq!(at,if model_pair {old_at}else{old_at+32});
 } else {assert_eq!((i,w,at),(old_i,old_w,old_at));assert_eq!(idx[j],before[j]);}
}
// The actual deduplicating leaf_insert. Key monotonicity is supplied by the
// independently proved packed-key sort; truncation is excluded by its bound.
pub fn check_leaf() {
 let mut idx:[u32;16]=kani::any();let before=idx;let mut val:[[u8;32];16]=kani::any();
 let mut d:usize=kani::any();let index:u32=kani::any();let leaf:[u8;32]=kani::any();
 kani::assume(d<16);
 for a in 0..16 {for b in 0..16 {if a<b && b<d {kani::assume(idx[a]<idx[b]);}}}
 for a in 0..16 {if a<d {kani::assume(idx[a]<=index);}}
 let old=d;
 let ok=f::batch::leaf_insert(&mut idx,&mut val,&mut d,index,leaf);
 let a:usize=kani::any();let b:usize=kani::any();let j:usize=kani::any();kani::assume(a<16 && b<16 && j<16);
 if ok {
  assert_eq!(d,if old>0 && before[old-1]==index {old}else{old+1});
  if a<b && b<d {assert!(idx[a]<idx[b]);}
  if a<d {assert!(idx[a]<=index);}
  if j>=d {assert_eq!(idx[j],before[j]);}
 } else {assert_eq!(d,old);assert_eq!(idx[j],before[j]);}
}
