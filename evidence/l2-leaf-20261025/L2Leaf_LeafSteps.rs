// Split source-expression obligations after larger symbolic-loop timeouts.
// No whole-kernel, extraction, independence-law or std-cost claim.
const P:u32=0x7fff_ffff;
fn contains_step(stored:u32,candidate:u32)->(bool,bool) {
 let hit=stored==candidate;(hit,hit)
}
#[kani::proof]
fn L2Leaf_query_comparison_two_run() {
 let a:u32=kani::any();let b:u32=kani::any();
 assert_eq!(contains_step(a,b),contains_step(a,b));
}
fn eq(a:&[u32;4],b:&[u32;4],events:&mut [u8;8],n:&mut usize)->bool {
 for i in 0..4 {
  let hit=a[i]==b[i];events[*n]=2*i as u8+u8::from(hit);*n+=1;
  if !hit {return false;}
 }
 true
}
fn suffix_step(q:[u32;4])->(bool,[u8;8],usize) {
 let mut t=[0;8];let mut n=0;
 let boolean=eq(&q,&[0;4],&mut t,&mut n)||eq(&q,&[1,0,0,0],&mut t,&mut n);
 (boolean,t,n)
}
#[kani::proof]
#[kani::unwind(9)]
fn L2Leaf_sparse_coordinate_erasure_and_two_run() {
 let q:[u32;4]=kani::any();let a=suffix_step(q);let b=suffix_step(q);
 assert_eq!(a.0,(q[0]==0 || q[0]==1) && q[1]==0 && q[2]==0 && q[3]==0);assert_eq!(a.0,b.0);assert_eq!(a.2,b.2);
 for i in 0..8 {assert_eq!(a.1[i],b.1[i]);}
}
fn div_step(remainder:u64,word:u32)->(u32,u32,u64) {
 let dividend=(remainder<<32)|u64::from(word);
 ((dividend/P as u64) as u32,(dividend%P as u64) as u32,dividend)
}
#[kani::proof]
fn L2Leaf_division_limb_two_run() {
 let r:u64=kani::any();let w:u32=kani::any();kani::assume(r<P as u64);
 let a=div_step(r,w);let b=div_step(r,w);assert_eq!(a,b);
 assert!(a.2 < (P as u64)*(1u64<<32));assert!(a.1<P);
}
// z9c::TagEch::insert decision at one column; pivot arithmetic/updates and
// the derivation of the row from R1PublicChallenges remain separate.
fn pivot_step(value:u32,pivot:Option<usize>)->u8 {
 if value==0 {return 0;}
 if let Some(_) = pivot {1} else {2}
}
#[kani::proof]
fn L2Leaf_checker_pivot_decision_two_run() {
 let v:u32=kani::any();let p:Option<usize>=kani::any();
 assert_eq!(pivot_step(v,p),pivot_step(v,p));
}
