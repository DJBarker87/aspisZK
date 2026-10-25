// Proof-local expressions. Does not instrument std sort or allocator internals.
// Source: constraints_v4::sparse_eq_weights prefix/suffix selection.
type Q=[u32;4];
const ZERO:Q=[0;4]; const ONE:Q=[1,0,0,0];
#[derive(Clone,Copy,Debug)]
struct Trace { values:[u32;128], n:usize }
impl Trace {
 fn new()->Self {Self {values:[0;128],n:0}}
 fn push(&mut self,x:u32) {self.values[self.n]=x;self.n+=1;}
}
fn same(a:&Trace,b:&Trace) {
 assert_eq!(a.n,b.n);
 for i in 0..32 {for j in 0..4 {assert_eq!(a.values[i*4+j],b.values[i*4+j]);}}
}
fn eq(a:&Q,b:&Q,t:&mut Trace)->bool {
 for i in 0..4 {let hit=a[i]==b[i];t.push((i as u32)*2+u32::from(hit));if !hit {return false;}}
 true
}
fn source_shape(point:&[Q;10])->(usize,usize) {
 let trailing_boolean=point.iter().rev().take_while(|value| **value==ZERO || **value==ONE).count();
 let prefix_len=point.len()-trailing_boolean;
 let mut suffix=0usize;
 for coordinate in &point[prefix_len..] {suffix=(suffix<<1)|usize::from(*coordinate==ONE);}
 (prefix_len,suffix)
}
fn traced_shape(point:&[Q;10],t:&mut Trace)->(usize,usize) {
 let mut trailing=0;
 for k in 0..10 {let i=9-k;
     if eq(&point[i],&ZERO,t)||eq(&point[i],&ONE,t) {trailing+=1;} else {break;}
 }
 let prefix_len=10-trailing;let mut suffix=0;
 for i in prefix_len..10 {suffix=(suffix<<1)|usize::from(eq(&point[i],&ONE,t));}
 (prefix_len,suffix)
}
#[kani::proof]
#[kani::unwind(33)]
fn L2Leaf_sparse_suffix_erasure_and_two_run() {
 let point:[Q;10]=kani::any();let mut a=Trace::new();let mut b=Trace::new();
 let x=traced_shape(&point,&mut a);let y=traced_shape(&point,&mut b);
 assert_eq!(x,source_shape(&point));assert_eq!(x,y);same(&a,&b);
 let prefix:usize=kani::any();kani::assume(prefix < (1usize<<x.0));
 let row=(prefix<<(10-x.0))|x.1;assert!(row<1024);
}
// One actual generate binary-parent group: node bytes are never inspected.
// Returns consumed positions, missing child addresses and a payload buffer.
// Full 18-level induction, node_count and std collection costs remain open.
fn group(level:&[u32;2],len:usize,start:usize,node:[u8;32])->(usize,[Option<u32>;2],[[u8;32];2]) {
 let mut i=start;let parent=level[i]>>1;let mut trace=[None;2];let mut out=[[0;32];2];
 for slot in 0..2 {
  let child=(parent<<1)|slot as u32;
  if i<len && level[i]==child {i+=1;} else {trace[slot]=Some(child);out[slot]=node;}
 }
 (i,trace,out)
}
#[kani::proof]
#[kani::unwind(4)]
fn L2Leaf_multiproof_group_payload_two_run() {
 let level:[u32;2]=kani::any();let len:usize=kani::any();let start:usize=kani::any();
 kani::assume(len>0 && len<=2 && start<len);
 kani::assume(level[0]<level[1] && level[1]<(1<<18));
 let a:[u8;32]=kani::any();let b:[u8;32]=kani::any();
 let x=group(&level,len,start,a);let y=group(&level,len,start,b);
 assert_eq!(x.0,y.0);
 for i in 0..2 {assert_eq!(x.1[i],y.1[i]);}
}
