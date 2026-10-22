#![allow(dead_code)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct C {a:u32,b:u32}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Q {c0:C,c1:C}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct Trace {n:usize,args:[(u8,u32,u32);5],answers:[u32;5]}
impl Trace {
 fn add(&mut self,a:u32,b:u32)->u32 {self.args[self.n]=(0,a,b);let z=self.answers[self.n];self.n+=1;z}
 fn cm(&mut self,a:C,b:C)->C {C{a:self.add(a.a,b.a),b:self.add(a.b,b.b)}}
}
fn source_prepare(x:Q,t:&mut Trace)->[[u32;3];3] {
 let sum=t.cm(x.c0,x.c1);
 [[x.c0.a,x.c0.b,t.add(x.c0.a,x.c0.b)],
  [x.c1.a,x.c1.b,t.add(x.c1.a,x.c1.b)],
  [sum.a,sum.b,t.add(sum.a,sum.b)]]
}
fn owner_c(x:C,t:&mut Trace)->[u32;3] {[x.a,x.b,t.add(x.a,x.b)]}
fn owner_prepare(x:Q,t:&mut Trace)->[[u32;3];3] {
 let sum=t.cm(x.c0,x.c1);
 [owner_c(x.c0,t),owner_c(x.c1,t),owner_c(sum,t)]
}
fn source_totals(p:[[[u64;3];3];3])->[[u64;3];3] {
 let mut sums=[[0u64;3];3];let mut index=0;
 while index<3 {for c in 0..3 {for h in 0..3 {sums[c][h]+=p[index][c][h];}}index+=1;}
 sums
}
fn owner_channel(p:[[[u64;3];3];3],c:usize,h:usize,i:usize,left:u8,total:u64)->u64 {
 if left==0 {total} else {owner_channel(p,c,h,i+1,left-1,total.wrapping_add(p[i][c][h]))}
}
fn owner_totals(p:[[[u64;3];3];3])->[[u64;3];3] {
 [[owner_channel(p,0,0,0,3,0),owner_channel(p,0,1,0,3,0),owner_channel(p,0,2,0,3,0)],
  [owner_channel(p,1,0,0,3,0),owner_channel(p,1,1,0,3,0),owner_channel(p,1,2,0,3,0)],
  [owner_channel(p,2,0,0,3,0),owner_channel(p,2,1,0,3,0),owner_channel(p,2,2,0,3,0)]]
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(8)] fn prepare() {
  let x=Q{c0:C{a:kani::any(),b:kani::any()},c1:C{a:kani::any(),b:kani::any()}};
  let mut a=Trace{n:0,args:[(0,0,0);5],answers:kani::any()};let mut b=a;
  let z=source_prepare(x,&mut a);let w=owner_prepare(x,&mut b);
  for c in 0..3 {for h in 0..3 {assert_eq!(z[c][h],w[c][h]);}}
  assert_eq!(a,b);
 }
 #[kani::proof] #[kani::unwind(8)] fn totals() {
  let p:[[[u64;3];3];3]=kani::any();
  for i in 0..3 {for c in 0..3 {for h in 0..3 {kani::assume(p[i][c][h]<=2147483646u64*2147483646u64);}}}
  let a=source_totals(p);let b=owner_totals(p);
  for c in 0..3 {for h in 0..3 {assert_eq!(a[c][h],b[c][h]);}}
 }
}
