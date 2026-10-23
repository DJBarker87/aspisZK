#![allow(dead_code)]
type K=[u32;4];
const E:[u8;26]=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25,1,3,5,7,9,11,15,17,19,21];
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct Trace{n:usize,args:[(K,u8);26],answers:[K;26]}
impl Trace{fn tower(&mut self,x:K,j:u8)->K{let n=self.n;self.n+=1;self.args[n]=(x,j);self.answers[n]}}
fn native(c1:[K;16],mo:[K;10],t:&mut Trace)->[K;27]{
 let mut out=[[0;4];27];
 for column in 0..16 {out[E[column] as usize]=t.tower(c1[column],(column&3) as u8);}
 for column in 0..10 {out[E[16+column] as usize]=t.tower(mo[column],(column&3) as u8);}
 out
}
fn go(input:[K;26],e:[u8;26],left:u8,mut out:[K;27],t:&mut Trace)->[K;27]{
 if left==0{return out;}let i=26u8.wrapping_sub(left);
 let v=t.tower(input[i as usize],i%4);out[e[i as usize] as usize]=v;
 go(input,e,left.wrapping_sub(1),out,t)
}
#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof]#[kani::unwind(29)]fn coefficient_writes(){
 let c1:[K;16]=kani::any();let mo:[K;10]=kani::any();
 let mut t=Trace{n:0,args:[([0;4],0);26],answers:kani::any()};let mut u=t;
 let mut input=[[0;4];26];for i in 0..16{input[i]=c1[i];}for i in 0..10{input[16+i]=mo[i];}
 let a=native(c1,mo,&mut t);let b=go(input,E,26,[[0;4];27],&mut u);for i in 0..27{for j in 0..4{assert_eq!(a[i][j],b[i][j]);}}assert_eq!(t.n,u.n);for i in 0..26{assert_eq!(t.args[i].1,u.args[i].1);for j in 0..4{assert_eq!(t.args[i].0[j],u.args[i].0[j]);}}
 for i in 0..26{let j=i as u8;let f=if j<14{2*j}else if j==14{13}else if j==15{25}else if j<22{2*(j-16)+1}else{2*(j-16)+3};assert_eq!(f,E[i]);}
 }
}

include!("columns.rs");

include!("coefficient_array.rs");

include!("half_prefix.rs");
