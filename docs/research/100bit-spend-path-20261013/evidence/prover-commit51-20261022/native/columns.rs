mod columns_gate{
type K=[u32;4];
#[derive(Clone,Copy)]struct Trace{n:usize,args:[(u32,[K;10]);26],answers:[K;26]}
impl Trace{fn ev(&mut self,c:u32,p:[K;10])->K{let i=self.n;self.n+=1;self.args[i]=(c,p);self.answers[i]}}
fn native(columns:[u32;26],p:[K;10],t:&mut Trace)->[K;26]{let mut c1=[[0;4];16];for(i,c)in c1.iter_mut().enumerate(){*c=t.ev(columns[i],p);}let mut mo=[[0;4];10];for(i,c)in mo.iter_mut().enumerate(){*c=t.ev(columns[16+i],p);}core::array::from_fn(|i|if i<16{c1[i]}else{mo[i-16]})}
fn go(columns:[u32;26],p:[K;10],left:u8,mut out:[K;26],t:&mut Trace)->[K;26]{if left==0{return out;}let i=26u8.wrapping_sub(left);out[i as usize]=t.ev(columns[i as usize],p);go(columns,p,left.wrapping_sub(1),out,t)}
#[cfg(kani)]mod proofs{use super::*;
#[kani::proof]#[kani::unwind(29)]fn columns(){let c:[u32;26]=kani::any();let p:[K;10]=kani::any();let mut a=Trace{n:0,args:[(0,[[0;4];10]);26],answers:kani::any()};let mut b=a;let v=native(c,p,&mut a);let w=go(c,p,26,[[0;4];26],&mut b);assert_eq!(a.n,b.n);for i in 0..26{assert_eq!(a.args[i].0,b.args[i].0);for j in 0..4{assert_eq!(v[i][j],w[i][j]);}for j in 0..10{for k in 0..4{assert_eq!(a.args[i].1[j][k],b.args[i].1[j][k]);}}}}
}
}
