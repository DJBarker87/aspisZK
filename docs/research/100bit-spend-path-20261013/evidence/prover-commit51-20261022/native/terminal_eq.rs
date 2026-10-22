mod terminal_eq_gate{
type K=[u32;4];const ONE:K=[1,0,0,0];
#[derive(Clone,Copy)]struct Trace{n:usize,args:[(u8,K,K);59],answers:[K;59]}
impl Trace{fn op(&mut self,tag:u8,a:K,b:K)->K{let i=self.n;self.n+=1;self.args[i]=(tag,a,b);self.answers[i]}}
fn factor(a:K,b:K,t:&mut Trace)->K{let ab=t.op(0,a,b);let q=t.op(1,ONE,a);let q1=t.op(1,q,b);let q2=t.op(2,q1,ab);t.op(2,q2,ab)}
fn native(left:[K;10],right:[K;10],t:&mut Trace)->K{let mut product=factor(left[0],right[0],t);let mut index=1usize;while index<left.len(){let f=factor(left[index],right[index],t);product=t.op(0,product,f);index+=1;}product}
fn go(left:[K;10],right:[K;10],index:u8,product:K,t:&mut Trace)->K{if index==10{return product;}let f=factor(left[index as usize],right[index as usize],t);let next=t.op(0,product,f);go(left,right,index.wrapping_add(1),next,t)}
fn owner(left:[K;10],right:[K;10],t:&mut Trace)->K{let product=factor(left[0],right[0],t);go(left,right,1,product,t)}
fn native_suffix(eq:K,comp:K,h1:K,active:K,mu:K,t:&mut Trace)->K{let q=t.op(0,eq,comp);let q1=t.op(0,mu,h1);let q2=t.op(2,q,q1);let q3=t.op(0,mu,mu);let q4=t.op(1,ONE,active);let q5=t.op(0,q4,h1);let q6=t.op(0,q3,q5);t.op(2,q2,q6)}
fn owner_suffix(eq:K,comp:K,h1:K,active:K,mu:K,t:&mut Trace)->K{let q=t.op(0,eq,comp);let q1=t.op(0,mu,h1);let q2=t.op(2,q,q1);let q3=t.op(0,mu,mu);let q4=t.op(1,ONE,active);let q5=t.op(0,q4,h1);let q6=t.op(0,q3,q5);t.op(2,q2,q6)}
#[cfg(kani)]mod proofs{use super::*;
fn trace()->Trace{Trace{n:0,args:[(0,[0;4],[0;4]);59],answers:kani::any()}}
fn compare(a:Trace,b:Trace,z:K,w:K){assert_eq!(a.n,b.n);for k in 0..4{assert_eq!(z[k],w[k]);}for i in 0..59{assert_eq!(a.args[i].0,b.args[i].0);for k in 0..4{assert_eq!(a.args[i].1[k],b.args[i].1[k]);assert_eq!(a.args[i].2[k],b.args[i].2[k]);}}}
#[kani::proof]#[kani::unwind(62)]fn equality(){let a:[K;10]=kani::any();let b:[K;10]=kani::any();let mut t=trace();let mut u=t;let z=native(a,b,&mut t);let w=owner(a,b,&mut u);compare(t,u,z,w);}
#[kani::proof]#[kani::unwind(62)]fn suffix(){let x:[K;5]=kani::any();let mut t=trace();let mut u=t;let z=native_suffix(x[0],x[1],x[2],x[3],x[4],&mut t);let w=owner_suffix(x[0],x[1],x[2],x[3],x[4],&mut u);compare(t,u,z,w);}
}
}
