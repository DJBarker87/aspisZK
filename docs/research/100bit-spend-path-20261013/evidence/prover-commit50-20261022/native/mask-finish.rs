
mod mask_finish_gate {
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct K(u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]struct Trace{n:usize,args:[(u8,u32,u32);4],answers:[u32;4]}
impl Trace{fn call(&mut self,o:u8,a:K,b:K)->K{let i=self.n;self.n+=1;self.args[i]=(o,a.0,b.0);K(self.answers[i])}}
fn native(shared:K,linear:K,g:K,t:&mut Trace)->K {
 let power=t.call(0,linear,K(0));let factor=t.call(1,K(1),power);let extra=t.call(2,factor,g);t.call(1,shared,extra)
}
fn owner(shared:K,linear:K,g:K,t:&mut Trace)->K {
 let p=t.call(0,linear,K(0));let f=t.call(1,K(1),p);let e=t.call(2,f,g);t.call(1,shared,e)
}
#[cfg(kani)]mod proofs{use super::*;
 #[kani::proof]#[kani::unwind(6)]fn finish(){
 let shared=K(kani::any());let linear=K(kani::any());let g=K(kani::any());
 let mut a=Trace{n:0,args:[(0,0,0);4],answers:kani::any()};let mut b=a;
 assert_eq!(native(shared,linear,g,&mut a),owner(shared,linear,g,&mut b));assert_eq!(a,b);
 }
}
}
