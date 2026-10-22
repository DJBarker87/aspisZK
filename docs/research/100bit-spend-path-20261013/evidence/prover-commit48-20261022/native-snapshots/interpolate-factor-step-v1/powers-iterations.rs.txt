#[derive(Debug,PartialEq,Eq)] enum PowerStep<const N:usize> {Done([E;N]),More([E;N],E,usize)}
fn native_power<const N:usize>(mut out:[E;N],x:E,mut p:E,mut i:usize)->PowerStep<N> {
  out[i]=p;
  i+=1;
  if i==N { return PowerStep::Done(out); }
  p=p.mul(x);
 PowerStep::More(out,p,i)
}
fn owner_power<const N:usize>(mut out:[E;N],x:E,p:E,i:usize,left:usize)->PowerStep<N> {
 out[i]=p;
 if left==1 {PowerStep::Done(out)} else {PowerStep::More(out,p.mul(x),i+1)}
}
#[cfg(kani)] mod power_proofs {
 use super::*;
 fn check<const N:usize>(out:[E;N]) {
  let i:usize=kani::any();kani::assume(i<N);
  let x=E(kani::any());let p=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_power(out,x,p,i);let ta=trace();
  reset(answers);let b=owner_power(out,x,p,i,N-i);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,if i+1==N {0} else {1});
 }
 #[kani::proof] #[kani::unwind(32)] fn gamma_step() {let r:[u32;29]=kani::any();check(r.map(E));}
 #[kani::proof] #[kani::unwind(10)] fn kappa_step() {let r:[u32;7]=kani::any();check(r.map(E));}
}
