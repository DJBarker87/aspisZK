
fn native_factor_step(factors:&[[[E;4];5];5],kind:usize,j:usize,d:usize,v:E)->E {
 let k=if kind<4 {kind-1}else{kind-2};
 v.mul(factors[k][d][(j>>(2*d))&3])
}
fn owner_factor_step(q:[E;5],d:usize,s:E)->E {s.mul(q[d])}
#[cfg(kani)] mod factor_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn raw_product_transition() {
  let raw:[u32;100]=kani::any();let factors:[[[E;4];5];5]=unsafe {core::mem::transmute(raw)};
  let kind:usize=kani::any();kani::assume(kind==1 || kind==2 || kind==3 || kind==5 || kind==6);
  let j:usize=kani::any();let d:usize=kani::any();kani::assume(j<1024 && d<5);
  let k=if kind<4 {kind-1}else{kind-2};
  let selected:[E;5]=core::array::from_fn(|d|factors[k][d][(j>>(2*d))&3]);
  let v=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_factor_step(&factors,kind,j,d,v);let ta=trace();
  reset(answers);let b=owner_factor_step(selected,d,v);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,1);
 }
}
