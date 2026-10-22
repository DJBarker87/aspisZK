
impl E { fn mul_qm31(self,rhs:E)->E { call(5,self,rhs) } }
fn native_weight(kp:&[E;7],raw:E,kind:usize,v:E)->E {v.add(kp[kind].mul_qm31(raw))}
fn owner_weight(kp:[E;7],raw:[E;7],kind:usize,sum:E)->E {sum.add(kp[kind].mul_qm31(raw[kind]))}
fn native_inactive(q:&[E;1024],j:usize,raw:E,s:E)->E {s.add(q[j].mul_qm31(raw))}
fn owner_inactive(q:[E;1024],raw:[E;1024],j:usize,sum:E)->E {sum.add(q[j].mul_qm31(raw[j]))}
#[cfg(kani)] mod weight_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(34)] fn material_cell_transition() {
  let kp:[E;7]=unsafe {core::mem::transmute(kani::any::<[u32;7]>())};
  let raw:[E;7]=unsafe {core::mem::transmute(kani::any::<[u32;7]>())};
  let k:usize=kani::any();kani::assume(k<7);let v=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_weight(&kp,raw[k],k,v);let ta=trace();
  reset(answers);let b=owner_weight(kp,raw,k,v);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
 #[kani::proof] #[kani::unwind(34)] fn inactive_transition() {
  let q:[E;1024]=unsafe {core::mem::transmute(kani::any::<[u32;1024]>())};
  let raw:[E;1024]=unsafe {core::mem::transmute(kani::any::<[u32;1024]>())};
  let j:usize=kani::any();kani::assume(j<1024);let s=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_inactive(&q,j,raw[j],s);let ta=trace();
  reset(answers);let b=owner_inactive(q,raw,j,s);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
}
