// Literal shipped expressions at the arbitrary current source iteration.
struct Column {index:usize,value:E}
impl core::ops::Index<usize> for Column {
 type Output=E;
 fn index(&self,i:usize)->&E {assert_eq!(i,self.index);&self.value}
}
fn native_mix(gp:&[E;29],coefficients:&[Column;29],j:usize,l:usize,s:E)->E {
 s.add(gp[l].mul(coefficients[l][j]))
}
fn owner_mix(powers:[E;29],coefficients:[E;29],i:usize,sum:E)->E {
 sum.add(powers[i].mul(coefficients[i]))
}
fn native_fold(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}
fn owner_fold(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[1].add(alpha.mul(h[2].add(alpha.mul(h[3]))))))
}
#[cfg(kani)] mod opening_proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(32)]
 fn mix_iteration() {
  let raw:[u32;29]=kani::any();let gp=raw.map(E);
  let raw:[u32;29]=kani::any();let coefficients=raw.map(E);
  let j:usize=kani::any();let l:usize=kani::any();kani::assume(j<1024 && l<29);
  let columns=coefficients.map(|value|Column{index:j,value});
  let sum=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_mix(&gp,&columns,j,l,sum);let ta=trace();
  reset(answers);let b=owner_mix(gp,coefficients,l,sum);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,2);
 }
 #[kani::proof] #[kani::unwind(10)]
 fn fold_primal_cell() {
  let raw:[u32;4]=kani::any();let h=raw.map(E);let alpha=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_fold(h,alpha);let ta=trace();
  reset(answers);let b=owner_fold(h,alpha);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,6);
 }
}
