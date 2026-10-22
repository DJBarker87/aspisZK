fn native_dual(h:[E;4],alpha:E)->E {
 h[0].add(alpha.mul(h[3].add(alpha.mul(h[2].add(alpha.mul(h[1])))))).mul_m31(M31(536870912))
}
fn owned_dual(h:[E;4],alpha:E)->E {
 let m1=alpha.mul(h[1]);let s2=h[2].add(m1);let m2=alpha.mul(s2);
 let s3=h[3].add(m2);let m3=alpha.mul(s3);let v=h[0].add(m3);v.mul_m31(M31(536870912))
}
#[cfg(kani)] mod dual_proofs {use super::*;
 #[kani::proof] #[kani::unwind(34)] fn dual_cell_iteration() {
 let raw:[u32;4]=kani::any();let h=raw.map(E);let a=E(kani::any());let answers=kani::any();
 reset(answers);let actual=native_dual(h,a);let ta=trace();
 reset(answers);let expected=owned_dual(h,a);let tb=trace();
 assert_eq!(actual,expected);assert_eq!(ta,tb);assert_eq!(ta.1,7);
 }
}
