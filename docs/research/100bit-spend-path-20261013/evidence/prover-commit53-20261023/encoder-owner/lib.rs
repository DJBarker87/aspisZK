#![allow(unexpected_cfgs)]
pub mod field;
pub mod encoder53 {
use super::field::{M31,CM31,QM31,WideExact as E};
pub fn phi_inverse(x:E,y:E,h:[E;4])->[E;4] {
 let [h0,h1,h2,h3]=h;
 let a=y.mul(h1);let b=x.mul(h2);let c=x.mul(y).mul(h3);
 [h0.add(a).add(b).add(c),h0.sub(a).add(b).sub(c),
 h0.sub(a).sub(b).add(c),h0.add(a).sub(b).sub(c)]
}
pub fn eval_rec(coefficients:&[E],depth:usize,nodes:&[M31;9])->E {
 if coefficients.len()==1 {return coefficients[0];}
 let even:Vec<E>=coefficients.iter().step_by(2).copied().collect();
 let odd:Vec<E>=coefficients.iter().skip(1).step_by(2).copied().collect();
 eval_rec(&even,depth+1,nodes).add(E::from_qm31(QM31::from_cm31(CM31::from_m31(nodes[depth]))).mul(eval_rec(&odd,depth+1,nodes)))
}
}
