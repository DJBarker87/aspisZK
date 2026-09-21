//! Uncompiled SAME-PROFILE optimization draft. Keeps rho^1..rho^44 exactly.
use super::corelib::{field::{M31,QM31 as K,qm31_dot},sumcheck::WeightAccumulator};
pub struct SharedQueries {pub weights:WeightAccumulator,pub lambda:K,pub increment:K}
pub fn prepare(xs:&[M31],r:&[K],g:&[K],rho:K)->Option<SharedQueries>{
    if xs.len()!=22||r.len()!=22||g.len()!=22{return None;}
    let mut scales=[K::ZERO;22];let mut power=rho;
    for s in &mut scales{*s=power;power=power.mul(rho);}
    let lambda=scales[21]; // rho^22, including rho=0. No division.
    let increment=qm31_dot(&scales,r).add(lambda.mul(qm31_dot(&scales,g)));
    let mut weights=WeightAccumulator::empty(8);
    weights.add_line_m31_batch(&scales,xs).ok()?;
    Some(SharedQueries{weights,lambda,increment})
}
impl SharedQueries{
    /// Only the THREE post-injection folds; never alpha0.
    pub fn fold(&mut self,a:K){self.weights.fold_deferred_relation_arity4(a);}
    pub fn final_values(&self,r:[K;4],g:[K;4])->[K;4]{
        core::array::from_fn(|i|r[i].add(self.lambda.mul(g[i])))
    }
}
