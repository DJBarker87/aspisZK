use super::*;
pub fn copy_a(a:&Accumulator)->Accumulator {Accumulator{weights:a.weights.clone(),rhs:a.rhs,power:a.power,next:a.next}}
pub fn copy_b(b:&BatchedWeights)->BatchedWeights {BatchedWeights{raw:b.raw.clone(),terms:b.terms}}
pub fn same(a:&Accumulator,b:&Accumulator,x:&BatchedWeights,y:&BatchedWeights) {
 assert_eq!(a.weights,b.weights);assert_eq!(a.rhs,b.rhs);assert_eq!(a.power,b.power);assert_eq!(a.next,b.next);
 assert_eq!(x.raw,y.raw);assert_eq!(x.terms,y.terms);
}
pub fn prepared(queries:[u32;22])->Prepared {
 Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ONE,queries,semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ONE,y:K::ZERO};2],claim:E::ZERO,state:[0;32]}
}
