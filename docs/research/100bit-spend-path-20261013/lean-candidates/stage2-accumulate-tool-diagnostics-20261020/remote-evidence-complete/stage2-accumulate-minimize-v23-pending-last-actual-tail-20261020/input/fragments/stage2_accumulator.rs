pub struct Accumulator { pub weights:Vec<K>,pub rhs:E,pub power:K,pub next:usize }
fn accumulate_with_node(p:&Prepared,a:&mut Accumulator,mut node:M31,value:E,mut pending:Option<&mut BatchedWeights>) {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;
    for j in 0..a.weights.len() {
        let _ = j;
    }
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
    if let Some(weights)=pending {weights.terms+=1;}
}
