fn accumulate_with_node(p:&Prepared,a:&mut Accumulator,mut node:M31,value:E,mut pending:Option<&mut BatchedWeights>) {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..a.weights.len() {
        if let Some(weights)=pending.as_deref_mut() {
            weights.push(j,a.power,basis[j]);
            #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        } else {a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));}
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    if let Some(weights)=pending {weights.terms+=1;}
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
}
