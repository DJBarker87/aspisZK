pub fn accumulate_owned(p:&Prepared,mut a:Accumulator,mut node:M31,value:E,mut weights:BatchedWeights)->(Accumulator,BatchedWeights) {
    let width=a.weights.len();
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<width {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..width {
        weights.push(j,a.power,basis_at(&basis,j));
        #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        crate::trace::value(12,a.next*width+j,E::from_qm31(accumulated_weight_at(&a.weights,j)));
        crate::trace::value(13,a.next*width+j,E::from_m31(basis_at(&basis,j)));
    }
    weights.terms+=1;
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
    (a,weights)
}
fn opening(proof: &[u8], i: usize) -> &[u8] {
    let at = compact::OFF_OPENINGS + i * OPENING;
    &proof[at..at + OPENING]
}
pub fn query_owned(proof: &[u8], p: &Prepared, mut a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, mut pending: BatchedWeights) -> Result<(Accumulator, BatchedWeights), Error> {
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    crate::trace::value(9, 4 * i, dots[0]);
    crate::trace::value(9, 4 * i + 1, dots[1]);
    crate::trace::value(9, 4 * i + 2, dots[2]);
    crate::trace::value(9, 4 * i + 3, dots[3]);
    let inverse = *geometry.for_query(i);
    let folded = circle_fold_with_inverses(p.alpha[0], dots, &inverse);
    crate::trace::value(10, 2 * i, folded);
    let values = core::array::from_fn(|s| field(&q[672..800], s));
    if folded != values[u % 4] {
        return Err(Error::Query);
    }
    let folded = line_fold_with_inverses(p.alpha[1], values, &inverse);
    crate::trace::value(10, 2 * i + 1, folded);
    let z = geometry.line_z[i - geometry.start];
    let node = z.mul(z).double().sub(M31::ONE);
    let (a, pending) = accumulate_owned(p, a, node, folded, pending);
    mark(obs, Phase::Query(i));
    Ok((a, pending))
}
pub fn query_loop_owned(proof: &[u8], p: &Prepared, mut a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: BatchedWeights, end: usize) -> Result<(Accumulator, BatchedWeights), Error> {
    let mut state = Ok((a, pending));
    loop {
        match state {
            Err(error) => return Err(error),
            Ok((a, pending)) => {
                if a.next >= end {
                    return Ok((a, pending));
                }
                state = query_owned(proof, p, a, g, obs, geometry, pending);
            }
        }
    }
}
pub fn accumulate_optional_owned(p:&Prepared,mut a:Accumulator,mut node:M31,value:E,mut pending:Option<BatchedWeights>)->(Accumulator,Option<BatchedWeights>) {
    let mut basis=[M31::ZERO;256];basis[0]=M31::ONE;let mut n=1;
    while n<a.weights.len() {for j in 0..n {basis[n+j]=basis[j].mul(node);} node=node.mul(node).double().sub(M31::ONE);n*=2;}
    for j in 0..a.weights.len() {
        pending = if let Some(mut weights)=pending {
            weights.push(j,a.power,basis[j]);
            #[cfg(feature="prover")] {a.weights[j]=weights.value(j);}
        Some(weights) } else {a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j])); None };
        crate::trace::value(12,a.next*a.weights.len()+j,E::from_qm31(a.weights[j]));
        crate::trace::value(13,a.next*a.weights.len()+j,E::from_m31(basis[j]));
    }
    if let Some(weights)=pending.as_mut() {weights.terms+=1;}
    a.rhs=a.rhs.add(value.mul_qm31(a.power));crate::trace::value(11,a.next,a.rhs);
    a.power=a.power.mul(p.rho);a.next+=1;
    (a,pending)
}
