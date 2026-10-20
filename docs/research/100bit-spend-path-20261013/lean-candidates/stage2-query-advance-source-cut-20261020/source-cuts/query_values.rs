fn query_values(proof: &[u8], p: &Prepared, a: &mut Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: Option<&mut BatchedWeights>) -> Result<(), Error> {
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    for s in 0..4 {
        crate::trace::value(9, 4 * i + s, dots[s]);
    }
    let inverse = geometry.for_query(i);
    let folded = circle_fold_with_inverses(p.alpha[0], dots, inverse);
    crate::trace::value(10, 2 * i, folded);
    let values = core::array::from_fn(|s| field(&q[672..800], s));
    if folded != values[u % 4] {
        return Err(Error::Query);
    }
    let folded = line_fold_with_inverses(p.alpha[1], values, inverse);
    crate::trace::value(10, 2 * i + 1, folded);
    let z = geometry.line_z[i - geometry.start];
    let node = z.mul(z).double().sub(M31::ONE);
    accumulate_with_node(p, a, node, folded, pending);
    mark(obs, Phase::Query(i));
    Ok(())
}
