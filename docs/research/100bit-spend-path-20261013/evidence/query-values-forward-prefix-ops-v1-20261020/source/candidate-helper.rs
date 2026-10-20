fn query_values_forward_prefix<'a>(proof: &'a [u8], p: &Prepared, a: Accumulator, g: &[E; 29], obs: Observer, geometry: &QueryGeometry, pending: BatchedWeights) -> Result<(usize, usize, &'a [u8], [E; 4]), Error> {
    let i = a.next;
    let u = p.queries[i] as usize;
    let q = opening(proof, i);
    let dots = crate::fast_dots::four_dots(q, g);
    Ok((i, u, q, dots))
}
