#[inline(never)]
fn tx2_common<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    let (p, mut a) = resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
    if a.next != SPLIT {
        return Err(Error::Checkpoint);
    }
    let g = powers::<29>(p.gamma);
    mark(obs, Phase::CheckpointRead);
    let v = wide_view(proof, &[], &[])?;
    batch_merkle(proof, &p, v.folded_root.unwrap(), 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, a.next, 22)?;
    let mut pending = BatchedWeights::new(&a.weights)?;
    while a.next < 22 {
        query_values(proof, &p, &mut a, &g, obs, &geometry, Some(&mut pending))?;
    }
    pending.finish(&mut a.weights);
    finish_relation(&v, &p, &a, obs)
}