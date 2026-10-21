fn tx2_common<H: Digest32>(public_bytes: &[u8], proof: &[u8], checkpoint: &[u8], hash: H, obs: Observer) -> Result<(), Error> {
    let (p, a) = resume(checkpoint, proof, public_bytes, Variant::S2, hash)?;
    if a.next != SPLIT {
        return Err(Error::Checkpoint);
    }
    let g = powers::<29>(p.gamma);
    mark(obs, Phase::CheckpointRead);
    let inactive = E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    batch_merkle(proof, &p, &folded_root, 1, hash)?;
    mark(obs, Phase::Merkle(SPLIT));
    let geometry = QueryGeometry::for_range(&p.queries, a.next, 22)?;
    let pending = BatchedWeights::new(&a.weights)?;
    let (a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, 22)?;
    // End the loop accumulator borrow before finishing its weights.
    let Accumulator { mut weights, rhs, power, next } = a;
    pending.finish(&mut weights);
    let a = Accumulator { weights, rhs, power, next };
    // Construct only the relation view after the last proof-consuming loop.
    let v = View {
        variant: Variant::S2, semantic: &[], y1: &[], inactive,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: None,
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    };
    finish_relation(&v, &p, &a, obs)
}
