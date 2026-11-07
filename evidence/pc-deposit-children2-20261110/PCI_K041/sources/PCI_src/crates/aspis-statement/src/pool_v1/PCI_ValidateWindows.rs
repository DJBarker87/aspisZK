fn gates_window(w:&PoolV1PairLeafWitnessV1)->Result<(),PoolV1PairLeafErrorV1> {
        if !digest_is_canonical(&w.first_commitment)
            || !digest_is_canonical(&w.second_commitment)
        {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalCommitment);
        }
        if w.second_occupied.0 >= P {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalOccupancy);
        }
        if w.second_occupancy_inverse.0 >= P {
            return Err(PoolV1PairLeafErrorV1::NonCanonicalInverse);
        }

        Ok(())
}
fn operands_window(w:&PoolV1PairLeafWitnessV1)->[M31;6]{
 [w.second_occupied,w.second_occupied.sub(M31::ONE),w.second_sentinel(),w.second_occupancy_inverse,M31::ONE.sub(w.second_occupied),w.second_occupancy_inverse]
}
fn post_product0(product:M31,occupied:M31)->Result<(),PoolV1PairLeafErrorV1>{
 if product != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupancyNotBoolean);
        }
 Ok(())
}
fn post_product1(product:M31,occupied:M31)->Result<(),PoolV1PairLeafErrorV1>{
 if product != occupied {
            return Err(PoolV1PairLeafErrorV1::SentinelInverseMismatch);
        }
 Ok(())
}
fn post_product2(product:M31,occupied:M31)->Result<(),PoolV1PairLeafErrorV1>{
 if product != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::EmptyInverseNonZero);
        }
 Ok(())
}
fn tail_window(w:&PoolV1PairLeafWitnessV1,scan_nonzero:bool)->Result<(),PoolV1PairLeafErrorV1> {
    if scan_nonzero
        {
            return Err(PoolV1PairLeafErrorV1::EmptyCommitmentNonZero);
        }
        if w.second_occupied == M31::ONE && w.second_sentinel() == M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupiedSentinelZero);
        }
        Ok(())
    }
