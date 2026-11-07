fn validate_fission(w: &PoolV1PairLeafWitnessV1, scan_nonzero: bool, log: &mut Log) -> Result<(),PoolV1PairLeafErrorV1> {
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

        let one_minus_occupied = M31::ONE.sub(w.second_occupied);
        if mul_window(w.second_occupied, w.second_occupied.sub(M31::ONE), log) != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupancyNotBoolean);
        }
        if mul_window(w.second_sentinel(), w.second_occupancy_inverse, log) != w.second_occupied {
            return Err(PoolV1PairLeafErrorV1::SentinelInverseMismatch);
        }
        if mul_window(one_minus_occupied, w.second_occupancy_inverse, log) != M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::EmptyInverseNonZero);
        }
        if scan_nonzero
        {
            return Err(PoolV1PairLeafErrorV1::EmptyCommitmentNonZero);
        }
        if w.second_occupied == M31::ONE && w.second_sentinel() == M31::ZERO {
            return Err(PoolV1PairLeafErrorV1::OccupiedSentinelZero);
        }
        Ok(())
    }
