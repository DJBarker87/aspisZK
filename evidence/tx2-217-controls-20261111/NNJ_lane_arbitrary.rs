// Included only under cfg(kani), in the type's defining module.
// All fields unrestricted, including noncanonical M31 bit patterns.
impl kani::Arbitrary for PoolV1PairForestLaneStateV1 {
    fn any() -> Self {
        Self { bump: kani::any(), master: kani::any(), lane_id: kani::any(),
            tree: IncrementalMerkleTreeV1 {
                next_leaf_index: kani::any(), root: kani::any(), frontier: kani::any(),
            }
        }
    }
}
