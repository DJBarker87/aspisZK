// Proof-only section checks; compact functions called from unchanged source.
#[cfg(kani)]
mod serialization16 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(65)]
    fn compact_value_prefix() {
        let low: [u8;16] = kani::any();
        let prefix: [u8;3] = kani::any();
        let mut logical = [0u8;32];
        logical[..16].copy_from_slice(&low);
        let mut out = prefix.to_vec();
        assert_eq!(compact_values(&logical, &mut out), Ok(()));
        assert_eq!(&out[..3], &prefix);
        assert_eq!(&out[3..], &low);
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn compact_value_error() {
        let logical: [u8;32] = kani::any();
        kani::assume(logical[16..].iter().any(|&b| b != 0));
        let prefix: [u8;3] = kani::any();
        let mut out = prefix.to_vec();
        assert_eq!(compact_values(&logical, &mut out), Err(CodecError::NonZeroHigh));
        assert_eq!(out.as_slice(), &prefix);
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn expand_value() {
        let low: [u8;16] = kani::any();
        let mut out: [u8;32] = kani::any();
        assert_eq!(expand_values(&low, &mut out), Ok(()));
        assert_eq!(&out[..16], &low);
        assert!(out[16..].iter().all(|&b| b == 0));
    }
    #[kani::proof]
    #[kani::unwind(8)]
    fn node_slot_offsets() {
        let slot: usize = kani::any();
        kani::assume(slot < 6);
        let offsets = [28_359,33_031,37_703,41_799,47_303,52_807,57_607];
        assert_eq!(slot_offset(slot), offsets[slot]);
        assert_eq!(slot_offset(slot+1)-slot_offset(slot), 32*SLOT_NODES[slot]);
    }
    // Literal three-line index block of prover.rs, with the same ordered
    // ranges and per-tree map. This is a block comparison, not a whole caller.
    #[kani::proof]
    #[kani::unwind(64)]
    fn ordered_batch_indices() {
        let queries: [u32;22] = kani::any();
        let batch: usize = kani::any();
        let t: usize = kani::any();
        kani::assume(batch < 2 && t < 3);
        let range = if batch==0 {0..SPLIT} else {SPLIT..22};
        let mut idx:Vec<u32>=queries[range.clone()].iter().map(|&u|if t==2 {u/4} else {u}).collect();
        idx.sort();idx.dedup();
        let key: u32 = kani::any();
        let mut member = false;
        for i in range {
            member |= key == if t==2 {queries[i]/4} else {queries[i]};
        }
        assert_eq!(idx.contains(&key), member);
        let probe: usize = kani::any();
        kani::assume(probe < idx.len());
        if probe+1 < idx.len() {assert!(idx[probe] < idx[probe+1]);}
    }
}
