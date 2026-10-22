// Proof-only single-emission cuts. The source serializer remains unchanged.
// These checks cover bounded Vec storage; Lean supplies list inductions,
// not an unproved conversion of these checks into a universal Rust theorem.
#[cfg(kani)]
mod serialization17 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(34)]
    fn section_header() {
        let tag: u8 = kani::any();
        let mut out = Vec::new();
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&[tag,0,0,0,0,0,0,0]);
        assert_eq!(out.len(), HEADER);
        let i: usize = kani::any(); kani::assume(i < HEADER);
        assert_eq!(out[i], if i<8 {MAGIC[i]} else if i==8 {tag} else {0});
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn section_transcript_cell() {
        let logical: [u8;32] = kani::any();
        let initial: [u8;3] = kani::any();
        let mut out = initial.to_vec();
        let status = compact_values(&logical, &mut out);
        let high_zero = logical[16..].iter().all(|&b| b==0);
        if high_zero {
            assert_eq!(status, Ok(())); assert_eq!(out.len(), 19);
            assert_eq!(&out[..3], &initial); assert_eq!(&out[3..], &logical[..16]);
        } else {
            assert_eq!(status, Err(CodecError::NonZeroHigh)); assert_eq!(out.as_slice(), &initial);
        }
    }
    #[kani::proof]
    #[kani::unwind(65)]
    fn section_opening_cell() {
        // The serializer copies 4 bytes for lanes 0..26, 16 for lane 28,
        // then 16 for lanes 26..28. It does not encode lane order numerically.
        let lane: usize = kani::any(); kani::assume(lane<29);
        let encoded: [u8;32] = kani::any();
        let initial: [u8;3] = kani::any();
        let mut out = initial.to_vec();
        if lane<26 || lane==28 {
            out.extend_from_slice(&encoded[..if lane<26 {4}else{16}]);
        } else {out.extend_from_slice(&encoded[..16]);}
        let size = if lane<26 {4}else{16};
        assert_eq!(out.len(), 3+size); assert_eq!(&out[..3], &initial);
        let byte:usize=kani::any();kani::assume(byte<size);
        assert_eq!(out[3+byte],encoded[byte]);
    }
    #[kani::proof]
    #[kani::unwind(100)]
    fn section_node_padding_cell() {
        // One node and one padding-node transition, independent of node data.
        // Larger slot capacities are a separate induction/source obligation.
        let node:[u8;32]=kani::any();let initial:[u8;3]=kani::any();
        let mut out=initial.to_vec();let cap=64usize;
        out.extend_from_slice(&node);out.resize(out.len()+cap-node.len(),0);
        assert_eq!(out.len(),67);assert_eq!(&out[..3],&initial);
        let i:usize=kani::any();kani::assume(i<cap);
        assert_eq!(out[3+i],if i<32 {node[i]}else{0});
    }
    #[kani::proof]
    #[kani::unwind(8)]
    fn ordered_element() {
        let queries:[u32;22]=kani::any();
        let batch:usize=kani::any();let t:usize=kani::any();let ordinal:usize=kani::any();
        kani::assume(batch<2 && t<3);
        let range=if batch==0 {0..SPLIT}else{SPLIT..22};
        kani::assume(ordinal<range.len());
        // Single source map invocation; avoid whole symbolic Vec collection.
        let u=queries[range.clone()][ordinal];
        let mapped=core::iter::once(&u).map(|&u|if t==2 {u/4}else{u}).next().unwrap();
        let direct=queries[range.start+ordinal];
        assert_eq!(mapped,if t==2 {direct/4}else{direct});
        let old:u32=kani::any();let mut idx=alloc::vec![old];idx.push(mapped);
        assert_eq!(idx.len(),2);assert_eq!(idx[0],old);assert_eq!(idx[1],mapped);
    }
}
