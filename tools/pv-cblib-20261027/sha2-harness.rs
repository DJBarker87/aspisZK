
#[cfg(kani)]
mod pv_cblib_library_checks {
    use super::*;
    // Owned safe reference on the actual private core carrier. Batch compression
    // remains the shipped function, executed once per supplied block; no stub.
    fn update_reference(c: &mut Sha256VarCore, blocks: &[Block<Sha256VarCore>]) {
        for b in blocks {
            c.block_len=c.block_len.wrapping_add(1);
            compress256(&mut c.state,core::slice::from_ref(b));
        }
    }
    #[kani::proof]
    #[kani::unwind(70)]
    fn op208_one_block() {
        let state:[u32;8]=kani::any();let count:u64=kani::any();
        let bytes:[u8;64]=kani::any();
        let n:usize=kani::any();kani::assume(n<=1);
        let blocks=[Block::<Sha256VarCore>::clone_from_slice(&bytes)];
        let mut native=Sha256VarCore{state,block_len:count};
        let mut reference=Sha256VarCore{state,block_len:count};
        UpdateCore::update_blocks(&mut native,&blocks[..n]);
        update_reference(&mut reference,&blocks[..n]);
        assert_eq!(native.state,reference.state);
        assert_eq!(native.block_len,reference.block_len);
    }
}
