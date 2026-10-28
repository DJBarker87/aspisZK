// Appended only to this job's byte-prefix-verified native test copy.
impl Sha256VarCore {
    pub fn pv_dl_from_state(state:[u32;8],block_len:u64)->Self {Self{state,block_len}}
    pub fn pv_dl_state(&self)->([u32;8],u64) {(self.state,self.block_len)}
    pub fn pv_dl_compress_slice(state:&mut[u32;8],blocks:&[Block<Self>]) {
        compress256(state,blocks);
    }
    pub fn pv_dl_finalize_param<F>(&mut self,buffer:&mut Buffer<Self>,out:&mut Output<Self>,mut compress:F)
    where F:FnMut(&mut[u32;8],&[Block<Self>]) {
        let bs = <Self as BlockSizeUser>::BlockSize::U64;
        let bit_len = 8 * (buffer.get_pos() as u64 + bs * self.block_len);
        buffer.len64_padding_be(bit_len, |b| compress(&mut self.state, from_ref(b)));
        for (chunk, v) in out.chunks_exact_mut(4).zip(self.state.iter()) {
            chunk.copy_from_slice(&v.to_be_bytes());
        }
    }
}
