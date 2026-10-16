    pub fn absorb(&mut self, row:u8, payload:&[u8]) {
        self.state=self.hash.digest(&[&self.state,&[0,0xa0+row],&(payload.len() as u32).to_le_bytes(),payload]);
    }