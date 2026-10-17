    pub fn queries(&mut self, row:u8, payload:&[u8])->Result<[u32;22],crate::verifier::Error> {
        self.absorb(row,payload);
        let mut blocks=[[0;32];8];let mut advances=blocks; let mut state=self.state;
        for k in 0..8 {
            blocks[k]=self.hash.digest(&[&state,&[1]]);
            advances[k]=self.hash.digest(&[&state,&[2]]);state=advances[k];
        }
        let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        for (i,&u) in q.iter().enumerate() { crate::trace::value(5,i,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
    }