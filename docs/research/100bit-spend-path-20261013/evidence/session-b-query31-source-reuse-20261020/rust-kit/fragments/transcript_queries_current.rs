    pub fn queries(&mut self, row:u8, payload:&[u8])->Result<[u32;22],crate::verifier::Error> {
        self.absorb(row,payload);
        let mut blocks=[[0;32];8];let mut advances=blocks; let mut state=self.state;
        blocks[0]=self.hash.digest(&[&state,&[1]]);
        advances[0]=self.hash.digest(&[&state,&[2]]);state=advances[0];
        blocks[1]=self.hash.digest(&[&state,&[1]]);
        advances[1]=self.hash.digest(&[&state,&[2]]);state=advances[1];
        blocks[2]=self.hash.digest(&[&state,&[1]]);
        advances[2]=self.hash.digest(&[&state,&[2]]);state=advances[2];
        blocks[3]=self.hash.digest(&[&state,&[1]]);
        advances[3]=self.hash.digest(&[&state,&[2]]);state=advances[3];
        blocks[4]=self.hash.digest(&[&state,&[1]]);
        advances[4]=self.hash.digest(&[&state,&[2]]);state=advances[4];
        blocks[5]=self.hash.digest(&[&state,&[1]]);
        advances[5]=self.hash.digest(&[&state,&[2]]);state=advances[5];
        blocks[6]=self.hash.digest(&[&state,&[1]]);
        advances[6]=self.hash.digest(&[&state,&[2]]);state=advances[6];
        blocks[7]=self.hash.digest(&[&state,&[1]]);
        advances[7]=self.hash.digest(&[&state,&[2]]);state=advances[7];
        let (q,state)=aspis_core::r0_transcript::queries_from_pairs(&blocks,&advances).map_err(|_|crate::verifier::Error::Transcript)?;
        self.state=state;
        { let u=q[0]; crate::trace::value(5,0,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[1]; crate::trace::value(5,1,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[2]; crate::trace::value(5,2,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[3]; crate::trace::value(5,3,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[4]; crate::trace::value(5,4,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[5]; crate::trace::value(5,5,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[6]; crate::trace::value(5,6,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[7]; crate::trace::value(5,7,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[8]; crate::trace::value(5,8,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[9]; crate::trace::value(5,9,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[10]; crate::trace::value(5,10,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[11]; crate::trace::value(5,11,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[12]; crate::trace::value(5,12,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[13]; crate::trace::value(5,13,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[14]; crate::trace::value(5,14,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[15]; crate::trace::value(5,15,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[16]; crate::trace::value(5,16,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[17]; crate::trace::value(5,17,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[18]; crate::trace::value(5,18,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[19]; crate::trace::value(5,19,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[20]; crate::trace::value(5,20,E::from_m31(aspis_core::field::M31(u))); }
        { let u=q[21]; crate::trace::value(5,21,E::from_m31(aspis_core::field::M31(u))); }
        Ok(q)
    }
