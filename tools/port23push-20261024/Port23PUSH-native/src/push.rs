    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let flush=self.terms&3==3;
        update_residue_row(&mut self.raw[index],power,basis,flush);
    }
