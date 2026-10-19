    pub fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E {
        let block=self.block(row,payload);
        let out=if nonzero {crate::sampler::gamma_sample(&block)} else {crate::sampler::ordinary_sample(&block)};
        crate::trace::value(4,row as usize,out); out
    }