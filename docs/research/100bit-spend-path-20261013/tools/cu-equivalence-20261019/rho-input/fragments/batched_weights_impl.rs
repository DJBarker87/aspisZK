impl BatchedWeights {
    fn new(weights:&[K])->Result<Self,Error> {
        let mut raw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;
        for (out,w) in raw.iter_mut().zip(weights) {
            *out=[w.c0.a.0 as u64,w.c0.b.0 as u64,w.c1.a.0 as u64,w.c1.b.0 as u64];
        }
        Ok(Self{raw,terms:0})
    }
    #[inline(always)]
    fn push(&mut self,index:usize,power:K,basis:M31) {
        let limbs=[power.c0.a.0,power.c0.b.0,power.c1.a.0,power.c1.b.0];
        for j in 0..4 {self.raw[index][j]+=u64::from(limbs[j])*u64::from(basis.0);}
        if self.terms&3==3 {
            for limb in &mut self.raw[index] {*limb=(*limb&0x7fff_ffff)+(*limb>>31);}
        }
    }
    fn value(&self,index:usize)->K {
        let [a,b,c,d]=self.raw[index].map(M31::reduce_u64);
        K{c0:aspis_core::field::CM31{a,b},c1:aspis_core::field::CM31{a:c,b:d}}
    }
    fn finish(&self,weights:&mut[K]) {for (i,w) in weights.iter_mut().enumerate(){*w=self.value(i);}}
}