    #[inline(always)]
    pub fn finish(self) -> E {
        let [a,b,c,d]=self.c0.finish().limbs();
        let [e,f,g,h]=self.c1.finish().limbs();
        // The private accumulator produces canonical coordinates already.
        E::from_limbs([a,b,c,d,e,f,g,h]).unwrap()
    }