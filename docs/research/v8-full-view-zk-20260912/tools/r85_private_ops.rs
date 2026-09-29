// Appended to the retained private Q module. Only Q can reach the raw path:
// its limbs are private, constructors validate, and operations preserve <P.
impl Q {
    #[inline(always)]
    fn raw(self,rhs:Self)->[u64;4] {
        let [a,b,c,d]=self.0.map(u64::from);let [e,f,g,h]=rhs.0.map(u64::from);
        const PP:u64=(P as u64)*(P as u64);
        let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31);
        let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
        let v=partial((c*h).wrapping_add(d*g));
        [(a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
         (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v),
         (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f),
         (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)]
    }
    #[inline(always)]
    pub fn dot<const N:usize>(left:[Self;N],right:[Self;N])->Self {
        assert!(N<=4);let mut sums=[0u64;4];
        for i in 0..N {
            let raw=left[i].raw(right[i]);
            for j in 0..4 {sums[j]=sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31));}
        }
        // Retained R59 bounds: each folded raw value <2^34, N<=4.
        Self(sums.map(reduce))
    }
    #[inline(always)] pub fn neg(self)->Self {Self::ZERO.sub(self)}
    #[inline(always)] pub fn square(self)->Self {self.mul(self)}
}
