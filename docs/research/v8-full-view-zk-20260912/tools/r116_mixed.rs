// Included in the private canonical Q module, never the public field API.
impl Q {
    #[inline(always)]
    pub fn dot_m31<const N:usize>(left:[Self;N],right:[u32;N])->Option<Self>{
        assert!(N<=4);
        if right.iter().any(|&x|x>=P){return None;}
        let mut sums=[0u64;4];
        for i in 0..N {for j in 0..4 {
            // Four canonical products are strictly below 2^64.
            sums[j]=sums[j].wrapping_add(u64::from(left[i].0[j])*u64::from(right[i]));
        }}
        Some(Self(sums.map(reduce)))
    }
}
pub struct LineSums {sums:[[u64;4];4],count:usize}
impl LineSums {
    pub fn new()->Self{Self{sums:[[0;4];4],count:0}}
    #[inline(always)]
    pub fn push(&mut self,scale:Q,factors:[u32;3])->Option<()> {
        assert!(self.count<22);self.count+=1;
        if factors.iter().any(|&x|x>=P){return None;}
        for limb in 0..4 {
            self.sums[0][limb]=self.sums[0][limb].wrapping_add(u64::from(scale.0[limb]));
            for i in 0..3 {
                let raw=u64::from(scale.0[limb])*u64::from(factors[i]);
                let partial=(raw&u64::from(P)).wrapping_add(raw>>31);
                self.sums[i+1][limb]=self.sums[i+1][limb].wrapping_add(partial);
            }
        }
        // Each partial is <2P; at most 22 terms, so each sum is <44P.
        Some(())
    }
    pub fn finish(self,halvings:u8)->Option<[Q;4]>{
        if halvings>30{return None;}
        Some(self.sums.map(|v|Q(v.map(reduce)).half_pow(halvings).unwrap()))
    }
}
