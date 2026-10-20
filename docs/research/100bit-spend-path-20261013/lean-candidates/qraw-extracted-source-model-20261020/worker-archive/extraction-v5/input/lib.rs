mod canonical {
    pub const P:u32=0x7fff_ffff;
    #[derive(Clone,Copy,Debug,PartialEq,Eq,Default)]
    pub struct Q([u32;4]);
    impl Q {
        fn raw(self,rhs:Self)->[u64;4] {
            let [a,b,c,d]=self.0.map(|x|u64::from(x));let [e,f,g,h]=rhs.0.map(|x|u64::from(x));
            const PP:u64=(P as u64)*(P as u64);
            let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31);
            let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
            let v=partial((c*h).wrapping_add(d*g));
            [(a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
             (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v),
             (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f),
             (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)]
        }
    }
    pub fn raw_entry(a:[u32;4],b:[u32;4])->[u64;4] { Q(a).raw(Q(b)) }
}
pub fn raw_entry(a:[u32;4],b:[u32;4])->[u64;4] { canonical::raw_entry(a,b) }
