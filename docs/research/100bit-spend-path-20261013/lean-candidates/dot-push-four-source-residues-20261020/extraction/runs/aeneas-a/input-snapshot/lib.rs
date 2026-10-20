pub mod canonical {
    pub const P:u32=0x7fff_ffff;
    pub struct Q([u32;4]);
    impl Q {
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
    }
    pub struct Dot { sums:[u64;4] }
    impl Dot {
        pub fn push(&mut self,a:Q,b:Q) {
            // Both enclosing public accumulators check the 4096-term bound.
            // This private accumulator cannot be reached by raw callers.
            let raw=a.raw(b);
            self.sums[0]=self.sums[0].wrapping_add((raw[0]&u64::from(P)).wrapping_add(raw[0]>>31));
            self.sums[1]=self.sums[1].wrapping_add((raw[1]&u64::from(P)).wrapping_add(raw[1]>>31));
            self.sums[2]=self.sums[2].wrapping_add((raw[2]&u64::from(P)).wrapping_add(raw[2]>>31));
            self.sums[3]=self.sums[3].wrapping_add((raw[3]&u64::from(P)).wrapping_add(raw[3]>>31));
        }
    }
}
pub fn dot_push_entry(mut dot:canonical::Dot,a:canonical::Q,b:canonical::Q)->canonical::Dot {dot.push(a,b);dot}
pub fn option_context_anchor(v:Option<u8>)->Option<u8>{v}
