//! Exact-field dot accumulator candidates; arithmetic-only equivalence code.
mod canonical {
    //! Private canonical representation: validate at the boundary, preserve internally.
    //! No public unchecked constructor. This does NOT change aspis_core::M31.
    pub const P:u32=0x7fff_ffff;
    const MASK:u64=0x7fff_ffff_7fff_ffff;
    const ONES:u64=0x0000_0001_0000_0001;
    #[derive(Clone,Copy,Debug,PartialEq,Eq,Default)]
    pub struct Q([u32;4]);
    #[inline(always)] pub(crate) fn reduce(mut x:u64)->u32 {
        x=(x & u64::from(P))+(x>>31);
        x=(x & u64::from(P))+(x>>31);
        if x>=u64::from(P) {(x-u64::from(P)) as u32}else{x as u32}
    }
    #[inline(always)] pub(crate) fn add(a:u32,b:u32)->u32 {
        let s=a.wrapping_add(b);if s>=P{s-P}else{s}
    }
    #[inline(always)] fn pair(a:u32,b:u32)->u64 {u64::from(a)|(u64::from(b)<<32)}
    #[inline(always)] fn reduce_pair(s:u64)->u64 {
        (s.wrapping_add(((s.wrapping_add(ONES))>>31)&ONES))&MASK
    }
    impl Q {
        pub const ZERO:Self=Self([0;4]);pub const ONE:Self=Self([1,0,0,0]);
        pub fn from_limbs(x:[u32;4])->Option<Self>{if x.iter().all(|&v|v<P){Some(Self(x))}else{None}}
        pub fn from_m31(x:u32)->Option<Self>{if x<P{Some(Self([x,0,0,0]))}else{None}}
        pub const fn limbs(self)->[u32;4]{self.0}
        /// WideExact owns private, canonical coordinates; this constructor
        /// accepts only that validated type, never raw QM31 limbs or bytes.
        #[inline(always)]
        pub(super) fn from_wide(value:super::E)->[Self;2] {
            let [a,b,c,d,e,f,g,h]=value.to_limbs();
            [Self([a,b,c,d]),Self([e,f,g,h])]
        }
        #[inline(always)]
        pub fn prepare(self)->Prepared {
            let [a,b,c,d]=self.0;
            let ac=add(a,c);let bd=add(b,d);
            Prepared([a,b,add(a,b),c,d,add(c,d),ac,bd,add(ac,bd)])
        }
        #[inline(always)] pub fn add(self,rhs:Self)->Self {
            let a=reduce_pair(pair(self.0[0],self.0[1]).wrapping_add(pair(rhs.0[0],rhs.0[1])));
            let b=reduce_pair(pair(self.0[2],self.0[3]).wrapping_add(pair(rhs.0[2],rhs.0[3])));
            Self([a as u32,(a>>32) as u32,b as u32,(b>>32) as u32])
        }
        #[inline(always)] pub fn sub(self,rhs:Self)->Self {
            let a=reduce_pair(pair(self.0[0],self.0[1]).wrapping_add(MASK).wrapping_sub(pair(rhs.0[0],rhs.0[1])));
            let b=reduce_pair(pair(self.0[2],self.0[3]).wrapping_add(MASK).wrapping_sub(pair(rhs.0[2],rhs.0[3])));
            Self([a as u32,(a>>32) as u32,b as u32,(b>>32) as u32])
        }
        #[inline(always)] pub fn half(self)->Self {
            let h=|x:u32|(x>>1)|((x&1)<<30);Self(self.0.map(h))
        }
        pub fn half_pow(self,n:u8)->Option<Self>{
            if n>30{return None}if n==0{return Some(self)}
            Some(Self(self.0.map(|x|(x>>n)|((x&((1u32<<n)-1))<<(31-n)))))
        }
        #[inline(always)] pub fn mul_m31(self,rhs:u32)->Option<Self>{
            if rhs>=P{return None}Some(Self(self.0.map(|x|reduce(u64::from(x)*u64::from(rhs)))))
        }
        /// Benchmark candidate, not an assertion of superiority over staged R19.
        /// All intermediates are nonnegative and strictly below 2^64.
        #[inline(always)] pub fn mul(self,rhs:Self)->Self {
            let [a,b,c,d]=self.0.map(u64::from);let [e,f,g,h]=rhs.0.map(u64::from);
            const PP:u64=(P as u64)*(P as u64);
            let partial=|x:u64|(x&u64::from(P)).wrapping_add(x>>31);
            let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
            let v=partial((c*h).wrapping_add(d*g));
            Self([reduce((a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v)),
                reduce((a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v)),
                reduce((a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f)),
                reduce((a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e))])
        }
    }

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

    /// Nine canonical Karatsuba channels, constructible only from canonical Q.
    pub struct Prepared([u32;9]);
    /// Four raw products per channel fit u64: 4*(P-1)^2 < 2^64.
    /// Fold each group once; <=1024 groups and a final residual give sums <2^44.
    /// The outer E accumulators enforce <=4096 terms and supply a shared flush.
    pub struct Dot { batch:[u64;9], sums:[u64;9] }
    impl Dot {
        pub fn new()->Self {Self{batch:[0;9],sums:[0;9]}}
        #[inline(always)]
        pub fn push(&mut self,a:&Prepared,b:&Prepared,flush:bool) {
            for j in 0..9 {self.batch[j]+=u64::from(a.0[j])*u64::from(b.0[j]);}
            if flush {
                for j in 0..9 {
                    self.sums[j]+=(self.batch[j]&u64::from(P))+(self.batch[j]>>31);
                    self.batch[j]=0;
                }
            }
        }
        pub fn finish(self)->Q {
            let channels:[u32;9]=core::array::from_fn(|j|
                reduce(self.sums[j]+(self.batch[j]&u64::from(P))+(self.batch[j]>>31)));
            let sub=|a:u32,b:u32|if a>=b {a-b}else{a.wrapping_add(P).wrapping_sub(b)};
            let cm=|i:usize|[sub(channels[i],channels[i+1]),sub(sub(channels[i+2],channels[i]),channels[i+1])];
            let m0=cm(0);let m1=cm(3);let m2=cm(6);
            Q([sub(add(m0[0],add(m1[0],m1[0])),m1[1]),
               add(m0[1],add(m1[0],add(m1[1],m1[1]))),
               sub(sub(m2[0],m0[0]),m1[0]),sub(sub(m2[1],m0[1]),m1[1])])
        }
    }

}


use aspis_core::field::{CM31, QM31, WideExact as E};

const MAX_TERMS: usize = 4096;

#[inline(always)]
fn limbs_of(k: QM31) -> [u32; 4] {
    [k.c0.a.0, k.c0.b.0, k.c1.a.0, k.c1.b.0]
}

#[inline(always)]
fn checked_q(k: QM31) -> Result<canonical::Q, ()> {
    canonical::Q::from_limbs(limbs_of(k)).ok_or(())
}

#[inline(always)]
fn qm31_of(q: canonical::Q) -> QM31 {
    let [a, b, c, d] = q.limbs();
    QM31 {
        c0: CM31 { a: aspis_core::field::M31(a), b: aspis_core::field::M31(b) },
        c1: CM31 { a: aspis_core::field::M31(c), b: aspis_core::field::M31(d) },
    }
}

/// Candidate exact accumulator for sums of `WideExact * QM31`.
/// Canonical QM31 coordinates and the 4096-term limit are checked at push.
pub struct EbyKDot {
    c0: canonical::Dot,
    c1: canonical::Dot,
    count: usize,
}

impl EbyKDot {
    pub fn new() -> Self {
        Self { c0: canonical::Dot::new(), c1: canonical::Dot::new(), count: 0 }
    }

    #[inline(always)]
    pub fn push(&mut self, value: E, scalar: QM31) -> Result<(), ()> {
        if self.count >= MAX_TERMS { return Err(()); }
        let [value_c0,value_c1] = canonical::Q::from_wide(value);
        let scalar = checked_q(scalar)?.prepare();
        let value_c0=value_c0.prepare();let value_c1=value_c1.prepare();
        let flush=self.count&3==3;
        self.c0.push(&value_c0, &scalar, flush);
        self.c1.push(&value_c1, &scalar, flush);
        self.count += 1;
        Ok(())
    }

    #[inline(always)]
    pub fn finish(self) -> E {
        let [a,b,c,d]=self.c0.finish().limbs();
        let [e,f,g,h]=self.c1.finish().limbs();
        // The private accumulator produces canonical coordinates already.
        E::from_limbs([a,b,c,d,e,f,g,h]).unwrap()
    }
}

/// Candidate exact accumulator for sums of `WideExact * WideExact`.
/// Four canonical QM31 dot accumulators implement the outer quadratic tower.
pub struct EbyEDot {
    ac: canonical::Dot,
    bd: canonical::Dot,
    ad: canonical::Dot,
    bc: canonical::Dot,
    count: usize,
}

impl EbyEDot {
    pub fn new() -> Self {
        Self {
            ac: canonical::Dot::new(), bd: canonical::Dot::new(),
            ad: canonical::Dot::new(), bc: canonical::Dot::new(), count: 0,
        }
    }

    #[inline(always)]
    pub fn push(&mut self, left: E, right: E) -> Result<(), ()> {
        if self.count >= MAX_TERMS { return Err(()); }
        let [a,b] = canonical::Q::from_wide(left);
        let [c,d] = canonical::Q::from_wide(right);
        let a=a.prepare();let b=b.prepare();let c=c.prepare();let d=d.prepare();
        let flush=self.count&3==3;
        self.ac.push(&a, &c, flush);
        self.bd.push(&b, &d, flush);
        self.ad.push(&a, &d, flush);
        self.bc.push(&b, &c, flush);
        self.count += 1;
        Ok(())
    }

    #[inline(always)]
    pub fn finish(self) -> E {
        let ac = qm31_of(self.ac.finish());
        let bd = qm31_of(self.bd.finish());
        let ad = qm31_of(self.ad.finish());
        let bc = qm31_of(self.bc.finish());
        // v^2 = u, where WideExact::U embeds the QM31 generator in the base.
        E::new(ac.add(bd.mul(E::U)), ad.add(bc))
    }
}
