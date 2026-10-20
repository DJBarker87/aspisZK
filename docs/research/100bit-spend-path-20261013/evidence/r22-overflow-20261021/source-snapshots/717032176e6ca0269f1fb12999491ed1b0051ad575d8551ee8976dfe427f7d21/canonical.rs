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
        let s=a.r22_add(b);if s>=P{s-P}else{s}
    }
    #[inline(always)] fn pair(a:u32,b:u32)->u64 {u64::from(a)|(u64::from(b)<<32)}
    #[inline(always)] fn reduce_pair(s:u64)->u64 {
        (s.r22_add(((s.r22_add(ONES))>>31)&ONES))&MASK
    }
    impl Q {
        pub const ZERO:Self=Self([0;4]);pub const ONE:Self=Self([1,0,0,0]);
        pub fn from_limbs(x:[u32;4])->Option<Self>{if x.iter().all(|&v|v<P){Some(Self(x))}else{None}}
        pub fn from_m31(x:u32)->Option<Self>{if x<P{Some(Self([x,0,0,0]))}else{None}}
        pub const fn limbs(self)->[u32;4]{self.0}
        /// WideExact owns private, canonical coordinates; this constructor
        /// accepts only that validated type, never raw QM31 limbs or bytes.
        #[inline(always)]
        // from_wide excluded: external WideExact constructor boundary
        #[inline(always)] pub fn add(self,rhs:Self)->Self {
            let a=reduce_pair(pair(self.0[0],self.0[1]).r22_add(pair(rhs.0[0],rhs.0[1])));
            let b=reduce_pair(pair(self.0[2],self.0[3]).r22_add(pair(rhs.0[2],rhs.0[3])));
            Self([a as u32,(a>>32) as u32,b as u32,(b>>32) as u32])
        }
        #[inline(always)] pub fn sub(self,rhs:Self)->Self {
            let a=reduce_pair(pair(self.0[0],self.0[1]).r22_add(MASK).r22_sub(pair(rhs.0[0],rhs.0[1])));
            let b=reduce_pair(pair(self.0[2],self.0[3]).r22_add(MASK).r22_sub(pair(rhs.0[2],rhs.0[3])));
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
            let partial=|x:u64|(x&u64::from(P)).r22_add(x>>31);
            let u=partial((c*g).r22_add(PP).r22_sub(d*h));
            let v=partial((c*h).r22_add(d*g));
            Self([reduce((a*e).r22_add(PP).r22_sub(b*f).r22_add(2*u).r22_add(3*u64::from(P)).r22_sub(v)),
                reduce((a*f).r22_add(b*e).r22_add(u).r22_add(2*v)),
                reduce((a*g).r22_add(c*e).r22_add(2*PP).r22_sub(b*h).r22_sub(d*f)),
                reduce((a*h).r22_add(b*g).r22_add(c*f).r22_add(d*e))])
        }
    }

    // Appended to the retained private Q module. Only Q can reach the raw path:
    // its limbs are private, constructors validate, and operations preserve <P.
    impl Q {
        #[inline(always)]
        fn raw(self,rhs:Self)->[u64;4] {
            let [a,b,c,d]=self.0.map(u64::from);let [e,f,g,h]=rhs.0.map(u64::from);
            const PP:u64=(P as u64)*(P as u64);
            let partial=|x:u64|(x&u64::from(P)).r22_add(x>>31);
            let u=partial((c*g).r22_add(PP).r22_sub(d*h));
            let v=partial((c*h).r22_add(d*g));
            [(a*e).r22_add(PP).r22_sub(b*f).r22_add(2*u).r22_add(3*u64::from(P)).r22_sub(v),
             (a*f).r22_add(b*e).r22_add(u).r22_add(2*v),
             (a*g).r22_add(c*e).r22_add(2*PP).r22_sub(b*h).r22_sub(d*f),
             (a*h).r22_add(b*g).r22_add(c*f).r22_add(d*e)]
        }
        #[inline(always)]
        pub fn dot<const N:usize>(left:[Self;N],right:[Self;N])->Self {
            assert!(N<=4);let mut sums=[0u64;4];
            for i in 0..N {
                let raw=left[i].raw(right[i]);
                for j in 0..4 {sums[j]=sums[j].r22_add((raw[j]&u64::from(P)).r22_add(raw[j]>>31));}
            }
            // Retained R59 bounds: each folded raw value <2^34, N<=4.
            Self(sums.map(reduce))
        }
        #[inline(always)] pub fn neg(self)->Self {Self::ZERO.sub(self)}
        #[inline(always)] pub fn square(self)->Self {self.mul(self)}
    }

    // Private canonical operands; bounded raw representatives, canonical result.
    // At most 4096 partial folds, each <2^34, sum <2^46. No u64 wrap.
    pub struct Dot { sums:[u64;4] }
    impl Dot {
        pub fn new()->Self {Self{sums:[0;4]}}
        #[inline(always)]
        pub fn push(&mut self,a:Q,b:Q) {
            // Both enclosing public accumulators check the 4096-term bound.
            // This private accumulator cannot be reached by raw callers.
            let raw=a.raw(b);
            for j in 0..4 {
                self.sums[j]=self.sums[j].r22_add(
                    (raw[j]&u64::from(P)).r22_add(raw[j]>>31));
            }
        }
        pub fn finish(self)->Q {Q(self.sums.map(reduce))}
    }
// Explicit wrapping operations need checks in addition to Kani's defaults.
trait R22Checked: Sized {
    fn r22_add(self, rhs: Self) -> Self;
    fn r22_sub(self, rhs: Self) -> Self;
}
macro_rules! checks {
    ($t:ty) => { impl R22Checked for $t {
        fn r22_add(self,rhs:Self)->Self {self.checked_add(rhs).expect("R22 wrapping add must not overflow")}
        fn r22_sub(self,rhs:Self)->Self {self.checked_sub(rhs).expect("R22 wrapping sub must not underflow")}
    }};
}
checks!(u32); checks!(u64);
#[cfg(kani)]
fn arbitrary_q()->Q {
    let a:[u32;4]=kani::any();
    for x in a {kani::assume(x<P);}
    Q(a)
}
#[cfg(kani)] #[kani::proof]
fn reduce_all_u64() { let x:u64=kani::any(); assert!(reduce(x)<P); }
#[cfg(kani)] #[kani::proof]
fn scalar_add_canonical() {
    let a:u32=kani::any();let b:u32=kani::any();
    kani::assume(a<P && b<P);assert!(add(a,b)<P);
}
#[cfg(kani)] #[kani::proof]
fn packed_add() {
    let a=arbitrary_q();let b=arbitrary_q();let c=a.add(b);
    for x in c.limbs() {assert!(x<P);}
}
#[cfg(kani)] #[kani::proof]
fn packed_sub() {
    let a=arbitrary_q();let b=arbitrary_q();let c=a.sub(b);
    for x in c.limbs() {assert!(x<P);}
}
#[cfg(kani)] #[kani::proof]
fn half_and_half_pow() {
    let a=arbitrary_q();let n:u8=kani::any();
    for x in a.half().limbs() {assert!(x<P);}
    if let Some(b)=a.half_pow(n) {for x in b.limbs() {assert!(x<P);}}
}
// Products from canonical limbs satisfy these caps. Independent products
// overapproximate their correlations: no solver assumption claims Q::mul total.
#[cfg(kani)] fn prod()->u64 {let x:u64=kani::any();kani::assume(x<=(u64::from(P)-1).pow(2));x}
#[cfg(kani)] fn partial_bound()->u64 {let x:u64=kani::any();kani::assume(x<=3*u64::from(P));x}
#[cfg(kani)] #[kani::proof]
fn widened_u32_product() {
    let a:u32=kani::any();let b:u32=kani::any();
    let product=u64::from(a)*u64::from(b);
    assert!(product<=u64::from(u32::MAX).pow(2));
}
#[cfg(kani)] #[kani::proof]
fn raw_partial_ranges() {
    const PP:u64=(P as u64)*(P as u64);
    let cg=prod();let dh=prod();let ch=prod();let dg=prod();
    let partial=|x:u64|(x&u64::from(P)).r22_add(x>>31);
    let u=partial(cg.r22_add(PP).r22_sub(dh));
    let v=partial(ch.r22_add(dg));
    assert!(u<=3*u64::from(P));assert!(v<=3*u64::from(P));
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate0() {
    const PP:u64=(P as u64)*(P as u64);
    let ae=prod();let bf=prod();let u=partial_bound();let v=partial_bound();
    let _x=ae.r22_add(PP).r22_sub(bf).r22_add(2*u).r22_add(3*u64::from(P)).r22_sub(v);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate1() {
    let af=prod();let be=prod();let u=partial_bound();let v=partial_bound();
    let _x=af.r22_add(be).r22_add(u).r22_add(2*v);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate2() {
    const PP:u64=(P as u64)*(P as u64);
    let ag=prod();let ce=prod();let bh=prod();let df=prod();
    let _x=ag.r22_add(ce).r22_add(2*PP).r22_sub(bh).r22_sub(df);
}
#[cfg(kani)] #[kani::proof]
fn raw_coordinate3() {
    let ah=prod();let bg=prod();let cf=prod();let de=prod();
    let _x=ah.r22_add(bg).r22_add(cf).r22_add(de);
}
#[cfg(kani)] #[kani::proof]
fn dot_prefix_step() {
    // Inductive phase: previous count <=4095, each previous partial <2^34.
    let count:usize=kani::any();let old:u64=kani::any();let raw:u64=kani::any();
    kani::assume(count<4096);kani::assume(old<=(count as u64)*((1u64<<34)-1));
    let folded=(raw&u64::from(P)).r22_add(raw>>31);
    assert!(folded<1u64<<34);
    let next=old.r22_add(folded);let next_count=count+1;
    assert!(next<=(next_count as u64)*((1u64<<34)-1));
    assert!(next<1u64<<46);
}

}
