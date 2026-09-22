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
        let u=u64::from(reduce(c*g+PP-d*h));let v=u64::from(reduce(c*h+d*g));
        Self([reduce(a*e+PP-b*f+2*u+u64::from(P)-v),
              reduce(a*f+b*e+u+2*v),
              reduce(a*g+c*e+2*PP-b*h-d*f),
              reduce(a*h+b*g+c*f+d*e)])
    }
    pub(crate) fn from_reduced_limbs(x:[u32;4])->Self{
        debug_assert!(x.iter().all(|&a|a<P));Self(x)
    }
}
