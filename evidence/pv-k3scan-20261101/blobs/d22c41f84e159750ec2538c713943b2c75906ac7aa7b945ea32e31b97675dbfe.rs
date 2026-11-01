#![allow(dead_code,non_snake_case)]
const P:u32=0x7fffffff;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct M31(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
mod ct {
pub fn is_zero(a: u32) -> bool {
    a == 0
}
}
impl M31 {
pub fn is_zero(self) -> bool { ct::is_zero(self.0) }
}
impl CM31 { #[inline(always)] pub fn is_zero(self) -> bool { self.a.is_zero() & self.b.is_zero() } }
impl QM31 { #[inline(always)] pub fn is_zero(self) -> bool { self.c0.is_zero() & self.c1.is_zero() } }
impl WideExact {
pub fn is_zero(self) -> bool { self.c0.is_zero() & self.c1.is_zero() }
pub const LIMB_COUNT:usize=8;
pub const BYTE_LEN:usize=32;
pub fn from_limbs(limbs: [u32; Self::LIMB_COUNT]) -> Option<Self> {
        if limbs[0] >= P || limbs[1] >= P || limbs[2] >= P || limbs[3] >= P
            || limbs[4] >= P || limbs[5] >= P || limbs[6] >= P || limbs[7] >= P {
            return None;
        }
        let [a, b, c, d, e, f, g, h] = limbs;
        Some(Self {
            c0: QM31 {
                c0: CM31 {
                    a: M31(a),
                    b: M31(b),
                },
                c1: CM31 {
                    a: M31(c),
                    b: M31(d),
                },
            },
            c1: QM31 {
                c0: CM31 {
                    a: M31(e),
                    b: M31(f),
                },
                c1: CM31 {
                    a: M31(g),
                    b: M31(h),
                },
            },
        })
    }
pub const fn to_limbs(self) -> [u32; Self::LIMB_COUNT] {
        [
            self.c0.c0.a.0,
            self.c0.c0.b.0,
            self.c0.c1.a.0,
            self.c0.c1.b.0,
            self.c1.c0.a.0,
            self.c1.c0.b.0,
            self.c1.c1.a.0,
            self.c1.c1.b.0,
        ]
    }
pub fn from_le_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != Self::BYTE_LEN {
            return None;
        }
        let limbs = [
            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]),
            u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]),
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            u32::from_le_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]),
            u32::from_le_bytes([bytes[16], bytes[17], bytes[18], bytes[19]]),
            u32::from_le_bytes([bytes[20], bytes[21], bytes[22], bytes[23]]),
            u32::from_le_bytes([bytes[24], bytes[25], bytes[26], bytes[27]]),
            u32::from_le_bytes([bytes[28], bytes[29], bytes[30], bytes[31]]),
        ];
        Self::from_limbs(limbs)
    }
pub fn to_le_bytes(self) -> [u8; Self::BYTE_LEN] {
        let mut bytes = [0; Self::BYTE_LEN];
        for (chunk, limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs()) {
            chunk.copy_from_slice(&limb.to_le_bytes());
        }
        bytes
    }
}

fn q(x:[u32;4])->QM31 {QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
#[cfg(kani)] mod PV_L2_zero {
use super::*;
#[kani::proof] fn m31_zero(){let x:u32=kani::any();assert_eq!(M31(x).is_zero(),x==0);}
#[kani::proof] fn cm31_zero(){let x:[u32;2]=kani::any();assert_eq!(CM31{a:M31(x[0]),b:M31(x[1])}.is_zero(),x==[0;2]);}
#[kani::proof] fn qm31_zero(){let x:[u32;4]=kani::any();assert_eq!(q(x).is_zero(),x==[0;4]);}
#[kani::proof] fn wide_zero(){let x:[u32;8]=kani::any();let w=WideExact{c0:q([x[0],x[1],x[2],x[3]]),c1:q([x[4],x[5],x[6],x[7]])};assert_eq!(w.is_zero(),(0..8).all(|i|x[i]==0));}
#[kani::proof] #[kani::unwind(10)] fn limbs_success_pointwise(){let x:[u32;8]=kani::any();if let Some(w)=WideExact::from_limbs(x){for i in 0..8{assert_eq!(w.to_limbs()[i],x[i]);}for v in x{assert!(v<P);}}}
#[kani::proof] #[kani::unwind(10)] fn limbs_complete(){let x:[u32;8]=kani::any();for v in x{kani::assume(v<P);}assert!(WideExact::from_limbs(x).is_some());}
#[kani::proof] #[kani::unwind(10)] fn limbs_zero(){let x:[u32;8]=kani::any();if let Some(w)=WideExact::from_limbs(x){assert_eq!(w.is_zero(),(0..8).all(|i|x[i]==0));}}
#[kani::proof] #[kani::unwind(34)] fn bytes_success(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){assert_eq!(w.to_le_bytes(),b);}}
#[kani::proof] #[kani::unwind(10)] fn bytes_canonical(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){for v in w.to_limbs(){assert!(v<P);}}}
#[kani::proof] #[kani::unwind(34)] fn bytes_zero(){let b:[u8;32]=kani::any();if let Some(w)=WideExact::from_le_bytes(&b){assert_eq!(w.is_zero(),b==[0;32]);}}
#[kani::proof] #[kani::unwind(10)] fn wrong_length(){let b:[u8;33]=kani::any();let n:usize=kani::any();kani::assume(n<=33&&n!=32);assert!(WideExact::from_le_bytes(&b[..n]).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_0(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[0]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_1(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[1]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_2(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[2]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_3(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[3]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_4(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[4]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_5(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[5]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_6(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[6]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn reject_limb_7(){let mut x:[u32;8]=kani::any();let bad:u32=kani::any();kani::assume(bad>=P);x[7]=bad;assert!(WideExact::from_limbs(x).is_none());}
#[kani::proof] #[kani::unwind(10)] fn nonzero_limb(){let x:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8&&x[i]!=0);if let Some(w)=WideExact::from_limbs(x){assert!(!w.is_zero());}}
}
