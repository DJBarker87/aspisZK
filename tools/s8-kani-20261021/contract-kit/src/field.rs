// Literal frozen field items; only contract attributes/Arbitrary derives added.
pub const P:u32=0x7fffffff;
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub struct M31(pub u32);
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
#[derive(Clone,Copy,PartialEq,Eq,Debug,Default)]
#[cfg_attr(kani,derive(kani::Arbitrary))]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
fn reduce_u64(x: u64) -> u32 {
    // reference_canonical: two mask/shift folds bring any u64 to at most
    // P+3, then one conditional subtract canonicalizes. Supporting the full
    // u64 range lets four maximal M31 products be accumulated before one
    // reduction: 4*(P-1)^2 < 2^64.
    let x = (x & P as u64) + (x >> 31u32);
    let x = (x & P as u64) + (x >> 31u32);
    let x = x as u32;
    if x >= P {
        x - P
    } else {
        x
    }
}
impl M31 {
#[cfg_attr(kani,kani::ensures(|r:&M31| r.0==crate::reduce_spec(value)))]
pub fn reduce_u64(value: u64) -> M31 {
        M31(reduce_u64(value))
    }
pub fn from_le_bytes(bytes: [u8; 4]) -> Option<M31> {
        let v = u32::from_le_bytes(bytes);
        if v >= P {
            None
        } else {
            Some(M31(v))
        }
    }
}
impl CM31 {
pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31> {
        let a_bytes = match bytes[0..4].try_into() {
            Ok(value) => value,
            Err(_) => return None,
        };
        let a = M31::from_le_bytes(a_bytes)?;
        let b_bytes = match bytes[4..8].try_into() {
            Ok(value) => value,
            Err(_) => return None,
        };
        let b = M31::from_le_bytes(b_bytes)?;
        Some(CM31 { a, b })
    }
}
impl QM31 {
pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31> {
        let c0 = CM31::from_le_bytes(&bytes[0..8])?;
        let c1 = CM31::from_le_bytes(&bytes[8..16])?;
        Some(QM31 { c0, c1 })
    }
}
