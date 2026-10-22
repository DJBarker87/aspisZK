//! Raw codec input witness, not claimed reachable from the generator.
const P:u32=0x7fff_ffff;
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct M31(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct CM31 {a:M31,b:M31}
#[derive(Clone,Copy,Debug,PartialEq,Eq)] struct QM31 {c0:CM31,c1:CM31}
#[derive(Debug,PartialEq,Eq)] enum CodecError {Length,NonZeroHigh,NonCanonical}
impl M31 {
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
pub fn compact_values(logical: &[u8], out: &mut Vec<u8>) -> Result<(), CodecError> {
    if logical.len() % 32 != 0 {
        return Err(CodecError::Length);
    }
    for v in logical.chunks_exact(32) {
        if v[16..].iter().any(|&b| b != 0) {
            return Err(CodecError::NonZeroHigh);
        }
        out.extend_from_slice(&v[..16]);
    }
    Ok(())
}
fn main() {
 let mut wide=[0u8;32];wide[..4].copy_from_slice(&P.to_le_bytes());
 let mut compact=Vec::new();
 assert_eq!(compact_values(&wide,&mut compact),Ok(()));
 assert_eq!(compact.len(),16);assert_eq!(&compact[..4],&P.to_le_bytes());
 assert_eq!(QM31::from_le_bytes(&compact),None);
 println!("codec_ok=true compact_len=16 first_limb=2147483647 canonical_qm31_parse=None");
}
