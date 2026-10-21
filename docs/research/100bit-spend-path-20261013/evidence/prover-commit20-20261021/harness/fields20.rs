// Owned state: the consumed byte prefix never borrows across recursion.
// Short suffixes follow chunks_exact(32): they are not validated.
#[cfg(any(kani,aeneas_ref))]
pub mod fields20 {
    use alloc::vec::Vec;
    use aspis_core::field::{WideExact,QM31};
    use super::Error;
    pub fn validate(row:u8,payload:Vec<u8>,value:usize)->Result<(),Error> {
        if payload.len()<32 { return Ok(()); }
        let bytes=&payload[..32];
        let x=match WideExact::from_le_bytes(bytes) { Some(x)=>x, None=>return Err(Error::NonCanonical {row,value}) };
        if x.c1()!=QM31::ZERO { return Err(Error::NonCanonical {row,value}); }
        let tail=payload[32..].to_vec();
        validate(row,tail,value+1)
    }
}
