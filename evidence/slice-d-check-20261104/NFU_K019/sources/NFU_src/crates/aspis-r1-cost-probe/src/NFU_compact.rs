use super::*;
#[kani::proof] #[kani::unwind(6)]
fn check_one(){let c:[u8;16]=kani::any();let result=check_values(&c);let valid=(0..4).all(|i|u32::from_le_bytes([c[4*i],c[4*i+1],c[4*i+2],c[4*i+3]])<0x7fffffff);assert!((result==if valid{Ok(())}else{Err(CodecError::NonCanonical)}) != cfg!(NFU_invert));}
