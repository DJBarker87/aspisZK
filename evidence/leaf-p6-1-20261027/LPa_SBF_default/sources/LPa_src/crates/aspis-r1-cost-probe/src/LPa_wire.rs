//! Direct private-library calls; safe references correspond to XRg_reference.rs.
use super::*;
pub(crate) fn prefix<'a>(framed:&'a[u8])->Prefix<'a>{Prefix{c1_root:&[0;32],records:[framed;27]}}
fn reference_validate(row:u8,b:&[u8])->Result<(),Error>{
 for i in 0..b.len()/32 {for j in 0..8 {
  let x=u32::from_le_bytes(b[32*i+4*j..32*i+4*j+4].try_into().unwrap());
  if x>=0x7fff_ffff||(j>=4&&x!=0){return Err(Error::NonCanonical{row,value:i})}
 }}Ok(())
}
fn reference_decode<const N:usize>(row:u8,b:&[u8],offset:usize)->Result<[QM31;N],Error>{
 if row<14{return Err(Error::InvalidRow)}
 let start=offset.checked_mul(32).ok_or(Error::Length{row})?;
 let end=start.checked_add(N.checked_mul(32).ok_or(Error::Length{row})?).ok_or(Error::Length{row})?;
 let payload=&b[5..];if end>payload.len(){return Err(Error::Length{row})}
 let mut out=[QM31::ZERO;N];for i in 0..N {
  for j in 0..4 {let x=u32::from_le_bytes(payload[start+32*i+4*j..start+32*i+4*j+4].try_into().unwrap());
   if x>=0x7fff_ffff{return Err(Error::NonCanonical{row,value:offset+i})}
  }out[i]=QM31::from_le_bytes(&payload[start+32*i..start+32*i+16]).unwrap();
 }Ok(out)
}
#[kani::proof] #[kani::unwind(10)] fn LPa_decode_stage(){
 let b:[u8;37]=kani::any();let row:u8=kani::any();let offset:usize=kani::any();
 assert_eq!(ValidatedRecord{row,framed:&b}.decode_k::<1>(offset),reference_decode::<1>(row,&b,offset));
}
#[kani::proof] #[kani::unwind(10)] fn LPa_decode_guard29(){
 let b:[u8;37]=kani::any();let row:u8=kani::any();let offset:usize=kani::any();
 assert_eq!(ValidatedRecord{row,framed:&b}.decode_k::<29>(offset),reference_decode::<29>(row,&b,offset));
}
#[kani::proof] #[kani::unwind(10)] fn LPa_validate_stage(){
 let b:[u8;32]=kani::any();let row:u8=kani::any();assert_eq!(validate_record_fields(row,&b),reference_validate(row,&b));
}
#[kani::proof] #[kani::unwind(10)] fn LPa_validate_composition(){
 let b:[u8;64]=kani::any();let row:u8=kani::any();
 let staged=validate_record_fields(row,&b[..32]).and_then(|()|validate_record_fields(row,&b[32..]).map_err(|e|match e{Error::NonCanonical{row,value}=>Error::NonCanonical{row,value:value+1},e=>e}));
 assert_eq!(validate_record_fields(row,&b),staged);
}
