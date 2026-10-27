//! Owned reference: XRf_reference_echeck. Shipped echeck is called directly.
use super::*;
fn reference(b:&[u8],k:bool)->Result<(),Error>{
 for i in 0..b.len()/32 {for j in 0..8 {
  let x=u32::from_le_bytes(b[32*i+4*j..32*i+4*j+4].try_into().unwrap());
  if x>=0x7fff_ffff||(k&&j>=4&&x!=0){return Err(Error::Parse)}
 }}Ok(())
}
#[kani::proof] #[kani::unwind(10)] fn LPa_echeck_stage(){
 let b:[u8;32]=kani::any();let k:bool=kani::any();assert_eq!(echeck(&b,k),reference(&b,k));
}
#[kani::proof] #[kani::unwind(10)] fn LPa_echeck_tail(){
 let b:[u8;63]=kani::any();let n:usize=kani::any();kani::assume(n<=63);let k:bool=kani::any();
 assert_eq!(echeck(&b[..n],k),reference(&b[..n],k));
}
#[kani::proof] #[kani::unwind(10)] fn LPa_echeck_composition(){
 let b:[u8;64]=kani::any();let k:bool=kani::any();
 assert_eq!(echeck(&b,k),echeck(&b[..32],k).and_then(|()|echeck(&b[32..],k)));
}
