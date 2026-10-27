use super::*;
fn expand_valid<const N:usize,const O:usize>() {
 let bytes:[u8;N]=kani::any();let mut out:[u8;O]=kani::any();let mut expected=out;
 let actual=compact::expand_values(&bytes,&mut out);let model=XRf_reference_expand_values(&bytes,&mut expected);
 assert_eq!(actual,model);let i:usize=kani::any();kani::assume(i<O);assert_eq!(out[i],expected[i]);
}
// One exact 16-byte stage, including both halves and every arbitrary byte.
#[kani::proof] #[kani::unwind(35)] fn XRf_expand_one(){expand_valid::<16,32>()}
// Caller supplies a destination sub-slice, with live bytes on both sides.
#[kani::proof] #[kani::unwind(35)] fn XRf_expand_frame(){
 let bytes:[u8;16]=kani::any();let mut out:[u8;48]=kani::any();let before=out;
 assert_eq!(compact::expand_values(&bytes,&mut out[8..40]),Ok(()));
 let i:usize=kani::any();kani::assume(i<48);
 assert_eq!(out[i],if i<8||i>=40 {before[i]} else if i<24 {bytes[i-8]} else {0});
}
#[kani::proof] #[kani::unwind(8)] fn XRf_expand_bad_multiple(){
 let bytes:[u8;33]=kani::any();let n:usize=kani::any();kani::assume(n<=33&&n%16!=0);
 let mut out:[u8;66]=kani::any();let old=out;let m:usize=kani::any();kani::assume(m<=66);
 assert_eq!(compact::expand_values(&bytes[..n],&mut out[..m]),Err(compact::CodecError::Length));
 let i:usize=kani::any();kani::assume(i<66);assert_eq!(out[i],old[i]);
}
#[kani::proof] #[kani::unwind(8)] fn XRf_expand_bad_output(){
 let bytes:[u8;32]=kani::any();let mut out:[u8;65]=kani::any();let old=out;
 let n:usize=kani::any();kani::assume(n<=32&&n%16==0);let m:usize=kani::any();kani::assume(m<=65&&m!=2*n);
 assert_eq!(compact::expand_values(&bytes[..n],&mut out[..m]),Err(compact::CodecError::Length));
 let i:usize=kani::any();kani::assume(i<65);assert_eq!(out[i],old[i]);
}
fn check_staged<const N:usize>() {
 let bytes:[u8;N]=kani::any();let a=compact::check_values(&bytes);
 let split=16;let l=compact::check_values(&bytes[..split]);
 let b=match l {Err(e)=>Err(e),Ok(())=>compact::check_values(&bytes[split..])};assert_eq!(a,b);
}
#[kani::proof] #[kani::unwind(10)] fn XRf_check_two(){check_staged::<32>()}
#[kani::proof] #[kani::unwind(10)] fn XRf_check_two_tail(){check_staged::<47>()}
#[kani::proof] #[kani::unwind(10)] fn XRf_check_canonical(){
 let limbs:[u32;4]=kani::any();let mut bytes=[0;16];for j in 0..4 {bytes[4*j..4*j+4].copy_from_slice(&limbs[j].to_le_bytes())}
 assert_eq!(compact::check_values(&bytes).is_ok(),limbs.iter().all(|x|*x<0x7fff_ffff));
}
#[kani::proof] #[kani::unwind(10)] fn XRf_check_rejected_prefix(){
 let bytes:[u8;48]=kani::any();kani::assume(compact::check_values(&bytes[..16]).is_err());
 assert_eq!(compact::check_values(&bytes),Err(compact::CodecError::NonCanonical));
}
#[kani::proof] #[kani::unwind(10)] fn XRf_check_tail_ignored(){
 let bytes:[u8;47]=kani::any();let n:usize=kani::any();kani::assume(n>=32&&n<=47);
 assert_eq!(compact::check_values(&bytes[..n]),compact::check_values(&bytes[..32]));
}
#[kani::proof] #[kani::unwind(35)] fn XRf_expand_chunk_composition(){
 let bytes:[u8;32]=kani::any();let mut whole:[u8;64]=kani::any();let mut staged=whole;
 let r=compact::expand_values(&bytes,&mut whole);
 let a=compact::expand_values(&bytes[..16],&mut staged[..32]);let b=compact::expand_values(&bytes[16..],&mut staged[32..]);
 assert_eq!(r,Ok(()));assert_eq!(a,Ok(()));assert_eq!(b,Ok(()));
 let i:usize=kani::any();kani::assume(i<64);assert_eq!(whole[i],staged[i]);
}
