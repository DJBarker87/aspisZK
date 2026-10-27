//! Direct calls to the shipped library. Owned references: XRf_reference.rs:28-47.
use super::*;
fn reference_check(b:&[u8])->Result<(),CodecError>{
 let mut i=0;while i<b.len()/16 {for j in 0..4 {
  let n=u32::from_le_bytes(b[16*i+4*j..16*i+4*j+4].try_into().unwrap());
  if n>=0x7fff_ffff{return Err(CodecError::NonCanonical)}
 }i+=1;}Ok(())
}
fn reference_expand(b:&[u8],o:&mut[u8])->Result<(),CodecError>{
 if b.len()%16!=0||o.len()!=2*b.len(){return Err(CodecError::Length)}
 for i in 0..b.len()/16 {for j in 0..32{o[32*i+j]=if j<16{b[16*i+j]}else{0};}}Ok(())
}
#[kani::proof] #[kani::unwind(6)] fn LPa_check_stage(){
 let b:[u8;16]=kani::any();assert_eq!(check_values(&b),reference_check(&b));
}
#[kani::proof] #[kani::unwind(6)] fn LPa_check_composition(){
 let b:[u8;32]=kani::any();let left=check_values(&b[..16]);
 let staged=left.and_then(|()|check_values(&b[16..]));assert_eq!(check_values(&b),staged);
}
#[kani::proof] #[kani::unwind(6)] fn LPa_check_tail(){
 let b:[u8;31]=kani::any();let n:usize=kani::any();kani::assume(n<=31);
 assert_eq!(check_values(&b[..n]),reference_check(&b[..n]));
}
#[kani::proof] #[kani::unwind(35)] fn LPa_expand_stage(){
 let b:[u8;16]=kani::any();let mut o:[u8;48]=kani::any();let mut r=o;
 assert_eq!(expand_values(&b,&mut o[8..40]),reference_expand(&b,&mut r[8..40]));
 let j:usize=kani::any();kani::assume(j<48);assert_eq!(o[j],r[j]);
}
#[kani::proof] #[kani::unwind(6)] fn LPa_expand_alignment(){
 let b:[u8;464]=kani::any();let mut o:[u8;928]=kani::any();let before=o;
 let n:usize=kani::any();kani::assume(n<=464&&n%16!=0);
 assert_eq!(expand_values(&b[..n],&mut o),Err(CodecError::Length));
 let j:usize=kani::any();kani::assume(j<928);assert_eq!(o[j],before[j]);
}
#[kani::proof] #[kani::unwind(35)] fn LPa_expand_indexed_stage(){
 let b:[u8;464]=kani::any();let mut o:[u8;928]=kani::any();let before=o;
 let i:usize=kani::any();kani::assume(i<29);
 assert_eq!(expand_values(&b[16*i..16*i+16],&mut o[32*i..32*i+32]),Ok(()));
 let j:usize=kani::any();kani::assume(j<928);
 assert_eq!(o[j],if j<32*i||j>=32*i+32{before[j]}else if j<32*i+16{b[16*i+j-32*i]}else{0});
}
#[kani::proof] #[kani::unwind(6)] fn LPa_expand_length(){
 let b:[u8;464]=kani::any();let mut o:[u8;928]=kani::any();let before=o;
 let n:usize=kani::any();kani::assume(n<=464&&n%16==0);
 let m:usize=kani::any();kani::assume(m<=928&&m!=2*n);
 assert_eq!(expand_values(&b[..n],&mut o[..m]),Err(CodecError::Length));
 let j:usize=kani::any();kani::assume(j<928);assert_eq!(o[j],before[j]);
}
