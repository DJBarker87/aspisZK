use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct DecodeLog {proof:usize,reply:Option<E>,calls:usize}
impl DecodeLog {fn decode(&mut self,bytes:&[u8])->Option<E>{self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);
 let mut canonical=true;let mut i=0;
 while i<8{let at=4*i;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);canonical=canonical&&word<2147483647;i+=1;}
 match self.reply{
  None=>kani::assume(!canonical),
  Some(value)=>{kani::assume(canonical);let limbs=value.to_limbs();let mut j=0;
   while j<8{let at=4*j;let word=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(limbs[j]==word);j+=1;}}
 }
 self.reply}}
fn cut<'a>(proof:&'a[u8],semantic:&'a[u8],y1:&'a[u8],log:&mut DecodeLog)->Result<View<'a>,Error>
{
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: log.decode(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0+usize::from(cfg!(NHF_bad_view))..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}
// Full byte/Option packet constraints are enforced in DecodeLog::decode.
// The same-input natural law is NHF_ViewDecoder.result; no success premise.
fn wide_result(){
 let proof:[u8;57607]=kani::any();let semantic:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();
 let words:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(words[i]<2147483647);i+=1;}
 let reply=if kani::any(){E::from_limbs(words)}else{None};
 let slot:usize=kani::any();kani::assume(slot<8);
 let mut log=DecodeLog{proof:proof.as_ptr() as usize,reply,calls:0};
 let result=cut(&proof,&semantic,&y1,&mut log);
 kani::cover!(reply.is_some());kani::cover!(reply.is_none());
 assert_eq!(log.calls,1);
 match (reply,result){
 (None,Err(e))=>assert!(e==Error::Parse),
 (Some(expected),Ok(v))=>{
  assert_eq!(v.inactive.to_limbs()[slot],expected.to_limbs()[slot]);
  assert!(v.variant==Variant::S2);
  assert!(v.semantic.as_ptr()==semantic.as_ptr()&&v.semantic.len()==13831);
  assert!(v.y1.as_ptr()==y1.as_ptr()&&v.y1.len()==928);
  assert!(v.round0.as_ptr()==proof[7527..].as_ptr()&&v.round0.len()==224);
  assert!(v.folded_root.unwrap().as_ptr()==proof[7751..].as_ptr());
  assert!(v.round1.as_ptr()==proof[7783..].as_ptr()&&v.round1.len()==224);
  assert!(v.final_message.as_ptr()==proof[8007..].as_ptr()&&v.final_message.len()==2048);
  assert!(v.query_bytes.is_empty());
 },_=>assert!(false),}
}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn wide_view_result(){wide_result()}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn wide_copy(){let a:[u8;32]=kani::any();let mut b:[u8;32]=kani::any();b.copy_from_slice(&a);let i:usize=kani::any();kani::assume(i<32);assert!((b[i]==a[i])!=cfg!(NHF_invert));}
