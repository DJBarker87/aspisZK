use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct DecodeLog {proof:usize,reply:Option<E>,calls:usize,original_byte:u8}
const NHF_BYTE:usize=0;
impl DecodeLog {fn decode(&mut self,bytes:&[u8])->Option<E>{
 self.calls+=1;assert!(bytes.as_ptr() as usize==self.proof+7495&&bytes.len()==32);
 assert_eq!(bytes[NHF_BYTE],self.original_byte);
 if let Some(value)=self.reply{
  let actual=((value.to_limbs()[NHF_BYTE/4]>>(8*(NHF_BYTE%4)))&255) as u8;
  kani::assume(actual==bytes[NHF_BYTE]);
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
// One immutable byte window on the ORIGINAL arbitrary full proof. The CLOSED
// decoder packet supplies the tag and all other byte laws; this cut enforces
// its selected Some-byte law and treats None conservatively. Lean assembles
// all32 observations on the SAME produced record, not independent replies.
fn wide_result(){
 let mut storage=Box::<[u8;57607]>::new_uninit();
 unsafe{kani::internal::write_any(kani::internal::Pointer::assignable(storage.as_mut_ptr()));}
 let proof=unsafe{storage.assume_init()};let semantic:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();
 let words:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(words[i]<2147483647);i+=1;}
 let reply=if kani::any(){E::from_limbs(words)}else{None};
 let slot=NHF_BYTE/4;
 let mut log=DecodeLog{proof:proof.as_ptr() as usize,reply,calls:0,original_byte:proof[7495+NHF_BYTE]};
 let result=cut(&proof[..],&semantic,&y1,&mut log);
 kani::cover!(reply.is_some());kani::cover!(reply.is_none());
 assert_eq!(log.calls,1);
 match (reply,result){
 (None,Err(e))=>assert!(e==Error::Parse),
 (Some(expected),Ok(v))=>{
  assert_eq!(v.inactive.to_limbs()[slot],expected.to_limbs()[slot]);
  assert_eq!(((v.inactive.to_limbs()[slot]>>(8*(NHF_BYTE%4)))&255) as u8,proof[7495+NHF_BYTE]);
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
