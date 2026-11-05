use super::*;
use crate::{KMX_copy_nonoverlapping,KMX_copy_from_slice};
struct Log<'a,const C:usize>{bytes:&'a[u8],proof:&'a[u8],public:&'a[u8],replies:[[u8;32];3],header_bad:bool,calls:usize,headers:usize,byte:usize}
impl<'a,const C:usize> Log<'a,C>{
 fn reserved(&mut self,b:&[u8])->bool{let mut pointer=b.as_ptr() as usize;if cfg!(NIL_invert)&&C==0{pointer^=1;}assert_eq!(pointer,self.bytes[11..16].as_ptr() as usize);assert_eq!(b.len(),5);self.headers+=1;let value=if cfg!(NIL_invert)&&C==13{!self.header_bad}else{self.header_bad};if C==13{assert_eq!(value,self.header_bad);}value}
 fn digest(&mut self,parts:&[&[u8]])->[u8;32]{let c=self.calls;assert!(c<3);let mut pointer=parts[if c==2{1}else{0}].as_ptr() as usize;
 if cfg!(NIL_invert)&&((C==2&&c==0)||(C==4&&c==1)){pointer^=1;}
 match c{0=>{assert_eq!(parts.len(),1);assert_eq!(pointer,self.proof.as_ptr() as usize);assert_eq!(parts[0].len(),self.proof.len());},1=>{assert_eq!(parts.len(),1);assert_eq!(pointer,self.public.as_ptr() as usize);assert_eq!(parts[0].len(),self.public.len());},_=>{assert_eq!(parts.len(),2);assert_eq!(pointer,self.bytes.as_ptr() as usize);assert_eq!(parts[1].len(),self.bytes.len()-32);let tag=parts[0];let mut byte=tag[self.byte%22];if cfg!(NIL_invert)&&C==6{byte^=1;}assert_eq!(tag.len(),22);assert_eq!(byte,b"UNPROVED:R1:checkpoint"[self.byte%22]);}}
 self.calls+=1;
 if C>=10&&C<=12&&c==C-10{if cfg!(NIL_invert){assert_eq!(self.calls,c);}else{assert_eq!(self.calls,c+1);}kani::assume(false);}
 let mut out=self.replies[c];if cfg!(NIL_invert)&&((C==1&&c==0)||(C==3&&c==1)||(C==5&&c==2)){out[self.byte]^=1;}
 assert_eq!(out[self.byte],self.replies[c][self.byte]);out
 }
}
fn prefix<const C:usize>(bytes:&[u8],proof:&[u8],public:&[u8],v:Variant,log:&mut Log<C>)->Result<(usize,usize),Error>{
    if bytes.len()!=checkpoint_size(v)||&bytes[..8]!=b"R1P2CKP2"||bytes[8]!=v.tag()||bytes[9]>22||bytes[10]!=1||log.reserved(&bytes[11..16]) {return Err(Error::Checkpoint);}
    let end=bytes.len()-32;
    if bytes[16..48]!=log.digest(&[proof])||bytes[48..80]!=log.digest(&[public])||bytes[end..]!=log.digest(&[b"UNPROVED:R1:checkpoint",&bytes[..end]]) {return Err(Error::Checkpoint);}
Ok((end,bytes[9] as usize))}
fn check<const C:usize>(){
 let bytes:[u8;1768]=kani::any();let proof:[u8;57607]=kani::any();let public:[u8;688]=kani::any();let replies:[[u8;32];3]=kani::any();let header_bad:bool=kani::any();let byte:usize=kani::any();kani::assume(byte<32);
 let early=bytes[..8]==*b"R1P2CKP2"&&bytes[8]==2&&bytes[9]<=22&&bytes[10]==1;
 let valid=early&&!header_bad;let r0=replies[0]==bytes[16..48];let r1=replies[1]==bytes[48..80];let r2=replies[2]==bytes[1736..];
 let mut log=Log::<C>{bytes:&bytes,proof:&proof,public:&public,replies,header_bad,calls:0,headers:0,byte};
 let mut result=prefix(&bytes,&proof,&public,Variant::S2,&mut log);
 if cfg!(NIL_invert){if C==7{result=match result{Ok(_)=>Err(Error::Checkpoint),Err(_)=>Ok((1736,0))};}if C==8{log.calls^=1;}if C==9{if let Ok((end,next))=result{result=Ok((end,next^1));}}}
 let expected_calls=if !valid{0}else if !r0{1}else if !r1{2}else{3};
 assert_eq!(log.calls,expected_calls);assert_eq!(log.headers,if early{1}else{0});
 match result{Ok((end,next))=>{assert!(valid&&r0&&r1&&r2);assert_eq!(end,1736);assert_eq!(next,bytes[9] as usize);assert!(next<=22);},Err(error)=>{assert_eq!(error,Error::Checkpoint);assert!(!(valid&&r0&&r1&&r2));}}
}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet0(){check::<0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet0_renamed(){check::<0>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet1(){check::<1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet1_renamed(){check::<1>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet2(){check::<2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet2_renamed(){check::<2>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet3(){check::<3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet3_renamed(){check::<3>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet4(){check::<4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet4_renamed(){check::<4>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet5(){check::<5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet5_renamed(){check::<5>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet6(){check::<6>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet6_renamed(){check::<6>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet7(){check::<7>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet7_renamed(){check::<7>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet8(){check::<8>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet8_renamed(){check::<8>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet9(){check::<9>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet9_renamed(){check::<9>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet10(){check::<10>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet10_renamed(){check::<10>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet11(){check::<11>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet11_renamed(){check::<11>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet12(){check::<12>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet12_renamed(){check::<12>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet13(){check::<13>();}
#[kani::proof]
#[kani::unwind(36)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn prefix_facet13_renamed(){check::<13>();}
